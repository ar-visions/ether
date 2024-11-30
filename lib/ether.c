#include <llvm-c/DebugInfo.h>
#include <llvm-c/Core.h>
#include <llvm-c/ExecutionEngine.h>
#include <llvm-c/Target.h>
#include <llvm-c/Analysis.h>
#include <llvm-c/TargetMachine.h>
#include <llvm-c/BitWriter.h>
#include <clang-c/Index.h>

typedef LLVMMetadataRef LLVMScope;

#include <import>
#include <ether>

// def -> base for change from type to member (member has model 
//#define ecall(M, ...) ether_##M(e, ## __VA_ARGS__) # .cms [ c-like module in silver ]

#define emodel(N)     ({            \
    member  m = lookup(e, string(N), null); \
    model mdl = m ? m->mdl : null;  \
    mdl;                            \
})

#define emember(M, N) member(mod, e, name, str(N), mdl, M);

#define value(m,vr) (e->no_build) ? \
    node(mod, e, mdl, emodel("void")) : \
    node(mod, e, value, vr, mdl, m)

// Convert a hex color string (#RRGGBB) to ANSI escape code
void generate_ansi_from_hex(const char *hex_color) {
    if (hex_color[0] != '#' || strlen(hex_color) != 7) {
        printf("Invalid color format. Use #RRGGBB.\n");
        return;
    }

    // Extract RGB values from the hex string
    int r = (int)strtol(&hex_color[1], NULL, 16) >> 16;        // Red
    int g = ((int)strtol(&hex_color[1], NULL, 16) & 0xFF00) >> 8; // Green
    int b = (int)strtol(&hex_color[1], NULL, 16) & 0xFF;         // Blue

    // Print the ANSI escape code
    printf("\033[38;2;%d;%d;%dm", r, g, b);
}

// Reset ANSI colors
void reset_ansi_color() {
    printf("\033[0m");
}

member ether_lookup(ether e, object name, AType omit);

member ether_push_model(ether e, model mdl) {
    bool is_func = instanceof(mdl, function) != null;
    member mem   = member(
        mod, e, mdl, mdl, name, mdl->name,
        is_func,  is_func,
        is_type, !is_func);
    if (strcmp(mdl->name->chars, "A") == 0) {
        int test = 2;
        test += 2;
    }
    set(e->top->members, str(mdl->name->chars), mem);
    return mem;
}

void ether_push_member(ether e, member mem) {
    if (mem->registered)
        return;
    mem->registered = true;
    map members = e->top->members;
    string  key = str(mem->name->chars);
    array  list = get(members, key);
    if (!list) {
        list = array(32);
        set(members, key, list);
    }
    set(members, str(mem->name->chars), mem);
    set_model(mem, mem->mdl);
}

#define no_target null

AType model_primitive(model mdl) {
    model src = mdl->src;
    while (instanceof(src, model)) {
        src = src->src;
    }
    return isa(src);
}
bool is_bool     (model f) { return f->src && isa(f->src) == typeid(bool); }
bool is_float    (model f) { return f->src && isa(f->src) == typeid(f32);  }
bool is_double   (model f) { return f->src && isa(f->src) == typeid(f64);  }
bool is_realistic(model f) { return f->src && isa(f->src)->traits & A_TRAIT_REALISTIC; }
bool is_integral (model f) { return f->src && isa(f->src)->traits & A_TRAIT_INTEGRAL;  }
bool is_signed   (model f) { return f->src && isa(f->src)->traits & A_TRAIT_SIGNED;    }
bool is_unsigned (model f) { return f->src && isa(f->src)->traits & A_TRAIT_UNSIGNED;  }
bool is_primitive(model f) {
    return f->src && isa(f->src)->traits & A_TRAIT_PRIMITIVE;
}

bool is_void     (model f) {
    return f ? f->size == 0 : false;
}

bool is_generic  (model f) {
    return f->src == typeid(object);
}

bool is_record   (model f) {
    return isa(f) == typeid(structure) || 
           isa(f) == typeid(class);
}

bool is_class    (model f) {
    return isa(f) == typeid(class);
}

bool is_struct   (model f) {
    return isa(f) == typeid(structure);
}

bool is_ref      (model f) {
    if (f->ref != reference_value)
        return true;
    model src = f->src;
    while (instanceof(src, model)) {
        src = src->src;
        if (f->ref != reference_value)
            return true;
    }
    return false;
}

void init() {
    LLVMInitializeNativeTarget();
    LLVMInitializeNativeAsmPrinter();
    LLVMInitializeNativeAsmParser();

    log("LLVM-Version", "%d.%d.%d",
        LLVM_VERSION_MAJOR,
        LLVM_VERSION_MINOR,
        LLVM_VERSION_PATCH);
}

module_init(init);

void print_ctx(ether e, string msg) {
    string res = string(alloc, 32);
    for (int i = 0; i < len(e->lex); i++) {
        model ctx = e->lex->elements[i];
        if (res->len)
            append(res, "/");
        append(res, ctx->name->chars);
    }
    print("%o: %o", res, msg);
}

#define print_context(msg, ...) print_ctx(e, format(msg, ## __VA_ARGS__))

void model_process_finalize(model mdl) { // nobody calls finalize except us, here
    ether e = mdl->mod;
    if (mdl->finalized) return;
    mdl->finalized = true;
    preprocess(mdl);
    function fn = instanceof(mdl, function);
    if (mdl->process) {
        if (fn && fn->record) push(e, fn->record);
        push(e, mdl);
        class cl = fn ? fn->record : null;
        if (cl) pairs(cl->members, m) log("class", "member: %o: %o", cl->name, m->key);
        invoke(mdl->process, mdl);
        pop(e);
        if (fn && fn->record) pop(e);
    }
    finalize(mdl); /// 'process' is too coupled in function
    mdl->process = null;
}

/// 'record' does things with this, as well as 'function'
void model_finalize(model mdl) {
}

void model_preprocess(model mdl) {
}

string model_cast_string(model mdl) {
    if (mdl->name) return mdl->name;
    int depth = 0;
    while (mdl->src) {
        if (mdl->ref != reference_value)
            depth++;
        mdl = mdl->src;
        if (mdl->name) {
            if (depth == 1)
                return format("ref %o", mdl->name);
            else {
                string res = format("%o", mdl->name);
                for (int i = 0; i < depth; i++)
                    append(res, "*");
                return res;
            }
        }
    }
    fault("could not get name for model");
    return null;
}

i64 model_cmp(model mdl, model b) {
    return mdl->type == b->type ? 0 : -1;
}

void model_init(model mdl) {
    ether  e = mdl->mod;

    if (mdl->name && instanceof(mdl->name, string)) {
        string n = mdl->name;
        mdl->name = token(chars, cstring(n), source, e ? e->source : null, line, 1);
    }

    if (!mdl->members)
        mdl->members = map(hsize, 32);

    if (!mdl->src)
        return;

    /// narrow down type traits
    string name = cast(string, mdl);
    model mdl_src = mdl;
    if (isa(mdl_src) == typeid(model)) {
        while (isa(mdl_src) == typeid(model) && mdl_src->src) {
            if (mdl_src->ref)
                break;
            mdl_src = mdl_src->src;
        }
    }

    AType type = isa(mdl_src);

    if (type->traits & A_TRAIT_PRIMITIVE || type == typeid(object)) {
        if (type == typeid(f32))
            mdl->type = LLVMFloatType();
        else if (type == typeid(f64))
            mdl->type = LLVMDoubleType();
        else if (type == typeid(f128))
            mdl->type = LLVMFP128Type();
        else if (type == typeid(none))
            mdl->type = LLVMVoidType  ();
        else if (type == typeid(bool))
            mdl->type = LLVMInt1Type  ();
        else if (type == typeid(i8)  || type == typeid(u8))
            mdl->type = LLVMInt8Type();
        else if (type == typeid(i16) || type == typeid(u16))
            mdl->type = LLVMInt16Type();
        else if (type == typeid(i32) || type == typeid(u32))
            mdl->type = LLVMInt32Type();
        else if (type == typeid(i64) || type == typeid(u64))
            mdl->type = LLVMInt64Type();
        else
            fault("unsupported primitive: %s", type->name);

        if (mdl->type && mdl->type != LLVMVoidType())
            mdl->debug = LLVMDIBuilderCreateBasicType(
                e->dbg_builder,                // Debug info builder
                type->name,                    // Name of the primitive type (e.g., "int32", "float64")
                strlen(type->name),            // Length of the name
                LLVMABISizeOfType(e->target_data, mdl->type) * 8, // Size in bits (e.g., 32 for int, 64 for double)
                type->name[0] == 'f' ? 0x04 : 0x05, // switching based on f float or u/i int (on primitives)
                0);
    } else {
        // we still need static array (use of integral shape), aliases

        // can be a class, structure, function
        if (type == typeid(model)) {
            /// now we should handle the case 
            model  src = mdl->src;
            AType src_type = isa(src);
            /// this is a reference, so we create type and debug based on this
            u64 ptr_sz = LLVMPointerSize(e->target_data);
            mdl->type  = LLVMPointerType(
                src->type == LLVMVoidType() ? LLVMInt8Type() : src->type, 0);
            model src_name = mdl->name ? mdl : (model)mdl->src;
            if (src_name->name)
                mdl->debug = LLVMDIBuilderCreatePointerType(e->dbg_builder, src->debug,
                    ptr_sz * 8, 0, 0, name->chars, len(name));
        } else if (instanceof(mdl_src, record)) {
            record rec = mdl_src;
            mdl->type  = rec->type;
            mdl->debug = rec->debug;
        } else if (type == typeid(function)) {
            function fn = mdl_src;
            mdl->type  = fn->type;
            mdl->debug = fn->debug;
        } else if (type == typeid(ether))
            return;
        else if (type != typeid(ether)) {
            fault("unsupported model type: %s", type->name);
        }
    }
    if (mdl->type && mdl->type != LLVMVoidType()) { /// we will encounter errors with aliases to void
        LLVMTypeRef type = mdl->type;
        /// todo: validate: when referencing these, we must find src where type != null
        mdl->size      = LLVMABISizeOfType     (mdl->mod->target_data, type);
        mdl->alignment = LLVMABIAlignmentOfType(mdl->mod->target_data, type);
    }
    if (instanceof(mdl, record)) {
        mdl->scope = mdl->debug; // set this in record manually when debug is set
    } else if (!mdl->scope)
        mdl->scope = e->scope;
}

model model_alias(model src, object name, reference r, array shape);

/// we allocate all pointer models this way
model model_pointer(model mdl) {
    if (!mdl->ptr)
        mdl->ptr = model(mod, mdl->mod, name, mdl->name, ref, reference_pointer,
                        src, mdl, type, mdl->type);
    return mdl->ptr;
}

void statements_init(statements st) {
    ether e = st->mod;
    AType atop = isa(e->top);
    st->scope = LLVMDIBuilderCreateLexicalBlock(e->dbg_builder, e->top->scope, e->file, 1, 0);
}

void ether_eprint_node(ether e, node n) {
    member printf_fn  = lookup(e, string("printf"), null);
    model  mdl_cstr   = lookup(e, string("cstr"),   null);
    model  mdl_symbol = lookup(e, string("symbol"), null);
    model  mdl_i32    = lookup(e, string("i32"),    null);
    model  mdl_i64    = lookup(e, string("i64"),    null);
    cstr fmt = null;
    if (n->mdl == mdl_cstr || n->mdl == mdl_symbol) {
        fmt = "%s";
    } else if (n->mdl == mdl_i32) {
        fmt = "%i";
    } else if (n->mdl == mdl_i64) {
        fmt = "%lli";
    }
    verify(fmt, "eprint_node: unsupported model: %o", n->mdl->name);
    fn_call(e, printf_fn,
        array_of(null, operand(e, string(fmt)), n, null));
}

#define eprint(...) ether_eprint(__VA_ARGS__)

void ether_eprint(ether e, symbol format, ...) {
    va_list args;
    va_start(args, format);

    int   format_len  = strlen(format);
    int   pos         = 0;
    int   max_arg     = -1;
    char* buf         = calloc(1, format_len + 1);
    char* ptr         = format;
    array schema      = array(32);
    char* start       = null;

    while (*ptr) {
        if (*ptr == '{' && isdigit(*(ptr + 1))) {
            if (start) {
                int block_sz = ((sz)ptr - (sz)start);
                memcpy(buf, start, block_sz);
                buf[block_sz] = 0;
                push(schema, string(buf));
            }
            // Parse the number inside {N}
            int i = 0;
            ptr++;
            while (isdigit(*ptr)) {
                buf[i++] = *ptr++;
            }
            buf[i] = '\0';
            i32 n = atoi(buf);
            if (max_arg < n)
                max_arg = n;
            push(schema, A_i32(n));
            verify(*ptr == '}', "expected }");
            ptr++;
            start = ptr;
        } else if (!start) {
            start = ptr;
        }
        ptr++;
    }

    if (start && start[0]) {
        int block_sz = ((sz)ptr - (sz)start);
        memcpy(buf, start, block_sz);
        buf[block_sz] = 0;
        push(schema, string(buf));
    }

    node *arg_nodes = calloc(max_arg + 1, sizeof(i32));
    for (int i = 0; i < max_arg; i++)
        arg_nodes[i] = va_arg(args, node);
    
    string res = string(alloc, 32);
    model mdl_cstr = lookup(e, string("cstr"), null);
    model mdl_i32  = lookup(e, string("i32"), null);
    each(schema, object, obj) {
        node n = instanceof(obj, node);
        if (n) {
            eprint_node(e, n);
        } else {
            string s = instanceof(obj, string);
            verify(s, "invalid type data");
            node n_str = operand(e, s);
            eprint_node(e, n_str);
        }
    }

    va_end(args);
    free(arg_nodes);
    free(buf);
}



member ether_evar(ether e, model mdl, string name) {
    node   a =  create(e, mdl, null);
    member m = member(mod, e, name, name, mdl, mdl);
    push_member(e, m);
    assign(e, m, a, OPType__assign);
    return m;
}

void code_init(code c) {
    function fn = context_model(c->mod, typeid(function));
    c->block = LLVMAppendBasicBlock(fn->value, c->label);
}

void code_select(code c) {
    LLVMPositionBuilderAtEnd(c->mod->builder, c->block);
}

void ether_ecmp(ether e, node l, comparison comp, node r, code lcode, code rcode) {
    node load_l = load(e, l);
    node load_r = load(e, l);
    LLVMValueRef cond = LLVMBuildICmp(
        e->builder, (LLVMIntPredicate)comp, load_l->value, load_r->value, "cond");
    LLVMBuildCondBr(e->builder, cond, lcode->block, rcode->block);
}

node ether_eelement(ether e, node array, object index) {
    node i = operand(e, index);
    node element_v = value(e, LLVMBuildInBoundsGEP2(
        e->builder, array->mdl->type, array->value, &i->value, 1, "eelement"));
    return load(e, element_v);
}

void ether_einc(ether e, node v, num amount) {
    node lv = load(e, v);
    LLVMValueRef one = LLVMConstInt(LLVMInt64Type(), amount, 0);
    LLVMValueRef nextI = LLVMBuildAdd(e->mod->builder, lv->value, one, "nextI");
    LLVMBuildStore(e->mod->builder, nextI, v->value);
}

void ether_ebranch(ether e, code c) {
    LLVMBuildBr(e->builder, c->block);
}

void function_start(function fn) {
    ether e = fn->mod;
    // Create function debug info
    LLVMMetadataRef subroutine = LLVMDIBuilderCreateSubroutineType(
        e->dbg_builder,
        e->compile_unit,   // Scope (file)
        NULL,              // Parameter types (None for simplicity)
        0,                 // Number of parameters
        LLVMDIFlagZero     // Flags
    );

    fn->scope = LLVMDIBuilderCreateFunction(
        e->dbg_builder,
        e->compile_unit,        // Scope (compile_unit)
        fn->name->chars, len(fn->name),
        fn->name->chars, len(fn->name),
        e->file,                // File
        e->name->line,          // Line number
        subroutine,             // Function type
        1,                      // Is local to unit
        1,                      // Is definition
        1,                      // Scope line
        LLVMDIFlagZero,         // Flags
        0                       // Is optimized
    );

    // attach debug info to function
    LLVMSetSubprogram(fn->value, fn->scope);
    fn->entry = LLVMAppendBasicBlockInContext(
        e->module_ctx, fn->value, "entry");

    /// create debug info for arguments (including target)
    int index = 0;
    if (fn->target) {
        fn->target->value = LLVMGetParam(fn->value, index++);
        fn->target->is_arg = true;
        set(fn->members, str("this"), fn->target); /// here we have the LLVM Value Ref of the first arg, or, our instance pointer
    }
    each(fn->args, member, arg) {
        arg->value = LLVMGetParam(fn->value, index++);
        arg->is_arg = true;
        set(fn->members, str(arg->name->chars), arg);
    }

    if (fn->main_member) {
        member main_member = fn->main_member; /// has no value, so we must create one
        
        push(e, fn);
        member mm = member(mod, e, mdl, main_member->mdl, name, main_member->name);

        /// allocate and assign main-member [ main context class ]
        push_member(e, mm);
        node a = create(e, mm->mdl, null); /// call allocate, does not call init yet!
        zero  (e, a);

        assign(e, mm, a, OPType__assign);
        eprint(e, "this is a text");

        /// loop through arguments and print
        model  i64  = emodel("i64");
        member argc = lookup(e, string("argc"), null);
        member argv = lookup(e, string("argv"), null);
        member i    = evar(e, i64, string("i"));
        zero(e, i);

        /// define code blocks
        code cond = code(mod, e, label, "loop.cond");
        code body = code(mod, e, label, "loop.body");
        code end  = code(mod, e, label, "loop.end");

        /// emit code
        ebranch(e, cond);
        select (cond);
        ecmp   (e, i, comparison_s_less_than, argc, body, end);
        select (body);
        node arg = eelement(e, argv, i);
        eprint (e, "{0}", arg);
        einc   (e, i, 1);
        ebranch(e, cond);
        select (end);
        pop (e);
    } else if (e->module_init && fn == e->module_init->mdl) {
        push(e, fn);
        pairs (e->members, i) {
            member mem = i->value;
            // todo: reflection on member if public
            if (mem->initializer) {
                build_initializer(e, mem);
            } else {
                // we need a default(e, mem) call!
                //zero(e, mem);
            }
        }
        pop (e);
    }
}

void ether_build_initializer(ether e, member m) { }

/// lazy load the function, so we do not add everything we import
void function_use(function fn) {
    if (fn->value) return;
    fn->type  = LLVMFunctionType(fn->rtype->type, fn->arg_types, fn->arg_count, fn->va_args);
    fn->value = LLVMAddFunction(fn->mod->module, fn->name->chars, fn->type);
    member fmem = lookup(fn->mod, fn->name, null);
    //verify(fmem, "function member access not found");
    LLVMSetLinkage(fn->value,
        (!fmem || fmem->access == interface_intern) ? LLVMInternalLinkage : LLVMExternalLinkage);
}

void function_preprocess(function fn) {
    ether e = fn->mod;
    if (eq(fn->name, "run")) {
        br();
    }
    int              n_args    = len(fn->args);
    LLVMTypeRef*     arg_types = calloc(4 + (fn->target != null) + n_args, sizeof(LLVMTypeRef));
    int              index     = 0;
    model            top       = fn->init_top;

    if (fn->record) {
        verify (isa(fn->record) == typeid(structure) || 
                isa(fn->record) == typeid(class),
            "target [incoming] must be record type (struct / class) -- it is then made pointer-to record");
        
        member m_fn = lookup(e, fn->record->name, null);

        fn->target = member(mod, e, mdl, m_fn->mdl, name, string("this"));
        arg_types[index++] = fn->target->mdl->type;
        if (eq(fn->name, "run")) {
            br();
            // so the function args were being registered to entire struct 
            // values prior; with the base membership defined to make our 
            // 'record' a reference to struct, we are utilizing 'model' to its potential
        }
    }

    //print("function %o", fn->name);
    verify(isa(fn->args) == typeid(arguments), "arg mismatch");
    
    each(fn->args, member, arg) {
        verify (arg->mdl->type, "no LLVM type found for arg %o", arg->name);
        arg_types[index++]   = arg->mdl->type;
        if (is_void(arg->mdl)) {
            int test = 1;
            test++;
        }
        //print("arg type [%i] = %s", index - 1, LLVMPrintTypeToString(arg->mdl->type));
    }

    if (eq(fn->name, "run"))
        br();

    /// this is the first user of an object model, so we will also need to initialize any object model
    /// that has runtime types.  when the main code runs, we will need to load our module initializer
    /// 
    if (!fn->record && eq(fn->name, "main") && index == 1 && len(fn->args) == 1) {
        member arg = get(fn->args, 0);
        if (instanceof(arg->mdl->src, record)) {
            fn->main_member = hold(arg); /// this one we'll alloc ourselves if its there
            clear(fn->args->args);
            member arg0 = emember(lookup(e, string("int"), null)->mdl,     string("argc"));
            member arg1 = emember(lookup(e, string("symbols"), null)->mdl, string("argv"));
            push(fn->args, arg0);
            push(fn->args, arg1);
            arg_types[0] = arg0->mdl->type;
            arg_types[1] = arg1->mdl->type;
            index = 2; /// our main will be rtype main[int, symbol]
        }
    }

    fn->arg_types = arg_types;
    fn->arg_count = index;

    if (fn->process)
        use(fn);
    
    //print("preprocess function: %o, type: %p, value: %p (va_args: %i)", fn->name, fn->type, fn->value, fn->va_args);
    //free(arg_types); (llvm seems to not copy these)

    if (fn->process)
        function_start(fn);
}

void function_finalize(function fn) {
    ether e = fn->mod;
    int index = 0;
    if (!fn->process)
        return;
    
    index = 0;
    if (fn->target) {
        LLVMMetadataRef meta = LLVMDIBuilderCreateParameterVariable(
            e->dbg_builder,          // DIBuilder reference
            fn->scope,         // The scope (subprogram/function metadata)
            "this",            // Parameter name
            4,
            1,                 // Argument index (starting from 1, not 0)
            e->file,           // File where it's defined
            fn->name->line,    // Line number
            fn->target->mdl->debug,   // Debug type of the parameter (LLVMMetadataRef for type)
            1,                 // AlwaysPreserve (1 to ensure the variable is preserved in optimized code)
            0                  // Flags (typically 0)
        );
        LLVMValueRef first_instr = LLVMGetFirstInstruction(fn->entry);
        
        assert(LLVMIsAInstruction(first_instr), "not a instr"); /// we may simply insert a return if there is nothing?
        
        LLVMValueRef decl  = LLVMDIBuilderInsertDeclareRecordBefore(
            e->dbg_builder,                 // The LLVM builder
            fn->target->value,              // The LLVMValueRef for the first parameter
            meta,                           // The debug metadata for the first parameter
            LLVMDIBuilderCreateExpression(e->dbg_builder, NULL, 0), // Empty expression
            LLVMGetCurrentDebugLocation2(e->builder),       // Current debug location
            first_instr);                   // Attach it in the function's entry block
        index++;
    }

    each(fn->args, member, arg) {
        /// create debug for parameter here
        LLVMMetadataRef param_meta = LLVMDIBuilderCreateParameterVariable(
            e->dbg_builder,          // DIBuilder reference
            fn->scope,         // The scope (subprogram/function metadata)
             cstring(arg->name),    // Parameter name
            len(arg->name),
            1 + index,         // Argument index (starting from 1, not 0)
            e->file,           // File where it's defined
            arg->name->line,   // Line number
            arg->mdl->debug,   // Debug type of the parameter (LLVMMetadataRef for type)
            1,                 // AlwaysPreserve (1 to ensure the variable is preserved in optimized code)
            0                  // Flags (typically 0)
        );
        LLVMValueRef param_value = LLVMGetParam(fn->value, index);
        LLVMValueRef decl        = LLVMDIBuilderInsertDeclareRecordAtEnd(
            e->dbg_builder,                   // The LLVM builder
            param_value,                
            param_meta,                 // The debug metadata for the first parameter
            LLVMDIBuilderCreateExpression(e->dbg_builder, NULL, 0), // Empty expression
            LLVMGetCurrentDebugLocation2(e->builder),       // Current debug location
            fn->entry);                 // Attach it in the function's entry block
        arg->value = param_value;
        index++;
    }
}

void function_init(function fn) {
    ether e = fn->mod;
    fn->init_top = hold(e->top);
}

void record_finalize(record rec) {
    if (eq(rec->name, "class1")) {
        int test = 0;
        test++;
    }
    int   total = 0;
    ether e     = rec->mod;
    array a     = array(32);
    if (rec->parent_name) {
        model parent = emodel(rec->parent_name->chars);
        verify(parent, "could not find class: %o", rec->parent_name);
        class cl     = instanceof(parent->src, class);
        verify(cl, "expected src of model to be class %o", rec->parent_name);
        rec->parent  = cl;
    }
    record r = rec;
    while (r) {
        total += len(r->members);
        push(a, r);
        r = r->parent;
    }
    if (len(a) > 1) {
        array rev = array((int)len(a));
        for (int i = len(a) - 1; i >= 0; i--)
            push(rev, a->elements[i]);
        a = rev;
    }
    LLVMTargetDataRef target_data = rec->mod->target_data;
    LLVMTypeRef*     member_types = calloc(total, sizeof(LLVMTypeRef));
    LLVMMetadataRef* member_debug = calloc(total, sizeof(LLVMMetadataRef));
    bool             is_uni       = instanceof(rec, uni) != null;
    int              index        = 0;
    member           largest      = null;
    sz               sz_largest   = 0;

    each (a, record, r) {
        pairs(r->members, i) {
            member mem = i->value;
            verify( mem->name,  "no name on member");
            if (instanceof(mem->mdl, function))
                continue;
            /// in poly classes, we will encounter the same member twice
            if (!mem->debug) {
                model_process_finalize(mem->mdl);
                mem->debug = LLVMDIBuilderCreateMemberType(
                    e->dbg_builder,              // LLVMDIBuilderRef
                    e->top->scope,         // Scope of the member (can be the struct, class or base module)
                    cstring(mem->name),         // Name of the member
                    len(mem->name),        // Length of the name
                    e->file,               // The file where the member is declared
                    mem->name->line,       // Line number where the member is declared
                    mem->mdl->size * 8,    // Size of the member in bits (e.g., 32 for a 32-bit int)
                    mem->mdl->alignment * 8, // Alignment of the member in bits
                    0,                     // Offset in bits from the start of the struct or class
                    0,                     // Debug info flags (e.g., 0 for none)
                    mem->mdl->debug        // The LLVMMetadataRef for the member's type (created earlier)
                );
            }
            if (eq(mem->name, "a")) {
                int test = 1;
                test++;
            }
            if (!mem->mdl->type) {
                model_process_finalize(mem->mdl);
                verify(mem->mdl->type, "expected resolution on type");
            }
            member_types[index]   = mem->mdl->type;
            int abi_size = LLVMABISizeOfType(target_data, mem->mdl->type);
            member_debug[index++] = mem->debug;
            if (!sz_largest || abi_size > sz_largest) {
                largest = mem;
                sz_largest = abi_size;
            }
        }
    }

    if (is_uni) {
        verify(sz_largest, "cannot determine size of union");
        LLVMStructSetBody(rec->type, &largest->mdl->type, 1, 0);
    } else
        LLVMStructSetBody(rec->type, member_types, index, 0);

    /// set record size
    rec->size = LLVMABISizeOfType(target_data, rec->type);
    
    /// set offsets on members (needed for the method finalization)
    num imember = 0;
    each (a, record, r)
        pairs(r->members, i) {
            member mem = i->value;
            if (instanceof(mem->mdl, function)) // functions do not occupy membership on the instance
                continue;
            mem->index  = imember;
            mem->offset = LLVMOffsetOfElement(target_data, rec->type, imember);
            if (!instanceof(r, uni)) // unions have 1 member
                imember++;
        }
    
    /// finalize methods on record (which use its members)
    each (a, record, r) {
        pairs(r->members, i) {
            member mem = i->value;
            if (instanceof(mem->mdl, function))
                model_process_finalize(mem->mdl);
        }
    }
    
    int sz = LLVMABISizeOfType     (target_data, rec->type);
    int al = LLVMABIAlignmentOfType(target_data, rec->type);
    
    LLVMMetadataRef prev = rec->debug;

    // mdl is required on member
    rec->debug = LLVMDIBuilderCreateStructType(
        e->dbg_builder,                     // Debug builder
        e->top->scope,                // Scope (module or file)
        cstring(rec->name),                // Name of the struct
        len(rec->name),
        e->file,                      // File where it’s defined
        rec->name->line,              // Line number where it’s defined
        sz, al,                       // Size, Alignment in bits
        LLVMDIFlagZero,               // Flags
        rec->parent ? rec->parent->debug : null, // Derived from (NULL in C)
        member_debug,                 // Array of member debug info
        total,                        // Number of members
        0,                            // Runtime language (0 for none)
        NULL,                         // No VTable
        NULL, 0);

    if (prev) {
        LLVMMetadataReplaceAllUsesWith(prev, rec->debug);
    }
    rec->process = null;
}

#define LLVMDwarfTag(tag) (tag)
#define DW_TAG_structure_type 0x13  // DWARF tag for structs.

void record_init(record rec) {
    ether e = rec->mod;
    if (eq(rec->name, "struct A")) { /// find when it gets aliased afterwrads, make sure the aliasing finds the proper reference
        int test = 2;
        test += 2;
    }
    rec->type = LLVMStructCreateNamed(LLVMGetGlobalContext(), rec->name->chars);

    if (strcmp(rec->name->chars, "A") == 0) {
        int test = 2;
        test += 2;
    }
    // Create a forward declaration for the struct's debug info
    rec->debug = LLVMDIBuilderCreateReplaceableCompositeType(
        e->dbg_builder,                      // Debug builder
        LLVMDwarfTag(DW_TAG_structure_type), // Tag for struct
         cstring(rec->name),                      // Name of the struct
        len(rec->name),
        e->top->scope,                       // Scope (this can be file or module scope)
        e->file,                             // File
        rec->name->line,                     // Line number
        0,
        0,
        0,
        LLVMDIFlagZero,                      // Flags
        NULL,                                // Derived from (NULL in C)
        0                                    // Size and alignment (initially 0, finalized later)
    );
    if (eq(rec->name, "struct A")) {
        int test = 2;
        test += 2;
    }
    if (len(rec->members)) {
        model_process_finalize(rec);
    }
}

member member_resolve(member mem, string name) {
    ether  e   = mem->mod;
    i64  index = 0;
    model base = mem->mdl->ref ? mem->mdl->src : mem->mdl; // needs to support more than indirection here
    pairs(base->members, i) {
        if (compare(i->key, name) == 0) {
            member schema = i->value; /// value is our pair value, not a llvm-value
            if (schema->is_const) {
                return schema; /// for enum members, they are const integer; no target stored but we may init that
            }

            LLVMValueRef actual_ptr = mem->is_arg ? mem->value : LLVMBuildLoad2(
                e->builder,
                LLVMPointerType(base->type, 0), // The type of the loaded value
                mem->value,                     // The stack-allocated pointer
                "load_actual_ptr"
            );

            member target_member = member(
                mod,    e,          name,   mem->name,
                mdl,    mem->mdl,   value,  actual_ptr);
            
            /// by pass automatic allocation of this member, as we are assigning to StructGEP from its container
            member  res = member(mod, e, name, name, mdl, null, target_member, target_member);
            res->mdl    = schema->mdl;
            function fn = instanceof(schema->mdl, function);
            res->value  = fn ? fn->value : LLVMBuildStructGEP2(
                    e->builder, base->type, actual_ptr, index, "resolve"); // GPT: mem->value is effectively the ptr value on the stack
            if (fn)
                res->is_func = true;
            
            return res;
        }
        index++;
    }
    fault("member %o not found in type %o", name, base->name);
    return null;
}

node ether_operand(ether e, object op);

void member_set_value(member mem, object value) {
    node n = operand(mem->mod, value);
    mem->mdl   = n->mdl;
    mem->value = n->value; /// todo: verify its constant
}

bool member_has_value(member mem) {
    return mem->value != null;
}

void member_init(member mem) {
    ether e   = mem->mod;
    if (instanceof(mem->name, string)) {
        string n = mem->name;
        mem->name = token(chars, cstring(n), source, e->source, line, 1);
    }
    set_model(mem, mem->mdl);
}

void member_set_model(member mem, model mdl) {
    if (!mdl || !mdl->debug)
        return;
    if (mem->mdl != mdl) {
        verify(!mem->mdl, "model already set on member");
        mem->mdl = hold(mdl);
    }

    ether    e  = mem->mod;
    function fn = ether_context_model(e, typeid(function));
    bool is_init = false;
    if (fn && fn->imdl) {
        is_init = true;
        fn = null;
    }
    
    /// if we are creating a new member inside of a function, we need
    /// to make debug and value info here
    if (fn && !mem->value) {
        verify (!mem->value, "value-ref already set auto member");
        mem->value = LLVMBuildAlloca(e->builder, mem->mdl->type, cstring(mem->name));
        mem->debug = LLVMDIBuilderCreateAutoVariable(
            e->dbg_builder,           // DIBuilder reference
            fn->scope,          // The scope (subprogram/function metadata)
             cstring(mem->name),     // Variable name
            len(mem->name),
            e->file,            // File where it’s declared
            mem->name->line,    // Line number
            mem->mdl->debug,    // Type of the variable (e.g., LLVMMetadataRef for int)
            true,               // Is this variable always preserved (DebugPreserveAll)?
            0,                  // Flags (usually 0)
            0                   // Align (0 is default)
        );

        // Attach the debug info to the actual LLVM IR value using llvm.dbg.value
        //LLVMBuildDbgValue(
        //    e->builder,              // LLVM Builder
        //    mem->value,              // The LLVMValueRef for the value being assigned to the member
        //    mem->debug,              // Debug info for the variable
        //    LLVMGetCurrentDebugLocation2(e->builder));
        
        LLVMValueRef firstInstr = LLVMGetFirstInstruction(fn->entry);
        if (!firstInstr) {
            // If there’s no instruction in the block yet, use the block itself as the insertion point
            firstInstr = (LLVMValueRef)fn->entry;
        }

        LLVMDIBuilderInsertDeclareRecordBefore(
            e->dbg_builder,                   // The LLVM builder
            mem->value,                 // The LLVMValueRef for the first parameter
            mem->debug,                 // The debug metadata for the first parameter
            LLVMDIBuilderCreateExpression(e->dbg_builder, NULL, 0), // Empty expression
            LLVMGetCurrentDebugLocation2(e->builder),       // Current debug location
            firstInstr);
    } else if (!fn && !mem->is_type && !e->current_include && is_init && !mem->is_decl) {
        symbol name = mem->name->chars;
        LLVMTypeRef type = mem->mdl->type;
        verify(!mem->is_const || mem->value, "const value mismatch");
        if (!mem->value)
            mem->value = LLVMAddGlobal(e->module, type, name);
 
        // this would be for very basic primitives, ones where we can eval in design
        // for now its much easier to do them all the same way, via expression in global init
        // they can reference each other there
        //if (mem->is_const) {
        //    LLVMSetInitializer(mem->value, LLVMConstInt(i32_type, 42, 0));
        //}

        bool is_public = mem->access == interface_public;
        LLVMSetLinkage(mem->value, is_public ? LLVMExternalLinkage : LLVMInternalLinkage);
        LLVMMetadataRef expr = LLVMDIBuilderCreateExpression(e->dbg_builder, NULL, 0);
        LLVMMetadataRef meta = LLVMDIBuilderCreateGlobalVariableExpression(
            e->dbg_builder, e->scope, name, len(mem->name), NULL, 0, e->file, 1, mem->mdl->debug, 
            0, expr, NULL, 0);
        LLVMGlobalSetMetadata(mem->value, LLVMGetMDKindID("dbg", 3), meta);
    }
}

#define int_value(b,l) \
    node(mod, e, \
        literal, l, mdl, emodel(stringify(i##b)), \
        value, LLVMConstInt(emodel(stringify(i##b))->type, *(i##b*)l, 0))

#define uint_value(b,l) \
    node(mod, e, \
        literal, l, mdl, emodel(stringify(u##b)), \
        value, LLVMConstInt(emodel(stringify(u##b))->type, *(u##b*)l, 0))

#define real_value(b,l) \
    node(mod, e, \
        literal, l, mdl, emodel(stringify(f##b)), \
        value, LLVMConstReal(emodel(stringify(f##b))->type, *(f##b*)l))

node ether_operand(ether e, object op) {
    if (!op) return value(emodel("void"), null);

         if (instanceof(op,   node)) return op;
    else if (instanceof(op,     u8)) return uint_value(8,  op);
    else if (instanceof(op,    u16)) return uint_value(16, op);
    else if (instanceof(op,    u32)) return uint_value(32, op);
    else if (instanceof(op,    u64)) return uint_value(64, op);
    else if (instanceof(op,     i8)) return  int_value(8,  op);
    else if (instanceof(op,    i16)) return  int_value(16, op);
    else if (instanceof(op,    i32)) return  int_value(32, op);
    else if (instanceof(op,    i64)) return  int_value(64, op);
    else if (instanceof(op,     sz)) return  int_value(64, op); /// instanceof is a bit broken here and we could fix the generic; its not working with aliases
    else if (instanceof(op,    f32)) return real_value(32, op);
    else if (instanceof(op,    f64)) return real_value(64, op);
    else if (instanceof(op, string)) {
        LLVMTypeRef  gs      = LLVMBuildGlobalStringPtr(e->builder, ((string)op)->chars, "chars");
        LLVMValueRef cast_i8 = LLVMBuildBitCast(e->builder, gs, LLVMPointerType(LLVMInt8Type(), 0), "cast_symbol");
        return node(mod, e, value, cast_i8, mdl, emodel("symbol"), literal, op);
    }
    else {
        error("unsupported type in ether_add");
        return NULL;
    }
}

model model_alias(model src, object name, reference r, array shape) {
    record rec = instanceof(src, record);
    if (rec && !rec->process)
        model_process_finalize(rec); /// finalize imported types
    if (instanceof(name, token))
        name = string(((token)name)->chars);
    if (!name && shape) {
        /// lets create a bindable name here
        int slen = len(shape);
        if (slen == 0) {
            name = format("array_%o", src->name);
        } else {
            node  n = first(shape);
            AType component_type = n->literal ? isa(n->literal) : isa(n);
            verify(component_type == typeid(i64) || 
                   component_type == typeid(sz), "expected size type in model wrap");
            sz size = *(sz*)n->literal;
            name = format("array_%i_%o", (int)size, src->name);
        }
    }

    model  ref = model(
        mod,    src->mod,
        name,   name,
        shape,  shape,
        ref,    r,
        src,   src);
    return ref;
}

node ether_default_value(ether e, model mdl) {
    return create(e, mdl, null);
}

node ether_alloc(ether e, model imdl) {
    model        mdl        = imdl->src;
    LLVMValueRef size_A     = LLVMConstInt(LLVMInt64Type(), 32, false);
    LLVMValueRef size_mdl   = LLVMConstInt(LLVMInt64Type(), mdl->size, false);
    LLVMValueRef total_size = LLVMBuildAdd(e->builder, size_A, size_mdl, "total-size");
    LLVMValueRef alloc      = LLVMBuildArrayMalloc(e->builder, LLVMInt8Type(), total_size, "malloc-A-mdl");
    LLVMValueRef zero       = LLVMConstInt(LLVMInt8Type(), 0, false);  // Value to fill with
    LLVMBuildMemSet(e->builder, alloc, zero, total_size, 0);
    LLVMValueRef user       = LLVMBuildGEP2(e->builder, imdl->type, alloc, &size_A, 1, "user-mdl");
    return value(imdl, user);
}


node ether_obj(ether e, model mdl, object args) {
    node a = operand(e, args);
    member mfn = convertible(a->mdl, mdl);
    verify(mfn, "could not find suitable conversion for %o to %o", a->mdl->name, mdl->name);
    function fn = instanceof(mfn->mdl, function);
    node n = null;
    if (fn->function_type & A_TYPE_CONSTRUCT) {
        /// this means we are calling constructor and must do so after alloc'ing ourself
        n = alloc(e, mdl); 
    } else {
        verify(fn->function_type & A_TYPE_CAST, "expected cast");
        /// we call the cast function (a = singular mdl instance) to receive our object of imdl
        n = fn_call(e, fn, array_of(null, a, null));
    }
    return n;
}

node ether_stack(ether e, model mdl) {
    LLVMValueRef alloc = LLVMBuildAlloca(e->builder, mdl->type, "alloca-mdl");
    return value(mdl, alloc);
}

/// create primitives and objects, constructs with singular args or a map of them when applicable
node ether_create(ether e, model mdl, object args) {
    LLVMValueRef alloc = null;
    map    imap = instanceof(args, map);
    node   n    = null;
    member ctr  = null;

    /// construct / cast methods
    node input = instanceof(args, node);
    if (input) {
        verify(!imap, "unexpected data");
        member fmem = convertible(input->mdl, mdl);
        verify(fmem, "no suitable conversion found for %o -> %o",
            input->mdl->name, mdl->name);
        function fn = instanceof(fmem->mdl, function);
        if (fn->function_type & A_TYPE_CONSTRUCT) {
            /// ctr: call before init
            /// this also means the mdl is not a primitive
            verify(!is_primitive(fn->rtype), "expected struct/class");
            ctr = fmem;
        } else if (fn->function_type & A_TYPE_CAST) {
            /// cast call on input
            return fn_call(e, fn, array_of(null, input, null));
        } else
            fault("unknown error");
    }
    bool perform_assign = false;
    if (mdl->ref == reference_value) {
        verify(isa(mdl) != typeid(class), "unsupported data store (inlay not supported in 0.8.8)");
        verify(!input, "code path error");
        n     = stack(e, mdl); 
        perform_assign = !!args;
    } else if (mdl->ref == reference_pointer) {
        n     = alloc(e, mdl);
    } else {
        fault("not implemented");
    }

    /// iterate through args in map, setting values
    if (imap) {
        verify(mdl->ref == reference_pointer, "model mismatch");
        verify(instanceof(mdl, record), "model not a record, and given a map"); ///
        map used  = map();
        int total = 0;
        pairs(imap, i) {
            string arg_name  = instanceof(i->key, string);
            node   arg_value = instanceof(i->value, node);
            verify (!contains(used, arg_name), "duplicate argument: %o", arg_name);
            set    (used, arg_name, A_bool(true));
            member m = get(mdl->members, arg_name);
            verify(m, "member %o not found on record: %o", arg_name, mdl->name);
            LLVMValueRef ptr = LLVMBuildStructGEP2(e->builder,
                mdl->type, n->value, m->index, arg_name->chars);
            //arg_value->value = LLVMConstInt(LLVMInt64Type(), 44, 0);
            // for objects, we must increment the ref, too [call the method A_hold]
            LLVMBuildStore(e->builder, arg_value->value, ptr);
            total++;
        }
        pairs(mdl->members, i) {
            member mem = i->value;
            if (mem->is_require)
                verify (contains(used, mem->name), "required argument not set: %o", mem->name);
        }
        /// generic > object
        /// call init on the object

    } else if (args) {
        node a = operand(e, args);
        /// this should only happen on primitives
        if (perform_assign) {
            node conv = convert(e, a, n->mdl);
            n         = assign (e, n, conv, OPType__assign);
        }
    }
    return n;
}

LLVMValueRef get_memset_function(ether e) {
    // Parameters for memset: void* (i8*), int (i8), size_t (i64)
    LLVMTypeRef param_types[] = {
        LLVMPointerType(LLVMInt8TypeInContext(e->module_ctx), 0),  // void* (i8*)
        LLVMInt8TypeInContext(e->module_ctx),                      // int (i8)
        LLVMInt64TypeInContext(e->module_ctx)                     // size_t (i64)
    };

    LLVMTypeRef memset_type = LLVMFunctionType(
        LLVMVoidTypeInContext(e->module_ctx),  // Return type (void)
        param_types,                           // Parameters
        3,                                     // Number of parameters
        false                                  // Not variadic
    );

    // Check if memset is already declared, if not, declare it
    LLVMValueRef memset_func = LLVMGetNamedFunction(e->module, "memset");
    if (!memset_func) {
        memset_func = LLVMAddFunction(e->module, "memset", memset_type);
    }

    return memset_func;
}

node ether_zero(ether e, node n) {
    model      mdl = n->mdl;
    LLVMValueRef v = n->value;
    LLVMValueRef zero   = LLVMConstInt(LLVMInt8Type(), 0, 0);          // value for memset (0)
    LLVMValueRef size   = LLVMConstInt(LLVMInt64Type(), mdl->size, 0); // size of alloc
    LLVMValueRef memset = LLVMBuildMemSet(e->builder, v, zero, size, 0);
    return n;
}


node ether_ternary(ether e, node cond_expr, node true_expr, node false_expr) {
    if (e->no_build) return node(mod, e);
    ether mod = e;
    // Step 1: Create the blocks for the ternary structure
    LLVMBasicBlockRef current_block = LLVMGetInsertBlock(mod->builder);
    LLVMBasicBlockRef then_block    = LLVMAppendBasicBlock(current_block, "ternary_then");
    LLVMBasicBlockRef else_block    = LLVMAppendBasicBlock(current_block, "ternary_else");
    LLVMBasicBlockRef merge_block   = LLVMAppendBasicBlock(current_block, "ternary_merge");

    // Step 2: Build the conditional branch based on the condition
    LLVMValueRef condition_value = cond_expr->value;
    LLVMBuildCondBr(mod->builder, condition_value, then_block, else_block);

    // Step 3: Handle the "then" (true) branch
    LLVMPositionBuilderAtEnd(mod->builder, then_block);
    LLVMValueRef true_value = true_expr->value;
    LLVMBuildBr(mod->builder, merge_block);  // Jump to merge block after the "then" block

    // Step 4: Handle the "else" (false) branch
    LLVMPositionBuilderAtEnd(mod->builder, else_block);
    LLVMValueRef false_value = false_expr->value;
    LLVMBuildBr(mod->builder, merge_block);  // Jump to merge block after the "else" block

    // Step 5: Build the "merge" block and add a phi node to unify values
    LLVMPositionBuilderAtEnd(mod->builder, merge_block);
    LLVMTypeRef result_type = LLVMTypeOf(true_value);
    LLVMValueRef phi_node = LLVMBuildPhi(mod->builder, result_type, "ternary_result");
    LLVMAddIncoming(phi_node, &true_value, &then_block, 1);
    LLVMAddIncoming(phi_node, &false_value, &else_block, 1);

    // Return some node or result if necessary (e.g., a node indicating the overall structure)
    return node(mod, mod, mdl, emodel("void"), value, null);
}

node ether_builder(ether e, subprocedure cond_builder) {
    if (e->no_build) return node(mod, e, mdl, emodel("void"));
    LLVMBasicBlockRef block = LLVMGetInsertBlock(e->builder);
    LLVMPositionBuilderAtEnd(e->builder, block);
    node   n = invoke(cond_builder, null);
    return n;
}

node ether_if_else(ether e, array conds, array exprs, subprocedure cond_builder, subprocedure expr_builder) {
    if (e->no_build) return node(mod, e, mdl, emodel("void"));
    verify(len(conds) == len(exprs) - 1 || 
           len(conds) == len(exprs), "mismatch between conditions and expressions");
    
    LLVMBasicBlockRef block = LLVMGetInsertBlock  (e->builder);
    LLVMBasicBlockRef merge = LLVMAppendBasicBlock(block, "ifcont");  // Merge block for the end of if-else chain

    // Iterate over the conditions and expressions
    for (int i = 0; i < len(conds); i++) {
        // Create the blocks for "then" and "else"
        LLVMBasicBlockRef then_block = LLVMAppendBasicBlock(block, "then");
        LLVMBasicBlockRef else_block = LLVMAppendBasicBlock(block, "else");

        // Build the condition
        object cond_obj = conds->elements[i];
        node cond_result = invoke(cond_builder, cond_obj);  // Silver handles the actual condition parsing and building
        LLVMValueRef condition = ether_convert(e, cond_result, emodel("bool"))->value;

        // Set the sconditional branch
        LLVMBuildCondBr(e->builder, condition, then_block, else_block);

        // Build the "then" block
        LLVMPositionBuilderAtEnd(e->builder, then_block);
        object expr_obj = exprs->elements[i];
        node expressions = invoke(expr_builder, expr_obj);  // Silver handles the actual block/statement generation
        LLVMBuildBr(e->builder, merge);

        // Move the builder to the "else" block
        LLVMPositionBuilderAtEnd(e->builder, else_block);
        block = else_block;
    }

    // Handle the fnal "else" (if applicable)
    if (len(exprs) > len(conds)) {
        object else_expr = exprs->elements[len(conds)];
        invoke(expr_builder, else_expr);  // Process the final else block
        LLVMBuildBr(e->builder, merge);
    }

    // Move the builder to the merge block
    LLVMPositionBuilderAtEnd(e->builder, merge);

    // Return some node or result if necessary (e.g., a node indicating the overall structure)
    return node(mod, e, mdl, emodel("void"), value, null);  // Dummy node, replace with real node if needed
}

node ether_addr_of(ether e, node expr, model mdl) {
    if (e->no_build) return node(mod, e, mdl, emodel("void"));
    model        ref   = pointer(mdl ? mdl : expr->mdl); // this needs to set mdl->type to LLVMPointerType(mdl_arg->type, 0)
    member      m_expr = instanceof(expr, member);
    LLVMValueRef value = m_expr ? expr->value :
        LLVMBuildGEP2(e->builder, ref->type, expr->value, NULL, 0, "ref_expr");
    return node(
        mod,   e,
        value, value,
        mdl,   ref);
}

bool is_const_v(LLVMValueRef val) {
    if (!LLVMIsConstant(val))
        return false;
    
    LLVMTypeRef type = LLVMTypeOf(val);
    if (LLVMGetTypeKind(type) == LLVMPointerTypeKind)
        return false;
    
    return true;
}

node ether_offset(ether e, node n, object offset) {
    if (e->no_build) return member(mod, e, mdl, emodel("void"));

    member mem = instanceof(n, member);
    model  mdl = n->mdl;
    node   i   = operand(e, offset);

    verify(mdl->ref == reference_pointer, "offset requires pointer");

    LLVMValueRef ptr_load   = LLVMBuildLoad2(e->builder,
        LLVMPointerType(mdl->type, 0), n->value, "load");
    LLVMValueRef ptr_offset = LLVMBuildGEP2(e->builder,
         mdl->type, ptr_load, &i->value, 1, "offset");

    return mem ? (node)member(mod, e, mdl, mdl, value, ptr_offset, name, mem->name) :
                         node(mod, e, mdl, mdl, value, ptr_offset);
}

node ether_load(ether e, node n) {
    if (n->loaded) return n;
    verify(!e->left_hand, "should not be calling load on L hand side");

    member mem = instanceof(n, member);
    if (!mem || mem->is_const) return n; /// const check 1
    if (e->no_build) return node(mod, e, mdl, emodel("void"));
    
    // constants do not require loading
    if (n->value && is_const_v(n->value)) /// const check 2
        return n;

    model        mdl = n->mdl;
    LLVMValueRef ptr = n->value;

    // if this is a member on record, build an offset given its 
    // index and 'this' argument pointer
    if (!ptr) {
        verify(mem,    "invalid model given to load");
        if (mem->is_module) {
            verify(ptr, "makes no sense");
        } else {
            member target = lookup(e, string("this"), null); // unique to the function in class, not the class
            verify(target, "no target found when looking up member");
            /// static methods do not have this in context
            record rec = target->mdl->src;
            ptr = LLVMBuildStructGEP2(
                e->builder, rec->type, target->value, mem->index, "member-ptr");
        }
    }

    LLVMValueRef res = null;
    string label = format("load-member-%o", mem->name);

    if (e->left_hand) {
        res = ptr;
        verify(mem, "member expected on left-hand");
    } else
        res = LLVMBuildLoad2(e->builder, mdl->type, ptr, cstring(label));
    
    node r;
    if (mem)
        r = member(mod, e, name, mem->name, mdl, mdl, value, res);
    else
        r = value(mdl, res);

    r->loaded = true;
    return r;
}

/// general signed/unsigned/1-64bit and float/double conversion
/// [optionally] load and convert expression
node ether_convert(ether e, node expr, model rtype) {
    if (e->no_build) return node(mod, e, mdl, emodel("void"));
    expr = load(e, expr);
    model        F = expr->mdl;
    model        T = rtype;
    LLVMValueRef V = expr->value;

    if (F == T) return expr;  // no cast needed

    // LLVM type kinds
    LLVMTypeKind F_kind = LLVMGetTypeKind(F->type);
    LLVMTypeKind T_kind = LLVMGetTypeKind(T->type);
    LLVMBuilderRef B = e->builder;

    // integer conversion
    if (F_kind == LLVMIntegerTypeKind &&  T_kind == LLVMIntegerTypeKind) {
        uint F_bits = LLVMGetIntTypeWidth(F->type), T_bits = LLVMGetIntTypeWidth(T->type);
        if (F_bits < T_bits)
            V = is_signed(F) ? LLVMBuildSExt(B, V, T->type, "sext")
                             : LLVMBuildZExt(B, V, T->type, "zext");
        else if (F_bits > T_bits)
            V = LLVMBuildTrunc(B, V, T->type, "trunc");
        else if (is_signed(F) != is_signed(T))
            V = LLVMBuildIntCast2(B, V, T->type, is_signed(T), "int-cast");
        else
            V = expr->value;
    }

    // int to real
    else if (F_kind == LLVMIntegerTypeKind && (T_kind == LLVMFloatTypeKind || T_kind == LLVMDoubleTypeKind))
        V = is_signed(F) ? LLVMBuildSIToFP(B, V, T->type, "sitofp")
                         : LLVMBuildUIToFP(B, V, T->type, "uitofp");

    // real to int
    else if ((F_kind == LLVMFloatTypeKind || F_kind == LLVMDoubleTypeKind) && T_kind == LLVMIntegerTypeKind)
        V = is_signed(T) ? LLVMBuildFPToSI(B, V, T->type, "fptosi")
                         : LLVMBuildFPToUI(B, V, T->type, "fptoui");

    // real conversion
    else if ((F_kind == LLVMFloatTypeKind || F_kind == LLVMDoubleTypeKind) && 
             (T_kind == LLVMFloatTypeKind || T_kind == LLVMDoubleTypeKind))
        V = F_kind == LLVMDoubleTypeKind && T_kind == LLVMFloatTypeKind ? 
            LLVMBuildFPTrunc(B, V, T->type, "fptrunc") :
            LLVMBuildFPExt  (B, V, T->type, "fpext");

    // ptr conversion
    else if (is_ref(F) && is_ref(T))
        V = LLVMBuildPointerCast(B, V, T->type, "ptr_cast");

    // ptr to int
    else if (is_ref(F) && is_integral(T))
        V = LLVMBuildPtrToInt(B, V, T->type, "ptr_to_int");

    // int to ptr
    else if (is_integral(F) && is_ref(T))
        V = LLVMBuildIntToPtr(B, V, T->type, "int_to_ptr");

    // bitcast for same-size types
    else if (F_kind == T_kind)
        V = LLVMBuildBitCast(B, V, T->type, "bitcast");

    else if (F_kind == LLVMVoidTypeKind)
        V = LLVMConstNull(T->type);
    else
        fault("unsupported cast");

    node res = value(T,V);
    res->literal = hold(expr->literal);
    return res;
}

model ether_context_model(ether e, AType type) {
    for (int i = len(e->lex) - 1; i >= 0; i--) {
        model ctx = e->lex->elements[i];
        if (isa(ctx) == type)
            return ctx;
    }
    return null;
}

model ether_return_type(ether e) {
    for (int i = len(e->lex) - 1; i >= 0; i--) {
        model ctx = e->lex->elements[i];
        if (ctx->rtype) return ctx->rtype;
    }
    return null;
}

void assign_args(ether e, node L, object R, node* r_L, node* r_R) {
    *r_R = operand(e, R);
    member Lm = instanceof(L, member);
    if (Lm && !Lm->is_const)
        *r_L = L;//load(e, Lm);
    else
        *r_L = L;

    LLVMTypeRef RType = LLVMTypeOf((*r_R)->value);
    LLVMTypeRef LType = LLVMTypeOf((*r_L)->value);
    printf("assign_args: ");
    LLVMDumpType(RType);
    printf(" ");
    LLVMDumpType(LType);
    printf("\n");
}

struct op_entry {
    LLVMValueRef(*f_op)(LLVMBuilderRef, LLVMValueRef L, LLVMValueRef R, symbol);
};

static struct op_entry op_table[] = {
    { LLVMBuildAdd },
    { LLVMBuildSub }, 
    { LLVMBuildMul }, 
    { LLVMBuildSDiv }, 
    { LLVMBuildOr }, 
    { LLVMBuildAnd },
    { LLVMBuildXor },  
    { LLVMBuildURem }, 
};

node ether_assign(ether e, node L, object R, OPType op) {
    int v_op = op;
    verify(op >= OPType__assign && op <= OPType__assign_left, "invalid assignment-operator");
    node rL, rR = operand(e, R);
    node res = rR;
    if (op != OPType__assign) {
        rL = load(e, L);
        res = value(L->mdl,
            op_table[op - OPType__assign - 1].f_op
                (e->builder, rL->value, rR->value, estr(OPType, op)->chars));
    }
    LLVMBuildStore(e->builder, res->value, L->value);
    return res;
}

model ether_base_model(ether e, symbol name, AType native) {
    void* result[8];
    A prim = A_primitive(native, result); /// make a mock instance out of the type
    model mdl = model(
        mod, e, name, str(name), src, prim);
    verify (!contains(e->base, str(name)), "duplicate definition");
    set(e->base, str(name), mdl);
    ether_push_model(e, mdl);
    return mdl;
}

model ether_define_generic(ether e) {
    A  object = A_alloc(typeid(object), 1, true);
    string  n = string("generic");
    model mdl = model(mod, e, name, n, src, object);
    set(e->base, n, mdl);
    ether_push_model(e, mdl);
    return mdl;
}

/// A-type must be read
void ether_define_primitive(ether e) {
    e->base = map(hsize, 64);
    model none = ether_base_model(e, "void", typeid(none));
                ether_base_model(e, "bool", typeid(bool));
                ether_base_model(e, "u8", typeid(u8));
    model u16 = ether_base_model(e, "u16", typeid(u16));
                ether_base_model(e, "u32", typeid(u32));
    model u64 = ether_base_model(e, "u64", typeid(u64));
    model i8  = ether_base_model(e, "i8",  typeid(i8));
    model i16 = ether_base_model(e, "i16", typeid(i16));
    model i32 = ether_base_model(e, "i32", typeid(i32));
    model i64 = ether_base_model(e, "i64", typeid(i64));
                ether_base_model(e, "f32",  typeid(f32));
                ether_base_model(e, "f64",  typeid(f64));
                ether_base_model(e, "f128", typeid(f128));

    model _cstr = alias(i8, str("cstr"), reference_pointer, null);
    set(e->base, str("cstr"), _cstr);
    ether_push_model(e, _cstr);

    model symbol = alias(i8, str("symbol"), reference_constant, null);
    set(e->base, str("symbol"), symbol);
    ether_push_model(e, symbol);

    model symbols = alias(symbol, str("symbols"), reference_constant, null);
    set(e->base, str("symbols"), symbols);
    ether_push_model(e, symbols);

    model _char = alias(i32, str("char"), 0, null);
    set(e->base, str("char"), _char);
    ether_push_model(e, _char);

    model _int  = alias(i64, str("int"), 0, null);
    set(e->base, str("int"), _int);
    ether_push_model(e, _int);

    model _uint = alias(u64, str("uint"), 0, null);
    set(e->base, str("uint"), _uint);
    ether_push_model(e, _uint);

    model _short  = alias(i16, str("short"), 0, null);
    set(e->base, str("short"), _short);
    ether_push_model(e, _short);

    model _ushort = alias(u16, str("ushort"), 0, null);
    set(e->base, str("ushort"), _ushort);
    ether_push_model(e, _ushort);
}

/// look up a member in lexical scope
/// this applies to models too, because they have membership as a type entry
member ether_lookup(ether e, object name, AType omit) {
    if (!name) return null;
    if (instanceof(name, token))
        name = cast(string, (token)name);
    for (int i = len(e->lex) - 1; i >= 0; i--) {
        model ctx = e->lex->elements[i];
        AType ctx_type = isa(ctx);
        member  m = get(ctx->members, name);
        if (m && (!m->mdl || !m->mdl->lookup_omit)) {
            return  m;
        }
        class cl = instanceof(ctx, class);
        if (cl) {
            class parent = cl->parent;
            while (parent) {
                member  m = get(parent->members, name);
                if (m) return  m;
                parent = parent->parent;
            }
        }
    }
    return null;
}

model ether_push(ether e, model mdl) {
    verify(mdl, "no context given");
    push(e->lex, mdl);
    e->top = mdl;
    function fn = instanceof(mdl, function);
    if (fn) {
        LLVMPositionBuilderAtEnd(e->builder, fn->entry);
        if (LLVMGetBasicBlockTerminator(fn->entry) == NULL) {
            // set debug location
            LLVMMetadataRef loc = LLVMDIBuilderCreateDebugLocation(
                e->module_ctx, fn->name->line, 0, fn->scope, NULL);
            LLVMSetCurrentDebugLocation2(e->builder, loc);
        }
    } 
    return mdl;
}


model ether_pop(ether e) {
    pop(e->lex);
    if (len(e->lex))
        e->top = last(e->lex);
    else
        e->top = null;
    return e->top;
}


enum CXChildVisitResult visit_member(CXCursor cursor, CXCursor parent, CXClientData client_data);

model cx_to_model(ether e, CXType cxType, symbol name, bool arg_rules) {
    string    t = null;
    int   depth = 0;
    CXType base = cxType;
    array shape = null;

    while (base.kind == CXType_Elaborated)
        base = clang_Type_getNamedType(base);
    
    while (base.kind == CXType_Pointer || base.kind == CXType_ConstantArray || base.kind == CXType_IncompleteArray) {
        if (base.kind == CXType_Pointer) {
            base = clang_getPointeeType(base);
            depth++;
        } else {
            if (!arg_rules) {
                shape = array(32);
                sz size = clang_getArraySize(base);
                node component = operand(e, A_sz(size)); /// contains a literal on the node
                push(shape, component);
            } else {
                depth++;
            }
            base = clang_getArrayElementType(base);
        }
    }

    while (base.kind == CXType_Elaborated)
        base = clang_Type_getNamedType(base);

    switch (base.kind) {
        case CXType_Enum: {
            CXString n = clang_getTypeSpelling(base);
            symbol ename = clang_getCString(n);
            t = str(ename);
            if (starts_with(t, "enum "))
                t = mid(t, 5, len(t) - 5);
            clang_disposeString(n);
            break;
        }
        case CXType_Typedef: {
            CXString n = clang_getTypedefName(base);
            symbol  cs = clang_getCString(n);

            CXType canonicalType = clang_getCanonicalType(base);
            model  resolved_mdl  = cx_to_model(e, canonicalType, name, arg_rules);
            if (strcmp(cs, "A") == 0) {

                int test = 2;
                test += 2;
            }
            t = str(cs);
            clang_disposeString(n);
            if (!emodel(t->chars)) {
                CXType canonicalType = clang_getCanonicalType(base);
                model  resolved_mdl  = cx_to_model(e, canonicalType, name, arg_rules);
                model  typedef_mdl   = model_alias(resolved_mdl, t, reference_value, null);
                ether_push_model(e, typedef_mdl);
                return typedef_mdl;
            }
            break;
        }
        case CXType_Void:       t = str("void"); break;
        case CXType_Char_S:     t = str("i8");   break;
        case CXType_Char_U:     t = str("u8");   break;
        case CXType_SChar:      t = str("i8");   break;
        case CXType_UChar:      t = str("u8");   break;
        case CXType_Char16:     t = str("i16");  break;
        case CXType_Char32:     t = str("i32");  break;
        case CXType_Bool:       t = str("bool"); break;
        case CXType_UShort:     t = str("u16");  break;
        case CXType_Short:      t = str("i16");  break;
        case CXType_UInt:       t = str("u32");  break;
        case CXType_Int:        t = str("i32");  break;
        case CXType_ULong:      t = str("u64");  break;
        case CXType_Long:       t = str("i64");  break;
        case CXType_LongLong:   t = str("i64");  break;
        case CXType_ULongLong:  t = str("u64");  break;
        case CXType_Float:      t = str("f32");  break;
        case CXType_Double:     t = str("f64");  break;
        case CXType_LongDouble: t = str("f128"); break;
        case CXType_Record: {
            CXString n = clang_getTypeSpelling(base);
            t = str(clang_getCString(n));
            clang_disposeString(n);
            if (!emodel(t->chars)) {
                CXCursor rcursor       = clang_getTypeDeclaration(base);
                enum CXCursorKind kind = clang_getCursorKind(rcursor);
                bool anon              = clang_Cursor_isAnonymous(rcursor);
                record def;
                
                if (kind == CXCursor_StructDecl)
                    def = structure(
                        mod, e, from_include, e->current_include, name, t);
                else if (kind == CXCursor_UnionDecl)
                    def = uni( // lets assume its anonymous, how do we get the members associated to it?  how do you differentiate from the other peers if its blended into parent?  makes no sense.
                        mod, e, from_include, e->current_include, name, t);
                else {
                    fault("unknown record kind");
                }
                ether_push_model(e, def);
                clang_visitChildren(rcursor, visit_member, def);
                return def;
            }
            break;
        }
        default:
            t = str("void");
    }

    model mdl = emodel(t->chars);
    verify(mdl, "could not find %o", t);
    for (int i = 0; i < depth; i++)
        mdl = model_alias(mdl, null, reference_pointer, null); // this is not making a different 'type-ref' for ref -> i8

    if (shape && len(shape))
        mdl = model_alias(mdl, null, reference_value, shape);
    
    return mdl;
}

enum CXChildVisitResult visit_member(CXCursor cursor, CXCursor parent, CXClientData client_data) {
    model  type_def = (model)client_data;
    ether  e      = type_def->mod;
    enum CXCursorKind kind = clang_getCursorKind(cursor);
    if (kind == CXCursor_FieldDecl) {
        ether_push(e, type_def);
        //ether_pop(e);
        CXType   field_type    = clang_getCursorType(cursor);
        CXString field_name    = clang_getCursorSpelling(cursor);
        CXString field_ts      = clang_getTypeSpelling(field_type);
        symbol   field_type_cs = clang_getCString(field_ts);
        symbol   field_name_cs = clang_getCString(field_name);
        model    mdl = cx_to_model(e, field_type, (cstr)field_name_cs, false);
        member   mem = member(mod, e, mdl, mdl,
            name, string((cstr)field_name_cs), from_include, e->current_include);
        set(type_def->members, str(field_name_cs), mem);
        clang_disposeString(field_name);
        clang_disposeString(field_ts);
        ether_pop(e);
    }
    
    return CXChildVisit_Recurse;
}

enum CXChildVisitResult visit_enum_constant(CXCursor cursor, CXCursor parent, CXClientData client_data) {
    if (clang_getCursorKind(cursor) == CXCursor_EnumConstantDecl) {
        model         def = (model)client_data;
        ether           e = def->mod;
        CXString spelling = clang_getCursorSpelling(cursor);
        const char*  name = clang_getCString(spelling);
        long long   value = clang_getEnumConstantDeclValue(cursor);
        //member        mem = emember(emodel("i32"), name);
        member        mem = member(mod, e, mdl, emodel("i32"),
            name, string((cstr)name), from_include, e->current_include);
        set_value(mem, A_i32((i32)value)); /// this should set constant since it should know
        mem->is_const     = true;
        set(def->members, str(name), mem);
        clang_disposeString(spelling);
    }
    return CXChildVisit_Continue;
}

enum CXChildVisitResult visit(CXCursor cursor, CXCursor parent, CXClientData client_data) {
    ether       e = (ether)client_data;
    CXString  fcx = clang_getCursorSpelling(cursor);
    symbol     cs = clang_getCString(fcx);
    string   name = str(cs);
    model     def = null;
    enum CXCursorKind k = clang_getCursorKind(cursor);

    model current = emodel(name->chars);
    if   (current) return CXChildVisit_Continue;

    verify (!current, "duplicate definition when importing: %o", name);
    
    switch (k) {
        case CXCursor_EnumDecl: {
            def = enumerable( // or create a specific enum type
                mod,          e,
                from_include, e->current_include,
                size,         4,
                name,         name);
            
            // Visit enum constants
            clang_visitChildren(cursor, visit_enum_constant, def);
            break;
        }
        case CXCursor_FunctionDecl: {
            CXType   cx_rtype = clang_getCursorResultType(cursor);
            model    rtype    = cx_to_model(e, cx_rtype, null, true);
            int      n_args   = clang_Cursor_getNumArguments(cursor);
            arguments args    = arguments(mod, e);

            for (int i = 0; i < n_args; i++) {
                CXCursor arg_cursor = clang_Cursor_getArgument(cursor, i);
                CXString pcx        = clang_getCursorSpelling (arg_cursor);
                symbol   arg_name   = clang_getCString        (pcx);
                CXType   arg_cxtype = clang_getCursorType     (arg_cursor);
                CXString pcx_type   = clang_getTypeSpelling   (arg_cxtype);
                symbol   arg_type   = clang_getCString        (pcx_type);
                model    arg_mdl    = cx_to_model(e, arg_cxtype, arg_name, true);

                member   mem = emember(arg_mdl, arg_name);
                push(args, mem);
                clang_disposeString(pcx);
            }
            bool is_var = clang_Cursor_isVariadic(cursor);
            if (eq(name, "printf")) assert(is_var, "expected var arg");
            def = function(
                mod,            e,
                from_include,   e->current_include,
                name,           name,
                va_args,        is_var,
                rtype,          rtype,
                args,           args);

            /// read format attributes from functions, through llvm contribution
            /// PR #3.5k in queue, but its useful for knowing context in formatter functions
            CXCursor format = clang_Cursor_getFormatAttr(cursor);
            if (!clang_Cursor_isNull(format)) {
                CXString f_type  = clang_FormatAttr_getType     (format);
                symbol   f_stype = clang_getCString             (f_type);
                unsigned f_index = clang_FormatAttr_getFormatIdx(format);
                unsigned f_first = clang_FormatAttr_getFirstArg (format);
                ((function)def)->format = format_attr(
                    type, str(f_stype), format_index, f_index, arg_index, f_first);
                clang_disposeString(f_type);
            }
            break;
        }
        case CXCursor_StructDecl: {
            if (eq(name, "A")) {
                int test = 2;
                test += 2;
            }
            def = structure(
                mod,     e,
                from_include, e->current_include,
                name,       name);
            clang_visitChildren(cursor, visit_member, def);
            break;
        }
        case CXCursor_TypedefDecl: { /// these might be given out of order.
            CXType  underlying_type = clang_getTypedefDeclUnderlyingType(cursor);
            while (underlying_type.kind == CXType_Typedef) {
                CXCursor u = clang_getTypeDeclaration(underlying_type);
                underlying_type = clang_getTypedefDeclUnderlyingType(u);
            }
            CXString underlying_type_name = clang_getTypeSpelling(underlying_type);
            const char *type_name = clang_getCString(underlying_type_name);

            if (eq(name, "A")) {
                int test = 2;
                test += 2;
            }
            /// this may be a different depth, which we need to adjust for
            model model_base = underlying_type.kind ?
                cx_to_model(e, underlying_type, null, false) : null; 

            def = model_alias(model_base, name, 0, null);
            def->from_include = hold(e->current_include); 
            break;
        }
        default:
            break;
    }
    if (def) {
        ether_push_model(e, def);
    }
    clang_disposeString(fcx);
    return CXChildVisit_Recurse;
}

member model_initializer(model mdl) {
    /// create initialization function for module
    /// could be a bit more facilitated by apis in ether
    /// we need to also make this for class/struct defaults
    ether    e       = mdl->mod;
    model    rtype   = emodel("void");
    string   fn_name = format("_%o_init", mdl->name);
    function fn_init = function(
        mod,      mdl->mod,
        name,     token(chars, fn_name->chars),
        imdl,     mdl,
        rtype,    rtype,
        args,     arguments());
    
    /// we may place build cursor in function block and start building
    fn_init->process = string("placeholder");
    model_process_finalize(fn_init);

    /// we should start 'building' after this call,
    mdl->fn_init = push_model(e, fn_init);
    drop(fn_init->process);
    fn_init->process = null;

    /// but should be left to caller
    return mdl->fn_init;
}

/// return a map of defs found by their name (we can isolate the namespace this way by having separate maps)
void ether_include(ether e, string include) {
    string   include_path  = format("%o/include", e->install);
    path     full_path = null;
    symbol   ipaths[]  = {
        include_path->chars,
        "/usr/include"
    };
    symbol templates[3] = {
        "%s/%o-flat", /// this is how we read our A-types without a fancy pre-processor
        "%s/%o",
        "%s/%o.h"
    };
    bool br = false;
    for (int i = 0; !br && i < sizeof(ipaths) / sizeof(symbol); i++) {
        for (int ii = 0; ii < 3; ii++) {
            path r0 = form(path, templates[ii], ipaths[i], include);
            if (exists(r0)) {
                full_path = r0;
                br = true;
                break;
            }
        }
    }
    verify (full_path, "include path not found for %o", include);
    CXIndex index = clang_createIndex(0, 0);
    const char* args[] = {"-x", "c-header"}; /// allow 'A' to parse as a 
    CXTranslationUnit unit = clang_parseTranslationUnit(
        index, full_path->chars, args, 2, NULL, 0, CXTranslationUnit_None);

    verify(unit, "unable to parse translation unit %o", include);
    
    CXCursor cursor = clang_getTranslationUnitCursor(unit);
    e->current_include = full_path;
    clang_visitChildren(cursor, visit, (CXClientData)e);
    clang_disposeTranslationUnit(unit);
    clang_disposeIndex(index);
    e->current_include = null;
}


void ether_set_token(ether e, token t) {
    LLVMMetadataRef loc = LLVMDIBuilderCreateDebugLocation(
        e->module_ctx, t->line, t->column, e->top->scope, null);
    LLVMSetCurrentDebugLocation2(e->builder, loc);
}



void ether_llflag(ether e, symbol flag, i32 ival) {
    LLVMMetadataRef v = LLVMValueAsMetadata(
        LLVMConstInt(LLVMInt32Type(), ival, 0));

    char sflag[64];
    memcpy(sflag, flag, strlen(flag) + 1);
    LLVMAddModuleFlag(e->module, LLVMModuleFlagBehaviorError, sflag, strlen(sflag), v);
}


void ether_write(ether e) {
    cstr err = NULL;
    if (LLVMVerifyModule(e->module, LLVMPrintMessageAction, &err))
        fault("error verifying module");

    path ll = form(path, "%o.ll", e->name);
    path bc = form(path, "%o.bc", e->name);
    if (LLVMPrintModuleToFile(e->module, cstring(ll), &err))
        fault("LLVMPrintModuleToFile failed");

    if (LLVMWriteBitcodeToFile(e->module, cstring(bc)) != 0)
        fault("LLVMWriteBitcodeToFile failed");
}


void ether_llvm_init(ether e) {
    e->lex            = array(alloc, 32);
    //e->type_refs    = map(hsize, 64);
    e->module         = LLVMModuleCreateWithName(e->name->chars);
    e->module_ctx     = LLVMGetModuleContext(e->module);
    e->dbg_builder          = LLVMCreateDIBuilder(e->module);
    e->builder        = LLVMCreateBuilderInContext(e->module_ctx);
    e->target_triple  = LLVMGetDefaultTargetTriple();

    cstr err = NULL;
    if (LLVMGetTargetFromTriple(e->target_triple, &e->target, &err))
        fault("error: %s", err);
    e->target_machine = LLVMCreateTargetMachine(
        e->target, e->target_triple, "generic", "",
        LLVMCodeGenLevelDefault, LLVMRelocDefault, LLVMCodeModelDefault);
    
    e->target_data = LLVMCreateTargetDataLayout(e->target_machine);
    llflag(e, "Dwarf Version",      5);
    llflag(e, "Debug Info Version", 3);

    string src_file =      filename (e->source);
    string src_path = cast(string, directory(e->source));
    e->file = LLVMDIBuilderCreateFile( // create e file reference (the source file for debugging)
        e->dbg_builder,
        cast(cstr, src_file), cast(sz, src_file),
        cast(cstr, src_path), cast(sz, src_path));
    
    e->compile_unit = LLVMDIBuilderCreateCompileUnit(
        e->dbg_builder, LLVMDWARFSourceLanguageC, e->file,
        "silver", 6, 0, "", 0,
        0, "", 0, LLVMDWARFEmissionFull, 0, 0, 0, "", 0, "", 0);

    e->scope = e->compile_unit; /// this var is not 'current scope' on silver, its what silver's scope is initialized as

    path  full_path = form(path, "%o/%o", src_path, src_file);
    verify(exists(full_path), "source (%o) does not exist", full_path);
    e->builder = LLVMCreateBuilderInContext(e->module_ctx);

    // for silver, jit is probably misguided.
    // it does not need another test environment for all developers
    //if (LLVMCreateExecutionEngineForModule(&e->jit, e->module, &err))
    //    fault("failed to create execution engine: %s", err);
}


/// we may have a kind of 'module' given here; i suppose instanceof(ether) is enough
void ether_init(ether e) {
    e->with_debug = true;
    ether_llvm_init(e);
    e->lex = array(32);
    struct ether_f* table = isa(e);

    push(e, e);
    ether_define_primitive(e);
    //ether_define_generic(e); todo: import from A
}


void ether_destructor(ether e) {
    //LLVMDisposeExecutionEngine(e->jit);
    LLVMDisposeBuilder(e->builder);
    LLVMDisposeDIBuilder(e->dbg_builder);
    LLVMDisposeModule(e->module);
    LLVMContextDispose(e->module_ctx);
    LLVMDisposeMessage(e->target_triple);
}

/// C type rules implemented
model determine_rtype(ether e, OPType optype, model L, model R) {
    switch (optype) {
        case OPType__assign:
        case OPType__assign_add:
        case OPType__assign_sub:
        case OPType__assign_mul:
        case OPType__assign_div:
        case OPType__assign_or:
        case OPType__assign_and:
        case OPType__assign_xor:
        case OPType__assign_mod:
        case OPType__assign_right:
        case OPType__assign_left:
            return L;  // Assignment operations always return the type of the left operand
        
        case OPType__value_default:
        case OPType__cond_value:
        case OPType__or:
        case OPType__and:
        case OPType__xor:
            if (is_bool(L) && is_bool(R))
                return emodel("bool");  // Logical operations on booleans return boolean
            // For bitwise operations, fall through to numeric promotion
            break;

        default:
            //fault("not implemented");
            break;
    }

    // Numeric type promotion
    if (is_realistic(L) || is_realistic(R)) {
        // If either operand is float, result is float
        if (is_double(L) || is_double(R))
            return emodel("f64");
        else
            return emodel("f32");
    }

    // Integer promotion
    int L_size = L->size;
    int R_size = R->size;
    if (L_size > R_size)
        return L;
    else if (R_size > L_size)
        return R;

    bool L_signed = is_signed(L);
    bool R_signed = is_signed(R);
    if (L_signed && R_signed)
        return L;  // Both same size and signed
    else if (!L_signed && !R_signed)
        return L;  // Both same size and unsigned
    
    return L_signed ? R : L;  // Same size, one signed one unsigned
}


/// we may check against true/false/instance
/// here we are acting a bit more like python with A-type
/// its not caution to the wind, because no valid pointer can legally 
/// ever be 0x01 on any system in the world.
/// they lock up your threads if allocate one
member model_castable(model fr, model to) { 
    bool fr_ptr = fr->ref == reference_pointer;
    if ((fr_ptr || is_primitive(fr)) && is_bool(to))
        return (member)true;
    
    /// compatible by match, or with basic integral/real types
    if ((fr == to) ||
        ((is_realistic(fr) && is_realistic(to)) ||
         (is_integral (fr) && is_integral (to))))
        return (member)true;
    
    /// primitives may be converted to A-type object
    if (is_primitive(fr) && is_generic(to))
        return (member)true;

    /// check constructors on to
    /// single-arg construction model, same as as A-type
    pairs (to->members, i) {
        member mem = i->value;
        function fn = instanceof(mem->mdl, function);
        if (!fn || !(fn->function_type & A_TYPE_CONSTRUCT))
            continue;
        member first = null;
        pairs (fn->members, i) {
            member arg = i->value;
            first = arg;
            break;
        }
        verify(first, "invalid constructor");
        if (model_convertible(fr, first->mdl))
            return (member)true;
    }

    /// check cast methods on from
    pairs (fr->members, i) {
        member mem = i->value;
        function fn = instanceof(mem->mdl, function);
        if (!fn || !(fn->function_type & A_TYPE_CAST))
            continue;
        if (fn->rtype == to)
            return mem;
    }
    return (member)false;
}

/// constructors are reduced too, 
/// first arg as how we match them,
/// the rest are optional args by design
/// this cannot enforce required args ...which is a bit of a problem
/// so we may just check for those!
/// that would serve to limit applicable constructors and might be favored
member model_constructable(model fr, model to) {
    if (fr == to)
        return (member)true;
    pairs (to->members, i) {
        member mem = i->value;
        function fn = instanceof(mem->mdl, function);
        if (!fn || !(fn->function_type & A_TYPE_CONSTRUCT))
            continue;
        member first = null;
        pairs (fn->members, i) {
            first = i->value;
            break;
        }
        if (first->mdl == fr)
            return mem;
    }
    return (member)false;
}

member model_convertible(model fr, model to) {
    if (fr == to)
        return (member)true;
    member mcast = castable(fr, to);
    return mcast ? mcast : constructable(fr, to);
}

member ether_compatible(ether e, record r, string n, AFlag f, array args) {
    pairs (r->members, i) {
        member mem = i->value;
        function fn = instanceof(mem->mdl, function);
        /// must be function with optional name check
        if (!fn || (((f & fn->function_type) == f) && (n && !eq(n, fn->name->chars))))
            continue;
        /// arg count check
        if (len(fn->args) != len(args))
            continue;
        
        bool compatible = true;
        int ai = 0;
        each(fn->args->args, member, to_arg) {
            node fr_arg = args->elements[ai];
            if (!convertible(fr_arg->mdl, to_arg->mdl)) {
                compatible = false;
                break;
            }
            ai++;
        }
        if (compatible)
            return mem;
    }
    return (member)false;
}

node ether_negate(ether e, node L) {
    if (e->no_build) return node(mod, e);
    if (is_float(L->mdl))
        return LLVMBuildFNeg(e->builder, L->value, "f-negate");
    else if (is_signed(L->mdl)) // our enums should fall into this category
        return LLVMBuildNeg(e->builder, L->value, "i-negate");
    else if (is_unsigned(L->mdl)) {
        // Convert unsigned to signed, negate, then convert back to unsigned
        LLVMValueRef signed_value  = LLVMBuildIntCast2(
            e->builder, L->value, LLVMIntType(L->mdl->size * 8), 1, "to-signed");
        LLVMValueRef negated_value = LLVMBuildNeg(
            e->builder, signed_value, "i-negate");
        model i64 = emodel("i64");
        LLVMValueRef i64_value = LLVMBuildIntCast2(
            e->builder, negated_value, i64->type, 1, "to-i64");
        return value(i64, negated_value);
    }
    else {
        fault("object negation not valid");
    }
}

node ether_not(ether e, node L) {
    if (e->no_build) return node(mod, e);
    LLVMValueRef result;
    if (is_float(L->mdl->type)) {
        // for floats, compare with 0.0 and return true if > 0.0
        result = LLVMBuildFCmp(e->builder, LLVMRealOLE, L->value,
                               LLVMConstReal(L->mdl->type, 0.0), "float-not");
    } else if (is_unsigned(L->mdl->type)) {
        // for unsigned integers, compare with 0
        result = LLVMBuildICmp(e->builder, LLVMIntULE, L->value,
                               LLVMConstInt(L->mdl->type, 0, 0), "unsigned-not");
    } else {
        // for signed integers, compare with 0
        result = LLVMBuildICmp(e->builder, LLVMIntSLE, L->value,
                               LLVMConstInt(L->mdl->type, 0, 0), "signed-not");
    }
    return value(emodel("bool"), result);
}

node ether_bitwise_not(ether e, node L) {
    if (e->no_build) return node(mod, e);
    return LLVMBuildNot(e->builder, L->value, "bitwise-not");
}

// object o = obj("type-name", props)
node ether_eq(ether e, node L, node R);

node ether_is(ether e, node L, object R) {
    if (e->no_build) return node(mod, e);
    node L_type =  offset(e, L, A_i64(-sizeof(A)));
    node L_ptr  =    load(e, L_type); /// must override the mdl type to a ptr, but offset should not perform a unit translation but rather byte-based
    node R_ptr  = operand(e, R);
    return ether_eq(e, L_ptr, R_ptr);
}

node ether_eq(ether e, node L, node R) {
    if (e->no_build) return node(mod, e);
    model t0 = L->mdl;
    model t1 = R->mdl;
    verify (t0 == t1, "types must be same at primitive operation level");
    bool i0 = is_integral(t0);
    bool f0 = is_realistic(t1);
    if (i0 || !f0)
        return value(emodel("bool"), LLVMBuildICmp(e->builder, LLVMIntEQ,   L->value, R->value, "eq-i"));
    return     value(emodel("bool"), LLVMBuildFCmp(e->builder, LLVMRealOEQ, L->value, R->value, "eq-f"));
}

node ether_not_eq(ether e, node L, node R) {
    if (e->no_build) return node(mod, e);
    model t0 = L->mdl;
    model t1 = R->mdl;
    verify (t0 == t1, "types must be same at primitive operation level");
    bool i0 = is_integral(t0);
    bool f0 = is_realistic(t1);
    if (i0 || !f0)
        return value(emodel("bool"), LLVMBuildICmp(e->builder, LLVMIntNE,   L->value, R->value, "not-eq-i"));
    return     value(emodel("bool"), LLVMBuildFCmp(e->builder, LLVMRealONE, L->value, R->value, "not-eq-f"));
}

node ether_fn_return(ether e, object o) {
    if (e->no_build) return node(mod, e);
    function fn = context_model(e, typeid(function));
    verify (fn, "function not found in context");

    if (!o) return value(fn->rtype, LLVMBuildRetVoid(e->builder));

    node conv = ether_convert(e, operand(e, o), fn->rtype);
    return value(fn->rtype, LLVMBuildRet(e->builder, conv->value));
}

model formatter_type(ether e, cstr input) {
    cstr p = input;
    // skip flags/width/precision
    while (*p && strchr("-+ #0123456789.", *p)) p++;
    if (strncmp(p, "lld", 3) == 0 || 
        strncmp(p, "lli", 3) == 0) return emodel("i64");
    if (strncmp(p, "llu", 3) == 0) return emodel("u64");
    
    switch (*p) {
        case 'd': case 'i':
                  return emodel("i32"); 
        case 'u': return emodel("u32");
        case 'f': case 'F': case 'e': case 'E': case 'g': case 'G':
                  return emodel("f64");
        case 's': return emodel("symbol");
        case 'p': return model_alias(emodel("i8"), null, reference_pointer, null);
    }
    fault("formatter implementation needed");
    return null;
}

node ether_fn_call(ether e, member fn_mem, array args) {
    if (e->no_build) return node(mod, e);
    verify(isa(fn_mem->mdl) == typeid(function), "model provided is not function");
    function fn = fn_mem->mdl;
    use(fn); /// value and type not registered until we use it (sometimes; less we are exporting this from module)
    int n_args = len(args);
    LLVMValueRef* arg_values = calloc((fn_mem->target_member != null) + n_args, sizeof(LLVMValueRef));
    //verify (LLVMTypeOf(fdef->function->value) == fdef->ref, "integrity check failure");
    LLVMTypeRef  F = fn->type;
    LLVMValueRef V = fn->value; // todo: args in ether should be a map.  that way we can do a bit more

    int index = 0;
    verify(!!fn_mem->target_member == !!fn->target, "target mismatch");
    //member target = fn_mem->target_member;
    if (fn->target)
        arg_values[index++] = fn_mem->target_member->value;

    /// so know if we have a literal string or not
    /// if we dont, then how on earth are we supposed to know what to do with args lol
    /// i think we dont allow it..
    int fmt_idx  = fn->format ? fn->format->format_index - 1 : -1;
    int arg_idx  = fn->format ? fn->format->arg_index    - 1 : -1;
    each (args, object, value) {
        if (index == arg_idx) break;
        if (index == fmt_idx) {
            index++;
            continue;
        }

        member    f_arg = get(fn->args, index);
        AType     vtype = isa(value);
        node      op    = operand(e, value);
        node      conv  = ether_convert(e, op, f_arg ? f_arg->mdl : op->mdl);
        
        LLVMValueRef vr = arg_values[index] = conv->value;
        //print("ether_fcall: %o arg[%i]: vr: %p, type: %s", fn_mem->name, index, vr, LLVMPrintTypeToString(LLVMTypeOf(vr)));
        index++;
    }
    int istart = index;

    if (fn->format) {
        AType a0 = isa(args->elements[fmt_idx]);
        node   fmt_node = instanceof(args->elements[fmt_idx], node);
        string fmt_str  = instanceof(fmt_node->literal, string);
        verify(fmt_str, "expected string literal at index %i for format-function: %o", fmt_idx, fn->name);
        arg_values[fmt_idx] = fmt_node->value;
        // process format specifiers and map to our types
        int soft_args = 0;
        cstr p = fmt_str->chars;
        // we will have to convert %o to %s, unless we can be smart with %s lol.
        // i just dont like how its different from A-type
        // may simply be fine to use %s for string, though.  its natural to others
        // alternately we may copy the string from %o to %s.
        while  (p[0]) {
            if (p[0] == '%' && p[1] != '%') {
                model arg_type = formatter_type(e, &p[1]);
                node  arg      = operand(e, args->elements[arg_idx + soft_args]);
                node  conv     = ether_convert(e, arg, arg_type); 
                arg_values[arg_idx + soft_args] = conv->value;
                soft_args++;
                index    ++;
                p += 2;
            } else
                p++;

        }
        verify((istart + soft_args) == len(args), "%o: formatter args mismatch", fn->name);
    }
    
    bool is_void_ = is_void(fn->rtype);
    LLVMValueRef R = LLVMBuildCall2(e->builder, F, V, arg_values, index, is_void_ ? "" : "call");
    free(arg_values);
    return value(fn->rtype, R);
}

/// ether is language agnostic so the user must pass the overload method
node ether_op(ether e, OPType optype, string op_name, object L, object R) {
    if (e->no_build) return node(mod, e);
    member mL = instanceof(L, member); 
    node   LV = operand(e, L);
    node   RV = operand(e, R);

    /// check for overload
    if (op_name && isa(op_name) == typeid(node) && is_class(((node)L)->mdl)) {
        node Ln = L;
        AType type = isa(Ln->mdl);
        if (type == typeid(structure) || type == typeid(record)) {
            record rec = Ln->mdl;
            member Lt = get(rec->members, op_name);
            if  (Lt && isa(Lt->mdl) == typeid(function)) {
                function fn = Lt->mdl;
                verify(len(fn->args) == 1, "expected 1 argument for operator method");
                /// convert argument and call method
                model  arg_expects = get(fn->args, 0);
                node  conv = ether_convert(e, Ln, arg_expects);
                array args = array_of(null, conv, null);
                verify(mL, "mL == null");
                member fmem = member(mod, e, mdl, Lt->mdl, name, Lt->name, target_member, mL);
                return fn_call(e, fmem, args); // todo: fix me: Lt must have target_member associated, so allocate a member() for this
            }
        }
    }

    /// LV cannot change its type if it is a member and we are assigning
    model rtype = determine_rtype(e, optype, LV->mdl, RV->mdl);
    LLVMValueRef RES;
    node LL = optype == OPType__assign ? LV : convert(e, LV, rtype); // we dont need the 'load' in here, or convert even
    node RL = convert(e, RV, rtype);

    symbol         N = cstring(op_name);
    LLVMBuilderRef B = e->builder;
    /// if are not storing ...
    if (optype >= OPType__add && optype <= OPType__left) {
        RES = op_table[optype - OPType__add].f_op(B, LL->value, RL->value, N);
    } else {
        /// 
        verify(optype >= OPType__assign && optype <= OPType__assign_left, "invalid assignment operation");
        verify(mL, "left-hand operator must be a member");
        /// already computed in R-value
        if (optype == OPType__assign)
            RES = RL->value;
        else
        /// store from operation we call, membered in OPType enumeration
            RES = op_table[optype - OPType__assign_add].f_op(B, LL->value, RL->value, N);
        LLVMBuildStore(B, RES, mL->value);
    }
    return node(
        mod,        e,
        mdl,        rtype,
        value,      RES);
}

node ether_or (ether e, object L, object R) { return ether_op(e, OPType__or,  str("or"),  L, R); }
node ether_xor(ether e, object L, object R) { return ether_op(e, OPType__xor, str("xor"), L, R); }
node ether_and(ether e, object L, object R) { return ether_op(e, OPType__and, str("and"), L, R); }
node ether_add(ether e, object L, object R) { return ether_op(e, OPType__add, str("add"), L, R); }
node ether_sub(ether e, object L, object R) { return ether_op(e, OPType__sub, str("sub"), L, R); }
node ether_mul(ether e, object L, object R) { return ether_op(e, OPType__mul, str("mul"), L, R); }
node ether_div(ether e, object L, object R) { return ether_op(e, OPType__div, str("div"), L, R); }
node ether_value_default(ether e, object L, object R) { return ether_op(e, OPType__value_default, str("value_default"), L, R); }
node ether_cond_value   (ether e, object L, object R) { return ether_op(e, OPType__cond_value,    str("cond_value"), L, R); }

node ether_inherits(ether e, node L, object R) {
    if (e->no_build) return node(mod, e);
    // Get the type pointer for L
    node L_type =  offset(e, L, A_i64(-sizeof(A)));
    node L_ptr  =    load(e, L);
    node R_ptr  = operand(e, R);

    // Create basic blocks for the loopf
    LLVMBasicBlockRef block      = LLVMGetInsertBlock(e->builder);
    LLVMBasicBlockRef loop_block = LLVMAppendBasicBlock(block, "inherit_loop");
    LLVMBasicBlockRef exit_block = LLVMAppendBasicBlock(block, "inherit_exit");

    // Branch to the loop block
    LLVMBuildBr(e->builder, loop_block);

    // Loop block
    LLVMPositionBuilderAtEnd(e->builder, loop_block);
    LLVMValueRef phi = LLVMBuildPhi(e->builder, L_ptr->mdl->type, "current_type");
    LLVMAddIncoming(phi, &L_ptr->value, &block, 1);

    // Compare current type with R_type
    node cmp       = ether_eq(e, value(L_ptr->mdl, phi), R_ptr);

    // Load the parent pointer (assuming it's the first member of the type struct)
    node parent    = ether_load(e, value(L_ptr->mdl, phi));

    // Check if parent is null
    node is_null   = ether_eq(e, parent, value(parent->mdl, LLVMConstNull(parent->mdl->type)));

    // Create the loop condition
    node not_cmp   = ether_not(e, cmp);
    node not_null  = ether_not(e, is_null);
    node loop_cond = ether_and(e, not_cmp, not_null);

    // Branch based on the loop condition
    LLVMBuildCondBr(e->builder, loop_cond->value, loop_block, exit_block);

    // Update the phi node
    LLVMAddIncoming(phi, &parent->value, &loop_block, 1);

    // Exit block
    LLVMPositionBuilderAtEnd(e->builder, exit_block);
    LLVMValueRef result = LLVMBuildPhi(e->builder, cmp->mdl->type, "inherit_result");
    LLVMAddIncoming(result, &cmp->value, &loop_block, 1);
    LLVMAddIncoming(result, &(LLVMValueRef){LLVMConstInt(LLVMInt1Type(), 0, 0)}, &block, 1);

    return value(emodel("bool"), result);
}


void ether_build(ether e) {
    /// define structs and classes before we write our functions (which reference the members)
    pairs(e->members, i) {
        member mem  = i->value;
        string name = instanceof(i->key, string);
        record rec  = instanceof(mem->mdl, record);
        if (rec)
            model_process_finalize(rec);
    }
    pairs(e->members, i) {
        member mem = i->value;
        model  f   = mem->mdl;
        if (isa(f) == typeid(function)) {
            function fn = f;
            if (fn->process) {
                push(e, fn);
                invoke(fn->process, f);
                pop(e);
            }
        }
    }
}

model ether_top(ether e) {
    return e->top;
}

A read_numeric(token a) {
    cstr cs = cstring(a);
    bool is_digit = cs[0] >= '0' && cs[0] <= '9';
    bool has_dot  = strstr(cs, ".") != 0;
    if (!is_digit && !has_dot)
        return null;
    char* e = null;
    if (!has_dot) {
        i64 v = strtoll(cs, &e, 10);
        return A_primitive(typeid(i64), &v);
    }
    f64 v = strtod(cs, &e);
    return A_primitive(typeid(f64), &v);
}

string token_location(token a) {
    string f = format("%o:%i:%i", a->source, a->line, a->column);
    return f;
}

AType token_get_type(token a) {
    return a->literal ? isa(a->literal) : null;
}

sz token_len(token a) {
    return a->len;
}

bool token_eq(token a, cstr cs) {
    return strcmp(a->chars, cs) == 0;
}

num token_cmp(token a, cstr cs) {
    return strcmp(a->chars, cs);
}

cstr token_cast_cstr(token a) {
    return a->chars;
}

string token_cast_string(token a) {
    return string(a->chars);
}

AType token_is_bool(token a) {
    string t = cast(string, a);
    return (cmp(t, "true") || cmp(t, "false")) ?
        (AType)typeid(bool) : null;
}

num token_compare(token a, token b) {
    return strcmp(a->chars, b->chars);
}

bool token_cast_bool(token a) {
    return a->len > 0;
}

string read_string(cstr cs) {
    int ln = strlen(cs);
    string res = string(alloc, ln);
    char*   cur = cs;
    while (*cur) {
        int inc = 1;
        if (cur[0] == '\\') {
            symbol app = null;
            switch (cur[1]) {
                case 'n':  app = "\n"; break;
                case 't':  app = "\t"; break;
                case 'r':  app = "\r"; break;
                case '\\': app = "\\"; break;
                case '\'': app = "\'"; break;
                case '\"': app = "\""; break;
                case '\f': app = "\f"; break;
                case '\v': app = "\v"; break;
                case '\a': app = "\a"; break;
                default:   app = "?";  break;
            }
            inc = 2;
            append(res, app);
        } else {
            char app[2] = { cur[0], 0 };
            append(res, app);
        }
        cur += inc;
    }
    return res;
}

bool model_has_scope(model mdl) {
    return !!mdl->scope;
}

void token_init(token a) {
    cstr prev = a->chars;
    sz length = a->len ? a->len : strlen(prev);
    a->chars  = (cstr)calloc(length + 1, 1);
    a->len    = length;
    a->namespace = null;
    memcpy(a->chars, prev, length);

    if (a->chars[0] == '\"' || a->chars[0] == '\'') {
        string crop = string(chars, &a->chars[1], ref_length, length - 2);
        a->literal = read_string(crop->chars);
    } else
        a->literal = read_numeric(a);
}

void    arguments_init  (arguments a)               { if (!a->args) a->args = array(32); }
object  arguments_get   (arguments a, num i)        { return a->args->elements[i]; }

void    arguments_push  (arguments a, member mem)   { push(a->args, mem); }

member  arguments_pop   (arguments a)               { return pop(a->args); }

sz      arguments_len   (arguments a)               { return len(a->args); }

// anything with a f_* is member field data
define_enum      (interface)
define_enum      (reference)
define_enum      (comparison)
define_class     (model)
define_class     (format_attr)
define_mod       (statements,  model)
define_mod       (arguments,   model)
define_mod       (function,    model)
define_mod       (record,      model)
define_mod       (uni,         record)
define_mod       (enumerable,  record)
define_mod       (structure,   record)
define_mod       (class,       record)
define_mod       (ether,       model)
define_class     (code)
define_class     (token)
define_class     (node)
define_mod       (member,      node)