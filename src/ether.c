#include <llvm-c/DebugInfo.h>
#include <llvm-c/Core.h>
#include <llvm-c/ExecutionEngine.h>
#include <llvm-c/Target.h>
#include <llvm-c/Analysis.h>
#include <llvm-c/TargetMachine.h>
#include <llvm-c/BitWriter.h>
#include <clang-c/Index.h>

typedef LLVMMetadataRef LLVMScope;

#define     ether_intern  intern(ether)
#define      node_intern  intern(node)
#define      type_intern  intern(type)
#define    member_intern  intern(member)
#define     fcall_intern  intern(fcall)
#define     model_intern  intern(model)
#define    record_intern  intern(record)
#define structure_intern  intern(structure)
#define     class_intern  intern(class)
#define  function_intern  intern(function)
#define        op_intern  intern(op)
#define       ret_intern  intern(ret)
#define     token_intern  intern(token)

#include <ether>

// def -> base for change from type to member (member has model 
#define ecall(M, ...) ether_##M(e, ## __VA_ARGS__)
#define elookup(name) ((member)ether_lookup(e, str(name)))
#define emodel(N)     ({            \
    member  m = elookup(N);         \
    model mdl = m ? m->mdl : null;  \
    mdl;                            \
})

#define emember(M, N) new(member, mod, e, name, str(N), mdl, M);

member ether_lookup(ether e, string name);

void ether_push_model(ether e, model mdl) {
    member mem   = emember (mdl, mdl->name->chars);
    mem->is_func = inherits(mdl, function);
    mem->is_type = !mem->is_type;
    set(e->top->members, str(mdl->name->chars), mem);
}

void ether_push_member(ether e, member mem) {
    set(e->top->members, str(mem->name->chars), mem);
}

#define no_target null

static map operators;

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

bool is_void     (model f) {
    return f ? f->size == 0 : false;
}

bool is_object   (model f) {
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
    return isa(f) == typeid(model);
}

void init() {
    LLVMInitializeNativeTarget();
    LLVMInitializeNativeAsmPrinter();

    print("ether: LLVM Version: %d.%d.%d",
        LLVM_VERSION_MAJOR,
        LLVM_VERSION_MINOR,
        LLVM_VERSION_PATCH);
    
    operators = map_of(
        "+",        str("add"),
        "-",        str("sub"),
        "*",        str("mul"),
        "/",        str("div"),
        "||",       str("or"),
        "&&",       str("and"),
        "^",        str("xor"),
        ">>",       str("right"),
        "<<",       str("left"),
        ":",        str("assign"),
        "=",        str("assign"),
        "+=",       str("assign_add"),
        "-=",       str("assign_sub"),
        "*=",       str("assign_mul"),
        "/=",       str("assign_div"),
        "|=",       str("assign_or"),
        "&=",       str("assign_and"),
        "^=",       str("assign_xor"),
        ">>=",      str("assign_right"),
        "<<=",      str("assign_left"),
        "==",       str("compare_equal"),
        "!=",       str("compare_not"),
        "%=",       str("mod_assign"),
        "is",       str("is"),
        "inherits", str("inherits"), null
    );
}

module_init(init);

void model_process_finalize(model mdl) { // nobody calls finalize except us, here
    ether e = mdl->mod;
    if (mdl->finalized) return;
    mdl->finalized = true;
    if (mdl->process) {
        push(e, mdl);
        invoke(mdl->process, mdl);
        mdl->process = null;
        pop(e);
    }
    call(mdl, finalize);
}

/// 'record' does things with this, as well as 'function'
void model_finalize(model mdl) {
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

    if (mdl->name && inherits(mdl->name, string)) {
        string n = mdl->name;
        mdl->name = new(token, chars, cs(n), source, e ? e->source : null, line, 1);
    }

    if (mdl->name && eq(mdl->name, "__fsid_t")) {
        int test = 0;
        test++;
    }

    mdl->members = new(map, hsize, 32);

    if (!mdl->src) {
        //verify (!e, "only ether model does not have 'src'");
        return;
    }

    /// narrow down type traits
    string name = cast(mdl, string);
    model mdl_src = mdl;
    if (isa(mdl_src) == typeid(model)) {
        while (isa(mdl_src) == typeid(model) && mdl_src->src) {
            if (mdl_src->ref)
                break;
            mdl_src = mdl_src->src;
        }
    }

    AType type = isa(mdl_src);

    if (type->traits & A_TRAIT_PRIMITIVE) {
        if      (type == typeid(f32))
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
                    ptr_sz * 8, 0, 0, cs(name), len(name));
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
    if (mdl->type != LLVMVoidType()) {
        mdl->size      = LLVMABISizeOfType     (mdl->mod->target_data, mdl->type);
        mdl->alignment = LLVMABIAlignmentOfType(mdl->mod->target_data, mdl->type);
    }
}

model model_alias(model src, string name, reference r, array shape);

void function_finalize(function fn) {
    ether e = fn->mod;
    int index = 0;
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
        
        LLVMValueRef decl  = LLVMDIBuilderInsertDeclareBefore(
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
             cs(arg->name),    // Parameter name
            len(arg->name),
            1 + index,         // Argument index (starting from 1, not 0)
            e->file,           // File where it's defined
            arg->name->line,   // Line number
            arg->mdl->debug,   // Debug type of the parameter (LLVMMetadataRef for type)
            1,                 // AlwaysPreserve (1 to ensure the variable is preserved in optimized code)
            0                  // Flags (typically 0)
        );
        LLVMValueRef param_value = LLVMGetParam(fn->value, index);
        LLVMValueRef decl        = LLVMDIBuilderInsertDeclareAtEnd(
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
    /// create function and its debug information
    int              n_args    = len(fn->args);
    LLVMTypeRef*     arg_types = calloc((fn->target != null) + n_args, sizeof(LLVMTypeRef));
    int              index     = 0;

    if (fn->record) {
        verify (isa(fn->record) == typeid(structure) || 
                isa(fn->record) == typeid(class),
            "target [incoming] must be record type (struct / class) -- it is then made pointer-to record");
        model target_type = !fn->is_instance ? fn->record : model_alias(fn->record, fn->name, reference_pointer, null);
        fn->target = emember(target_type, fn->name->chars);
        arg_types[index++] = fn->target->mdl->type;
        // verify this is a pointer type here! LLVMPointerType(fn->target->ref, 0);
    }

    print("function %o", fn->name);
    each(fn->args, member, arg) {
        verify (arg->mdl->type, "no LLVM type found for arg %o", arg->name);
        arg_types[index++] = arg->mdl->type;
        print("arg type [%i] = %s", index - 1,
            LLVMPrintTypeToString(arg->mdl->type));
    }

    fn->type  = LLVMFunctionType(fn->rtype->type, arg_types, index, fn->va_args);
    fn->value = LLVMAddFunction(e->module, fn->name->chars, fn->type);
    print("adding function: %o, type: %p, value: %p (va_args: %i)", fn->name, fn->type, fn->value, fn->va_args);
    //free(arg_types); (llvm seems to not copy these)

    LLVMSetLinkage(fn->value,
        fn->access == interface_intern ? LLVMInternalLinkage : LLVMExternalLinkage);

    if (!fn->process)
        return;
    
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
        cs(fn->name), len(fn->name),
        cs(fn->name), len(fn->name),
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

    LLVMPositionBuilderAtEnd(e->builder, fn->entry);
    // may need to push/pop the fn temporarily
    
    if (LLVMGetBasicBlockTerminator(fn->entry) == NULL) {
        // Set the debug location manually
        LLVMMetadataRef loc = LLVMDIBuilderCreateDebugLocation(
            e->module_ctx, fn->name->line, 0, fn->scope, NULL);
        LLVMSetCurrentDebugLocation2(e->builder, loc);
    }

    /// create debug info for arguments (including target)
    index = 0;
    if (fn->target) {
        fn->target->value = LLVMGetParam(fn->value, index++);
    }
    each(fn->args, member, arg) {
        arg->value = LLVMGetParam(fn->value, index++);
    }
}

void record_finalize(record rec) {
    ether e = rec->mod;
    int total = 0;
    record r = rec;
    array a = new(array, alloc, 32);
    while (r) {
        total += len(rec->members);
        push(a, r);
        r = r->parent;
    }
    LLVMTypeRef*     member_types = calloc(total, sizeof(LLVMTypeRef));
    LLVMMetadataRef* member_debug = calloc(total, sizeof(LLVMMetadataRef));
    bool is_uni = inherits(rec, uni);
    int index = 0;
    member largest = null;
    sz  sz_largest = 0;
    each (a, record, r) {
        pairs(r->members, i) {
            member mem = i->value;
            verify( mem->name,  "no name on member");
            verify(!mem->debug, "debug info already present on member created for structure");
            model_process_finalize(mem->mdl);
            if (instanceof(mem->mdl, function))
                continue;
            mem->debug = LLVMDIBuilderCreateMemberType(
                e->dbg_builder,              // LLVMDIBuilderRef
                e->top->scope,         // Scope of the member (can be the struct, class or base module)
                cs(mem->name),         // Name of the member
                len(mem->name),        // Length of the name
                e->file,               // The file where the member is declared
                mem->name->line,       // Line number where the member is declared
                mem->mdl->size * 8,    // Size of the member in bits (e.g., 32 for a 32-bit int)
                mem->mdl->alignment * 8, // Alignment of the member in bits
                0,                     // Offset in bits from the start of the struct or class
                0,                     // Debug info flags (e.g., 0 for none)
                mem->mdl->debug        // The LLVMMetadataRef for the member's type (created earlier)
            );

            /// this member would have been init'd already, so it may have debug however we have no debug for this 'structure'
            member_types[index]   = mem->mdl->type;

            LLVMTargetDataRef target_data = rec->mod->target_data;
            symbol cs = LLVMPrintTypeToString(mem->mdl->type);
            print("type for %o %o = %s", rec->name, mem->name, cs);
            int sz1 = LLVMABISizeOfType(target_data, mem->mdl->type);
            member_debug[index++] = mem->debug;
            print("member on %o:%o %i", rec->name, i->key, (int)sz1);
            if (!sz_largest || sz1 > sz_largest) {
                largest = mem;
                sz_largest = sz1;
            }
        }
    }
    if (is_uni) {
        verify(sz_largest, "cannot determine size of union");
        LLVMStructSetBody(rec->type, &largest->mdl->type, 1, 0);
    } else
        LLVMStructSetBody(rec->type, member_types, index, 0);
    
    LLVMTargetDataRef target_data = rec->mod->target_data;
    int sz = LLVMABISizeOfType     (target_data, rec->type);
    int al = LLVMABIAlignmentOfType(target_data, rec->type);

    LLVMMetadataRef prev = rec->debug;

    // mdl is required on member
    rec->debug = LLVMDIBuilderCreateStructType(
        e->dbg_builder,                     // Debug builder
        e->top->scope,                // Scope (module or file)
        cs(rec->name),                // Name of the struct
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
    rec->type = LLVMStructCreateNamed(LLVMGetGlobalContext(), rec->name->chars);
    // Create a forward declaration for the struct's debug info
    rec->debug = LLVMDIBuilderCreateReplaceableCompositeType(
        e->dbg_builder,                      // Debug builder
        LLVMDwarfTag(DW_TAG_structure_type), // Tag for struct
         cs(rec->name),                      // Name of the struct
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
    
    if (len(rec->members))
        model_process_finalize(rec);
}

member member_resolve(member mem, string name) {
    ether  e   = mem->mod;
    i64  index = 0;
    pairs(mem->mdl->members, i) {
        if (compare(i->key, name) == 0) {
            member schema = i->value;
            member res = emember(schema->mdl, name->chars);
            function fn = instanceof(schema->mdl, function);
            res->value = fn ? fn->value : LLVMBuildStructGEP2(
                    e->builder, mem->mdl->type, mem->value, index, "resolve");
            /// store what target this member came from
            res->target = mem;
            if (fn)
                res->is_func = true;
            return res;
        }
        index++;
    }
    fault("member %o not found in type %o", name, mem->mdl->name);
    return null;
}

void member_set_debug(member mem) {
    ether    e  = mem->mod;
    function fn = ether_context_model(e, typeid(function));

    /// if we are creating a new member inside of a function, we need
    /// to make debug and value info here
    if (fn) {
        verify (!mem->value, "value-ref already set auto member");

        mem->value = LLVMBuildAlloca(e->builder, mem->mdl->type, cs(mem->name));
        mem->debug = LLVMDIBuilderCreateAutoVariable(
            e->dbg_builder,           // DIBuilder reference
            fn->scope,          // The scope (subprogram/function metadata)
             cs(mem->name),     // Variable name
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

        LLVMDIBuilderInsertDeclareBefore(
            e->dbg_builder,                   // The LLVM builder
            mem->value,                 // The LLVMValueRef for the first parameter
            mem->debug,                 // The debug metadata for the first parameter
            LLVMDIBuilderCreateExpression(e->dbg_builder, NULL, 0), // Empty expression
            LLVMGetCurrentDebugLocation2(e->builder),       // Current debug location
            firstInstr);
    }
}

void member_init(member mem) {
    ether e   = mem->mod;
    model top = e->top;

    if (inherits(mem->name, string)) {
        string n = mem->name;
        mem->name = new(token, chars, cs(n), source, e->source, line, 1);
    }

    /// members are stored in context
    /// we can technically bring this one back due to the use of composite debug allowing us to create context info
    //string n = str(mem->name->chars);
    //if (!mem->is_arg && !instanceof(top, non_registered)) {
        //verify (!contains(top->members, n), "duplicate member definition");
        //set(top->members, n, mem);
    //}

    if (!mem->mdl->debug)
        return;
    
    member_set_debug(mem);
}

void op_init(op op) {
    /// lets create everything we need for LLVM call here
}


void ret_init(ret op) {
    /// lets create everything we need for LLVM call here
}

#define value(m,vr) new(node, mod, e, value, vr, mdl, m)


static node operand(ether e, object op) {
    if (!op) return value(emodel("void"), null);

         if (inherits(op,   node)) return op;
    else if (inherits(op,     u8)) return value(emodel("u8"),  LLVMConstInt (emodel( "u8")->type, *( u8*)op, 0));
    else if (inherits(op,    u16)) return value(emodel("u16"), LLVMConstInt (emodel("u16")->type, *(u16*)op, 0));
    else if (inherits(op,    u32)) return value(emodel("u32"), LLVMConstInt (emodel("u32")->type, *(u32*)op, 0));
    else if (inherits(op,    u64)) return value(emodel("u64"), LLVMConstInt (emodel("u64")->type, *(u64*)op, 0));
    else if (inherits(op,     i8)) return value(emodel("i8"),  LLVMConstInt (emodel( "i8")->type, *( i8*)op, 0));
    else if (inherits(op,    i16)) return value(emodel("i16"), LLVMConstInt (emodel("i16")->type, *(i16*)op, 0));
    else if (inherits(op,    i32)) return value(emodel("i32"), LLVMConstInt (emodel("i32")->type, *(i32*)op, 0));
    else if (inherits(op,    i64)) return value(emodel("i64"), LLVMConstInt (emodel("i64")->type, *(i64*)op, 0));
    else if (inherits(op,    f32)) return value(emodel("f32"), LLVMConstReal(emodel("f32")->type, *(f32*)op));
    else if (inherits(op,    f64)) return value(emodel("f64"), LLVMConstReal(emodel("f64")->type, *(f64*)op));
    else if (inherits(op, string)) {
        LLVMTypeRef  gs      = LLVMBuildGlobalStringPtr(e->builder, ((string)op)->chars, "chars");
        LLVMValueRef cast_i8 = LLVMBuildBitCast(e->builder, gs, LLVMPointerType(LLVMInt8Type(), 0), "cast_i8*");
        return value(emodel("i8"), cast_i8);
    }
    else {
        error("unsupported type in ether_add");
        return NULL;
    }
}

model model_alias(model src, string name, reference r, array shape) {
    record rec = instanceof(src, record);
    if (rec)
        model_process_finalize(rec);
    model  ref = new(model,
        mod,    src->mod,
        name,   name,
        shape,  shape,
        ref,    r,
        src,   src);
    return ref;
}

node ether_if_else(ether e, array conds, array exprs,
        subprocedure cond_builder, subprocedure expr_builder) {
    verify(len(conds) == len(exprs) - 1 || 
           len(conds) == len(exprs), "mismatch between conditions and expressions");
    
    LLVMBasicBlockRef block = LLVMGetInsertBlock(e->builder);
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

        // Set the conditional branch
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

    // Handle the final "else" (if applicable)
    if (len(exprs) > len(conds)) {
        object else_expr = exprs->elements[len(conds)];
        invoke(expr_builder, else_expr);  // Process the final else block
        LLVMBuildBr(e->builder, merge);
    }

    // Move the builder to the merge block
    LLVMPositionBuilderAtEnd(e->builder, merge);

    // Return some node or result if necessary (e.g., a node indicating the overall structure)
    return new(node, mod, e, mdl, emodel("void"), value, null);  // Dummy node, replace with real node if needed
}

node ether_addr_of(ether e, node expr, model mdl) {
    model        ref   = model_alias(mdl ? mdl : expr->mdl, null, reference_pointer, null);
    LLVMValueRef value = LLVMBuildGEP2(e->builder, ref->type, expr->value, NULL, 0, "ref_expr");
    return new(node,
        mod,   e,
        value, value,
        mdl,   ref);
}

node ether_load(ether e, node n, model mdl, object offset) {
    model mdl_result = mdl ? mdl : n->mdl;

    // address with offset applied
    // use GEP2 (get element pointer... 2) to calculate the address with offset
    LLVMValueRef ptr;

    if (offset) {
        node o = operand(e, offset);
        ptr = LLVMBuildGEP2(e->builder, LLVMInt8Type(), n->value, &o->value, 1, "ptr");
    } else
        ptr = n->value;
    
    LLVMValueRef res = LLVMBuildLoad2(e->builder, mdl_result->type, ptr, "load-member");
    return value(mdl_result, res);
}

/// general signed/unsigned/1-64bit and float/double conversion
node ether_convert(ether e, node expr, model rtype) {
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

    return value(T,V);
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

node ether_assign(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->mdl, LLVMBuildStore(e->builder, RV->value, L->value));
}
node ether_assign_add(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->mdl, LLVMBuildAdd (e->builder, RV->value, L->value, "assign-add"));
}
node ether_assign_sub(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->mdl, LLVMBuildSub (e->builder, RV->value, L->value, "assign-sub"));
}
node ether_assign_mul(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->mdl, LLVMBuildMul (e->builder, RV->value, L->value, "assign-mul"));
}
node ether_assign_div(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->mdl, LLVMBuildSDiv(e->builder, RV->value, L->value, "assign-div"));
}
node ether_assign_mod(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->mdl, LLVMBuildSRem(e->builder, RV->value, L->value, "assign-mod"));
}
node ether_assign_or (ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->mdl, LLVMBuildOr  (e->builder, RV->value, L->value, "assign-or"));
}
node ether_assign_and(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->mdl, LLVMBuildAnd (e->builder, RV->value, L->value, "assign-and"));
}
node ether_assign_xor(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->mdl, LLVMBuildXor (e->builder, RV->value, L->value, "assign-xor"));
}

model ether_base_model(ether e, symbol name, AType native) {
    void* result[8];
    A prim = A_primitive(native, result); /// make a mock instance out of the type
    model mdl = new(model,
        mod, e, name, str(name), src, prim);
    verify (!contains(e->base, str(name)), "duplicate definition");
    set(e->base, str(name), mdl);
    ether_push_model(e, mdl);
    return mdl;
}

void ether_define_primitive(ether e) {
    e->base = new(map, hsize, 64);
    model none = ether_base_model(e, "void", typeid(none));
                ether_base_model(e, "bool", typeid(bool));
                ether_base_model(e, "u8", typeid(u8));
                ether_base_model(e, "u16", typeid(u16));
                ether_base_model(e, "u32", typeid(u32));
    model u64 = ether_base_model(e, "u64", typeid(u64));
    model i8  = ether_base_model(e, "i8",  typeid(i8));
                ether_base_model(e, "i16", typeid(i16));
    model i32 = ether_base_model(e, "i32", typeid(i32));
    model i64 = ether_base_model(e, "i64", typeid(i64));
                ether_base_model(e, "f32",  typeid(f32));
                ether_base_model(e, "f64",  typeid(f64));
                ether_base_model(e, "f128", typeid(f128));

    model _cstr = model_alias(i8, str("cstr"), reference_pointer, null);
    set(e->base, str("cstr"), _cstr);
    ether_push_model(e, _cstr);

    model symbol = model_alias(i8, str("symbol"), reference_constant, null);
    set(e->base, str("symbol"), symbol);
    ether_push_model(e, symbol);

    model _char = model_alias(i32, str("char"), 0, null);
    set(e->base, str("char"), _char);
    ether_push_model(e, _char);

    model _int  = model_alias(i64, str("int"), 0, null);
    set(e->base, str("int"), _int);
    ether_push_model(e, _int);

    print("int = %s", LLVMPrintTypeToString(_int->type));

    model _uint = model_alias(u64, str("uint"), 0, null);
    set(e->base, str("uint"), _uint);
    ether_push_model(e, _uint);
}

/// look up a member in lexical scope
/// this applies to models too, because they have membership as a type entry
member ether_lookup(ether e, string name) {
    verify(instanceof(name, string), "name is not string");
    for (int i = len(e->lex) - 1; i >= 0; i--) {
        model ctx = e->lex->elements[i];
        AType ctx_type = isa(ctx);
        member  m = get(ctx->members, name);
        if (m)
            return  m;
    }
    return null;
}

model ether_push(ether e, model mdl_ctx) {
    verify(mdl_ctx, "no context given");
    if (instanceof(mdl_ctx, record)) {
        mdl_ctx->scope = mdl_ctx->debug;
    } else {
        if (mdl_ctx && !instanceof(mdl_ctx, non_registered) && !mdl_ctx->scope) {
            mdl_ctx->scope = e->top ? LLVMDIBuilderCreateLexicalBlock(
                e->dbg_builder, e->top->scope, e->file, 1, 0) : e->scope;
        }
    }
    push(e->lex, mdl_ctx);
    e->top = mdl_ctx;
    return mdl_ctx;
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
                shape = new(array, alloc, 32);
                sz size = clang_getArraySize(base);
                push(shape, A_sz(size));
            } else {
                depth++;
            }
            base = clang_getArrayElementType(base);
        }
    }

    while (base.kind == CXType_Elaborated)
        base = clang_Type_getNamedType(base);

    switch (base.kind) {
        case CXType_Typedef: {
            CXString n = clang_getTypedefName(base);
            symbol  cs = clang_getCString(n);
            t = str(cs);
            clang_disposeString(n);
            printf("typedef name: %s\n", t->chars);
            if (!emodel(cs)) {
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
                    def = new(structure,
                        mod, e, from_include, e->current_include, name, t);
                else if (kind == CXCursor_UnionDecl)
                    def = new(uni, // lets assume its anonymous, how do we get the members associated to it?  how do you differentiate from the other peers if its blended into parent?  makes no sense.
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

    if (len(shape))
        mdl = model_alias(mdl, null, reference_value, shape);
    
    return mdl;
}

enum CXChildVisitResult visit_member(CXCursor cursor, CXCursor parent, CXClientData client_data) {
    model  type_def = (model)client_data;
    ether  e      = type_def->mod;
    enum CXCursorKind kind = clang_getCursorKind(cursor);
    if (kind == CXCursor_FieldDecl) {
        ether_push(e, type_def);
        CXType   field_type    = clang_getCursorType(cursor);
        CXString field_name    = clang_getCursorSpelling(cursor);
        CXString field_ts      = clang_getTypeSpelling(field_type);
        symbol   field_type_cs = clang_getCString(field_ts);
        symbol   field_name_cs = clang_getCString(field_name);
        if (eq(type_def->name, "__atomic_wide_counter")) {
            static int test = 0;
            test++;
            if (test == 4)
                test++;
        }
        model    mdl = cx_to_model(e, field_type, (cstr)field_name_cs, false);
        member   mem = emember(mdl, field_name_cs);
        set(type_def->members, str(field_name_cs), mem);
        clang_disposeString(field_name);
        clang_disposeString(field_ts);
        ether_pop(e);
    }
    
    return CXChildVisit_Recurse;
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
        case CXCursor_FunctionDecl: {
            CXType   cx_rtype = clang_getCursorResultType(cursor);
            model    rtype    = cx_to_model(e, cx_rtype, null, true);
            int      n_args   = clang_Cursor_getNumArguments(cursor);
            array    args     = new(array, alloc, 32);

            //if (!eq(name, "printf"))
            //    return CXChildVisit_Recurse;
            
            for (int i = 0; i < n_args; i++) {
                CXCursor arg_cursor = clang_Cursor_getArgument(cursor, i);
                CXString pcx        = clang_getCursorSpelling (arg_cursor);
                symbol   arg_name   = clang_getCString        (pcx);
                CXType   arg_cxtype = clang_getCursorType     (arg_cursor);
                CXString pcx_type   = clang_getTypeSpelling   (arg_cxtype);
                symbol   arg_type   = clang_getCString        (pcx_type);

                if (eq(name, "qecvt")) {
                    int test = 1;
                    test++;
                }
                model    arg_mdl    = cx_to_model(e, arg_cxtype, arg_name, true);

                member   mem = emember(arg_mdl, arg_name);
                push(args, mem);
                clang_disposeString(pcx);
            }
            bool is_var = clang_Cursor_isVariadic(cursor);
            if (eq(name, "printf")) assert(is_var, "expected var arg");
            def = new(function,
                mod,            e,
                from_include,   e->current_include,
                name,           name,
                va_args,        is_var,
                rtype,          rtype,
                args,           args);
            break;
        }
        case CXCursor_StructDecl: {
            def = new(structure,
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

            if (strcmp(type_name, "off_t") == 0) {
                int test = 1;
                test++;
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
    if (def)
        ether_push_model(e, def);
    clang_disposeString(fcx);
    return CXChildVisit_Recurse;
}

/// return a map of defs found by their name (we can isolate the namespace this way by having separate maps)
void ether_include(ether e, string include) {
    string   include_path  = format("%o/include", e->install);
    path     full_path = null;
    symbol   ipaths[]  = {
        include_path->chars,
        "/usr/include"
    };
    for (int i = 0; i < sizeof(ipaths) / sizeof(symbol); i++) {
        path r = form(path, "%s/%o", ipaths[i], include);
        if (exists(r)) {
            full_path = r;
            break;
        }
        path r2 = form(path, "%s/%o.h", ipaths[i], include);
        if (exists(r2)) {
            full_path = r2;
            break;
        }
    }
    verify (full_path, "include path not found for %o", include);
    CXIndex index = clang_createIndex(0, 0);
    CXTranslationUnit unit = clang_parseTranslationUnit(
        index, full_path->chars, NULL, 0, NULL, 0, CXTranslationUnit_None);

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
    LLVMAddModuleFlag(e->module, LLVMModuleFlagBehaviorError, flag, strlen(flag), v);
}


void ether_write(ether e) {
    cstr err = NULL;
    if (LLVMVerifyModule(e->module, LLVMPrintMessageAction, &err))
        fault("error verifying module: %s", err);
    else
        print("module verified");

    path ll = form(path, "%o.ll", e->name);
    path bc = form(path, "%o.bc", e->name);
    if (!LLVMPrintModuleToFile(e->module, cs(ll), &err))
        print("IR: %o", ll);
    else
        fault("LLVMPrintModuleToFile failed");

    if (LLVMWriteBitcodeToFile(e->module, cs(bc)) != 0)
        fault("LLVMWriteBitcodeToFile failed");
    else
        print("bitcode: %o", bc);
}


void ether_llvm_init(ether e) {
    e->lex            = new(array, alloc, 32);
    //e->type_refs    = new(map, hsize, 64);
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
    ecall(llflag, "Dwarf Version",      5);
    ecall(llflag, "Debug Info Version", 3);

    string src_file =      filename (e->source);
    string src_path = cast(directory(e->source), string);
    e->file = LLVMDIBuilderCreateFile( // create e file reference (the source file for debugging)
        e->dbg_builder,
        cast(src_file, cstr), cast(src_file, sz),
        cast(src_path, cstr), cast(src_path, sz));
    
    e->compile_unit = LLVMDIBuilderCreateCompileUnit(
        e->dbg_builder, LLVMDWARFSourceLanguageC, e->file,
        "silver", 6, 0, "", 0,
        0, "", 0, LLVMDWARFEmissionFull, 0, 0, 0, "", 0, "", 0);

    path  full_path = form(path, "%o/%o", src_path, src_file);
    verify(exists(full_path), "source (%o) does not exist", full_path);
    e->builder = LLVMCreateBuilderInContext(e->module_ctx);
}


/// we may have a kind of 'module' given here; i suppose instanceof(ether) is enough
void ether_init(ether e) {
    ether_llvm_init(e);
    e->lex = new(array, alloc, 32);
    push(e, e);
    ether_define_primitive(e);
}


void ether_destructor(ether e) {
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
        case OPType__assign_right:
        case OPType__assign_left:
        case OPType__mod_assign:
            return L;  // Assignment operations always return the type of the left operand
        
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

node ether_negate(ether e, node L) {
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
    return LLVMBuildNot(e->builder, L->value, "bitwise-not");
}

// object o = obj("type-name", props)
node ether_eq(ether e, node L, node R);

node ether_is(ether e, node L, object R) {
    node L_ptr = ether_load(e, L, null, A_i64(-sizeof(A)));
    node R_ptr = operand(e, R);
    return ether_eq(e, L_ptr, R_ptr);
}

node ether_eq(ether e, node L, node R) {
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
    model t0 = L->mdl;
    model t1 = R->mdl;
    verify (t0 == t1, "types must be same at primitive operation level");
    bool i0 = is_integral(t0);
    bool f0 = is_realistic(t1);
    if (i0 || !f0)
        return value(emodel("bool"), LLVMBuildICmp(e->builder, LLVMIntNE,   L->value, R->value, "not-eq-i"));
    return     value(emodel("bool"), LLVMBuildFCmp(e->builder, LLVMRealONE, L->value, R->value, "not-eq-f"));
}

node ether_freturn(ether e, object o) {
    function fn = ether_context_model(e, typeid(function));
    verify (fn, "function not found in context");

    if (!o) return value(fn->rtype, LLVMBuildRetVoid(e->builder));

    node conv = ether_convert(e, operand(e, o), fn->rtype);
    return value(fn->rtype, LLVMBuildRet(e->builder, conv->value));
}

node ether_fcall(ether e, member fn_mem, node target, array args) {
    verify(isa(fn_mem->mdl) == typeid(function), "model provided is not function");
    int n_args = len(args);
    LLVMValueRef* arg_values = calloc((target != null) + n_args, sizeof(LLVMValueRef));
    //verify (LLVMTypeOf(fdef->function->value) == fdef->ref, "integrity check failure");
    function fn = fn_mem->mdl;
    
    LLVMTypeRef  F = fn->type;
    LLVMValueRef V = fn->value; // todo: args in ether should be a map.  that way we can do a bit more

    int index = 0;
    verify(!!target == !!fn->target, "target mismatch");

    if (target)
        arg_values[index++] = target->value;
    each (args, object, value) {
        member    f_arg = fn->args->elements[index];
        AType     vtype = isa(value);
        node      op    = operand(e, value);
        node      conv  = ether_convert(e, op, f_arg ? f_arg->mdl : op->mdl);
        LLVMValueRef vr = arg_values[index] = conv->value;
        print("ether_fcall: %o arg[%i]: vr: %p, type: %s", fn_mem->name, index, vr, LLVMPrintTypeToString(LLVMTypeOf(vr)));
        index++;
    }
    bool is_void_ = is_void(fn->rtype);
    LLVMValueRef R = LLVMBuildCall2(e->builder, F, V, arg_values, index, is_void_ ? "" : "call");
    free(arg_values);
    return value(F, R);
}

node ether_literal(ether e, object n) {
    AType ntype = isa(n);
    if (ntype == typeid(bool)) return value(emodel("bool"), LLVMConstInt( LLVMInt1Type(), *(bool*)n, 0));
    if (ntype == typeid(i8))   return value(emodel("i8"),   LLVMConstInt( LLVMInt8Type(),  *( i8*)n, 0));
    if (ntype == typeid(i16))  return value(emodel("i16"),  LLVMConstInt(LLVMInt16Type(),  *(i16*)n, 0));
    if (ntype == typeid(i32))  return value(emodel("i32"),  LLVMConstInt(LLVMInt32Type(),  *(i32*)n, 0));
    if (ntype == typeid(i64))  return value(emodel("i64"),  LLVMConstInt(LLVMInt64Type(),  *(i64*)n, 0));
    if (ntype == typeid(u8))   return value(emodel("u8"),   LLVMConstInt( LLVMInt8Type(),  *( u8*)n, 0));
    if (ntype == typeid(u16))  return value(emodel("u16"),  LLVMConstInt(LLVMInt16Type(),  *(u16*)n, 0));
    if (ntype == typeid(u32))  return value(emodel("u32"),  LLVMConstInt(LLVMInt32Type(),  *(u32*)n, 0));
    if (ntype == typeid(u64))  return value(emodel("u64"),  LLVMConstInt(LLVMInt64Type(),  *(u64*)n, 0));
    if (ntype == typeid(f32))  return value(emodel("f32"),  LLVMConstInt(LLVMFloatType(),  *(f32*)n, 0));
    if (ntype == typeid(f64))  return value(emodel("f64"),  LLVMConstInt(LLVMDoubleType(), *(f64*)n, 0));
    if (ntype == typeid(f128))  return value(emodel("f128"),  LLVMConstInt(LLVMFP128Type(), *(f128*)n, 0));
    if (ntype == typeid(string))
        return value(emodel("symbol"), LLVMBuildGlobalStringPtr(e->builder, ((string)n)->chars, "str"));
    fault ("literal not handled: %s", ntype->name);
}

node ether_op(ether e, OPType optype, string N, object L, object R) {
    node   LV  = operand(e, L);
    node   RV  = operand(e, R);
    //string N   = estr(OPType, optype);

    verify(!N || instanceof(N, string), "N is not string");

    /// check if N is a method on L
    if (N && isa(L) == typeid(node) && is_class(((node)L)->mdl))
    {
        node Ln = L;
        AType type = isa(Ln->mdl);
        if (type == typeid(structure) || type == typeid(record))
        {
            record rec = Ln->mdl;
            member Lt = get(rec->members, N);
            if  (Lt && isa(Lt->mdl) == typeid(function))
            {
                function fn = Lt->mdl;
                if (len(fn->args) == 1) {
                    /// convert argument and call method
                    model  arg_expects = fn->args->elements[0];
                    node  conv = ether_convert(e, Ln, arg_expects);
                    array args = array_of(null, conv, null);
                    return ecall(fcall, Lt, L, args);
                }
            }
        }
    }

    model rtype = determine_rtype(e, optype, LV->mdl, RV->mdl);
    LLVMValueRef RES;

    LV = ether_convert(e, LV, rtype);
    RV = ether_convert(e, RV, rtype);

    // we must set this, and also do we need to chang our calls to different ones depending on if there is going to be integer size change?
    // for each LV/RV there is a type to read, and that type has model of model_bool/u8/i64...f32/f64
    switch (optype) {
    case OPType__add:    RES = LLVMBuildAdd  (e->builder, LV->value, RV->value, cs(N)); break;
    case OPType__sub:    RES = LLVMBuildSub  (e->builder, LV->value, RV->value, cs(N)); break;
    case OPType__mul:    RES = LLVMBuildMul  (e->builder, LV->value, RV->value, cs(N)); break;
    case OPType__div:    RES = LLVMBuildSDiv (e->builder, LV->value, RV->value, cs(N)); break;
    case OPType__or:     RES = LLVMBuildOr   (e->builder, LV->value, RV->value, cs(N)); break;
    case OPType__and:    RES = LLVMBuildAnd  (e->builder, LV->value, RV->value, cs(N)); break;
    case OPType__xor:    RES = LLVMBuildXor  (e->builder, LV->value, RV->value, cs(N)); break;
    case OPType__right:  RES = LLVMBuildLShr (e->builder, LV->value, RV->value, cs(N)); break;
    case OPType__left:   RES = LLVMBuildShl  (e->builder, LV->value, RV->value, cs(N)); break;
    case OPType__assign: RES = LLVMBuildStore(e->builder, RV->value, LV->value);    break;
    default: {
        LLVMValueRef loaded = LLVMBuildLoad2(e->builder, LLVMTypeOf(LV), LV, "load");
        LLVMValueRef val;
        switch (optype) {
            case OPType__assign_add:   val = LLVMBuildAdd (e->builder, loaded, RV->value, cs(N)); break;
            case OPType__assign_sub:   val = LLVMBuildSub (e->builder, loaded, RV->value, cs(N)); break;
            case OPType__assign_mul:   val = LLVMBuildMul (e->builder, loaded, RV->value, cs(N)); break;
            case OPType__assign_div:   val = LLVMBuildSDiv(e->builder, loaded, RV->value, cs(N)); break;
            case OPType__assign_or:    val = LLVMBuildOr  (e->builder, loaded, RV->value, cs(N)); break;
            case OPType__assign_and:   val = LLVMBuildAnd (e->builder, loaded, RV->value, cs(N)); break;
            case OPType__assign_xor:   val = LLVMBuildXor (e->builder, loaded, RV->value, cs(N)); break;
            case OPType__assign_right: val = LLVMBuildLShr(e->builder, loaded, RV->value, cs(N)); break;
            case OPType__assign_left:  val = LLVMBuildShl (e->builder, loaded, RV->value, cs(N)); break;
            case OPType__mod_assign:   val = LLVMBuildSRem(e->builder, loaded, RV->value, cs(N)); break;
            default:
                fault("unexpected operation type");
                break;
        }
        RES = LLVMBuildStore(e->builder, val, LV->value);
        break;
    }}
    return new(node,
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


node ether_inherits(ether e, node L, object R) {
// Get the type pointer for L
    node L_ptr = ether_load(e, L, null, A_i64(-sizeof(A)));
    node R_ptr = operand(e, R);

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
    node parent    = ether_load(e, value(L_ptr->mdl, phi), L_ptr->mdl, null);

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

/// return model (type) for function
member ether_function(
        ether e,     token name, model record, bool is_instance,
        model rtype, array args, bool  va_args, subprocedure process) {
    function fn  = new(function, mod, e,
        name,    name,      record,  record, is_instance, is_instance,
        rtype,   rtype,     args,    args,
        va_args, va_args,   process, process);
    model  mdl = new(model,    mod, e, name, name, src, fn);
    member mem = emember(mdl, name->chars);
    /// function should not set 'is-type'
    ether_push_member(e, mem);
    return mdl;
}

void ether_builder_main(ether e, function fn, map ctx) {
    model  rtype    = emodel("i64");
    member template = emember(emodel("symbol"), "template");
    member printf   = ecall(function,
        "printf", null, false, rtype, array_of(null, template, null), true, null);
    array  args     = array_of(null, str("something"), null);
    node   n_printf = ecall(fcall,   printf, null, args);
    node   n_ret    = ecall(freturn, i(1));
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
                LLVMPositionBuilderAtEnd(e->builder, fn->entry);
                push(e, fn);
                set(fn->members, str("this"), fn->target);
                each(fn->args, member, arg_mem)
                    set(fn->members, str(arg_mem->name->chars), arg_mem);
                ether_set_token(e, fn->name);
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
    cstr cs = cs(a);
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

string token_cast_string(token a) {
    return new(string, chars, a->chars);
}

AType token_is_bool(token a) {
    string t = cast(a, string);
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
    string res = new(string, alloc, ln);
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

void token_init(token a) {
    cstr prev = a->chars;
    sz length = a->len ? a->len : strlen(prev);
    a->chars  = (cstr)calloc(length + 1, 1);
    a->len    = length;
    memcpy(a->chars, prev, length);

    if (a->chars[0] == '\"' || a->chars[0] == '\'') {
        string crop = new(string, chars, &a->chars[1], ref_length, length - 2);
        a->literal = read_string(crop->chars);
    } else
        a->literal = read_numeric(a);
}

// anything with a f_* is member field data
define_enum      (interface)
define_enum      (reference)
define_class     (model)

// we need a place to tag as deferred registration
// we parse args before we have the identity of the function type
define_mod       (non_registered,  model)
define_mod       (statements,      model)

define_mod       (function,  model)
define_mod       (record,    model)
define_mod       (uni,       record)
define_mod       (structure, record)
define_mod       (class,     record)
define_mod       (ether,     model)

define_class(token)

define_class(node)

define_mod(op,       node)
define_mod(member,   node)