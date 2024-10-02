#include <llvm-c/DebugInfo.h>
#include <llvm-c/Core.h>
#include <llvm-c/ExecutionEngine.h>
#include <llvm-c/Target.h>
#include <llvm-c/Analysis.h>
#include <llvm-c/TargetMachine.h>
#include <llvm-c/BitWriter.h>
#include <clang-c/Index.h>

typedef LLVMMetadataRef LLVMScope;

#define    ether_intern  intern(ether)
#define  context_intern  intern(context)
#define     node_intern  intern(node)
#define     type_intern  intern(type)
#define   member_intern  intern(member)
#define    fcall_intern  intern(fcall)
#define function_intern  intern(function)
#define       op_intern  intern(op)
#define      ret_intern  intern(ret)

#include <ether>

#define ecall(M, ...) ether_##M(e, ## __VA_ARGS__)
#define edef(name) (get(e->defs, str(name)))

static map operators;

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

/// 'im a token' -- Baldeck reg. Token Ring breakdown.  et al
void token_init(token a) {
    cstr prev = a->chars;
    sz length = a->len ? a->len : strlen(prev);
    a->chars  = (cstr)calloc(length + 1, 1);
    a->len    = length;
    memcpy(a->chars, prev, length);
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

A token_is_numeric(token a) {
    bool is_digit = a->chars[0] >= '0' && a->chars[0] <= '9';
    bool has_dot  = strstr(a->chars, ".") != 0;
    if (!is_digit && !has_dot)
        return null;
    char* e = null;
    if (!has_dot) {
        i64 v = strtoll(a->chars, &e, 10);
        return A_primitive(typeid(i64), &v);
    }
    f64 v = strtod(a->chars, &e);
    return A_primitive(typeid(f64), &v);
}

num token_compare(token a, token b) {
    return strcmp(a->chars, b->chars);
}

bool token_cast_bool(token a) {
    return a->len > 0;
}


LLVMMetadataRef primitive_dbg(type def) {
    return LLVMDIBuilderCreateBasicType(
        def->mod->dbg, def->name->chars, def->name->len, def->size,
        def->name->chars[0] == 'f' ? 0x04 : 0x05, 0);
}

LLVMMetadataRef cstr_dbg(type def, bool isConst) {
    LLVMMetadataRef charTypeMeta = LLVMDIBuilderCreateBasicType(
        def->mod->dbg, "char", 4, 8, 0x01, 0); // 0x01 = DW_ATE_unsigned_char
    symbol name = isConst ? "const char" : "char";
    u64 ptr_sz = LLVMPointerSize(def->mod->target_data);
    return LLVMDIBuilderCreatePointerType(def->mod->dbg, charTypeMeta,
        ptr_sz * 8, 0, 0, name, strlen(name));
}

void type_init(type def) {
    ether e = def->mod;

    if (inherits(def->name, string)) {
        string n = def->name;
        def->name = new(token, chars, n, source, e->source, line, 1);
    }

    // create for users of this data
    //def->context = new(context);
    bool handled_members = false;

    switch (def->mdl) {
        case model_class:
            fault ("not implemented");
            break;
        
        case model_function:
            break;
        
        case model_bool:   def->type = LLVMInt1Type  (); break;
        case model_i8:     def->type = LLVMInt8Type  (); break;
        case model_i16:    def->type = LLVMInt16Type (); break;
        case model_i32:    def->type = LLVMInt32Type (); break;
        case model_i64:    def->type = LLVMInt64Type (); break;
        case model_u8:     def->type = LLVMInt8Type  (); break;
        case model_u16:    def->type = LLVMInt16Type (); break;
        case model_u32:    def->type = LLVMInt32Type (); break;
        case model_u64:    def->type = LLVMInt64Type (); break;
        case model_f32:    def->type = LLVMFloatType (); break;
        case model_f64:    def->type = LLVMDoubleType(); break;
        case model_void:   def->type = LLVMVoidType  (); break;
        case model_typedef: {
            verify (def->origin && isa(def->origin) == typeid(member), "origin must be ident reference");
            def->type = def->origin->type;
            if (e->dbg) {
                member origin = def->origin;
                verify(origin, "origin not resolved");
                def->dbg = LLVMDIBuilderCreateTypedef(
                    e->dbg, def->origin->dbg, def->name->chars, len(def->name),
                    e->file, 0, e->scope, LLVMDIFlagZero);
            }
            break;
        }
        case model_struct: {
            LLVMTypeRef* member_types = calloc(len(def->members), sizeof(LLVMTypeRef));
            int index = 0;
            pairs(def->members, i) {
                member mem = i->value;
                verify(isa(mem) == typeid(member), "mismatch");
                member_types[index] = mem->type;
                index++;
            }
            def->type = LLVMStructCreateNamed(LLVMGetGlobalContext(), def->name);
            LLVMStructSetBody(def->type, member_types, index, 0);
            handled_members = true;
            break;
        }
        case model_union: {
            verify (false, "not implemented");
            break;
        }
    }

    if (def->type) {
        // type has depth applied, for ALL types
        for (int i = 0; i < def->depth; i++)
            def->type = LLVMPointerType(def->type, 0);
        // the size is the effective type size after applying (sizeof ptr if depth > 0)
        def->size = LLVMSizeOfTypeInBits(def->mod->target_data, def->type);
    }
    /// create debug info for primitives
    if (def->mdl >= model_bool && def->mdl <= model_f64)
        def->dbg = primitive_dbg(def);
    else if (eq(def->name, "symbol") || eq(def->name, "cstr"))
        def->dbg = cstr_dbg(def, eq(def->name, "symbol"));
    else if (def->mdl != model_function) {
        verify (def->dbg || eq(def->name, "void"), "debug info not set for type");
    }
    verify (!count(def->members) || handled_members, "members given and not processed");
}

void context_init(context ctx) {
    ctx->members = new(map, hsize, 32);
}

void member_init(member mem) {
    /// lets create everything we need for LLVM call here
    ether   e   = mem->mod;
    context top = e->top;

    verify (mem->type->dbg, "no debug info on type");
    mem->dbg = LLVMDIBuilderCreateMemberType(
        e->dbg,                // LLVMDIBuilderRef
        top->scope,            // Scope of the member (can be the struct or class)
        mem->name->chars,      // Name of the member
        len(mem->name),        // Length of the name
        e->file,               // The file where the member is declared
        mem->name->line,       // Line number where the member is declared
        mem->type->size * 8,   // Size of the member in bits (e.g., 32 for a 32-bit int)
        0,                     // Alignment of the member in bits
        0,                     // Offset in bits from the start of the struct or class
        0,                     // Debug info flags (e.g., 0 for none)
        mem->type->dbg         // The LLVMMetadataRef for the member's type (created earlier)
    );

    /// members are stored in context
    string n = str(mem->name->chars);
    verify (!contains(top->members, n), "duplicate member definition");
    set(top->members, n, mem);
}

void op_init(op op) {
    /// lets create everything we need for LLVM call here
}


void ret_init(ret op) {
    /// lets create everything we need for LLVM call here
}

void ether_define_primitive(ether e) {
    map defs = e->defs = new(map, hsize, 64);
    set(defs, str("bool"),    new(type, mod, e, name, str("bool"),   mdl, model_bool, imported, typeid(bool)));
    set(defs, str("i8"),      new(type, mod, e, name, str("i8"),     mdl, model_i8,   imported, typeid(i8)));
    set(defs, str("i16"),     new(type, mod, e, name, str("i16"),    mdl, model_i16,  imported, typeid(i16)));
    set(defs, str("i32"),     new(type, mod, e, name, str("i32"),    mdl, model_i32,  imported, typeid(i32)));
    set(defs, str("i64"),     new(type, mod, e, name, str("i64"),    mdl, model_i64,  imported, typeid(i64)));
    set(defs, str("u8"),      new(type, mod, e, name, str("u8"),     mdl, model_u8,   imported, typeid(u8)));
    set(defs, str("u16"),     new(type, mod, e, name, str("u16"),    mdl, model_u16,  imported, typeid(u16)));
    set(defs, str("u32"),     new(type, mod, e, name, str("u32"),    mdl, model_u32,  imported, typeid(u32)));
    set(defs, str("u64"),     new(type, mod, e, name, str("u64"),    mdl, model_u64,  imported, typeid(u64)));
    set(defs, str("f32"),     new(type, mod, e, name, str("f32"),    mdl, model_f32,  imported, typeid(f32)));
    set(defs, str("f64"),     new(type, mod, e, name, str("f64"),    mdl, model_f64,  imported, typeid(f64)));
    set(defs, str("void"),    new(type, mod, e, name, str("void"),   mdl, model_void, imported, typeid(none)));

    type chr = edef("i8");
    set(defs, str("symbol"),  new(type,
        mod,    e,   name,     str("symbol"), mdl,      model_typedef,
        origin, chr, is_const, true,          imported, typeid(symbol)));
    set(defs, str("cstr"),    new(type,
        mod,    e,   name,     str("cstr"),   mdl,      model_typedef,
        origin, chr, imported, typeid(cstr)));
    set(defs, str("int"),     get(defs, str("i64")));
    set(defs, str("uint"),    get(defs, str("u64")));
}

map ether_top_members(ether e) {
    assert (e->lex->len, "stack is empty");
    return last(e->lex);
}

member ether_find_member(ether e, string name) {
    for (int m = e->lex->len - 1; m >= 0; m--) {
        map members = e->lex->elements[m];
        member f = get(members, name);
        if (f) return f;
    }
    return null;
}

type ether_find_def(ether e, string name) {
    return get(e->defs, name);
}

context ether_push(ether e) {
    context top = new(context);
    push(e->lex, top);
    e->top = top;
    return top;
}

context ether_pop(ether e) {
    pop(e->lex);
    if (len(e->lex))
        e->top = last(e->lex);
    else
        e->top = null;
    return e->top;
}

/// return a map of defs found by their name (we can isolate the namespace this way by having separate maps)
map ether_include(ether e, string include) {
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
    }
    verify (full_path, "include path not found for %o", include);
    CXIndex index = clang_createIndex(0, 0);
    CXTranslationUnit unit = clang_parseTranslationUnit(
        index, full_path->chars, NULL, 0, NULL, 0, CXTranslationUnit_None);

    verify(unit, "unable to parse translation unit %o", include);
    
    CXCursor cursor = clang_getTranslationUnitCursor(unit);
    e->current_include = full_path;
    //clang_visitChildren(cursor, visit, (CXClientData)e);
    clang_disposeTranslationUnit(unit);
    clang_disposeIndex(index);
    e->current_include = null;
    return 0;
}

void ether_set_line(ether e, i32 line, i32 column) {
    LLVMMetadataRef loc = LLVMDIBuilderCreateDebugLocation(
        e->module_ctx, line, column, e->scope, null);
    LLVMSetCurrentDebugLocation2(e->dbg, loc);
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

    if (!LLVMPrintModuleToFile(e->module, "a.ll", &err))
        print("generated IR");
    else
        fault("LLVMPrintModuleToFile failed");

    symbol bc = "a.bc";
    if (LLVMWriteBitcodeToFile(e->module, bc) != 0)
        fault("LLVMWriteBitcodeToFile failed");
    else
        print("bitcode written to %s", bc);
}

void ether_llvm_init(ether e) {
    e->lex            = new(array, alloc, 32);
    //e->type_refs    = new(map, hsize, 64);
    e->module         = LLVMModuleCreateWithName(e->name->chars);
    e->module_ctx     = LLVMGetModuleContext(e->module);
    e->dbg            = LLVMCreateDIBuilder(e->module);
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
        e->dbg,
        cast(src_file, cstr), cast(src_file, sz),
        cast(src_path, cstr), cast(src_path, sz));
    
    e->compile_unit = LLVMDIBuilderCreateCompileUnit(
        e->dbg, LLVMDWARFSourceLanguageC, e->file,
        "silver", 6, 0, "", 0,
        0, "", 0, LLVMDWARFEmissionFull, 0, 0, 0, "", 0, "", 0);

    path  full_path = form(path, "%o/%o", src_path, src_file);
    verify(exists(full_path), "source (%o) does not exist", full_path);
    e->builder = LLVMCreateBuilderInContext(e->module_ctx);
}

void ether_init(ether e) {
    e->lex = new(array, alloc, 32);
    push(e);

    ether_llvm_init(e);
    ether_define_primitive(e);
}

void ether_destructor(ether e) {
    LLVMDisposeBuilder(e->builder);
    LLVMDisposeDIBuilder(e->dbg);
    LLVMDisposeModule(e->module);
    LLVMContextDispose(e->module_ctx);
    LLVMDisposeMessage(e->target_triple);
}

type preferred_type(ether e, type t0, type t1) {
    if (t0 == t1) return t0;
    bool f0 = t0->mdl == model_f32 || t0->mdl == model_f64;
    bool f1 = t1->mdl == model_f32 || t1->mdl == model_f64;
    if (f0) {
        if (f1)
            return (t1->mdl == model_f64) ? t1 : t0;
        return t0;
    }
    if (f1)
        return t1;
    if (t0->mdl > t1->mdl)
        return t0;
    return t1;
}

LLVMValueRef convert(ether e, LLVMValueRef vr, member type) {
    /// ether may have conversion rules on limiting truncation, however these are default
    LLVMTypeRef  src_type  = LLVMTypeOf(vr);
    LLVMTypeRef  dst_type = type->type;
    LLVMTypeKind src_kind = LLVMGetTypeKind(src_type);
    LLVMTypeKind dst_kind = LLVMGetTypeKind(dst_type);

    // Check if the types are already the same
    if (src_type == dst_type) {
        return vr;
    }

    // Convert between integer types (e.g., i8 to i64)
    if (src_kind == LLVMIntegerTypeKind && 
        dst_kind == LLVMIntegerTypeKind) {
        unsigned src_bits = LLVMGetIntTypeWidth(src_type);
        unsigned dest_bits = LLVMGetIntTypeWidth(dst_type);

        if (src_bits < dest_bits) {
            // Extend smaller integer to larger integer (e.g., i8 -> i64)
            return LLVMBuildZExtOrBitCast(e->builder, vr, dst_type, "zext");
        } else if (src_bits > dest_bits) {
            // Truncate larger integer to smaller integer (e.g., i64 -> i8)
            return LLVMBuildTrunc(e->builder, vr, dst_type, "trunc");
        }
    }

    // Convert integer to float
    if (src_kind == LLVMIntegerTypeKind && 
        dst_kind == LLVMFloatTypeKind) {
        return LLVMBuildSIToFP(e->builder, vr, dst_type, "sitofp");
    }

    // Convert float to integer
    if (src_kind == LLVMFloatTypeKind && 
        dst_kind == LLVMIntegerTypeKind) {
        return LLVMBuildFPToSI(e->builder, vr, dst_type, "fptosi");
    }

    if (src_kind == LLVMDoubleTypeKind && 
        dst_kind == LLVMFloatTypeKind) {
        return LLVMBuildFPTrunc(e->builder, vr, dst_type, "fptrunc");
    }

    if (src_kind == LLVMFloatTypeKind && 
        dst_kind == LLVMDoubleTypeKind) {
        return LLVMBuildFPExt(e->builder, vr, dst_type, "fpext");
    }

    // If no valid conversion, return NULL and handle the error elsewhere
    error("Unsupported type conversion");
    return NULL;
}

LLVMValueRef operand(ether e, object op) {
         if (inherits(op,   node)) return ((node)op)->value;
    else if (inherits(op,     u8)) return LLVMConstInt (edef( "u8")->type, *( u8*)op, 0);
    else if (inherits(op,    u16)) return LLVMConstInt (edef("u16")->type, *(u16*)op, 0);
    else if (inherits(op,    u32)) return LLVMConstInt (edef("u32")->type, *(u32*)op, 0);
    else if (inherits(op,    u64)) return LLVMConstInt (edef("u64")->type, *(u64*)op, 0);
    else if (inherits(op,     i8)) return LLVMConstInt (edef( "i8")->type, *( i8*)op, 0);
    else if (inherits(op,    i16)) return LLVMConstInt (edef("i16")->type, *(i16*)op, 0);
    else if (inherits(op,    i32)) return LLVMConstInt (edef("i32")->type, *(i32*)op, 0);
    else if (inherits(op,    i64)) return LLVMConstInt (edef("i64")->type, *(i64*)op, 0);
    else if (inherits(op,    f32)) return LLVMConstReal(edef("f32")->type, *(f32*)op);
    else if (inherits(op,    f64)) return LLVMConstReal(edef("f64")->type, *(f64*)op);
    else if (inherits(op, string)) return LLVMBuildGlobalStringPtr(e->builder, ((string)op)->chars, "chars");
    else {
        error("unsupported type in ether_add");
        return NULL;
    }
}

node ether_freturn(ether e, object o) {
    function fn = e->current_fn;
    /// fn->rtype->type is the LLVMTypeRef for this function
    /// if 'operand' doesnt equal teh same type, lets convert it
    LLVMValueRef vr = convert(e, operand(e, o), fn->rtype);
    return new(node, mod, e, value, LLVMBuildRet(e->builder, vr));
}

node ether_fcall(ether e, type fdef, member target, map args) {
    int n_args = len(args);
    LLVMValueRef* arg_values = calloc((target != null) + n_args, sizeof(LLVMValueRef));

    int index = 0;
    if (target)
        arg_values[index++] = target->value;
    pairs (args, i) {
        LLVMValueRef vr = arg_values[index++] = operand(e, i->value);
        print("vr = %p", vr);
    }

    //verify (LLVMTypeOf(fdef->function->value) == fdef->type, "integrity check failure");
    LLVMTypeRef  F = fdef->type;
    LLVMValueRef V = fdef->function->value;
    LLVMValueRef R = LLVMBuildCall2(e->builder, F, V, arg_values, index, "call");
    free(arg_values);
    return new(node, mod, e, value, R);
}

node ether_op(ether e, OPType optype, object L, object R) {
    node LV = new(node, mod, e, value, operand(e, L));
    node RV = new(node, mod, e, value, operand(e, R));
    if (!LV || !RV) {
        error("Invalid operands in ether_add");
        return NULL;
    }
    //OPType op = eval(OPType, type->chars);
    string N = estr(OPType, optype);
    LLVMValueRef RES;
    switch (optype) {
    case OPType_add:    RES = LLVMBuildAdd  (e->builder, LV, RV, N); break;
    case OPType_sub:    RES = LLVMBuildSub  (e->builder, LV, RV, N); break;
    case OPType_mul:    RES = LLVMBuildMul  (e->builder, LV, RV, N); break;
    case OPType_div:    RES = LLVMBuildSDiv (e->builder, LV, RV, N); break;
    case OPType_or:     RES = LLVMBuildOr   (e->builder, LV, RV, N); break;
    case OPType_and:    RES = LLVMBuildAnd  (e->builder, LV, RV, N); break;
    case OPType_xor:    RES = LLVMBuildXor  (e->builder, LV, RV, N); break;
    case OPType_right:  RES = LLVMBuildLShr (e->builder, LV, RV, N); break;
    case OPType_left:   RES = LLVMBuildShl  (e->builder, LV, RV, N); break;
    case OPType_assign: RES = LLVMBuildStore(e->builder, RV, LV);    break;
    default: {
        LLVMValueRef loaded = LLVMBuildLoad2(e->builder, LLVMTypeOf(LV), LV, "load");
        LLVMValueRef val;
        switch (optype) {
            case OPType_assign_add:   val = LLVMBuildAdd (e->builder, loaded, RV, N); break;
            case OPType_assign_sub:   val = LLVMBuildSub (e->builder, loaded, RV, N); break;
            case OPType_assign_mul:   val = LLVMBuildMul (e->builder, loaded, RV, N); break;
            case OPType_assign_div:   val = LLVMBuildSDiv(e->builder, loaded, RV, N); break;
            case OPType_assign_or:    val = LLVMBuildOr  (e->builder, loaded, RV, N); break;
            case OPType_assign_and:   val = LLVMBuildAnd (e->builder, loaded, RV, N); break;
            case OPType_assign_xor:   val = LLVMBuildXor (e->builder, loaded, RV, N); break;
            case OPType_assign_right: val = LLVMBuildLShr(e->builder, loaded, RV, N); break;
            case OPType_assign_left:  val = LLVMBuildShl (e->builder, loaded, RV, N); break;
            case OPType_mod_assign:   val = LLVMBuildSRem(e->builder, loaded, RV, N); break;
            default:
                fault("unexpected operation type");
                break;
        }
        RES = LLVMBuildStore(e->builder, val, LV->value);
        break;
    }}
    
    return new(op,
        optype,     optype,
        left,       LV,
        right,      RV,
        value,      RES);
}

node ether_add(ether e, object L, object R) { return ether_op(e, OPType_add, L, R); }
node ether_sub(ether e, object L, object R) { return ether_op(e, OPType_sub, L, R); }
node ether_mul(ether e, object L, object R) { return ether_op(e, OPType_mul, L, R); }
node ether_div(ether e, object L, object R) { return ether_op(e, OPType_div, L, R); }

/// implement or import with this
type ether_function(
        ether e,           cstr name, type target,
        type  return_type, map  args, bool va_args, subprocedure builder)
{
    LLVMTypeRef      rtype     = return_type->type;
    int              n_args    = len(args);
    LLVMMetadataRef* arg_meta  = calloc((target != null) + n_args, sizeof(LLVMTypeRef));
    LLVMTypeRef*     arg_types = calloc((target != null) + n_args, sizeof(LLVMTypeRef));
    int              index     = 0;

    if (target)
        arg_types[index++] = LLVMPointerType(target->type, 0);

    pairs(args, i) {
        member arg_mem     = i->value;
        arg_types[index++] = arg_mem->type;
    }

    string fname = str(name);
    type   fdef  = new(type,
        name,     fname,  type,   LLVMFunctionType(return_type->type, arg_types, index, va_args),
        function, null,   mdl,    model_function);
    function fn  = new(function,
        name,     fname,    target, target,
        type,     fdef,     rtype,  return_type->type,
        builder,  builder,  value,  LLVMAddFunction(e->module, fname->chars, fdef->type));
    fdef->function = fn;

    pairs(args, i) { // index == 0 at start
        member arg_mem     = i->value;
        verify(fn->scope, "fn scope not set");
        arg_meta[index] = LLVMDIBuilderCreateParameterVariable(
            e->dbg, fn->scope, arg_mem->name->chars, strlen(arg_mem->name->chars),
            index + 1, e->file, arg_mem->name->line, arg_mem->type->dbg, 1, LLVMDIFlagZero);
        LLVMDIBuilderInsertDeclareAtEnd(
            e->dbg, arg_mem->value, arg_meta[index],
            LLVMBuildAlloca(e->builder, arg_mem->type->type, "arg_alloca"),
            LLVMDIBuilderCreateDebugLocation(e->module_ctx, arg_mem->type->line, 0, fn->scope, NULL),
            LLVMGetInsertBlock(e->builder));
        arg_types[index++] = arg_mem->type;
    }

    set(e->defs, fname, fdef);

    free(arg_meta);
    free(arg_types);

    LLVMSetLinkage(fdef->function->value,
        builder ? LLVMInternalLinkage : LLVMExternalLinkage);

    if (builder) {
        // Create function debug info
        LLVMMetadataRef subroutine = LLVMDIBuilderCreateSubroutineType(
            e->dbg,
            e->file,           // Scope (file)
            NULL,              // Parameter types (None for simplicity)
            0,                 // Number of parameters
            LLVMDIFlagZero     // Flags
        );

        fdef->function->scope = LLVMDIBuilderCreateFunction(
            e->dbg,
            e->file,                // Scope (file)
            cstring(fname), len(fname),
            cstring(fname), len(fname),
            e->file,                // File
            1,                      // Line number
            subroutine,             // Function type
            1,                      // Is local to unit
            1,                      // Is definition
            1,                      // Scope line
            LLVMDIFlagZero,         // Flags
            0                       // Is optimized
        );

        // attach debug info to function
        LLVMSetSubprogram(fn->value, fdef->function->scope);
        fdef->function->entry = LLVMAppendBasicBlockInContext(
            e->module_ctx, fdef->function->value, "entry");
    }
    return fdef;
}

#define create_member(E, T, R, N) new(member, mod, E, name, str(N), is_ref, R, type, get(E->defs, str(T)));

void ether_builder_main(ether e, function fn, map ctx) {
    print("we may build the function now");
    
    member rmem     = create_member(e, "i64", false, ".rtype");
    member template = create_member(e, "i8",  true,  "template");
    //fdef(printf, rtype, template, true);

    type   printf   = ecall(function,
        "printf", null,  rmem, map_of("template", template, null), true, null);
    map    args     = map_of("template", str("something %llu"), "value", A_u64(1024 * 44), null);
    node   n_printf = ecall(fcall,   printf, null, args);
    node   n_ret    = ecall(freturn, i(1));
}

void ether_build(ether e) {
    pairs(e->defs, i) {
        type f = i->value;
        if (f->function) {
            function fn = f->function;
            if (fn->builder) {
                e->current_fn = fn;
                LLVMPositionBuilderAtEnd(e->builder, fn->entry);
                invoke(fn->builder, f);
                e->current_fn = null;
            }
        }
    }
}

#define no_target null

void main() {
    A_start();
    print("lets emit the llvm here, and abstract A-type for the basic declaration set");
    path    src   = new(path,  chars, "WGPU.si");
    ether   e     = new(ether, lang, str("silver"), source, src, name, str("module"));
    member  argc  = create_member(e, "i32",    0, "argc");
    member  argv  = create_member(e, "symbol", 1, "argv");
    member  ret   = create_member(e, "i32",    0, ".return");
    map     args  = map_of(
        "argc", argc,
        "argv", argv,
        null
    );

    /// create function named main
    type fdef = ecall(
        function, "main", no_target, ret, args, false,
        subproc(e, &ether_builder_main, null));
    
    ecall(build);
    ecall(write);
}

define_enum(interface)
define_enum(model)
define_class(token)
define_class(context)
define_class(ether)
define_class(node)

define_mod(op,       node)
define_mod(type,     node)
define_mod(function, node)
define_mod(member,   node)

define_primitive(LLVMValueRef, raw, 0)