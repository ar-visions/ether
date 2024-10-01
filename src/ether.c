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
#define      def_intern  intern(def)
#define    fcall_intern  intern(fcall)
#define function_intern  intern(function)
#define   member_intern  intern(member)
#define     node_intern  intern(node)
#define       op_intern  intern(op)
#define      ret_intern  intern(ret)

#include <ether>

#define ecall(M, ...) ether_##M(e, ## __VA_ARGS__)
#define def_lookup(name) ((def)get(e->defs, str(name)))

/// input is typeid -> 
static map llvm_types;
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

sz def_size(def ident) {
    return LLVMSizeOfTypeInBits(ident->mod->target_data, ident->type);
}

LLVMMetadataRef primitive_dbg(def ident) {
    return LLVMDIBuilderCreateBasicType(
        ident->mod->dbg, ident->name->chars, ident->name->len, def_size(ident),
        ident->name->chars[0] == 'f' ? 0x04 : 0x05, 0);
}

LLVMMetadataRef cstr_dbg(def ident, bool isConst) {
    LLVMMetadataRef charTypeMeta = LLVMDIBuilderCreateBasicType(
        ident->mod->dbg, "char", 4, 8, 0x01, 0); // 0x01 = DW_ATE_unsigned_char
    symbol name = isConst ? "const char" : "char";
    u64 ptr_sz = LLVMPointerSize(ident->mod->target_data);
    return LLVMDIBuilderCreatePointerType(ident->mod->dbg, charTypeMeta,
        ptr_sz * 8, 0, 0, name, strlen(name));
}

void def_init(def ident) {
    ether e = ident->mod;

    ident->members = new(map, hsize, 8);
    bool handled_members = false;

    switch (ident->mdl) {
        case model_class:
            fault ("not implemented");
            break;
        
        case model_function:
            break;
        
        case model_bool:   ident->type = LLVMInt1Type  (); break;
        case model_i8:     ident->type = LLVMInt8Type  (); break;
        case model_i16:    ident->type = LLVMInt16Type (); break;
        case model_i32:    ident->type = LLVMInt32Type (); break;
        case model_i64:    ident->type = LLVMInt64Type (); break;
        case model_u8:     ident->type = LLVMInt8Type  (); break;
        case model_u16:    ident->type = LLVMInt16Type (); break;
        case model_u32:    ident->type = LLVMInt32Type (); break;
        case model_u64:    ident->type = LLVMInt64Type (); break;
        case model_f32:    ident->type = LLVMFloatType (); break;
        case model_f64:    ident->type = LLVMDoubleType(); break;
        case model_void:   ident->type = LLVMVoidType  (); break;
        case model_cstr:   ident->type = LLVMPointerType(LLVMInt8Type(), 0); break;
        case model_typedef: {
            verify (ident->origin && isa(ident->origin) == typeid(member), "origin must be ident reference");
            ident->type = ident->origin->type;
            if (e->dbg) {
                member origin = ident->origin;
                verify(origin, "origin not resolved");
                ident->dbg = LLVMDIBuilderCreateTypedef(
                    e->dbg, ident->origin->def->dbg, ident->name->chars, len(ident->name),
                    e->file, 0, e->scope, LLVMDIFlagZero);
            }
            break;
        }
        case model_struct: {
            LLVMTypeRef* member_types = calloc(len(ident->members), sizeof(LLVMTypeRef));
            int index = 0;
            pairs(ident->members, i) {
                member mem = i->value;
                verify(isa(mem) == typeid(member), "mismatch");
                member_types[index] = mem->type;
                index++;
            }
            ident->type = LLVMStructCreateNamed(LLVMGetGlobalContext(), ident->name);
            LLVMStructSetBody(ident->type, member_types, index, 0);
            handled_members = true;
            break;
        }
        case model_union: {
            verify (false, "not implemented");
            break;
        }
    }

    /// create debug info for primitives
    if (ident->mdl >= model_bool && ident->mdl <= model_f64)
        ident->dbg = primitive_dbg(ident);
    else if (eq(ident->name, "symbol") || eq(ident->name, "cstr"))
        ident->dbg = cstr_dbg(ident, eq(ident->name, "symbol"));
    else if (ident->mdl != model_function) {
        verify (ident->dbg || eq(ident->name, "void"), "debug info not set for type");
    }
    verify (!count(ident->members) || handled_members, "members given and not processed");
}

void member_init(member mem) {
    /// lets create everything we need for LLVM call here
    if (mem->def && !mem->type)
        mem->type = mem->def->type;
}

void value_init(value val) {
    /// lets create everything we need for LLVM call here
}

void op_init(op op) {
    /// lets create everything we need for LLVM call here
}


void ret_init(ret op) {
    /// lets create everything we need for LLVM call here
}

void ether_define_primitive(ether e) {
    map defs = e->defs = new(map, hsize, 64);
    set(defs, str("bool"),    new(def, mod, e, name, str("bool"),   mdl, model_bool, imported, typeid(bool)));
    set(defs, str("i8"),      new(def, mod, e, name, str("i8"),     mdl, model_i8,   imported, typeid(i8)));
    set(defs, str("i16"),     new(def, mod, e, name, str("i16"),    mdl, model_i16,  imported, typeid(i16)));
    set(defs, str("i32"),     new(def, mod, e, name, str("i32"),    mdl, model_i32,  imported, typeid(i32)));
    set(defs, str("i64"),     new(def, mod, e, name, str("i64"),    mdl, model_i64,  imported, typeid(i64)));
    set(defs, str("u8"),      new(def, mod, e, name, str("u8"),     mdl, model_u8,   imported, typeid(u8)));
    set(defs, str("u16"),     new(def, mod, e, name, str("u16"),    mdl, model_u16,  imported, typeid(u16)));
    set(defs, str("u32"),     new(def, mod, e, name, str("u32"),    mdl, model_u32,  imported, typeid(u32)));
    set(defs, str("u64"),     new(def, mod, e, name, str("u64"),    mdl, model_u64,  imported, typeid(u64)));
    set(defs, str("f32"),     new(def, mod, e, name, str("f32"),    mdl, model_f32,  imported, typeid(f32)));
    set(defs, str("f64"),     new(def, mod, e, name, str("f64"),    mdl, model_f64,  imported, typeid(f64)));
    set(defs, str("void"),    new(def, mod, e, name, str("void"),   mdl, model_void, imported, typeid(none)));
    set(defs, str("symbol"),  new(def, mod, e, name, str("symbol"), mdl, model_cstr, imported, typeid(symbol)));
    set(defs, str("cstr"),    new(def, mod, e, name, str("cstr"),   mdl, model_cstr, imported, typeid(cstr)));
    set(defs, str("int"),     get(defs, str("i64")));
    set(defs, str("uint"),    get(defs, str("u64")));
}

map ether_top_members(ether e) {
    assert (e->members->len, "stack is empty");
    return last(e->members);
}

member ether_member_lookup(ether e, string name) {
    for (int m = e->members->len - 1; m >= 0; m--) {
        map members = e->members->elements[m];
        member f = get(members, name);
        if (f) return f;
    }
    return null;
}

map ether_push_members(ether e) {
    map members = new(map, hsize, 16);
    push(e->members, members);
    return members;
}

map ether_pop_members(ether e) {
    pop(e->members);
    return len(e->members) ? last(e->members) : null;
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
        e->context, line, column, e->scope, null);
    LLVMSetCurrentDebugLocation2(e->dbg, loc);
}

void ether_llflag(ether e, symbol flag, i32 ival) {
    LLVMMetadataRef v = LLVMValueAsMetadata(
        LLVMConstInt(LLVMInt32TypeInContext(e->context), ival, 0));
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
    e->members        = new(array, alloc, 32);
    //e->type_refs    = new(map, hsize, 64);
    e->module         = LLVMModuleCreateWithName(e->name->chars);
    e->context        = LLVMGetModuleContext(e->module);
    e->dbg            = LLVMCreateDIBuilder(e->module);
    e->builder        = LLVMCreateBuilderInContext(e->context);
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
    e->builder = LLVMCreateBuilderInContext(e->context);
}

/// its not bad for ether to describe primitives
void ether_init(ether e) {
    ether_llvm_init(e);
    ether_define_primitive(e);
}

void ether_destructor(ether e) {
    LLVMDisposeBuilder(e->builder);
    LLVMDisposeDIBuilder(e->dbg);
    LLVMDisposeModule(e->module);
    LLVMContextDispose(e->context);
    LLVMDisposeMessage(e->target_triple);
}

def preferred_type(ether e, def t0, def t1) {
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
    else if (inherits(op,     u8)) return LLVMConstInt (def_lookup( "u8")->type, *( u8*)op, 0);
    else if (inherits(op,    u16)) return LLVMConstInt (def_lookup("u16")->type, *(u16*)op, 0);
    else if (inherits(op,    u32)) return LLVMConstInt (def_lookup("u32")->type, *(u32*)op, 0);
    else if (inherits(op,    u64)) return LLVMConstInt (def_lookup("u64")->type, *(u64*)op, 0);
    else if (inherits(op,     i8)) return LLVMConstInt (def_lookup( "i8")->type, *( i8*)op, 0);
    else if (inherits(op,    i16)) return LLVMConstInt (def_lookup("i16")->type, *(i16*)op, 0);
    else if (inherits(op,    i32)) return LLVMConstInt (def_lookup("i32")->type, *(i32*)op, 0);
    else if (inherits(op,    i64)) return LLVMConstInt (def_lookup("i64")->type, *(i64*)op, 0);
    else if (inherits(op,    f32)) return LLVMConstReal(def_lookup("f32")->type, *(f32*)op);
    else if (inherits(op,    f64)) return LLVMConstReal(def_lookup("f64")->type, *(f64*)op);
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

node ether_fcall(ether e, def fdef, member target, map args) {
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

/// the only thing ether may import is functions, so 'import' implies we're importing a C function
def ether_fn_init(ether e, cstr name, def target, member return_type, map args, bool va_args) {
    
}

/// design a function with an additional arg of a subprocedure
def ether_function(ether e, cstr name, def target,
        member return_type, map args, bool va_args, subprocedure builder) {
    LLVMTypeRef  rtype     = return_type->type;
    int          n_args    = len(args);
    LLVMTypeRef* arg_types = calloc((target != null) + n_args, sizeof(LLVMTypeRef));
    int          index     = 0;
    if (target)
        arg_types[index++] = LLVMPointerType(target->type, 0);
    pairs(args, i) {
        member arg_mem     = i->value;
        arg_types[index++] = arg_mem->type;
    }

    string fname = str(name);
    def    fdef  = new(def,
        name,     fname,  type,   LLVMFunctionType(rtype, arg_types, index, va_args),
        function, null,   mdl,    model_function);
    def    fn    = new(function,
        name,     fname,    target, target,
        def,      fdef,     rtype,  return_type,
        builder,  builder,  value,  LLVMAddFunction(e->module, fname->chars, fdef->type));
    fdef->function = fn;
    set(e->defs, fname, fdef);

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

        LLVMMetadataRef fn_meta = LLVMDIBuilderCreateFunction(
            e->dbg,
            e->file,                // Scope (file)
            "main",                 // Name
            strlen("main"),
            "main",                 // Linkage name (same as name)
            strlen("main"),
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
        LLVMSetSubprogram(fn->value, fn_meta);
        fdef->function->entry = LLVMAppendBasicBlockInContext(
            e->context, fdef->function->value, "entry");
    }
    return fdef;
}

member member_assemble(def def, int depth, cstr name) {
    return new(member, def, def, depth, depth, name, name ? str(name) : null);
}

#define assemble(e, t, d, n) \
    member_assemble(get(e->defs, str(#t)), d, n)

void ether_builder_main(ether e, function fn, map ctx) {
    print("we may build the function now");
    
    member rtype    = assemble(e, i64,    0, ".rtype");
    member template = assemble(e, symbol, 0, "template");
    //fdef(printf, rtype, template, true);

    def    printf   = ecall(function,
        "printf", null,  rtype, map_of("template", template, null), true, null);
    map    args     = map_of("template", str("something %llu"), "value", A_u64(1024 * 44), null);
    node   n_printf = ecall(fcall,   printf, null, args);
    node   n_ret    = ecall(freturn, i(1));
}

void ether_build(ether e) {
    pairs(e->defs, i) {
        def f = i->value;
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
    member  argc  = assemble(e, i32,    0, "argc");
    member  argv  = assemble(e, symbol, 1, "argv");
    member  ret   = assemble(e, i32,    0, ".return");
    map     args  = map_of(
        "argc", argc,
        "argv", argv,
        null
    );

    /// create function named main
    def fdef = ecall(
        function, "main", no_target, ret, args, false,
        subproc(e, &ether_builder_main, null));
    
    ecall(build);
    ecall(write);
}

define_enum(interface)
define_enum(model)

define_class(ether)
define_class(node)

define_mod(op,       node)
define_mod(def,      node)
define_mod(function, node)
define_mod(member,   node)
