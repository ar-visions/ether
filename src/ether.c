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
#define def_lookup(name) get(e->defs, str(name))

/// input is typeid -> 
static map llvm_types;

void def_init(def ident) {
}

void member_init(member mem) {
    /// lets create everything we need for LLVM call here
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

/// its not bad for ether to describe primitives
void ether_init(ether e) {
    /// lets create everything we need for LLVM call here
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

void ether_destructor(ether e) {
    LLVMDisposeBuilder(e->builder);
    LLVMDisposeDIBuilder(e->dbg);
    LLVMDisposeModule(e->module);
    LLVMContextDispose(e->context);
    LLVMDisposeMessage(e->target_triple);
}

void ether_build(ether e) {
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

LLVMValueRef operand(ether e, object op) {
         if (inherits(op, node)) return ((node)op)->value;
    else if (inherits(op,   u8)) return LLVMConstInt (def_lookup( "u8")->type, *( u8*)op, 0);
    else if (inherits(op,  u16)) return LLVMConstInt (def_lookup("u16")->type, *(u16*)op, 0);
    else if (inherits(op,  u32)) return LLVMConstInt (def_lookup("u32")->type, *(u32*)op, 0);
    else if (inherits(op,  u64)) return LLVMConstInt (def_lookup("u64")->type, *(u64*)op, 0);
    else if (inherits(op,   i8)) return LLVMConstInt (def_lookup( "i8")->type, *( i8*)op, 0);
    else if (inherits(op,  i16)) return LLVMConstInt (def_lookup("i16")->type, *(i16*)op, 0);
    else if (inherits(op,  i32)) return LLVMConstInt (def_lookup("i32")->type, *(i32*)op, 0);
    else if (inherits(op,  i64)) return LLVMConstInt (def_lookup("i64")->type, *(i64*)op, 0);
    else if (inherits(op,  f32)) return LLVMConstReal(def_lookup("f32")->type, *(f32*)op);
    else if (inherits(op,  f64)) return LLVMConstReal(def_lookup("f64")->type, *(f64*)op);
    else {
        error("unsupported type in ether_add");
        return NULL;
    }
}

node ether_freturn(ether e, object o) {
    return new(node, mod, e, value, LLVMBuildRet(e->builder, operand(e, o)));
}

node ether_fcall(ether e, def fdef, member target, map args) {
    int n_args = len(args);
    LLVMValueRef* arg_values = calloc((target != null) + n_args, sizeof(LLVMValueRef));

    int index = 0;
    if (target)
        arg_values[index++] = target->value;
    pairs (args, i)
        arg_values[index++] = operand(e, i->value);

    verify (LLVMTypeOf(fdef->function->value) == fdef->type, "integrity check failure");
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
        def,      fdef,     rtype,  rtype,
        builder,  builder,  value,  LLVMAddFunction(e->module, fname->chars, fdef->type));
    fdef->function = fn;
    set(e->defs, fname, fdef);

    LLVMSetLinkage(fdef->function->value,
        builder ? LLVMInternalLinkage : LLVMExternalLinkage);
    return fdef;
}

member member_assemble(def def, int depth, cstr name) {
    return new(member, def, def, depth, depth, name, name ? str(name) : null);
}

#define assemble(e, t, d, n) \
    member_assemble(get(e->defs, str(#t)), d, n)

void ether_builder_main(function fn, ether e, map ctx) {
    print("we may build the function now");
    
    member rtype    = assemble(e, i64,    0, ".rtype");
    member template = assemble(e, symbol, 0, "template");
    //fdef(printf, rtype, template, true);

    def    printf   = ecall(function,
        "printf", null,  rtype, map_of("template", template, null), true, null);
    map    args     = map_of("template", str("something %llu"), "value", A_u64(1024 * 44));
    node   n_printf = ecall(fcall,   printf, args, args);
    node   n_ret    = ecall(freturn, i(1));
}

#define no_target null

void main() {
    A_start();
    print("lets emit the llvm here, and abstract A-type for the basic declaration set");
    ether   e      = new(ether, name, str("a-module"));
    member  i64_x  = assemble(e, i64, 0, "x");
    member  i64_y  = assemble(e, i64, 0, "y");
    member  i32_r  = assemble(e, i32, 0, ".return");
    map     args = map_of(
        "x", i64_x,
        "y", i64_y,
        null
    );
    map ctx  = map_of("2", A_i16(44), null);
    
    /// create function named main, i32 return, two i64 args (not sure if llvm supports that?), and va_args false
    def fdef = ecall(
        function, "main", no_target, i32_r, args, false,
        subproc(&ether_builder_main, ctx));
    
    ecall(build);
}

define_enum(interface)
define_enum(model)

define_class(ether)
define_class(node)

define_mod(op,       node)
define_mod(def,      node)
define_mod(function, node)
define_mod(member,   node)
