#include <llvm-c/DebugInfo.h>
#include <llvm-c/Core.h>
#include <llvm-c/ExecutionEngine.h>
#include <llvm-c/Target.h>
#include <llvm-c/Analysis.h>
#include <llvm-c/TargetMachine.h>
#include <llvm-c/BitWriter.h>
#include <clang-c/Index.h>

typedef LLVMMetadataRef LLVMScope;

#define i_ether    internal(ether)
#define i_def      internal(def)
#define i_fcall    internal(fcall)
#define i_function internal(function)
#define i_member   internal(member)
#define i_value    internal(value)
#define i_add      internal(add)
#define i_sub      internal(sub)
#define i_mul      internal(mul)
#define i_div      internal(div)
#define i_ret      internal(ret)

#include <ether>

#define ecall(M, ...) ether_##M(e, ## __VA_ARGS__)

/// input is typeid -> 
static map llvm_types;

void def_init(def ident) {
}

void fcall_init(fcall f) {
    /// lets create everything we need for LLVM call here
}

void function_init(function fn) {
    /// lets create everything we need for LLVM call here
}

void member_init(member mem) {
    /// lets create everything we need for LLVM call here
}

void value_init(value val) {
    /// lets create everything we need for LLVM call here
}

void add_init(add op) {
    /// lets create everything we need for LLVM call here
}

void mul_init(mul op) {
    /// lets create everything we need for LLVM call here
}

void div_init(div op) {
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


void ether_build_fn(function fn, object arg, map ctx) {
    print("we may build the function now");
}

void main() {
    print("lets emit the llvm here, and abstract A-type for the basic declaration set");
    ether e   = new(ether, name, str("a-module"));
    def   i64 = get(e->defs, str("i64"));
    map  args = map_of(
        "x", new(member, name, "x", def, i64, depth, 0),
        "y", new(member, name, "y", def, i64, depth, 0),
        null
    );
    map ctx = map_of("2", A_i16(44));
    function fn = new(function,
        mod,        e,
        args,       args,
        va_args,    false,
        content,    subproc(&ether_build_fn, ctx));

    ecall(build);
}

define_enum(interface)
define_enum(model)

define_class(ether)

define_class(node)
define_mod(value,    node)
define_mod(fcall,    node)
define_mod(add,      node)
define_mod(sub,      node)
define_mod(mul,      node)
define_mod(div,      node)
define_mod(def,      node)
define_mod(function, node)
define_mod(member,   node)
