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
#define   context_intern  intern(context)
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
#define elookup(name) ((type)lookup(e->base, str(name)))
#define no_target null

#define create_member(E, T, R, N) new(member, mod, E, name, str(N), is_ref, R, type, get(E->base, str(T)));

static map operators;

/// we should get a 'stride' for a given member
model member_model(member f, bool allow_ref) {
    return f->mdl;
}

bool is_bool     (member f) { return isa(f->mdl->data) == typeid(bool); }
bool is_float    (member f) { return isa(f->mdl->data) == typeid(f32);  }
bool is_double   (member f) { return isa(f->mdl->data) == typeid(f64);  }
bool is_realistic(member f) { return isa(f->mdl->data)->traits & A_TRAIT_REALISTIC; }
bool is_integral (member f) { return isa(f->mdl->data)->traits & A_TRAIT_INTEGRAL;  }
bool is_signed   (member f) { return isa(f->mdl->data)->traits & A_TRAIT_SIGNED;    }
bool is_unsigned (member f) { return isa(f->mdl->data)->traits & A_TRAIT_UNSIGNED;  }

bool is_object   (member f) {
    return isa(f->mdl->data) == typeid(structure) || 
           isa(f->mdl->data) == typeid(class);
}

bool is_class    (member f) {
    return isa(f->mdl->data) == typeid(class);
}

bool is_struct   (member f) {
    return isa(f->mdl->data) == typeid(structure);
}

bool is_ref      (member f) {
    return isa(f->mdl->data) == typeid(model);
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


i64 model_size(model mdl) {
    return LLVMABISizeOfType(mdl->mod->target_data, mdl->type);
}

i64 model_alignment(model mdl) {
    return LLVMABIAlignmentOfType(mdl->mod->target_data, mdl->type);
}

void model_init(model mdl) {
    ether  e = mdl->mod;

    if (mdl->name && inherits(mdl->name, string)) {
        string n = mdl->name;
        mdl->name = new(token, chars, cs(n), source, e->source, line, 1);
    }

    AType type = isa(mdl->data);

    if (type->traits & A_TRAIT_PRIMITIVE) {
        mdl->is_signed    = type->name[0] == 'i';
        mdl->is_realistic = type->name[0] == 'f';
        if (mdl->is_realistic) {
            if      (type == typeid(f32))
                mdl->type = LLVMFloatType();
            else if (type == typeid(f64))
                mdl->type = LLVMDoubleType();
            else fault("unsupported float: %s", type->name);
        } else {
            if      (type == typeid(none))
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
            else fault("unsupported primitive: %s", type->name); 
        }
    } else {
        // we still need static array (use of integral shape), aliases

        // can be a class, structure, function
        if (type == typeid(model)) {
            model  src = mdl->data;
            /// this is a reference, so we create type and debug based on this
            u64 ptr_sz = LLVMPointerSize(e->target_data);
            mdl->type  = LLVMPointerType(src->type, 0);
            if (mdl->name)
                mdl->debug = LLVMDIBuilderCreatePointerType(e->debug, src->type,
                    ptr_sz * 8, 0, 0, cs(mdl->name), len(mdl->name));
        } else if (type == typeid(structure) || type == typeid(class)) {
            record rec = mdl->data;
            mdl->type  = rec->type;
            mdl->debug = rec->debug;
        } else if (type == typeid(function)) {
            function fn = mdl->data;
            mdl->type  = fn->type;
            mdl->debug = fn->debug;
        } else if (type == typeid(alias)) {

        } else {
            fault("unsupported model type: %s", type->name);
        }
    }
}

void function_init(function fn) {
    ether e = var->type->mod;
    /// create function and its debug information
    LLVMTypeRef      rtype     = fn->rtype->type; // rtype should be 'model' not member
    int              n_args    = len(fn->args);
    LLVMTypeRef*     arg_types = calloc((fn->target != null) + n_args, sizeof(LLVMTypeRef));
    int              index     = 0;

    if (target) {
        verify (typeid(fn->target->mdl->data) == typeid(model),
            "target must be a pointer");
        model mdl_target = fn->target->mdl->data;
        verify (typeid(mdl_target->data) == typeid(struct) || typeid(mdl_target->data) == typeid(class),
            "target must be pointer to a record type (struct / class)");
        arg_types[index++] = fn->target->mdl->type; // verify this is a pointer type here! LLVMPointerType(fn->target->ref, 0);
    }

    print("function %o", fn->name);
    each(fn->args, member, arg) {
        arg_types[index++] = arg->type->ref;
        print("arg type [%i] = %s", index - 1,
            LLVMPrintTypeToString(arg->type->ref));
        /// create debug for parameter here
    }

    fn->type  = LLVMFunctionType(rtype, arg_types, index, va_args);
    fn->value = LLVMAddFunction(e->module, fn->name->chars, fn_type);

    //free(arg_types); (llvm seems to not copy these)

    LLVMSetLinkage(fn->value,
        fn->builder ? LLVMInternalLinkage : LLVMExternalLinkage);

    if (!fn->builder)
        return;
    
    // Create function debug info
    LLVMMetadataRef subroutine = LLVMDIBuilderCreateSubroutineType(
        e->debug,
        e->file,           // Scope (file)
        NULL,              // Parameter types (None for simplicity)
        0,                 // Number of parameters
        LLVMDIFlagZero     // Flags
    );

    fn->scope = LLVMDIBuilderCreateFunction(
        e->debug,
        e->file,                // Scope (file)
        cstring(fn->name), len(fn->name),
        cstring(fn->name), len(fn->name),
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
    fn->entry = LLVMAppendBasicBlockInContext(
        e->module_ctx, fn->value, "entry");

    /// create debug info for arguments (including target)
    index = 0;

    if (fn->target) {
        LLVMMetadataRef paramVarMeta = LLVMDIBuilderCreateParameterVariable(
            e->debug,          // DIBuilder reference
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
        LLVMValueRef param_value = LLVMGetParam(fn->value, 0);
        LLVMValueRef decl = LLVMBuildDeclare(
            e->builder,                 // The LLVM builder
            param_value,                // The LLVMValueRef for the first parameter
            param_meta,                 // The debug metadata for the first parameter
            LLVMDIBuilderCreateExpression(e->debug, NULL, 0), // Empty expression
            LLVMGetCurrentDebugLocation2(e->builder),       // Current debug location
            fn->entry);                 // Attach it in the function's entry block
        index++;
    }

    each(fn->args, member, arg) {
        /// create debug for parameter here
        LLVMMetadataRef param_meta = LLVMDIBuilderCreateParameterVariable(
            e->debug,          // DIBuilder reference
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
        LLVMValueRef decl        = LLVMBuildDeclare(
            e->builder,                 // The LLVM builder
            param_value,                // The LLVMValueRef for the first parameter
            param_meta,                 // The debug metadata for the first parameter
            LLVMDIBuilderCreateExpression(e->debug, NULL, 0), // Empty expression
            LLVMGetCurrentDebugLocation2(e->builder),       // Current debug location
            fn->entry);                 // Attach it in the function's entry block
    }

}

void record_init(record rec) {
    ether e = mem->mod;

    rec->type = LLVMStructCreateNamed(LLVMGetGlobalContext(), rec->name);
    verify(rec->ctx, "record/struct/class: no context given");

    /// rec has ctx -> members (map of str -> member) we iterate with 
    int total = 0;
    record r = rec;
    array a = new(array, alloc, 32);
    while (r) {
        total += len(rec->ctx->members);
        push(a, r);
        r = r->parent;
    }
    LLVMTypeRef*     member_types = calloc(total, sizeof(LLVMTypeRef));
    LLVMMetadataRef* member_debug = calloc(total, sizeof(LLVMMetadataRef));
    int index = 0;
    each (a, record, r) {
        pairs(r->ctx->members, i) {
            member mem = i->value;
            verify( mem->name,  "no name on member");
            verify(!mem->debug, "debug info already present on member created for structure");

            mem->debug = LLVMDIBuilderCreateMemberType(
                e->debug,              // LLVMDIBuilderRef
                e->top->scope,         // Scope of the member (can be the struct, class or base module)
                cs(mem->name),         // Name of the member
                name_len,              // Length of the name
                e->file,               // The file where the member is declared
                mem->name->line,       // Line number where the member is declared
                mem->type->size * 8,   // Size of the member in bits (e.g., 32 for a 32-bit int)
                0,                     // Alignment of the member in bits
                0,                     // Offset in bits from the start of the struct or class
                0,                     // Debug info flags (e.g., 0 for none)
                mem->model->debug      // The LLVMMetadataRef for the member's type (created earlier)
            );

            /// this member would have been init'd already, so it may have debug however we have no debug for this 'structure'
            member_types[index]   = mem->mdl->type;
            member_debug[index++] = mem->debug;
        }
    }

    LLVMStructSetBody(rec->type, member_types, index, 0);

    // mdl is required on member
    mem->debug = LLVMDIBuilderCreateStructType(
        e->debug,                     // Debug builder
        e->top->scope,                // Scope (module or file)
        cs(mem->name),                // Name of the struct
        e->file,                      // File where it’s defined
        mem->name->line,              // Line number where it’s defined
        model_size(mem->mdl),         // Size in bits (assuming 2 32-bit fields)
        model_alignment(mem->mdl),    // Alignment in bits
        LLVMDIFlagZero,               // Flags
        NULL,                         // Derived from (NULL in C)
        member_debug,                 // Array of member debug info
        total,                        // Number of members
        0,                            // Runtime language (0 for none)
        NULL,                         // No VTable
        NULL);
}

void member_init(member mem) {
    ether   e   = mem->mod;
    context top = e->top;

    if (inherits(mem->name, string)) {
        string n = mem->name;
        mem->name = new(token, chars, cs(n), source, e->source, line, 1);
    }

    verify (mem->mdl->debug, "no debug info on type");
    AType type_ctx = isa(top->container);

    /// if we are creating a new member inside of a function, we need
    /// to make debug and value info here
    if (type_ctx == typeid(function)) {
        function fn = top->container;

        verify (!mem->value, "value-ref already set auto member");

        mem->value = LLVMBuildAlloca(e->builder, mem->mdl->type, cs(mem->name));
        mem->debug = LLVMDIBuilderCreateAutoVariable(
            e->debug,           // DIBuilder reference
            top->scope,         // The scope (subprogram/function metadata)
             cs(mem->name),     // Variable name
            len(mem->name),
            e->file,            // File where it’s declared
            mem->name->line,    // Line number
            mem->mdl->debug,    // Type of the variable (e.g., LLVMMetadataRef for int)
            true,               // Is this variable always preserved (DebugPreserveAll)?
            0                   // Flags (usually 0)
        );

        // Attach the debug info to the actual LLVM IR value using llvm.dbg.value
        //LLVMBuildDbgValue(
        //    e->builder,              // LLVM Builder
        //    mem->value,              // The LLVMValueRef for the value being assigned to the member
        //    mem->debug,              // Debug info for the variable
        //    LLVMGetCurrentDebugLocation2(e->builder));
        
        LLVMBuildDeclare(
            e->builder,                 // The LLVM builder
            mem->value,                 // The LLVMValueRef for the first parameter
            mem->debug,                 // The debug metadata for the first parameter
            LLVMDIBuilderCreateExpression(e->debug, NULL, 0), // Empty expression
            LLVMGetCurrentDebugLocation2(e->builder),       // Current debug location
            fn->entry);
    }

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

#define value(def,vr) new(node, mod, e, value, vr, type, def)

node ether_get_ref(ether e, node expr, type of_type) {
    type ref_type = new(type, mod, e,
        mdl,    model_typedef,
        origin, of_type,
        depth,  1); // if type has depth, we are creating another depth to it. origin logic should work with both aliasing and referencing
    LLVMValueRef ref_value = LLVMBuildGEP2(e->builder, ref_type->ref, expr->value, NULL, 0, "ref_expr");
    return LLVMBuildLoad2(e->builder, of_type->ref, expr->value, "ref_expr"); // Build the reference
}

node ether_load(ether e, member mem) {
    print ("member type = %s", LLVMPrintTypeToString(LLVMTypeOf(mem->type->ref)));
    LLVMValueRef vr = LLVMBuildLoad2(e->builder, mem->type->ref, mem->value, "load-member");
    return new(node, mod, e, type, mem->type, value, vr);
}

/// this is the cast caller, too
node ether_convert(ether e, node expr, type rtype) {
    type         F = expr->type;
    type         T = rtype;
    LLVMValueRef V = NULL;

    if (F == T) return expr;  // No cast needed

    // Get the LLVM type kinds of source and destination types
    LLVMTypeKind F_kind = LLVMGetTypeKind(F->ref);
    LLVMTypeKind T_kind = LLVMGetTypeKind(T->ref);

    // Integer to Integer conversion
    if (F_kind == LLVMIntegerTypeKind && T_kind == LLVMIntegerTypeKind) {
        uint F_bits = LLVMGetIntTypeWidth(F->ref), T_bits = LLVMGetIntTypeWidth(T->ref);
        if (F_bits < T_bits)
            V = is_signed(F) ? LLVMBuildSExt(e->builder, expr->value, T->ref, "sext")
                             : LLVMBuildZExt(e->builder, expr->value, T->ref, "zext");
        else if (F_bits > T_bits)
            V = LLVMBuildTrunc(e->builder, expr->value, T->ref, "trunc");
        else
            V = LLVMBuildIntCast(e->builder, expr->value, T->ref, "intcast");
    }

    // Integer to Float conversion
    else if (F_kind == LLVMIntegerTypeKind && (T_kind == LLVMFloatTypeKind || T_kind == LLVMDoubleTypeKind))
        V = is_signed(F) ? LLVMBuildSIToFP(e->builder, expr->value, T->ref, "sitofp")
                         : LLVMBuildUIToFP(e->builder, expr->value, T->ref, "uitofp");

    // Float to Integer conversion
    else if ((F_kind == LLVMFloatTypeKind || F_kind == LLVMDoubleTypeKind) && T_kind == LLVMIntegerTypeKind)
        V = is_signed(T) ? LLVMBuildFPToSI(e->builder, expr->value, T->ref, "fptosi")
                         : LLVMBuildFPToUI(e->builder, expr->value, T->ref, "fptoui");

    // Float to Float conversion
    else if ((F_kind == LLVMFloatTypeKind || F_kind == LLVMDoubleTypeKind) && 
             (T_kind == LLVMFloatTypeKind || T_kind == LLVMDoubleTypeKind))
        V = F_kind == LLVMDoubleTypeKind && T_kind == LLVMFloatTypeKind ? 
            LLVMBuildFPTrunc(e->builder, expr->value, T->ref, "fptrunc") :
            LLVMBuildFPExt  (e->builder, expr->value, T->ref, "fpext");

    // Pointer to Pointer conversion
    else if (is_ref(F) && is_ref(T))
        V = LLVMBuildPointerCast(e->builder, expr->value, T->ref, "ptr_cast");

    // Pointer to Integer conversion
    else if (is_ref(F) && is_integral(T))
        V = LLVMBuildPtrToInt(e->builder, expr->value, T->ref, "ptr_to_int");

    // Integer to Pointer conversion
    else if (is_integral(F) && is_ref(T))
        V = LLVMBuildIntToPtr(e->builder, expr->value, T->ref, "int_to_ptr");

    // Bitcast for same-size types
    else if (F_kind == T_kind)
        V = LLVMBuildBitCast(e->builder, expr->value, T->ref, "bitcast");

    else
        fault("Unsupported cast from %o to %o", estr(model, F->mdl), estr(model, T->mdl));

    return value(T,V);
}

type ether_return_type(ether e) {
    for (int i = len(e->lex) - 1; i >= 0; i--) {
        context t = e->lex->elements[i];
        if (t->rtype) return t->rtype;
    }
    return null;
}


static node operand(ether e, object op) {

         if (inherits(op,   node)) return op;
    else if (inherits(op,     u8)) return value(edef("u8"),  LLVMConstInt (edef( "u8")->ref, *( u8*)op, 0));
    else if (inherits(op,    u16)) return value(edef("u16"), LLVMConstInt (edef("u16")->ref, *(u16*)op, 0));
    else if (inherits(op,    u32)) return value(edef("u32"), LLVMConstInt (edef("u32")->ref, *(u32*)op, 0));
    else if (inherits(op,    u64)) return value(edef("u64"), LLVMConstInt (edef("u64")->ref, *(u64*)op, 0));
    else if (inherits(op,     i8)) return value(edef("i8"),  LLVMConstInt (edef( "i8")->ref, *( i8*)op, 0));
    else if (inherits(op,    i16)) return value(edef("i16"), LLVMConstInt (edef("i16")->ref, *(i16*)op, 0));
    else if (inherits(op,    i32)) return value(edef("i32"), LLVMConstInt (edef("i32")->ref, *(i32*)op, 0));
    else if (inherits(op,    i64)) return value(edef("i64"), LLVMConstInt (edef("i64")->ref, *(i64*)op, 0));
    else if (inherits(op,    f32)) return value(edef("f32"), LLVMConstReal(edef("f32")->ref, *(f32*)op));
    else if (inherits(op,    f64)) return value(edef("f64"), LLVMConstReal(edef("f64")->ref, *(f64*)op));
    else if (inherits(op, string)) {
        LLVMTypeRef  gs      = LLVMBuildGlobalStringPtr(e->builder, ((string)op)->chars, "chars");
        LLVMValueRef cast_i8 = LLVMBuildBitCast(e->builder, gs, LLVMPointerType(LLVMInt8Type(), 0), "cast_i8*");
        return value(edef("i8"), cast_i8);
    }
    else {
        error("unsupported type in ether_add");
        return NULL;
    }
}

node ether_assign(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->type, LLVMBuildStore(e->builder, RV->value, L->value));
}
node ether_assign_add(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->type, LLVMBuildAdd (e->builder, RV->value, L->value, "assign-add"));
}
node ether_assign_sub(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->type, LLVMBuildSub (e->builder, RV->value, L->value, "assign-sub"));
}
node ether_assign_mul(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->type, LLVMBuildMul (e->builder, RV->value, L->value, "assign-mul"));
}
node ether_assign_div(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->type, LLVMBuildSDiv(e->builder, RV->value, L->value, "assign-div"));
}
node ether_assign_mod(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->type, LLVMBuildSRem(e->builder, RV->value, L->value, "assign-mod"));
}
node ether_assign_or (ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->type, LLVMBuildOr  (e->builder, RV->value, L->value, "assign-or"));
}
node ether_assign_and(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->type, LLVMBuildAnd (e->builder, RV->value, L->value, "assign-and"));
}
node ether_assign_xor(ether e, node L, object R) {
    node RV = operand(e, R);
    return value(L->type, LLVMBuildXor (e->builder, RV->value, L->value, "assign-xor"));
}

void ether_define(ether e, member e) {
    verify (!contains(e->base, str(name)), "duplicate definition");
    set(e->base, mem->name, mem);
}

void ether_base_model(ether e, symbol name, i32 bits, bool is_signed, bool is_realistic, AType native) {
    /// not always practical to set fields first, and provide to member
    /// so member probably wont do much in init
    model mdl = new(model, // debug info is created in the init
        bits,         bits,         is_signed,  is_signed,  mod, e,
        is_realistic, is_realistic, native,     native,     debug, debug);
    member mem = new(member, mod, e, name, name, mdl, mdl);
    ether_define(e, mem);
    verify (!contains(e->base, str(name)), "duplicate definition");
    set(e->base, str(name), mem);
}

member ether_alias(ether e, symbol cs) {
    member alias = new(member, mod, e, origin, );
}

void ether_define_primitive(ether e) {
    e->base = new(map, hsize, 64);
    ether_base_model(e, "bool", 1, false, false, typeid(bool));
    ether_base_model(e, "u8",   8, false, false, typeid(u8));
    ether_base_model(e, "u16", 16, false, false, typeid(u16));
    ether_base_model(e, "u32", 32, false, false, typeid(u32));
    ether_base_model(e, "u64", 64, false, false, typeid(u64));
    ether_base_model(e, "i8",   8, true,  false, typeid(i8));
    ether_base_model(e, "i16", 16, true,  false, typeid(i16));
    ether_base_model(e, "i32", 32, true,  false, typeid(i32));
    ether_base_model(e, "i64", 64, true,  false, typeid(i64));
    ether_base_model(e, "f32", 32, false, true,  typeid(i32));
    ether_base_model(e, "f64", 64, false, true,  typeid(i64));
    
    //member chr = edef("i8");
    member _cstr = new(member, mod, e);
    fset(_cstr,  name,   str("cstr"));
    fset(_cstr,  ref,    A_bool(true));
    fset(_cstr,  origin, elookup("i8"));
    set(e->base, fget(_cstr, name), _cstr);

    member _symbol = new(member, mod, e);
    fset(_symbol, name,   str("symbol"));
    fset(_symbol, const,  A_bool(true));
    fset(_symbol, origin, cs);
    set(e->base, fget(_symbol, name), _symbol);

    member _char = new(member, mod, e);
    fset(_char,  name,   str("char"));
    fset(_char,  origin, elookup("i32"));
    set(e->base, fget(_char, name), _char);

    member _int = new(member, mod, e);
    fset(_int,  name,   str("int"));
    fset(_int,  origin, elookup("i64"));
    set(e->base, fget(_int, name), _int);

    member _uint = new(member, mod, e);
    fset(_uint,  name,   str("uint"));
    fset(_uint,  origin, elookup("u64"));
    set(e->base, fget(_uint, name), _uint);
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


type ether_find_base(ether e, string name) {
    return get(e->base, name);
}

/// look up a member in lexical scope
member ether_lookup(ether e, string name) {
    for (int i = len(e->lex) - 1; i >= 0; i--) {
        context t = e->lex->elements[i];
        member  m = get(t->members, name);
        if (m)
            return  m;
    }
    return null;
}

context ether_push(ether e) {
    context t = new(context);
    t->scope  = e->top ? LLVMDIBuilderCreateLexicalBlock(
        e->debug, e->top->scope, e->file, 1, 0) : e->compile_unit;
    push(e->lex, t);
    e->top = t;
    return t;
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
    LLVMSetCurrentDebugLocation2(e->debug, loc);
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
    e->debug          = LLVMCreateDIBuilder(e->module);
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
        e->debug,
        cast(src_file, cstr), cast(src_file, sz),
        cast(src_path, cstr), cast(src_path, sz));
    
    e->compile_unit = LLVMDIBuilderCreateCompileUnit(
        e->debug, LLVMDWARFSourceLanguageC, e->file,
        "silver", 6, 0, "", 0,
        0, "", 0, LLVMDWARFEmissionFull, 0, 0, 0, "", 0, "", 0);

    path  full_path = form(path, "%o/%o", src_path, src_file);
    verify(exists(full_path), "source (%o) does not exist", full_path);
    e->builder = LLVMCreateBuilderInContext(e->module_ctx);
}


void ether_init(ether e) {
    ether_llvm_init(e);
    e->lex = new(array, alloc, 32);
    push(e);
    ether_define_primitive(e);
}


void ether_destructor(ether e) {
    LLVMDisposeBuilder(e->builder);
    LLVMDisposeDIBuilder(e->debug);
    LLVMDisposeModule(e->module);
    LLVMContextDispose(e->module_ctx);
    LLVMDisposeMessage(e->target_triple);
}

/// C type rules implemented
type determine_rtype(ether e, OPType optype, type L, type R) {
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
                return edef("bool");  // Logical operations on booleans return boolean
            // For bitwise operations, fall through to numeric promotion
            break;

        default:
            fault("not implemented");
            break;
    }

    // Numeric type promotion
    if (is_realistic(L) || is_realistic(R)) {
        // If either operand is float, result is float
        if (is_double(L) || is_double(R))
            return edef("f64");
        else
            return edef("f32");
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
    if (is_float(L->type))
        return LLVMBuildFNeg(e->builder, L->value, "f-negate");
    else if (is_signed(L->type)) // our enums should fall into this category
        return LLVMBuildNeg(e->builder, L->value, "i-negate");
    else if (is_unsigned(L->type)) {
        // Convert unsigned to signed, negate, then convert back to unsigned
        LLVMValueRef signed_value  = LLVMBuildIntCast2(
            e->builder, L->value, LLVMIntType(L->type->size * 8), 1, "to-signed");
        LLVMValueRef negated_value = LLVMBuildNeg(
            e->builder, signed_value, "i-negate");
        type itype = edef("i64");
        LLVMValueRef i64_value = LLVMBuildIntCast2(
            e->builder, negated_value, itype->ref, 1, "to-i64");

        return value(itype, negated_value);
    }
    else {
        fault("object negation not valid");
    }
}

node ether_not(ether e, node L) {
    LLVMValueRef result;
    if (is_float(L->type)) {
        // for floats, compare with 0.0 and return true if > 0.0
        result = LLVMBuildFCmp(e->builder, LLVMRealOLE, L->value,
                               LLVMConstReal(L->type, 0.0), "float-not");
    } else if (is_unsigned(L->type)) {
        // for unsigned integers, compare with 0
        result = LLVMBuildICmp(e->builder, LLVMIntULE, L->value,
                               LLVMConstInt(L->type, 0, 0), "unsigned-not");
    } else {
        // for signed integers, compare with 0
        result = LLVMBuildICmp(e->builder, LLVMIntSLE, L->value,
                               LLVMConstInt(L->type, 0, 0), "signed-not");
    }
    return value(edef("bool"), result);
}

node ether_bitwise_not(ether e, node L) {
    return LLVMBuildNot(e->builder, L->value, "bitwise-not");
}

node ether_is(ether e, node L,  node R) {
    type t0 = L->type;
    type t1 = R->type;
    assert(LLVMGetTypeKind(LLVMTypeOf(L))  == LLVMFunctionTypeKind &&
           LLVMGetTypeKind(LLVMTypeOf(R)) == LLVMFunctionTypeKind, 
           "is operator expects function type or initializer");
    bool      equals = t0 == t1;
    LLVMValueRef yes = LLVMConstInt(LLVMInt1Type(), 1, 0);
    LLVMValueRef no  = LLVMConstInt(LLVMInt1Type(), 0, 0);
    return value(edef("bool"), equals ? yes : no);
}

node ether_inherits(ether e, node L,  node R) {
    type t0 = L->type;
    type t1 = R->type;
    assert(LLVMGetTypeKind(LLVMTypeOf(L)) == LLVMFunctionTypeKind &&
           LLVMGetTypeKind(LLVMTypeOf(R)) == LLVMFunctionTypeKind, 
           "is operator expects function type or initializer");
    bool      equals = t0 == t1;
    LLVMValueRef yes = LLVMConstInt(LLVMInt1Type(), 1, 0);
    LLVMValueRef no  = LLVMConstInt(LLVMInt1Type(), 0, 0);
    type cur = t0;
    while (cur) {
        if (cur == t1)
            return yes;
        cur = cur->origin;
    }
    return no;
}

node ether_eq(ether e, node L, node R) {
    type t0 = L->type;
    type t1 = R->type;
    verify (t0 == t1, "types must be same at primitive operation level");
    bool i0 = t0->mdl >= model_bool && t0->mdl <= model_i64;
    bool f0 = t0->mdl >= model_f32  && t0->mdl <= model_f64;
    if (i0 || !f0)
        return LLVMBuildICmp(e->builder, LLVMIntEQ,   L->value, R->value, "eq-i");
    return     LLVMBuildFCmp(e->builder, LLVMRealOEQ, L->value, R->value, "eq-f");
}

node ether_not_eq(ether e, node L, node R) {
    type t0 = L->type;
    type t1 = R->type;
    verify (t0 == t1, "types must be same at primitive operation level");
    bool i0 = t0->mdl >= model_bool && t0->mdl <= model_i64;
    bool f0 = t0->mdl >= model_f32  && t0->mdl <= model_f64;
    if (i0 || !f0)
        return LLVMBuildICmp(e->builder, LLVMIntNE,   L->value, R->value, "not-eq-i");
    return     LLVMBuildFCmp(e->builder, LLVMRealONE, L->value, R->value, "not-eq-f");
}

node ether_freturn(ether e, object o) {
    function fn = e->current_fn;
    /// fn->rtype->ref is the LLVMTypeRef for this function
    /// if 'operand' doesnt equal teh same type, lets convert it
    node conv = ether_convert(e, operand(e, o), fn->rtype);
    return value(fn->rtype, LLVMBuildRet(e->builder, conv->value));
}

node ether_fcall(ether e, type fdef, node target, array args) {
    int n_args = len(args);
    LLVMValueRef* arg_values = calloc((target != null) + n_args, sizeof(LLVMValueRef));
    //verify (LLVMTypeOf(fdef->function->value) == fdef->ref, "integrity check failure");
    LLVMTypeRef  F = fdef->ref;
    map     f_args = fdef->function->args;
    LLVMValueRef V = fdef->function->value; // todo: args in ether should be a map.  that way we can do a bit more

    int index = 0;
    if (target)
        arg_values[index++] = target->value;
    each (args, object, value) {
        member    f_arg = fdef->function->args->elements[index];
        AType     vtype = isa(value);
        LLVMValueRef vr = arg_values[index++] = ether_convert(e, operand(e, value), f_arg->type)->value;
        print("vr = %p", vr);
        index++;
    }
    LLVMValueRef R = LLVMBuildCall2(e->builder, F, V, arg_values, index, "call");
    free(arg_values);
    return value(fdef->function->type, R);
}

node ether_literal(ether e, object n) {
    AType ntype = isa(n);
    if (ntype == typeid(bool)) return LLVMConstInt(LLVMInt1Type(), *(bool*)n, 0);
    if (ntype == typeid(i8))  return LLVMConstInt( LLVMInt8Type(),  *( i8*)n, 0);
    if (ntype == typeid(i16)) return LLVMConstInt(LLVMInt16Type(),  *(i16*)n, 0);
    if (ntype == typeid(i32)) return LLVMConstInt(LLVMInt32Type(),  *(i32*)n, 0);
    if (ntype == typeid(i64)) return LLVMConstInt(LLVMInt64Type(),  *(i64*)n, 0);
    if (ntype == typeid(u8))  return LLVMConstInt( LLVMInt8Type(),  *( u8*)n, 0);
    if (ntype == typeid(u16)) return LLVMConstInt(LLVMInt16Type(),  *(u16*)n, 0);
    if (ntype == typeid(u32)) return LLVMConstInt(LLVMInt32Type(),  *(u32*)n, 0);
    if (ntype == typeid(u64)) return LLVMConstInt(LLVMInt64Type(),  *(u64*)n, 0);
    if (ntype == typeid(f32)) return LLVMConstInt(LLVMFloatType(),  *(f32*)n, 0);
    if (ntype == typeid(f64)) return LLVMConstInt(LLVMDoubleType(), *(f64*)n, 0);
    if (ntype == typeid(string)) return LLVMBuildGlobalStringPtr(e->builder, ((string)n)->chars, "str");
    fault ("literal not handled: %s", ntype->name);
}

node ether_op(ether e, OPType optype, string N, object L, object R) {
    node   LV  = operand(e, L);
    node   RV  = operand(e, R);
    //string N   = estr(OPType, optype);

    /// check if N is a method on L
    if (N && isa(L) == typeid(node) && is_class(((node)L)->type)) {
        node Ln = L;
        type Lt = get(Ln->type->members, N);
        if  (Lt && Lt->mdl == model_function && len(Lt->function->args) == 1) {
            /// convert argument and call method
            type  arg_expects = Lt->function->args->elements[0];
            node  conv = ether_convert(e, Ln, arg_expects);
            array args = array_of(null, conv, null);
            return ecall(fcall, Lt, L, args);
        }
    }

    type rtype = determine_rtype(e, optype, LV->type, RV->type);
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
        type,       rtype,
        value,      RES);
}

node ether_add(ether e, object L, object R) { return ether_op(e, OPType__add, str("add"), L, R); }
node ether_sub(ether e, object L, object R) { return ether_op(e, OPType__sub, str("sub"), L, R); }
node ether_mul(ether e, object L, object R) { return ether_op(e, OPType__mul, str("mul"), L, R); }
node ether_div(ether e, object L, object R) { return ether_op(e, OPType__div, str("div"), L, R); }

/// implement or import with this
type ether_function(
        ether e,           cstr name, type target,
        type  return_type, array args, bool va_args, subprocedure builder)
{
    LLVMTypeRef      rtype     = return_type->ref;
    int              n_args    = len(args);
    LLVMTypeRef*     arg_types = calloc((target != null) + n_args, sizeof(LLVMTypeRef));
    int              index     = 0;

    if (target)
        arg_types[index++] = LLVMPointerType(target->ref, 0);

    print("function %s", name);
    each(args, member, arg) {
        arg_types[index++] = arg->type->ref;
        print("arg type [%i] = %s", index - 1,
            LLVMPrintTypeToString(arg->type->ref));
    }

    string       fname    = str(name);
    LLVMTypeRef  fn_type  = LLVMFunctionType(rtype, arg_types, index, va_args);
    LLVMValueRef fn_value = LLVMAddFunction(e->module, fname->chars, fn_type);

    type   fdef  = new(type,
        name,     fname,  ref,    fn_type,    mod, e,
        function, null,   mdl,    model_function);

    function fn  = new(function,
        name,     fname,    target, target, mod, e,     args, args,
        type,     fdef,     rtype,  return_type,
        builder,  builder,  value,  fn_value);
    fdef->function = fn;

    set(e->defs, fname, fdef);
    free(arg_types);

    LLVMSetLinkage(fdef->function->value,
        builder ? LLVMInternalLinkage : LLVMExternalLinkage);

    if (builder) {
        // Create function debug info
        LLVMMetadataRef subroutine = LLVMDIBuilderCreateSubroutineType(
            e->debug,
            e->file,           // Scope (file)
            NULL,              // Parameter types (None for simplicity)
            0,                 // Number of parameters
            LLVMDIFlagZero     // Flags
        );

        fdef->function->scope = LLVMDIBuilderCreateFunction(
            e->debug,
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

void ether_builder_main(ether e, function fn, map ctx) {
    member rmem     = create_member(e, "i64", false, ".rtype");
    member template = create_member(e, "i8",  true,  "template");

    type   printf   = ecall(function,
        "printf", null,  rmem->type, map_of("template", template, null), true, null);
    array  args     = array_of(null, str("something"), null);
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
                context ctx = push(e);
                ctx->rtype = fn->rtype;

                /// we may start building now, that includes this debug information for the function args
                int index = 0;
                each(fn->args, member, arg_mem) { // index == 0 at start
                    verify(fn->scope, "fn scope not set");

                    unsigned arg_count = LLVMCountParams(fn->value);
                    verify(index < arg_count, "Argument index out of bounds");

                    LLVMMetadataRef m = LLVMDIBuilderCreateParameterVariable(
                        e->debug, fn->scope, arg_mem->name->chars, len(arg_mem->name),
                        index + 1, e->file, arg_mem->name->line, arg_mem->type->debug, 1, LLVMDIFlagZero);
                    LLVMValueRef arg_value = LLVMGetParam(fn->value, index);
                    //LLVMValueRef arg_alloc = LLVMBuildAlloca(e->builder, arg_mem->type->type, "arg_alloca");

                    LLVMMetadataRef expr = LLVMDIBuilderCreateExpression(e->debug, NULL, 0);
                    print("debug %s", LLVMPrintValueToString(arg_value));
                    LLVMDIBuilderInsertDeclareAtEnd(
                        e->debug, arg_value, m, expr,
                        LLVMDIBuilderCreateDebugLocation(e->module_ctx, arg_mem->type->line, 0, fn->scope, NULL),
                        LLVMGetInsertBlock(e->builder));
                    index++;
                }

                invoke(fn->builder, f);
                e->current_fn = null;
                pop(e);
            }
        }
    }
}

context ether_top(ether e) {
    return e->top;
}

void context_init(context ctx) {
    ctx->members = new(map, hsize, 32);
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

void token_init(token a) {
    cstr prev = a->chars;
    sz length = a->len ? a->len : strlen(prev);
    a->chars  = (cstr)calloc(length + 1, 1);
    a->len    = length;
    memcpy(a->chars, prev, length);

    if (a->chars[0] == '\"' || a->chars[0] == '\'') {
        a->literal = new(string, chars, &a->chars[1], ref_length, length - 2);
    } else
        a->literal = read_numeric(a);
}

void main() {
    A_start();
    print("lets emit the llvm here, and abstract A-type for the basic declaration set");
    /// model data from 'member' was merged with 'def' to form a 'type'.  its better this way
    /// although complexity may arise with types, most of which we should not handle until we need to do so
    path    src   = new(path,  chars, "WGPU.si");
    ether   e     = new(ether, lang, str("silver"), source, src, name, str("module"));
    
    /*
    member  argc  = create_member(e, "i32",    0, "argc");
    member  argv  = create_member(e, "symbol", 1, "argv");
    member  ret   = create_member(e, "i32",    0, ".return");
    map     args  = array_of(null, argc, argv, null);

    /// create function named main
    type fdef = ecall(
        function, "main", no_target, ret->type, args, false,
        subproc(e, &ether_builder_main, null));
    
    ecall(build);
    ecall(write);
    */
}


define_enum      (field)

// anything with a f_* is member field data
define_enum      (f_interface)
define_primitive (f_static, numeric, A_TRAIT_INTEGRAL)
define_class     (f_model)
define_primitive (f_const,  numeric, A_TRAIT_INTEGRAL)
define_primitive (f_ref,    numeric, A_TRAIT_INTEGRAL)
define_class     (f_origin)
define_class     (f_function)
define_class     (f_record)
define_mod       (f_struct, f_record)
define_mod       (f_class,  f_record)
define_primitive (f_inlay,  numeric, A_TRAIT_INTEGRAL)
define_alias     (f_shape,  array)
define_class     (f_wrap)
define_class     (f_var)


define_class(token)
define_class(context)
define_class(ether)
define_class(node)


define_mod(op,       node)
define_mod(type,     node)
define_mod(member,   node)

define_primitive(LLVMValueRef, raw, 0)