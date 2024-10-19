cmake_minimum_required    (VERSION 2.8.12)
enable_language           (ASM)
project                   (ether)
set                       (is_exe FALSE)
include                   (../A/A.cmake)
target_link_libraries     (ether 
    ${L}/libA.so
    ${L}/libLLVMCore.so
    ${L}/libLLVMBitReader.so
    ${L}/libLLVMBitWriter.so
    ${L}/libLLVMIRReader.so
    ${L}/libLLVMSupport.so
    ${L}/libLLVMExecutionEngine.so
    ${L}/libLLVMTarget.so
    ${L}/libLLVMTargetParser.so
    ${L}/libLLVMTransformUtils.so
    ${L}/libLLVMAnalysis.so
    ${L}/libLLVMProfileData.so
    ${L}/libLLVMX86CodeGen.so
    ${L}/libLLVMX86AsmParser.so
    ${L}/libLLVMX86Desc.so
    ${L}/libLLVMX86Info.so
    ${L}/libclang.so.18.1.8)