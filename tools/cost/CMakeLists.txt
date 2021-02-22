add_executable (cost CostComputer.cpp)
target_link_libraries (cost ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
llvm_config (cost bitwriter)
install(TARGETS cost RUNTIME DESTINATION bin)
