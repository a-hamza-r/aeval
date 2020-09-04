add_executable (rel Rel.cpp)
target_link_libraries (rel ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
llvm_config (rel bitwriter)
install(TARGETS rel RUNTIME DESTINATION bin)
