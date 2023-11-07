add_executable (equiv-check Equiv.cpp)
target_link_libraries (equiv-check ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB} ${ARMADILLO_LIBRARIES})
install(TARGETS equiv-check RUNTIME DESTINATION bin)
