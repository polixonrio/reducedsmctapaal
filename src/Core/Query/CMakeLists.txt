

add_library(Query AST.cpp SMCQuery.cpp TranslationVisitor.cpp)
add_dependencies(Query unfoldtacpn-ext)
