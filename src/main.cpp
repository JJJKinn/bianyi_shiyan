#include "parser/SyntaxTree.hpp"
#include "ir/irbuilder.hpp"
#include "ir/ir_printer.hpp"
#include "loongarch/program_builder.hpp"
#include <fstream>
#include <stdlib.h>
ast::SyntaxTree syntax_tree;
int main(){
    ast::parse_file(std::cin);
    std::shared_ptr<ir::IrBuilder> irbuilder = std::make_shared<ir::IrBuilder>();
    syntax_tree.accept(*irbuilder);

    //下面是后端的部分
    std::shared_ptr<LoongArch::ProgramBuilder> progbuilder= std::make_shared<LoongArch::ProgramBuilder>();
    irbuilder->compunit->accept(*progbuilder);
    auto prog = progbuilder->prog;

    prog->get_asm(std::cout);
}