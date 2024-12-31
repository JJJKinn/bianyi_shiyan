#include "ir/irbuilder.hpp"

void ir::IrBuilder::visit(ast::compunit_syntax &node)
{
    /*
        init global variable
    */

    this->compunit = std::make_shared<ir::ir_module>();
    /*
        register lib functions
    */

    /*
        visit children
    */
    for(auto & i : node.global_defs)
        i->accept(*this);
}

void ir::IrBuilder::visit(ast::func_def_syntax &node){
    auto rettype = node.rettype;
    string name = node.name;
    
    this->cur_block = nullptr;
    this->cur_func = nullptr;
    this->cur_func_name = "";
    this->found_main = false;
    this->return_bb = nullptr;
    this->return_value.clear();
    /*
        first we should register this function in symbol table
    */
    cur_func = compunit->new_func(name);
    this->functions.push_func(name,cur_func);
    /*
        next we should deal with entry module
        in this module, we should insert instructions which is responsible for args.  
    */
    cur_func->entry = cur_func->new_block();
    cur_block = cur_func->entry;
    if(name == "main"){
        this->found_main = true;
    }
    return_bb = cur_func->new_block();
    /*
        deal with block
    */
    node.body->accept(*this);
    /*
        deal with ret
    */
    switch (rettype)
    {
    case vartype::VOID:
        {
            cur_block->push_back(std::make_shared<ir::jump>(return_bb));
            auto ret_value = std::make_shared<ir::ir_constant>(0);
            return_bb->push_back(std::make_shared<ir::ret>(ret_value,false));
            //false express non return
        }
        break;
    default:
        {
            auto ret_val = std::make_shared<ir::ir_constant>(0);
            return_value.emplace_back(ret_val,cur_block);
            cur_block->push_back(std::make_shared<ir::jump>(return_bb));
            /*
                set a default value to last block
            */
            /*
                add a phi inst
            */
            auto ret_dst = cur_func->new_reg(vartype::INT);
            auto phi_inst = std::make_shared<ir::phi>(ret_dst);
            phi_inst->uses = return_value;
            return_bb->push_back(phi_inst);
            return_bb->push_back(std::make_shared<ir::ret>(ret_dst,true));
        }
        break;
    }
}

void ir::IrBuilder::visit(ast::rel_cond_syntax &node)
{
    // complete
    node.lhs->accept(*this);
    auto exp1 = pass_value;
    node.rhs->accept(*this);
    auto exp2 = pass_value;
    auto dst = cur_func->new_reg(vartype::INT);
    cur_block->push_back(std::make_shared<ir::cmp_ins>(dst, exp1, exp2, node.op));
    pass_value = dst;
}

void ir::IrBuilder::visit(ast::logic_cond_syntax &node)
{
    std::cout << "@12" << std::endl;
    // complete 1
    // node.lhs->accept(*this);
    // auto exp1 = pass_value;
    // node.rhs->accept(*this);
    // auto exp2 = pass_value;
    // auto dst = cur_func->new_reg(vartype::INT);
    // cur_block->push_back(std::make_shared<ir::logic_ins>(dst,exp1,exp2,node.op));
    // this->pass_value=dst;
}

void ir::IrBuilder::visit(ast::binop_expr_syntax &node)
{
    /*
        the output of binary expression is a value, not a condition
    */
    node.lhs->accept(*this);
    auto exp1=pass_value;
    node.rhs->accept(*this);
    auto exp2=pass_value;
    auto dst = cur_func->new_reg(vartype::INT);
    cur_block->push_back(std::make_shared<ir::binary_op_ins>(dst,exp1,exp2,node.op));
    this->pass_value=dst;
}

void ir::IrBuilder::visit(ast::unaryop_expr_syntax &node)
{
    // complete
    node.rhs->accept(*this);
    auto exp = pass_value;
    auto dst = cur_func->new_reg(vartype::INT);
    cur_block->push_back(std::make_shared<ir::unary_op_ins>(dst, exp, node.op));
    pass_value = dst;
}

void ir::IrBuilder::visit(ast::lval_syntax &node)
{
    // complete
    auto obj = this->scope.find_var(node.name);
    auto addr = obj->addr;
    auto dst = cur_func->new_reg(node.restype);
    cur_block->push_back(std::make_shared<ir::load>(dst, addr));
    pass_value = dst;
}

void ir::IrBuilder::visit(ast::literal_syntax &node)
{
    auto constant = std::make_shared<ir::ir_constant>(node.intConst);
    pass_value = constant;
}

void ir::IrBuilder::visit(ast::var_def_stmt_syntax &node)
{
    // complete 3
    auto obj = cur_func->new_obj(node.name);
    cur_block->push_back(std::make_shared<ir::alloc>(obj));
    this->scope.push_var(node.name, obj);
}

void ir::IrBuilder::visit(ast::assign_stmt_syntax &node)
{
    // complete 4
    auto obj = this->scope.find_var(node.target->name);
    auto addr = obj->addr;
    node.value->accept(*this);
    auto value = pass_value;
    cur_block->push_back(std::make_shared<ir::store>(addr, value));
}

void ir::IrBuilder::visit(ast::block_syntax &node)
{
    //由于我们的函数没有参数，所以，直接让block来处理scope的事情
    this->scope.enter();
    for(auto i :node.body)
    {
        i->accept(*this);
    }
    this->scope.exit();
}

void ir::IrBuilder::visit(ast::if_stmt_syntax &node)
{
    // completed
    node.pred->accept(*this);
    auto cond = pass_value;
    auto target_true = cur_func->new_block();
    auto next_block = cur_func->new_block();

    if (node.else_body != nullptr) {
        auto target_false = cur_func->new_block();
        cur_block->push_back(std::make_shared<ir::br>(cond, target_true, target_false));
        cur_block = target_false;
        node.else_body->accept(*this);
        cur_block->push_back(std::make_shared<ir::jump>(next_block));
    } else {
        cur_block->push_back(std::make_shared<ir::br>(cond, target_true, next_block));
    }

    cur_block = target_true;
    node.then_body->accept(*this);
    cur_block->push_back(std::make_shared<ir::jump>(next_block));

    cur_block = next_block;
}

void ir::IrBuilder::visit(ast::return_stmt_syntax &node)
{

    if(cur_func->rettype != vartype::VOID)//有返回值
    {
        node.exp->accept(*this);
        //放置好返回值和来源BB后跳转到return_bb
        return_value.emplace_back(pass_value,cur_block);
        cur_block->push_back(std::make_shared<ir::jump>(return_bb));
    }
    else//没有返回值
    {
        //直接跳转到return的BB
        auto jmp_inst = std::make_shared<ir::jump>(return_bb);
        cur_block->push_back(jmp_inst);
    }
    //对BB进行划分，这个BB用于防止return后面的部分（这部分永远不会被执行到）
    this->cur_block = this->cur_func->new_block();
}

void ir::IrBuilder::visit(ast::var_decl_stmt_syntax &node)
{
    for(auto i :node.var_def_list)
    {
        i->accept(*this);
    }
}
