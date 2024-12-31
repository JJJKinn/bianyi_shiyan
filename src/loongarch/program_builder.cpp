#include "program_builder.hpp"

void LoongArch::ProgramBuilder::visit(ir::ir_reg &node) {
    pass_reg = cur_mapping->transfer_reg(node);
}

void LoongArch::ProgramBuilder::visit(ir::ir_constant &node) {
    auto value = std::get<int>(node.init_val.value());
    auto reg = cur_mapping->new_reg();
    cur_block->instructions.push_back(
        std::make_shared<LoongArch::RegImmInst>(RegImmInst::addi_w, reg, Reg{zero}, value)
    );
    pass_reg = reg;
}

void LoongArch::ProgramBuilder::visit(ir::ir_basicblock &node) 
{
    for(auto & i : node.instructions)
        i->accept(*this);
}

void LoongArch::ProgramBuilder::visit(ir::ir_module &node) { 

    this->prog = std::make_shared<LoongArch::Program>();
    this->cur_mapping = std::make_shared<IrMapping>();

    //可以调用寄存器分配函数进行寄存器分配
    // node.reg_allocate();

    for(auto & [name,func] : node.usrfuncs){
        this->func_name = name;
        prog->functions.emplace_back(std::make_shared<LoongArch::Function>(name));
        func->accept(*this);
    }
    //后面可以用来处理全局变量，不过这里没有
}

void LoongArch::ProgramBuilder::visit(ir::ir_userfunc &node) {
    
    this->cur_func = prog->functions.back();
    
    this->cur_func->stack_size = 16; //默认为16字节，分别存储$ra和父函数的fp值

    for(auto [ir_reg,backend_reg] : node.regAllocateOut)
    {
        this->cur_mapping->reg_mapping[ir_reg->id] = Reg{backend_reg};
    }
    
    //处理内存变量

    //build a entry
    cur_func->entry = std::make_shared<LoongArch::Block>(".entry_" + func_name);
    cur_func->blocks.push_back(cur_func->entry);
    prog->block_n++;
    
    //构造函数的进入部分
    this->cur_func->entry->instructions.push_back(std::make_shared<LoongArch::RegImmInst>(RegImmInst::addi_d,Reg{sp},Reg{sp},-cur_func->stack_size));  //sp:栈顶指针
    this->cur_func->entry->instructions.push_back(std::make_shared<LoongArch::st>(Reg{ra},Reg{sp},cur_func->stack_size-8,st::st_d));//保存ra//返回地址
    this->cur_func->entry->instructions.push_back(std::make_shared<LoongArch::RegImmInst>(RegImmInst::addi_d,Reg{fp},Reg{sp},cur_func->stack_size)); //确定

    
    for(auto & block : node.bbs){
        auto cur_block_name = ".L" + std::to_string(prog->block_n);
        auto backend_block = std::make_shared<LoongArch::Block>(cur_block_name);
        //把entry的终点设定成L0
        if(cur_block_name == ".L1"){
            this->cur_func->entry->instructions.push_back(std::make_shared<LoongArch::Jump>(backend_block.get()));       
        }
        prog->block_n++;
        //确定映射关系
        this->cur_mapping->blockmapping[block] = backend_block;
        this->cur_mapping->rev_blockmapping[backend_block] = block;

        cur_func->blocks.push_back(backend_block);
    }

    //在遍历block的过程中，可能会牵扯到下一个block
    for(int i = 0; i < cur_func->blocks.size(); ++i){
        if(cur_func->blocks[i] != cur_func->entry){
            this->cur_block = cur_func->blocks[i];
            if(i < cur_func->blocks.size() - 1) this->next_block = cur_func->blocks[i+1];
            else this->next_block = nullptr;
            this->cur_mapping->rev_blockmapping[cur_func->blocks[i]]->accept(*this);
        }
    }

    //消解phi指令
    struct PendingMove {
        std::shared_ptr<LoongArch::Block> block;
        LoongArch::Reg to, from;
    };

    std::vector<PendingMove> Pending_moves;
    for(auto &bb : node.bbs){
        for(auto &inst : bb->instructions){
            if(auto *cur = dynamic_cast<ir::phi*>(inst.get())){
                for(auto &prev : cur->uses){
                    auto b = cur_mapping->blockmapping[prev.second];
                    std::shared_ptr<ir::ir_reg> use_reg = std::dynamic_pointer_cast<ir::ir_reg>(prev.first);
                    if(use_reg) {
                        Reg temp = cur_mapping->transfer_reg(*use_reg.get());
                        Reg mid = cur_mapping->new_reg();
                        b->insert_before_jump(
                            std::make_shared<RegImmInst>(RegImmInst::addi_w,mid,temp,0)
                        );
                        Pending_moves.push_back({b,this->cur_mapping->transfer_reg(*cur->dst.get()),mid});
                    }else{
                        std::shared_ptr<ir::ir_constant> use_constant = std::dynamic_pointer_cast<ir::ir_constant>(prev.first);
                        //直接把那个立即数放到相应的phi的目的寄存器里面就行了，在uses block的的jump的前一句
                        //这里直接使用LoongArch的加载立即数指令
                        auto value = use_constant->init_val.value();
                        auto mid = cur_mapping->new_reg();
                        if(std::holds_alternative<int>(value)){
                            int value_num = std::get<int>(value);
                            b->insert_before_jump(
                                std::make_shared<LoongArch::LoadImm>(mid,value_num)
                            );
                        }
                        Pending_moves.push_back({b,this->cur_mapping->transfer_reg(*cur->dst.get()),mid});
                    }

                }
            }
        }
    }
    for(auto &i : Pending_moves){
        i.block->insert_before_jump(std::make_shared<RegImmInst>(RegImmInst::addi_w,i.to,i.from,0)); //插入一条move指令
        cur_func->regn = cur_mapping->regn;
    }
}

void LoongArch::ProgramBuilder::visit(ir::store &node) {
    node.value->accept(*this);
    auto value = pass_reg; 
    cur_block->instructions.push_back(
        std::make_shared<LoongArch::RegImmInst>(RegImmInst::addi_w, Reg{t0}, value, 0)
    );
    auto addr = std::dynamic_pointer_cast<ir::ir_reg>(node.addr);
    auto obj = cur_mapping->addrMemObj[addr];
    auto offset = cur_mapping->objoffset_mapping[obj];
    cur_block->instructions.push_back(
        std::make_shared<LoongArch::st>(Reg{t0}, Reg{fp}, offset, st::st_w)
    );
}

void LoongArch::ProgramBuilder::visit(ir::jump &node) {
    auto block = this->cur_mapping->blockmapping[node.target];
    cur_block->instructions.push_back(
        std::make_shared<LoongArch::Jump>(block.get())
    );
}

void LoongArch::ProgramBuilder::visit(ir::br &node) {
    node.cond->accept(*this);
    auto cond = pass_reg;
    auto block_true = this->cur_mapping->blockmapping[node.target_true];
    auto block_false = this->cur_mapping->blockmapping[node.target_false];
    cur_block->instructions.push_back(
        std::make_shared<LoongArch::JumpB>(block_true.get(), cond, Reg{zero})
    );
    cur_block->instructions.push_back(
        std::make_shared<LoongArch::Jump>(block_false.get())
    );
}

void LoongArch::ProgramBuilder::visit(ir::ret &node) {
    auto ret_reg = std::dynamic_pointer_cast<ir::ir_reg>(node.value);
    auto backend_reg = cur_mapping->transfer_reg(*ret_reg.get());
    cur_block->instructions.push_back(
        std::make_shared<LoongArch::RegRegInst>(RegRegInst::orw,Reg{4},backend_reg,Reg{0})
    );
    cur_block->instructions.push_back(
        std::make_shared<LoongArch::ld>(Reg{22},Reg{3},this->cur_func->stack_size - 8,ld::ld_d)
    );
    cur_block->instructions.push_back(
        std::make_shared<LoongArch::RegImmInst>(RegImmInst::addi_d,Reg{sp},Reg{sp},cur_func->stack_size)
    );
    cur_block->instructions.push_back(std::make_shared<LoongArch::jr>(true));
}

void LoongArch::ProgramBuilder::visit(ir::load &node) {
    auto addr = std::dynamic_pointer_cast<ir::ir_reg>(node.addr);
    auto dst_reg = cur_mapping->transfer_reg(*node.dst.get());
    int offset = cur_mapping->objoffset_mapping[cur_mapping->addrMemObj[addr]];
    cur_block->instructions.push_back(std::make_shared<LoongArch::ld>(dst_reg, Reg{fp}, offset, ld::ld_w));
}

void LoongArch::ProgramBuilder::visit(ir::alloc &node) {
    auto obj = node.var;
    auto ir_reg = obj->get_addr();
    cur_mapping->addrMemObj[ir_reg] = obj;
    cur_mapping->revAddMemObj[obj] = ir_reg;
    cur_mapping->objoffset_mapping[obj] = cur_func->cur_pos;
    cur_func->cur_pos -= 4;
}

void LoongArch::ProgramBuilder::visit(ir::phi &node) {
    node.dst->accept(*this);
    auto dst = pass_reg;
    for (auto p : node.uses) {
        p.first->accept(*this);
        auto value = pass_reg;
        auto b = cur_mapping->blockmapping[p.second];
        b->insert_before_jump(std::make_shared<LoongArch::RegImmInst>(RegImmInst::addi_w, dst, value, 0));
    }
}

void LoongArch::ProgramBuilder::visit(ir::unary_op_ins &node) {
    node.dst->accept(*this);
    auto dst = pass_reg;
    node.src->accept(*this);
    auto src = pass_reg;
    if (node.op == unaryop::plus) {
        cur_block->instructions.push_back(
            std::make_shared<LoongArch::RegRegInst>(RegRegInst::add_w, dst, src, Reg{zero})
        );
    } else {
        cur_block->instructions.push_back(
            std::make_shared<LoongArch::RegRegInst>(RegRegInst::sub_w, dst, Reg{zero}, src)
        );
    }
}

void LoongArch::ProgramBuilder::visit(ir::binary_op_ins &node) {
    node.dst->accept(*this);
    auto dst = pass_reg;
    node.src1->accept(*this);
    auto src1 = pass_reg;
    node.src2->accept(*this);
    auto src2 = pass_reg;
    if (node.op == binop::plus) {
        cur_block->instructions.push_back(
            std::make_shared<LoongArch::RegRegInst>(RegRegInst::add_w, dst, src1, src2)
        );
    } else if (node.op == binop::minus) {
        cur_block->instructions.push_back(
            std::make_shared<LoongArch::RegRegInst>(RegRegInst::sub_w, dst, src1, src2)
        );
    } else if (node.op == binop::multiply) {
        cur_block->instructions.push_back(
            std::make_shared<LoongArch::RegRegInst>(RegRegInst::mul_w, dst, src1, src2)
        );
    } else if (node.op == binop::divide) {
        cur_block->instructions.push_back(
            std::make_shared<LoongArch::RegRegInst>(RegRegInst::div_w, dst, src1, src2)
        );
    }
    pass_reg = dst;
}

void LoongArch::ProgramBuilder::visit(ir::cmp_ins &node) {
    node.dst->accept(*this);
    auto dst = pass_reg;
    node.src1->accept(*this);
    auto src1 = pass_reg;
    node.src2->accept(*this);
    auto src2 = pass_reg;
    if (node.op == relop::greater) {
        cur_block->instructions.push_back(
            std::make_shared<LoongArch::RegRegInst>(RegRegInst::slt, dst, src1, src2)
        );
    } else if (node.op == relop::equal) {
        cur_block->instructions.push_back(
            std::make_shared<LoongArch::RegRegInst>(RegRegInst::sub_w, dst, src1, src2)
        );
    }
    pass_reg = dst;
}

void LoongArch::ProgramBuilder::visit(ir::logic_ins &node) {
}
