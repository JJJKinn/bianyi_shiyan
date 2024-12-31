#include "register_allocator.hpp"

void LoongArch::ColoringAllocator::SimplifyGraph() {

}

void LoongArch::ColoringAllocator::Spill() {

}

void LoongArch::ColoringAllocator::BuildConflictGraph() {

}

std::unordered_map<std::shared_ptr<ir::ir_reg>, int> LoongArch::ColoringAllocator::getAllocate() {

}

LoongArch::ColoringAllocator::ColoringAllocator(std::shared_ptr<ir::ir_userfunc> _func) : func(_func)
{
  this->BuildConflictGraph();
}

std::unordered_map<std::shared_ptr<ir::ir_reg>,int> LoongArch::ColoringAllocator::run() {
  return this->getAllocate();
}
