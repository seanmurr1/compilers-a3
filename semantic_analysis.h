#ifndef SEMANTIC_ANALYSIS_H
#define SEMANTIC_ANALYSIS_H

#include <cstdint>
#include <memory>
#include <utility>
#include "type.h"
#include "symtab.h"
#include "ast_visitor.h"

class SemanticAnalysis : public ASTVisitor {
private:
  SymbolTable *m_global_symtab, *m_cur_symtab;

public:
  SemanticAnalysis();
  virtual ~SemanticAnalysis();

  virtual void visit_struct_type(Node *n);
  virtual void visit_union_type(Node *n);
  virtual void visit_variable_declaration(Node *n);
  virtual void visit_basic_type(Node *n);
  virtual void visit_function_definition(Node *n);
  virtual void visit_function_declaration(Node *n);
  virtual void visit_function_parameter(Node *n);
  virtual void visit_statement_list(Node *n);
  virtual void visit_struct_type_definition(Node *n);
  virtual void visit_binary_expression(Node *n);
  virtual void visit_unary_expression(Node *n);
  virtual void visit_postfix_expression(Node *n);
  virtual void visit_conditional_expression(Node *n);
  virtual void visit_cast_expression(Node *n);
  virtual void visit_function_call_expression(Node *n);
  virtual void visit_field_ref_expression(Node *n);
  virtual void visit_indirect_field_ref_expression(Node *n);
  virtual void visit_array_element_ref_expression(Node *n);
  virtual void visit_variable_ref(Node *n);
  virtual void visit_literal_value(Node *n);

private:
  // TODO: add helper functions
  std::pair<std::string &, std::shared_ptr<Type> &> process_declarator(Node *declarator, const std::shared_ptr<Type> &base_type);

  void enter_scope();
  void leave_scope();

  Node *promote_to_int(Node *n);
  Node *implicit_conversion(Node *n, const std::shared_ptr<Type> *type);
};

#endif // SEMANTIC_ANALYSIS_H
