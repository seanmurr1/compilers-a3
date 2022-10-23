#include <cassert>
#include <algorithm>
#include <utility>
#include <map>
#include "grammar_symbols.h"
#include "parse.tab.h"
#include "node.h"
#include "ast.h"
#include "exceptions.h"
#include "semantic_analysis.h"
#include "type.h"

SemanticAnalysis::SemanticAnalysis()
  : m_global_symtab(new SymbolTable(nullptr)) {
  m_cur_symtab = m_global_symtab;
}

SemanticAnalysis::~SemanticAnalysis() {
}

void SemanticAnalysis::visit_struct_type(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_union_type(Node *n) {
  RuntimeError::raise("union types aren't supported");
}

void SemanticAnalysis::visit_variable_declaration(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_basic_type(Node *n) {
  bool type_set = false;
  bool is_signed = true;
  bool sign_set = false;
  bool is_const = false; 
  bool is_volatile = false;
  BasicTypeKind type;

  // Analyze basic type and type qualifer keywords
  for (auto i = n->cbegin(); i != n->cend(); i++) {
    Node *type_child = *i;
    int tag = type_child->get_tag();
    switch (tag) {
      case TOK_CONST:
        if (is_const || (type_set && type == VOID)) SemanticError::raise(n->get_loc, "Malformed basic type");
        is_const = true;
        break;
      case TOK_VOLATILE:
        if (is_volatile || (type_set && type == VOID)) SemanticError::raise(n->get_loc, "Malformed basic type");
        is_volatile = true;
        break;
      case TOK_UNSIGNED:
        if (sign_set || (type_set && type == VOID)) SemanticError::raise(n->get_loc, "Malformed basic type");
        is_signed = false;
        sign_set = true;
        break;
      case TOK_SIGNED:
        if (sign_set || (type_set && type == VOID)) SemanticError::raise(n->get_loc, "Malformed basic type");
        is_signed = true;
        sign_set = true;
        break;
      case TOK_VOID:
        if (is_volatile || is_const || sign_set || type_set) SemanticError::raise(n->get_loc, "Malformed basic type");
        type = VOID;
        type_set = true;
        break;
      case TOK_INT:
        if (type_set && (type == SHORT || type == LONG)) break;
        if (type_set) SemanticError::raise(n->get_loc, "Malformed basic type");
        type = INT;
        type_set = true;
        break;
      case TOK_CHAR:
        if (type_set) SemanticError::raise(n->get_loc, "Malformed basic type");
        type = CHAR;
        type_set = true;
        break;
      case TOK_LONG: 
        if (type_set && type == INT) {
          type = LONG;
        } else if (type_set) {
          SemanticError::raise(n->get_loc, "Malformed basic type");
        } else {
          type = LONG;
        }
        break;
      case TOK_SHORT: 
        if (type_set && type == INT) {
          type = SHORT;
        } else if (type_set) {
          SemanticError::raise(n->get_loc, "Malformed basic type");
        } else {
          type = SHORT;
        }
        break;
      default:
        SemanticError::raise(n->get_loc, "Malformed basic type");
    }
  }
  // Int is default type
  if (!type_set) type = INT;
  // Create BasicType
  std::shared_ptr<Type> basic_type = std::shared_ptr<Type>(new BasicType(type, is_signed));
  // Create QualifiedType if necessary
  if (is_const) {
    basic_type = std::shared_ptr<Type>(new QualifiedType(type, CONST));
  } else if (is_volatile) {
    basic_type = std::shared_ptr<Type>(new QualifiedType(type, VOLATILE));
  }
  // Annotate node with type
  n->set_type(basic_type);
}

void SemanticAnalysis::visit_function_definition(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_function_declaration(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_function_parameter(Node *n) {
  // TODO: solution
}

void SemanticAnalysis::visit_statement_list(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_struct_type_definition(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_binary_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_unary_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_postfix_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_conditional_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_cast_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_function_call_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_field_ref_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_indirect_field_ref_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_array_element_ref_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_variable_ref(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_literal_value(Node *n) {
  // TODO: implement
}

// TODO: implement helper functions
