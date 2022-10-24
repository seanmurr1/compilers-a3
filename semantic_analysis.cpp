#include <cassert>
#include <algorithm>
#include <utility>
#include <map>
#include <string>
#include "grammar_symbols.h"
#include "parse.tab.h"
#include "node.h"
#include "ast.h"
#include "exceptions.h"
#include "semantic_analysis.h"
#include "type.h"
#include "symtab.h"

SemanticAnalysis::SemanticAnalysis()
  : m_global_symtab(new SymbolTable(nullptr)) {
  m_cur_symtab = m_global_symtab;
}

SemanticAnalysis::~SemanticAnalysis() {
}

void SemanticAnalysis::enter_scope() {
  SymbolTable *scope = new SymbolTable(m_cur_symtab);
  m_cur_symtab = scope;
}

void SemanticAnalysis::leave_scope() {
  m_cur_symtab = m_cur_symtab->get_parent();
  assert(m_cur_symtab != nullptr);
}

Node *SemanticAnalysis::promote_to_int(Node *n) {
  assert(n->get_type()->is_integral());
  assert(n->get_type()->get_basic_type_kind() < BasicTypeKind::INT);
  std::shared_ptr<Type> type(new BasicType(BasicTypeKind::INT, n->get_type()->is_signed()));
  return implicit_conversion(n, type);
}

Node *SemanticAnalysis::implicit_conversion(Node *n, const std::shared_ptr<Type> &type) {
  std::unique_ptr<Node> conversion(new Node(AST_IMPLICIT_CONVERSION, {n}));
  conversion->set_type(type);
  return conversion.release();
}

void SemanticAnalysis::visit_struct_type(Node *n) {
  // TODO: implement



}

void SemanticAnalysis::visit_union_type(Node *n) {
  RuntimeError::raise("union types aren't supported");
}

/**
 * Recursively processes a (possibly chained) declarator for a variable declaration.
 **/
void SemanticAnalysis::process_declarator(Node *declarator, const std::shared_ptr<Type> &base_type) {
  std::shared_ptr<Type> new_base_type;
  
  int tag = declarator->get_tag();
  switch (tag) {
    case AST_ARRAY_DECLARATOR:
      {
        int length = stoi(declarator->get_kid(1)->get_str());
        new_base_type = std::shared_ptr<Type>(new ArrayType(base_type, length));
        process_declarator(declarator->get_kid(0), new_base_type);
      }
      break;
    case AST_POINTER_DECLARATOR:
      new_base_type = std::shared_ptr<Type>(new PointerType(base_type));
      process_declarator(declarator->get_kid(0), new_base_type);
      break;
    case AST_NAMED_DECLARATOR:
      {
        const std::string &var_name = declarator->get_kid(0)->get_str();
        if (m_cur_symtab->has_symbol_local(var_name)) SemanticError::raise(declarator->get_loc(), "Name already defined");
        m_cur_symtab->define(SymbolKind::VARIABLE, var_name, base_type);
      }
      break;
    default:
      SemanticError::raise(declarator->get_loc(), "Unrecognized declarator");
      break;
  }
}

void SemanticAnalysis::visit_variable_declaration(Node *n) {
  // child 0 is storage

  // Visit base type
  visit(n->get_kid(1));
  std::shared_ptr<Type> base_type = n->get_kid(1)->get_type();

  // Iterate through declarators, adding vars to symbol table
  Node *decl_list = n->get_kid(2);
  for (auto i = decl_list->cbegin(); i != decl_list->cend(); i++) {
    Node *declarator = *i;
    process_declarator(declarator, base_type);
  }
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
        if (is_const || (type_set && type == BasicTypeKind::VOID)) SemanticError::raise(n->get_loc(), "Malformed basic type");
        is_const = true;
        break;
      case TOK_VOLATILE:
        if (is_volatile || (type_set && type == BasicTypeKind::VOID)) SemanticError::raise(n->get_loc(), "Malformed basic type");
        is_volatile = true;
        break;
      case TOK_UNSIGNED:
        if (sign_set || (type_set && type == BasicTypeKind::VOID)) SemanticError::raise(n->get_loc(), "Malformed basic type");
        is_signed = false;
        sign_set = true;
        break;
      case TOK_SIGNED:
        if (sign_set || (type_set && type == BasicTypeKind::VOID)) SemanticError::raise(n->get_loc(), "Malformed basic type");
        is_signed = true;
        sign_set = true;
        break;
      case TOK_VOID:
        if (is_volatile || is_const || sign_set || type_set) SemanticError::raise(n->get_loc(), "Malformed basic type");
        type = BasicTypeKind::VOID;
        type_set = true;
        break;
      case TOK_INT:
        if (type_set && (type == BasicTypeKind::SHORT || type == BasicTypeKind::LONG)) break;
        if (type_set) SemanticError::raise(n->get_loc(), "Malformed basic type");
        type = BasicTypeKind::INT;
        type_set = true;
        break;
      case TOK_CHAR:
        if (type_set) SemanticError::raise(n->get_loc(), "Malformed basic type");
        type = BasicTypeKind::CHAR;
        type_set = true;
        break;
      case TOK_LONG: 
        if (type_set && type == BasicTypeKind::INT) {
          type = BasicTypeKind::LONG;
        } else if (type_set) {
          SemanticError::raise(n->get_loc(), "Malformed basic type");
        } else {
          type = BasicTypeKind::LONG;
          type_set = true;
        }
        break;
      case TOK_SHORT: 
        if (type_set && type == BasicTypeKind::INT) {
          type = BasicTypeKind::SHORT;
        } else if (type_set) {
          SemanticError::raise(n->get_loc(), "Malformed basic type");
        } else {
          type = BasicTypeKind::SHORT;
          type_set = true;
        }
        break;
      default:
        SemanticError::raise(n->get_loc(), "Malformed basic type");
    }
  }
  // Int is default type
  if (!type_set) type = BasicTypeKind::INT;
  // Create BasicType
  std::shared_ptr<Type> basic_type = std::shared_ptr<Type>(new BasicType(type, is_signed));
  // Create QualifiedType if necessary
  if (is_const) {
    basic_type = std::shared_ptr<Type>(new QualifiedType(basic_type, TypeQualifier::CONST));
  } else if (is_volatile) {
    basic_type = std::shared_ptr<Type>(new QualifiedType(basic_type, TypeQualifier::VOLATILE));
  }
  // Annotate node with type
  n->set_type(basic_type);
}

void SemanticAnalysis::visit_function_definition(Node *n) {
  // Visit return type
  visit(n->get_kid(0));
  // Function name
  const std::string &fn_name = n->get_kid(1)->get_str();
  // Create function type
  std::shared_ptr<Type> fn_type(new FunctionType(n->get_kid(0)->get_type()));
  // Define function
  m_cur_symtab->define(SymbolKind::FUNCTION, fn_name, fn_type);

  // Visit parameters
  //Node *param_list = n->get_kid(2);
  enter_scope();
  visit(n->get_kid(2));
  leave_scope();
  // for (auto i = param_list->cbegin(); i != param_list->cend(); i++) {
  //   Node *parameter = *i;
  //   parameter->set_type(fn_type);
  //   visit(parameter);
  // }

  // Visit function body
  visit(n->get_kid(3));
}

void SemanticAnalysis::visit_function_declaration(Node *n) {
  // TODO: implement

  // Visit return type
  visit(n->get_kid(0));
  // Function name
  const std::string &fn_name = n->get_kid(1)->get_str();
  // Create function type
  std::shared_ptr<Type> fn_type(new FunctionType(n->get_kid(0)->get_type()));
  // Define function
  m_cur_symtab->declare(SymbolKind::FUNCTION, fn_name, fn_type);
  // Visit function parameters
  enter_scope();
  visit(n->get_kid(2));
  leave_scope();
}

void SemanticAnalysis::visit_function_parameter(Node *n) {
  //std::shared_ptr<Type> fn_type = n->get_type();
  // Visit base type
  visit(n->get_kid(0));
  std::shared_ptr<Type> base_type = n->get_kid(0)->get_type();
  // Process declarators
  process_declarator(n->get_kid(1), base_type);
  //const std::string &param_name = process_declarator(n->get_kid(1), base_type);
  //base_type = m_cur_symtab->lookup_local(param_name)->get_type();
  // Annotate node
  //fn_type->add_member(Member(param_name, base_type));
}

// Enter new scope and process each child in a statement list
void SemanticAnalysis::visit_statement_list(Node *n) {
  enter_scope();
  printf("Entering scope\n");
  for (auto i = n->cbegin(); i != n->cend(); i++) {
    Node *child = *i;
    visit(child);
  }
  leave_scope();
  printf("Leaving scope\n");
}

void SemanticAnalysis::visit_struct_type_definition(Node *n) {
  // TODO: implement

  // Create and define struct type
  const std::string &struct_name = n->get_kid(0)->get_str();
  std::shared_ptr<Type> struct_type(new StructType(struct_name));
  m_cur_symtab->define(SymbolKind::TYPE, "struct " + struct_name, struct_type);


  // TODO

}

void SemanticAnalysis::visit_binary_expression(Node *n) {
  // TODO: implement

  // Leaf nodes will be var refs
  // annotate leaf with type 

  // Visit left child 
  visit(n->get_kid(1));
  // Visit right child
  visit(n->get_kid(2));

  // TODO
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

// Annotates var reference with pointer to Symbol representing symbol table entry
void SemanticAnalysis::visit_variable_ref(Node *n) {
  const std::string &var_name = n->get_kid(0)->get_str();
  Symbol *sym = m_cur_symtab->lookup_recursive(var_name);
  if (sym == nullptr) SemanticError::raise(n->get_loc(), "Undeclared variable reference");

  assert (!n->has_symbol());
  n->set_symbol(sym);
}

void SemanticAnalysis::visit_literal_value(Node *n) {
  // TODO: implement
}

// TODO: implement helper functions
