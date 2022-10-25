Currently, my code does not support cast expressions.
When I would test them with the parser (e.g. (long) 5),
it would not provide correct parsing results, and would discard 
the 5. Because of this, and the fact that no tests seem to test this,
I have saved its implementation for later

Further, my code does not override the visit_conditional_expression
or visit_postfix_expression methods. I could not find what code input 
would cause the parser to output nodes with these tokens, and all binary 
expressions (including conditional expressions) are handled in my 
visit_binary_expression function. I am not sure which postfix expressions 
this subset of C is supposed to support.

Additionally, I do not override the visit_function_parameter function.
When dealing with function definitions or declarations, I call a helper function 
process_function_parameters that basically processes all parameters in the list,
causing no need for visit_function_parameter to ever be called. 

Further, my code does not deal with storage types yet. I could not find 
anywhere to annotate a type with a storage type. 

My code does annotate and add new nodes to represent implicit conversions.
It even does so for function call parameters.

My code does have Valgrind possibly lost and still reachable blocks.
I think these are more warning conditions as I deal with smart pointers for the 
most part and make sure to delete SymbolTable pointers. Yet, I could not 
find a way to make Valgrind note this.