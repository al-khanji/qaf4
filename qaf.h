#ifndef QAF_QAF_H
#define QAF_QAF_H

#include <stdint.h>
#include <string>
#include <initializer_list>

namespace qaf {

typedef uintptr_t pointer;

void *alloc(size_t size);

std::string external_representation(pointer obj);
std::istream & read_token(std::istream &input, pointer &var);

bool is_null(pointer obj);
pointer mk_null();

bool is_pair(pointer obj);
pointer cons(pointer a, pointer b);
pointer car(pointer obj);
pointer cdr(pointer obj);

bool is_list(pointer obj);
pointer mk_list(std::initializer_list<pointer> elems);
pointer list_reversed(pointer list);

bool is_tagged_list(pointer tag, pointer obj);

bool is_symbol(pointer obj);
pointer string_to_symbol(const std::string &name);
std::string symbol_to_string(pointer obj);

bool is_bool(pointer obj);
bool is_false(pointer obj);
pointer mk_bool(bool b);

bool is_string(pointer obj);
pointer mk_string(std::string s);
std::string get_string(pointer obj);

bool is_environment(pointer obj);
pointer mk_environment(pointer outer = mk_null());
pointer environment_outer(pointer env);
pointer environment_find(pointer env, pointer sym);
pointer environment_get(pointer env, pointer sym);
pointer environment_set(pointer env, pointer sym, pointer value);
pointer environment_define(pointer env, pointer sym, pointer value);

bool is_procedure(pointer obj);
pointer mk_procedure(pointer env, pointer parameters, pointer body);
pointer eval(pointer exp, pointer env);
pointer apply(pointer procedure, pointer arguments);

inline pointer   caar(pointer obj) { return car(  car(obj)); }
inline pointer   cadr(pointer obj) { return car(  cdr(obj)); }
inline pointer   cdar(pointer obj) { return cdr(  car(obj)); }
inline pointer   cddr(pointer obj) { return cdr(  cdr(obj)); }
inline pointer  caaar(pointer obj) { return car( caar(obj)); }
inline pointer  caadr(pointer obj) { return car( cadr(obj)); }
inline pointer  cadar(pointer obj) { return car( cdar(obj)); }
inline pointer  caddr(pointer obj) { return car( cddr(obj)); }
inline pointer  cdaar(pointer obj) { return cdr( caar(obj)); }
inline pointer  cdadr(pointer obj) { return cdr( cadr(obj)); }
inline pointer  cddar(pointer obj) { return cdr( cdar(obj)); }
inline pointer  cdddr(pointer obj) { return cdr( cddr(obj)); }
inline pointer caaaar(pointer obj) { return car(caaar(obj)); }
inline pointer caaadr(pointer obj) { return car(caadr(obj)); }
inline pointer caadar(pointer obj) { return car(cadar(obj)); }
inline pointer caaddr(pointer obj) { return car(caddr(obj)); }
inline pointer cadaar(pointer obj) { return car(cdaar(obj)); }
inline pointer cadadr(pointer obj) { return car(cdadr(obj)); }
inline pointer caddar(pointer obj) { return car(cddar(obj)); }
inline pointer cadddr(pointer obj) { return car(cdddr(obj)); }
inline pointer cdaaar(pointer obj) { return cdr(caaar(obj)); }
inline pointer cdaadr(pointer obj) { return cdr(caadr(obj)); }
inline pointer cdadar(pointer obj) { return cdr(cadar(obj)); }
inline pointer cdaddr(pointer obj) { return cdr(caddr(obj)); }
inline pointer cddaar(pointer obj) { return cdr(cdaar(obj)); }
inline pointer cddadr(pointer obj) { return cdr(cdadr(obj)); }
inline pointer cdddar(pointer obj) { return cdr(cddar(obj)); }
inline pointer cddddr(pointer obj) { return cdr(cdddr(obj)); }

} // namespace qaf

#endif // QAF_QAF_H
