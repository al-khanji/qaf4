#include "qaf.h"

#include <cstddef>
#include <cstdlib>
#include <cassert>

#include <memory>
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <iostream>
#include <array>

namespace qaf {

namespace compiler {
pointer compile(pointer env, pointer params, pointer body);
pointer analyze(pointer exp);

bool is_self_evaluating(pointer exp);

bool is_variable(pointer exp);

bool is_quoted(pointer exp);
pointer text_of_quotation(pointer exp);

bool is_assignment(pointer exp);
pointer assignment_variable(pointer exp);
pointer assignment_value(pointer exp);

bool is_definition(pointer exp);
pointer definition_variable(pointer exp);
pointer definition_value(pointer exp);

bool is_lambda(pointer exp);
pointer lambda_parameters(pointer exp);
pointer lambda_body(pointer exp);

bool is_if(pointer exp);
pointer if_predicate(pointer exp);
pointer if_consequent(pointer exp);
pointer if_alternative(pointer exp);

bool is_begin(pointer exp);
pointer begin_actions(pointer exp);
bool is_last_exp(pointer seq);
pointer first_exp(pointer seq);
pointer rest_exps(pointer seq);
pointer make_begin(pointer seq);
pointer sequence_to_exp(pointer seq);

bool is_application(pointer exp);
pointer operator_(pointer exp);
pointer operands(pointer exp);
bool has_no_operands(pointer ops);
pointer first_operand(pointer ops);
pointer rest_operands(pointer ops);

bool is_cond(pointer exp);
pointer cond_clauses(pointer exp);
pointer is_cond_else_clause(pointer clause);
pointer cond_predicate(pointer clause);
pointer cond_actions(pointer clause);
pointer cond_to_if(pointer exp);
pointer expand_clauses(pointer clauses);
} // namespace compiler

typedef uint32_t instruction;
typedef uint8_t opcode;

struct list_t {
    list_t *next = this;
    list_t *prev = this;
};

void list_insert(list_t *list, list_t *elem);
void list_remove(list_t *elem);

struct alloc_header_t {
    list_t gc_object_list;
    uintptr_t gc_flags = 0;
    uintptr_t dummy;
};

static constexpr size_t ALIGNMENT = 16;
static_assert((sizeof(alloc_header_t) % ALIGNMENT) == 0, "unsupported system");

void list_insert(list_t *list, list_t *elem)
{
    elem->next = list->next;
    elem->prev = list;
    list->next = elem;
    elem->next->prev = elem;
}

void list_remove(list_t *elem)
{
    elem->next->prev = elem->prev;
    elem->prev->next = elem->next;
    elem->next = elem;
    elem->prev = elem;
}

namespace tag {
enum : pointer {
    null         = 0x0,
    pair         = 0x1,
    symbol       = 0x2,
    string       = 0x3,
    environment  = 0x4,
    procedure    = 0x5,
    continuation = 0x6,
    mask         = 0xf
};
} // namespace tag

template <class T>
static inline pointer get_tag(T ptr)
{
    return pointer(ptr) & tag::mask;
}

static inline void tag_check(pointer ptr, pointer tag)
{
    assert(get_tag(ptr) == tag);
}

template <class T>
static inline pointer tagged(T ptr, pointer tag)
{
    tag_check(get_tag(ptr), 0);
    return pointer(ptr) | tag;
}

template <class T>
static inline T untagged(pointer ptr, pointer tag)
{
    tag_check(get_tag(ptr), tag);
    return reinterpret_cast<T>(ptr & ~tag::mask);
}

template <class T, class... Args>
inline T* make(Args... args)
{
    auto obj = alloc(sizeof(T));
    return new (obj) T(std::forward<Args>(args)...);
}

struct pair_t {
    pointer car;
    pointer cdr;
};

struct symbol_t {
    std::string name;
};

struct string_t {
    std::string str;
};

struct environment_t {
    pointer outer = mk_null();
    std::unordered_map<pointer, pointer> symtab;
};

struct procedure_t {
    pointer environment = mk_null();
    std::vector<instruction> code;
    std::vector<pointer> constants;
};

struct continuation_t {
    pointer outer = mk_null();

    pointer proc = mk_null();
    instruction *pc = nullptr;

    std::array<pointer, 8> registers;
    std::vector<pointer> stack;
};

namespace global {
static list_t allocations;
static std::vector<symbol_t *> symbols;

static bool trace_opcodes = true;
static bool trace_compiler = true;

static const pointer static_null = tag::null;
static const pointer static_true = string_to_symbol("#t");
static const pointer static_false = string_to_symbol("#f");
} // namespace global

void *alloc(size_t size)
{
    auto header = static_cast<alloc_header_t *>(malloc(sizeof(alloc_header_t) + size));
    list_insert(&global::allocations, &header->gc_object_list);
    return header + 1;
}

std::string external_representation(pointer obj)
{
    if (is_null(obj))
        return "()";

    else if (is_symbol(obj))
        return symbol_to_string(obj);

    else if (is_pair(obj)) {
        std::string repr;

        while (!is_null(obj)) {
            if (is_pair(obj)) {
                repr += " " + external_representation(car(obj));
                obj = cdr(obj);
            } else {
                repr += " . " + external_representation(obj);
                obj = mk_null();
            }
        }

        repr[0] = '(';
        return repr + ")";
    }

    else if (is_string(obj))
        return '"' + get_string(obj) + '"';

    else if (is_environment(obj))
        return "#<environment " + std::to_string(obj) + '>';

    else if (is_procedure(obj))
        return "#<procedure " + std::to_string(obj) + '>';

    fprintf(stderr, "external_representation: unknown type: %lx\n", obj);
    assert(false);
}

static bool is_symbol_initial(int c)
{
    return isalpha(c) || strchr("!$%&*/:<=>?^_~", c);
}

static bool is_symbol_subsequent(int c)
{
    return is_symbol_initial(c) || isdigit(c) || strchr("+-.@", c);
}

static bool is_delimiter(int c)
{
    return isspace(c) || strchr("()\";", c);
}

std::string parser_escape_string(std::string s)
{
    for (auto i = s.find('\\'); i != decltype(s)::npos; i = s.find('\\', i + 1)) {
        auto next = i + 1;
        if (next == s.size()) {
            // hmm the string ends in a backslash, what do? let's just remove it for now...
            s.erase(i, 1);
            continue;
        }

        switch (s[next]) {
        case ' ':
        case '\t': {
            bool saw_new_line = false;

            for (++next; next < s.size() && strchr(" \t\n", s[next]) && (s[next] != '\n' || !saw_new_line); ++next)
                saw_new_line = saw_new_line || s[next] == '\n';

            s.erase(i, next - i);
            continue;
        }

        case '"':
        case '\\':
        case '|':
            s.erase(i, 1);
            continue;

        case 't':
            s.erase(i, 1);
            s[i] = '\t';
            continue;

        case 'n':
            s.erase(i, 1);
            s[i] = '\n';
            continue;

        case 'r':
            s.erase(i, 1);
            s[i] = '\r';
            continue;

        case 'x': {
                const auto semicolon = s.find(';', next);
                if (semicolon == decltype(s)::npos)
                    continue;

                const auto sub = s.substr(next+1, semicolon - next-1);
                for (auto c : sub) {
                    if (!isxdigit(c)) {
                        std::cerr << "warning: bad hex escape \\x" << sub << "; ignored" << std::endl;
                        continue;
                    }
                }

                const auto hexvalue = std::stoi(sub, nullptr, 16);
                s.replace(i, 3 + sub.size(), 1, static_cast<decltype(s)::value_type>(hexvalue));
                continue;
            }
        }
    }

    return s;
}

static std::vector<pointer> read_list_or_vector(std::istream &input)
{
    char c;

    auto skipspace = [&] {
        while (isspace(input.peek()) && input.get(c))
            ;
        return input.peek();
    };

    pointer elem;
    std::vector<pointer> elements;

    while (input) {
        if (skipspace() == ')') {
            input.get(c);
            assert(c == ')');
            return elements;
        }

        if (read_token(input, elem))
            elements.push_back(elem);
    }

    return elements;
}


std::istream & read_token(std::istream &input, pointer &var)
{
    char c;

    while (input.get(c)) {
        if (isspace(c))
            continue;

        if (c == '.') {
            char dotdot[2] = { 0, 0 };

            if (input.read(dotdot, 2) && strncmp("..", dotdot, 2) == 0) {
                static const auto dotdotdot = string_to_symbol("...");
                var = dotdotdot;
                return input;
            } else {
                switch (input.gcount()) {
                case 2:
                    input.putback(dotdot[1]);
                case 1:
                    input.putback(dotdot[0]);
                }

                static const auto dot = string_to_symbol(".");
                var = dot;
                return input;
            }
        }

        if (is_symbol_initial(c)) {
            std::string symname(1, c);
            while (is_symbol_subsequent(input.peek()) && input.get(c))
                symname += c;
            var = string_to_symbol(symname);
            return input;
        }

        if ((c == '+' || c == '-') && is_delimiter(input.peek())) {
            var = string_to_symbol(std::string(1, c));
            return input;
        }

//        if (isdigit(c) || ((c == '+' || c == '-') && isdigit(input.peek()))) {
//            const int sign = (c == '-') ? -1 : 1;

//            if (isdigit(c))
//                input.putback(c);

//            long num;
//            input >> num;

//            if (input.peek() != '.')
//                return mk_exact_number(num * sign);

//            input.get(c);
//            assert(c == '.');

//            double fraction = 0;

//            if (isdigit(input.peek()))
//                input >> fraction;

//            while (fraction > 1)
//                fraction = fraction / 10.0;

//            const double n = (double(num) + fraction) * sign;
//            return mk_inexact_number(n);
//        }

        switch (c) {
        case ';':
            input.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
            break;

        case '\'': {
            static const auto quote = string_to_symbol("quote");
            pointer quoted;
            if (read_token(input, quoted))
                var = mk_list({quote, quoted});
            return input;
        }

        case '"':
        {
            puts("READING STRING");
            std::string string, sbuf;
            while (std::getline(input, sbuf, '"')) {
                string += sbuf;
                if (string.back() == '\\')
                    string.pop_back();
                else
                    break;
            }
            var = mk_string(parser_escape_string(string));
            return input;
        }

        case '(': {
            const std::vector<pointer> elems = read_list_or_vector(input);
            var = mk_null();

            for (auto i = elems.crbegin(); i != elems.crend(); ++i)
                var = cons(*i, var);

            return input;
        }

        case ')':
            throw std::runtime_error("parser error: encountered closing paren");
            break;

        case '#': {
            if (input.get(c)) switch (c) {
            case 't':
            case 'f':
            case '\\': {
                std::string word = "#" + std::string(1, c);
                while (!is_delimiter(input.peek()) && input.get(c))
                    word += std::string(1, c);

                if (word == "#t" || word == "#true") {
                    var = mk_bool(true);
                    return input;
                } else if (word == "#f" || word == "#f") {
                    var = mk_bool(false);
                    return input;
                } /*else if (word[1] == '\\') {
                    if (word.length() == 2 && input.get(c))
                        return mk_char(c);
                    else if (word.length() == 3)
                        return mk_char(word[2]);
                    else if (word == "#\\alarm")
                        return mk_char('\a');
                    else if (word == "#\\backspace")
                        return mk_char('\b');
                    else if (word == "#\\delete")
                        return mk_char('\x7f');
                    else if (word == "#\\escape")
                        return mk_char('\x1b');
                    else if (word == "#\\newline")
                        return mk_char('\n');
                    else if (word == "#\\null")
                        return mk_char('\0');
                    else if (word == "#\\return")
                        return mk_char('\r');
                    else if (word == "#\\space")
                        return mk_char(' ');
                    else if (word == "#\\tab")
                        return mk_char('\t');
                    else
                        throw std::runtime_error("unknown named character " + word);
                } */else {
                    throw std::runtime_error("cannot parse # sequence " + word + " at position " + std::to_string(input.tellg()));
                }

                break;
            }

//            case '(':
//                return mk_vector(read_list_or_vector(input));

            }
        }
        }
    }

    return input;
}

bool is_null(pointer obj)
{
    return obj == global::static_null;
}

pointer mk_null()
{
    return global::static_null;
}

bool is_pair(pointer obj)
{
    return get_tag(obj) == tag::pair;
}

pointer cons(pointer a, pointer b)
{
    auto pair = make<pair_t>();
    pair->car = a;
    pair->cdr = b;
    return tagged(pair, tag::pair);
}

pointer car(pointer obj)
{
    return untagged<pair_t *>(obj, tag::pair)->car;
}

pointer cdr(pointer obj)
{
    return untagged<pair_t *>(obj, tag::pair)->cdr;
}

bool is_list(pointer obj)
{
    while (is_pair(obj))
        obj = cdr(obj);

    return is_null(obj);
}

pointer mk_list(std::initializer_list<pointer> elems)
{
    auto data = elems.begin();
    auto i = elems.size();

    auto result = mk_null();

    while (i > 0)
        result = cons(data[--i], result);

    return result;
}

pointer list_reversed(pointer list)
{
    std::vector<pointer> elems;

    while (!is_null(list)) {
        elems.push_back(car(list));
        list = cdr(list);
    }

    auto reversed = mk_null();

    for (auto e = elems.crbegin(); e != elems.crend(); ++e)
        reversed = cons(*e, reversed);

    return reversed;
}

bool is_tagged_list(pointer tag, pointer obj)
{
    return is_pair(obj) && car(obj) == tag;
}

bool is_symbol(pointer obj)
{
    return get_tag(obj) == tag::symbol;
}

pointer string_to_symbol(const std::string &name)
{
    auto i = std::lower_bound(global::symbols.begin(), global::symbols.end(), name, [] (symbol_t *sym, const std::string &name) {
        return sym->name < name;
    });

    symbol_t *result = nullptr;

    if (i != global::symbols.end() && (*i)->name == name) {
        result = *i;
    } else {
        result = make<symbol_t>();
        result->name = name;
        global::symbols.insert(i, result);
    }

    return tagged(result, tag::symbol);
}

std::string symbol_to_string(pointer obj)
{
    return untagged<symbol_t *>(obj, tag::symbol)->name;
}

bool is_bool(pointer obj)
{
    return obj == global::static_false || obj == global::static_true;
}

bool is_false(pointer obj)
{
    return obj == global::static_false;
}

pointer mk_bool(bool b)
{
    return b ? global::static_true : global::static_false;
}

bool is_string(pointer obj)
{
    return get_tag(obj) == tag::string;
}

pointer mk_string(std::string s)
{
    auto obj = make<string_t>();
    obj->str = std::move(s);
    return tagged(obj, tag::string);
}

std::string get_string(pointer obj)
{
    return untagged<string_t *>(obj, tag::string)->str;
}

bool is_environment(pointer obj)
{
    return get_tag(obj) == tag::environment;
}

pointer mk_environment(pointer outer)
{
    auto env = make<environment_t>();
    env->outer = outer;
    return tagged(env, tag::environment);
}

pointer environment_outer(pointer env)
{
    return untagged<environment_t *>(env, tag::environment)->outer;
}

pointer environment_find(pointer env, pointer sym)
{
    while (!is_null(env)) {
        auto p = untagged<environment_t *>(env, tag::environment);
        if (p->symtab.find(sym) != p->symtab.end())
            return env;

        env = environment_outer(env);
    }

    return mk_bool(false);
}

pointer environment_get(pointer env, pointer sym)
{
    return untagged<environment_t *>(env, tag::environment)->symtab.at(sym);
}

pointer environment_set(pointer env, pointer sym, pointer value)
{
    auto environ = untagged<environment_t *>(env, tag::environment);
    assert(environ->symtab.find(sym) != environ->symtab.end());
    return environ->symtab[sym] = value;
}

pointer environment_define(pointer env, pointer sym, pointer value)
{
    return untagged<environment_t *>(env, tag::environment)->symtab[sym] = value;
}

bool is_procedure(pointer obj)
{
    return get_tag(obj) == tag::procedure;
}

pointer mk_procedure(pointer env, pointer parameters, pointer body)
{
    assert(is_environment(env));
    assert(is_list(parameters));
    assert(is_list(body));

    //body = compiler::analyze_sequence(body);
    return compiler::compile(mk_environment(env), parameters, body);
}

pointer eval(pointer exp, pointer env)
{
    auto proc = compiler::compile(env, mk_null(), exp);
    return apply(proc, mk_null());
}

#define OPCODES(X) \
    X(eq) \
    X(eqv) \
    X(equal) \
    X(jmp) \
    X(move) \
    X(push) \
    X(pop) \
    X(loadk) \
    X(loadbool) \
    X(loadnull) \
    X(get) \
    X(set) \
    X(define) \
    X(eval) \
    X(callcc)

enum : opcode {
#define X(CODE) OP_##CODE,
OPCODES(X)
#undef X
};

static inline void decode(uint32_t ins, uint8_t &b0)
{
    b0 = ins & 0xff;
}

static inline void decode(uint32_t ins, uint8_t &b0, uint8_t &b1)
{
    b0 = ins & 0xff;
    b1 = (ins >> 8) & 0xff;
}

static inline void decode(uint32_t ins, uint8_t &b0, uint8_t &b1, uint8_t &b2)
{
    b0 = ins & 0xff;
    b1 = (ins >> 8) & 0xff;
    b2 = (ins >> 16) & 0xff;
}

static inline void decode(uint32_t ins, uint8_t &b0, uint8_t &b1, uint8_t &b2, uint8_t &b3)
{
    b0 = ins & 0xff;
    b1 = (ins >> 8) & 0xff;
    b2 = (ins >> 16) & 0xff;
    b3 = (ins >> 24) & 0xff;
}

static inline void decode(uint32_t ins, uint8_t &b0, uint8_t &b1, uint16_t &s0)
{
    b0 = ins & 0xff;
    b1 = (ins >> 8) & 0xff;
    s0 = (ins >> 16) & 0xffff;
}

static inline void decode(uint32_t ins, uint8_t &b0, int16_t &s0)
{
    b0 = ins & 0xff;
    s0 = int16_t((ins >> 8) & 0xffff);
}


pointer apply(pointer procedure, pointer arguments)
{
    auto cont = make<continuation_t>();
    cont->proc = procedure;

    while (!is_null(arguments)) {
        cont->stack.insert(cont->stack.begin(), car(arguments));
        arguments = cdr(arguments);
    }

    uint8_t B0, B1, B2, B3;
    uint16_t US0;
    int16_t S0;

    auto proc = untagged<procedure_t *>(procedure, tag::procedure);
    const auto proc_end = proc->code.data() + proc->code.size();

    cont->pc = proc->code.data();

    while (cont->pc < proc_end) {
        auto &ins = *cont->pc;
        decode(ins, B0);

        switch (B0) {
        case OP_eq: {
            abort();
            break;
        }

        case OP_eqv: {
            abort();
            break;
        }

        case OP_equal: {
            abort();
            break;
        }

        case OP_jmp: {
            decode(ins, B0, S0);

            if (global::trace_opcodes)
                fprintf(stderr, "interpreter: jmp B0: %hhx S0: %d\n", B0, S0);

            cont->pc += S0;

            break;
        }

        case OP_move: {
            abort();
            break;
        }

        case OP_push: {
            decode(ins, B0, B1);

            if (global::trace_opcodes)
                fprintf(stderr, "interpreter: push B0: %hhx B1: %hhx\n", B0, B1);

            cont->stack.push_back(cont->registers[B1]);
            break;
        }

        case OP_pop: {
            decode(ins, B0, B1);

            if (global::trace_opcodes)
                fprintf(stderr, "interpreter: pop B0: %hhx B1: %hhx\n", B0, B1);

            cont->registers[B1] = cont->stack.back();
            cont->stack.pop_back();
            break;
        }

        case OP_loadk: {
            decode(ins, B0, B1, US0);

            if (global::trace_opcodes)
                fprintf(stderr, "interpreter: loadk B0: %hhx B1: %hhx US0: %hx\n", B0, B1, US0);

            cont->registers[B1] = proc->constants[US0];
            break;
        }

        case OP_loadbool: {
            decode(ins, B0, B1, B2, B3);

            if (global::trace_opcodes)
                fprintf(stderr, "interpreter: loadbool B0: %hhx B1: %hhx B2: %hhx B3: %hhx\n", B0, B1, B2, B3);

            cont->registers[B1] = mk_bool(!is_false(cont->registers[B2]));
            if (!is_false(cont->registers[B3]))
                ++cont->pc;

            break;
        }

        case OP_loadnull: {
            abort();
            break;
        }

        case OP_get: {
            decode(ins, B0, B1, B2);

            if (global::trace_opcodes)
                fprintf(stderr, "interpreter: get B0: %hhx B1: %hhx B2: %hhx\n", B0, B1, B2);

            cont->registers[B1] = environment_get(proc->environment, cont->registers[B2]);
            break;
        }

        case OP_set: {
            decode(ins, B0, B1, B2);

            if (global::trace_opcodes)
                fprintf(stderr, "interpreter: set B0: %hhx B1: %hhx B2: %hhx\n", B0, B1, B2);

            environment_set(proc->environment, cont->registers[B1], cont->registers[B2]);
            break;
        }

        case OP_define: {
            decode(ins, B0, B1, B2);

            if (global::trace_opcodes)
                fprintf(stderr, "interpreter: define B0: %hhx B1: %hhx B2: %hhx\n", B0, B1, B2);

            environment_define(proc->environment, cont->registers[B1], cont->registers[B2]);
            break;
        }

        case OP_eval: {
            decode(ins, B0, B1, B2);

            if (global::trace_opcodes)
                fprintf(stderr, "interpreter: eval B0: %hhx B1: %hhx B2: %hhx\n", B0, B1, B2);

            cont->registers[B1] = eval(cont->registers[B2], proc->environment);
            break;
        }

        case OP_callcc: {
            abort();
            break;
        }

        default: {
            fprintf(stderr, "interpreter: illegal instruction %x\n", ins);
            abort();
        }
        }

        ++cont->pc;
    }

    if (global::trace_opcodes) {
        for (auto p : cont->stack) {
            std::cout << "stack var: " << external_representation(p) << std::endl;
        }
    }

    return cont->stack.back();
}

namespace compiler {

struct codegen {
    codegen(procedure_t *aproc) : proc(aproc) {}

    uint16_t constant(pointer obj)
    {
        uint16_t pos = 0;

        for (; pos < proc->constants.size(); ++pos)
            if (proc->constants[pos] == obj)
                return pos;

        proc->constants.push_back(obj);
        return pos;
    }

    instruction pack(opcode op, int16_t arg)
    {
        return instruction(op) | (instruction(arg) << 8);
    }

    instruction pack(opcode op, uint8_t arg1, uint16_t arg2)
    {
        return instruction(op) | (instruction(arg1) << 8) | (instruction(arg2) << 16);
    }

    instruction pack(opcode op, uint8_t arg1, uint8_t arg2, uint8_t arg3)
    {
        return instruction(op) | (instruction(arg1) << 8) | (instruction(arg2) << 16) | (instruction(arg3) << 24);;
    }

    instruction pack(opcode op, uint8_t arg1, uint8_t arg2)
    {
        return instruction(op) | (instruction(arg1) << 8) | (instruction(arg2) << 16);
    }

    instruction pack(opcode op, uint8_t arg1)
    {
        return instruction(op) | (instruction(arg1) << 8);
    }

    void write(uint32_t instruction)
    {
        proc->code.push_back(instruction);
    }

    void op_loadk(uint8_t reg, pointer k)
    {
        auto val = constant(k);
        fprintf(stderr, "assembler: loadk %hhx %hx (%s)\n", reg, val, external_representation(k).c_str());
        write(pack(OP_loadk, reg, val));
    }

    void op_push(uint8_t reg)
    {
        fprintf(stderr, "assembler: push %hhx\n", reg);
        write(pack(OP_push, reg));
    }

    void op_pop(uint8_t reg)
    {
        fprintf(stderr, "assembler: pop %hhx\n", reg);
        write(pack(OP_pop, reg));
    }

    void op_define(uint8_t var, uint8_t val)
    {
        fprintf(stderr, "assembler: define %hhx %hhx\n", var, val);
        write(pack(OP_define, var, val));
    }

    void op_set(uint8_t var, uint8_t val)
    {
        fprintf(stderr, "assembler: set %hhx %hhx\n", var, val);
        write(pack(OP_set, var, val));
    }

    void op_get(uint8_t reg, uint8_t var)
    {
        fprintf(stderr, "assembler: get %hhx %hhx\n", reg, var);
        write(pack(OP_get, reg, var));
    }

    void op_eval(uint8_t reg, uint8_t exp)
    {
        fprintf(stderr, "assembler: eval %hhx %hhx\n", reg, exp);
        write(pack(OP_eval, reg, exp));
    }

    void op_loadbool(uint8_t A, uint8_t B, uint8_t C)
    {
        fprintf(stderr, "asembler: loadbool %hhx %hhx %hhx\n", A, B, C);
        write(pack(OP_loadbool, A, B, C));
    }

    void op_eq(uint8_t reg0, uint8_t reg1)
    {
        fprintf(stderr, "assembler: eq %hhx %hhx\n", reg0, reg1);
        write(pack(OP_eq, reg0, reg1));
    }

    void op_jmp(int16_t delta)
    {
        fprintf(stderr, "assembler: jmp %d\n", delta);
        write(pack(OP_jmp, delta));
    }

    procedure_t * const proc;
};

pointer compile(pointer env, pointer params, pointer exp)
{
    assert(is_environment(env));
    assert(is_list(params));

    auto proc = make<procedure_t>();
    proc->environment = env;

    codegen gen(proc);

    while (!is_null(params)) {
        auto name = car(params);
        assert(is_symbol(name));

        gen.op_loadk(0, name);
        gen.op_pop(1);
        gen.op_set(0, 1);

        params = cdr(params);
    }

    if (is_self_evaluating(exp)) {
        if (global::trace_compiler)
            printf("%s:%d: self-evaluating\n", __PRETTY_FUNCTION__, __LINE__);
        gen.op_loadk(0, exp);
        gen.op_push(0);
    } else if (is_variable(exp)) {
        if (global::trace_compiler)
            printf("%s:%d: variable\n", __PRETTY_FUNCTION__, __LINE__);
        gen.op_loadk(0, exp);
        gen.op_get(1, 0);
        gen.op_push(1);
    } else if (is_quoted(exp)) {
        if (global::trace_compiler)
            printf("%s:%d: quoted\n", __PRETTY_FUNCTION__, __LINE__);
        gen.op_loadk(0, text_of_quotation(exp));
        gen.op_push(0);
    } else if (is_assignment(exp)) {
        if (global::trace_compiler)
            printf("%s:%d: assignment\n", __PRETTY_FUNCTION__, __LINE__);
        gen.op_loadk(0, assignment_value(exp));
        gen.op_eval(1, 0);
        gen.op_loadk(0, assignment_variable(exp));
        gen.op_set(0, 1);
        gen.op_push(1);
    } else if (is_definition(exp)) {
        if (global::trace_compiler)
            printf("%s:%d: definition\n", __PRETTY_FUNCTION__, __LINE__);
        gen.op_loadk(0, definition_value(exp));
        gen.op_eval(1, 0);
        gen.op_loadk(0, definition_variable(exp));
        gen.op_define(0, 1);
        gen.op_push(1);
    } else if (is_if(exp)) {
        if (global::trace_compiler)
            printf("%s:%d: if\n", __PRETTY_FUNCTION__, __LINE__);
        gen.op_loadk(0, if_predicate(exp));
        gen.op_eval(0, 0);
        gen.op_loadbool(1, 0, 0);
        gen.op_eq(0, 1);
        gen.op_jmp(2);
        gen.op_loadk(0, if_alternative(exp));
        gen.op_jmp(1);
        gen.op_loadk(0, if_consequent(exp));
        gen.op_eval(0, 0);
        gen.op_push(0);
    } else if (is_lambda(exp)) {
        if (global::trace_compiler)
            printf("%s:%d: lambda\n", __PRETTY_FUNCTION__, __LINE__);
        gen.op_loadk(0, mk_procedure(env, lambda_parameters(exp), lambda_body(exp)));
        gen.op_push(0);
    } else {
        fprintf(stderr, "cannot compile expression: %s\n", external_representation(exp).c_str());
        abort();
    }

    return tagged(proc, tag::procedure);
}

bool is_self_evaluating(pointer exp)
{
    return is_string(exp) || is_bool(exp);
}

bool is_variable(pointer exp)
{
    return is_symbol(exp);
}

bool is_quoted(pointer exp)
{
    static const auto quote = string_to_symbol("quote");
    return is_tagged_list(quote, exp);
}

pointer text_of_quotation(pointer exp)
{
    assert(is_quoted(exp) && !is_null(cdr(exp)));
    return cadr(exp);
}

bool is_assignment(pointer exp)
{
    static const auto set = string_to_symbol("set!");
    return is_tagged_list(set, exp);
}

pointer assignment_variable(pointer exp)
{
    assert(is_assignment(exp));
    return cadr(exp);
}

pointer assignment_value(pointer exp)
{
    assert(is_assignment(exp));
    return caddr(exp);
}

bool is_definition(pointer exp)
{
    static const auto define = string_to_symbol("define");
    return is_tagged_list(define, exp);
}

pointer definition_variable(pointer exp)
{
    if (is_symbol(cadr(exp)))
        return cadr(exp);
    else
        return caadr(exp);
}

pointer definition_value(pointer exp)
{
    static const auto lambda = string_to_symbol("lambda");
    if (is_symbol(cadr(exp)))
        return caddr(exp);
    else
        return mk_list({lambda, cdadr(exp), cddr(exp)});
}

bool is_lambda(pointer exp)
{
    static const auto lambda = string_to_symbol("lambda");
    return is_tagged_list(lambda, exp);
}

pointer lambda_parameters(pointer exp)
{
    return cadr(exp);
}

pointer lambda_body(pointer exp)
{
    return cddr(exp);
}

bool is_if(pointer exp)
{
    static const auto ifsym = string_to_symbol("if");
    return is_tagged_list(ifsym, exp);
}

pointer if_predicate(pointer exp)
{
    return cadr(exp);
}

pointer if_consequent(pointer exp)
{
    return caddr(exp);
}

pointer if_alternative(pointer exp)
{
    if (is_null(cdddr(exp)))
        return mk_bool(false);
    else
        return cadddr(exp);
}

bool is_begin(pointer exp)
{
    static const auto begin = string_to_symbol("begin");
    return is_tagged_list(begin, exp);
}

pointer begin_actions(pointer exp)
{
    return cdr(exp);
}

bool is_last_exp(pointer seq)
{
    return is_null(cdr(seq));
}

pointer first_exp(pointer seq)
{
    return car(seq);
}

pointer rest_exps(pointer seq)
{
    return cdr(seq);
}

pointer make_begin(pointer seq)
{
    static const auto begin = string_to_symbol("begin");
    return cons(begin, seq);
}

pointer sequence_to_exp(pointer seq)
{
    if (is_null(seq))
        return seq;
    else if (is_last_exp(seq))
        return first_exp(seq);
    else
        return make_begin(seq);
}

bool is_application(pointer exp)
{
    return is_pair(exp);
}

pointer application_operator(pointer exp)
{
    return car(exp);
}

pointer application_operands(pointer exp)
{
    return cdr(exp);
}

bool has_no_operands(pointer ops)
{
    return is_null(ops);
}

pointer first_operand(pointer ops)
{
    return car(ops);
}

pointer rest_operands(pointer ops)
{
    return cdr(ops);
}

bool is_cond(pointer exp)
{
    static const auto cond = string_to_symbol("cond");
    return is_tagged_list(cond, exp);
}

pointer cond_clauses(pointer exp)
{
    return cdr(exp);
}

pointer is_cond_else_clause(pointer clause)
{
    static const auto else_sym = string_to_symbol("else");
    return else_sym == cond_predicate(clause);
}

pointer cond_predicate(pointer clause)
{
    return car(clause);
}

pointer cond_actions(pointer clause)
{
    return cdr(clause);
}

pointer cond_to_if(pointer exp)
{
    return expand_clauses(cond_clauses(exp));
}

pointer expand_clauses(pointer clauses)
{
    if (is_null(clauses))
        return mk_bool(false); // no else clause

    auto first = car(clauses);
    auto rest = cdr(clauses);

    if (is_cond_else_clause(first)) {
        if (is_null(rest)) {
            return sequence_to_exp(cond_actions(first));
        } else {
            fprintf(stderr, "cond_to_if: else clause isn't last ")
        }
    }
}

} // namespace compiler
} // namespace qaf

























