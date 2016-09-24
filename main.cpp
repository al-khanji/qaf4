#include <iostream>
#include "qaf.h"

int main()
{
    auto env = qaf::mk_environment();

    while (std::cin) {
        try {
            std::cout << ">> ";
            qaf::pointer expr;

            if (qaf::read_token(std::cin, expr)) {
                std::cout << "input token: " << qaf::external_representation(expr) << std::endl;
                auto result = qaf::eval(expr, env);
                std::cout << "eval result: " << qaf::external_representation(result) << std::endl;

            }
        } catch (std::exception &e) {
            std::cerr << "exception caught: " << e.what() << std::endl;
        }
    }

    std::cout << std::endl;

    return 0;
}
