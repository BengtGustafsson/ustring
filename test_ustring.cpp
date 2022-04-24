/*

Test program for a ustring class for possible introduction into the C++ standard library.

This software is provided under the MIT license:

Copyright 2022 Bengt Gustafsson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
(the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

Further information at: https://opensource.org/licenses/MIT.

*/



#include "ustring.h"

#include <iostream>

void test_ustring()
{
    using namespace STD::literals::string_literals;

    STD::ustring a;
    STD::ustring b{ "b" };  // Can't init with = without trailing u as the ctor from character pointer is explicit. b will contain a copy of the literal.
    STD::ustring c = "c"_u;  // Here the literal is not copied thanks to the _u suffix.
    STD::ustring d = L"c"_u;
    assert(c == d);
    assert(a.begin() == a.end());
    assert(b.begin() < b.end());

    STD::ustring e = b + "hej"_u;
    STD::ustring g = char32_t('!');
    STD::ustring f = e + g;

    std::cout << f.string() << std::endl;

    std::cout.imbue(std::locale(".850"));
    std::cout << std::cout.getloc().name();
    std::cout << "\nÅÄÖ\nåäö" << std::endl;
    STD::ustring u = "ÅÄÖ"_u;
    std::cout << u << std::endl;
    STD::ustring lower = tolower(u);
    std::cout << lower << std::endl;
}


int main()
{
    test_ustring();
}
