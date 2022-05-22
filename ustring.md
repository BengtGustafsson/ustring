ustring, an immutable Unicode string
====================================

`ustring` is a immutable string class presenting its contents as unicode code points (type `char32_t`). To open for internal representations like UTF-8 or UTF-16 which don't have a fixed number of bytes per code point its API does not allow random access or mutation, instead bidirectional iterators are used to access individual code points.

Thanks to the immutability sharing with a reference counted implementation is possible. It is also possible to implement `ustring` such that substrings can be created by sharing the same implementation while referring to a subset of its contents. Furthermore the somewhat limited API allows concatenation of multiple ustring objects to be performed by referring to the implementation for the concatenated parts. In addition implementations are allowed to just refer to literals and other data (that must outlive the ustring) object rather than copying the data to heap memory. The API also allows small object optimization and there is a trade off between time to copy those characters and the time to increment a reference count atomically to be made by implementers. Finally the API has been designed to allow reusing heap buffers if ustrings are created from *rvalue* `basic_string` objects.

## Synopsis

```C++
template<typename T> concept character;

class ustring {
public:
    enum encoding_t : uint8_t { utf8, utf16, utf32, wide, execution, system, single, multipart };

    class iterator;
    class loader;
    class saver;
    class filler;

    template<character T> static constexpr encoding_t encoding_of;
    template<encoding_t> using encoding_type;

    ustring()    
    
    ustring(const ustring& src);
    ustring(ustring&& src);

    template<character T> ustring(T c);
    template<character T> ustring(size_t count, T c);

    template<character T> explicit ustring(const T* src);
    template<character T> ustring(const T* src, size_t);

    ustring(const char* src, locale& loc);
    ustring(const char* src, size_t count, locale& loc);
    ustring(const string& src, locale& loc);

    template<character T, typename Tr = char_traits<T>, typename Al = allocator<T>> 
    ustring(const basic_string<T, Tr, Al>& src, size_t pos = 0, size_t count = npos);
    template<character T, typename Tr = char_traits<T>, typename Al = allocator<T>> 
    ustring(basic_string<T, Tr, Al>&& src);
    template<character T, typename Tr = char_traits<T>> 
    ustring(basic_string_view<T, Tr> src, size_t pos = 0, size_t count = npos);

    template<typename Tr = char_traits<char>, typename Al = allocator<char>> 
    ustring(const basic_string<char, Tr, Al>& src, const locale& loc, size_t pos = 0, size_t count = npos);
    template<typename Tr = char_traits<char>, typename Al = allocator<char>> 
    ustring(basic_string<char, Tr, Al>&& src, const locale& loc);
    template<typename Tr = char_traits<char>> 
    ustring(basic_string_view<char, Tr> src, const locale& loc, size_t pos = 0, size_t count = npos);

    ~ustring();

    ustring& operator=(const ustring& rhs);
    ustring& operator=(ustring&& rhs);

    friend ustring operator+(ustring&& lhs, ustring&& rhs);
    ustring& operator+=(const ustring& rhs);
    ustring& operator+=(ustring&& rhs);

    bool operator==(const ustring& rhs) const;
    strong_ordering operator<=>(const ustring& rhs) const;

    template<character T> static ustring view(const T* src);
    template<character T> static ustring view(const T*, std::size_t);                

    template<character T, typename Tr = char_traits<T>, typename Al = allocator<T>> 
    static ustring view(const basic_string<T, Tr, Al>& original, size_t pos = 0, size_t count = npos);
    template<character T, typename Tr = char_traits<T>>
    static ustring view(const basic_string_view<T, Tr>& original);
 
    static ustring view(const char*, size_t sz, const locale& loc);
    static ustring view(const char* src, const locale& loc);

    template<typename Tr = char_traits<char>, typename Al = allocator<char>>
    static ustring view(const basic_string<char, Tr, Al>& original, 
                        const locale& loc, size_t pos = 0, size_t count = npos);
    template<typename Tr = char_traits<char>>
    static ustring view(const basic_string_view<char, Tr>& original, const locale& loc);

    bool empty() const;

    iterator begin() const;
    iterator end() const;

    pair<iterator, iterator> find_ends(const ustring& pattern) const;
    iterator find(const ustring& pattern) const;
    pair<iterator, iterator> rfind_ends(const ustring& pattern) const;
    iterator rfind(const ustring& pattern) const;

    bool contains(const ustring& pattern) const;
    bool starts_with(const ustring& pattern) const;
    bool ends_with(const ustring& pattern) const;

    ustring substr(const iterator& start, const iterator& end) const;
    ustring substr(const pair<iterator, iterator>&) const;
    ustring first(const iterator& upto) const;
    ustring last(const iterator& from) const;
    
    template<character T> std::basic_string<T> basic_string(T bad_char = '?') const;
    std::string string(char bad_char = '?') const;
    std::wstring wstring() const;
    std::u8string u8string() const;
    std::u16string u16string() const;
    std::u32string u32string() const;

    encoding_t encoding() const;
    template<character T> const T* data() const;

    const byte* data() const;
    size_t bytes() const;

    template<character T> size_t estimated_size() const; 
    template<character T> size_t copy(T* dest, size_t count, T bad_char = '?') const;
    template<character T, size_t SZ> span<T> copy(span<T, SZ> dest, T bad_char = '?') const;
};
```

## Character types

The new *concept* `character` is a general concept that is true for the five types `char`, `char8_t`, `char16_t`, `char32_t` and `wchar_t`, i.e. the types that `ustring` handles. This concept is probably useful for other purposes, and there should probably be a
`is_character` / `is_character_v` trait to complement it. Note that `unsigned char` and `signed char` are not `character` as they
are used for arithmetic rather than text, sometimes with `int8_t` and `uint8_t` as type aliases.

For users to be able to optimize retrieving data from `ustring` when it is stored in the desired encoding there is a need for testing for character encoding at runtime. The enum `ustring::encoding_t` indicates the different encodings, basically corresponding to the different character types. The enumerators are named after the encodings UTF-8. UTF-16, UTF-32, wchar_t and narrow encodings. While wchar_t encoding will usually be the same as UTF-16 or UTF-32 depending on platform keeping a separate enumerator value simplifies some types of code which works with wstring and similar. For narrow encodings there are three distinct values, `execution`, `system` and `single` which indicate that char values represent the execution encoding (for char literals), the system encoding (default OS narrow encoding assumed when non-literal char data is provided to an ustring without any locale) and single, which is used when some other locale was provided with char data. Note that the user must keep track of which locale this may be in this case. [This possibility is debatable, maybe it is better to mandate conversion to one of the other encodings in this case]. In addition there is a separate enumerator `multipart` for strings which are don't have an internal storage of contiguous code units in any of the encodings.

To aid user code with encoding handling there is a variable template `ustring::encoding_of` which contains the `encoding_t` for each character type. This template is not defined for char.

For the opposite relation there is a type alias template `ustring::encoding_type` which evaluates to the character type
corresponding to each `encoding_t` enumerator. The `multipart` enumerator does not correspond to a character type and it is unclear whether trying to use is should be a compile time error, or yield std::byte or possibly void. As proposed it is not defined. 

Construction
------------

ustring has a lot of constructors to make it easy to use as a vocabulary type. Many constructors parallel those of `basic_string`
but are templated on the character type. The implementation is free to either retain the encoding of the source data or to convert the data to a common internal encoding, which is reasonable as the data has to be copied anyway.

```C++
    ustring()    
    
    ustring(const ustring& src);
    ustring(ustring&& src);

    template<character T> ustring(size_t count, char32_t c);

    template<character T> explicit ustring(const T* src);
    template<character T> ustring(const T* src, size_t);

    template<character T> 
    ustring(const basic_string<T>& src, size_t pos = 0, size_t count = npos);
    template<character T> 
    ustring(basic_string<T>&& src);
    template<character T> 
    ustring(basic_string_view<T> src);
```

### Character sequence constructors

The constructors from just a character pointer are explicit to encourage the use of the `""u` literals, see below. The advantage of using the `""u` literals is that the literal characters don't need to be copied, so that's a large win. The explicit declaration prevents using a regular literal as the argument for a ustring function parameter, which should catch most accidental use. A stronger measure would be to replace the non-literal const T* constructor by a pseudo-constructor called something like `create` or `from_buffer`.

Preventing direct construction of `ustring` from a character buffer or character pointer has the advantage that functions like `stoi` can be overloaded for ustring without breaking old code, that is, nothing which you can construct a `std::basic_string` from implicitly should be possible to construct a ustring from implicitly.

In addition there are constructors which also take an explicit count, saving on the strlen operation in some cases. Iterator pair constructors could be added, but would require that value_type or maybe decltype(*iter) be one of the character types to be able to determine the encoding of the source sequence.

### Character constructor

There is a templated constructor for one character or a repeated character. The char specialization of these constructors assume that the suitable encoding is execution. There is no single character constructor taking a char and a locale, although this could be added to improve orthogonality.

### basic_string and basic_string_view constructors.

The constructor from `basic_string<T>` copies the string contents. It has optional pos and size parameters, as well as optional Traits and Alloc template parameters, which is in line with how std::filesystem::path is constructed.

#### Rant about creating string_views for parts of strings.

You could have hoped that we wouldn't need those and instead use an intermediate `basic_string_view`. However, there is no easy way to get a string_view for part of a string, it seems. You have to use data() and pointer arithmetic or first create a view of the full string and then `substr` on that. This seems like an idea for another proposal:

```C++
std::string myString = "Hej hopp";

// Today version 1
std::string_view hoppView(myString.data() + 4, 4);

// Today version 2
std::string_view myView = myString;     // Invoke cast operator in basic_string.
auto hoppView = myView.substr(4, 4);

// I would like:
auto hoppView = myString.subview(4, 4);

// And of course for consistency, although it is a duplicate of string_view::substr:
auto ppView = hoppView.subview(2, 2);

// A discussion about whether string_view::substr should have returned a basic_string is purely academic at this point...
```

Note also that the intuitive way to first do substr on the string and then use that as a view often results in dangling references:

```C++
std::string myString = "Hej hopp";

string_view get_hopp()
{
    auto hopp = myString.substr(4, 4);
    return hopp;
}
```

Only Clang warns for this, both gcc and msvc are happy to get you in trouble: https://godbolt.org/z/6cM38rqWE

### rvalue basic_string constructors

The constructor from rvalue `basic_string` could in some implementations reuse the data block of the `basic_string` and even give it back later if the rvalue version of the corresponding `ustring::string()` function is called. This is relatively easy to implement if only the default Traits and Alloc types are supported (a union or variant can be used) while to support any Traits and Alloc type a full type erase of the ustring implementation must be done, for instance using an abstract base class to implementation subclasses. The implementation is free to implement or not implement any of these levels of complexity for any or all character types. Note that while a full virtualization of the implementation API may seem daunting the fact is that those virtual methods only need to be called when a new iterator is created, or in some cases only when the Impl object is destroyed.

It could be possible for some implementations to set up the ustring object correctly even if pos and size denotes part of the original string, although this means that the entire memory block will be retained even if the pos/size combination only denotes a small part. Currently it is not considered interesting enough to add pos and size parameters for the rvalue overload and any call site that provides them would fall back to the lvalue overload. Maybe it could be unspecified whether the rvalue overload has pos and size parameters.

### Converting constructors

```C++
    ustring(const char* src, locale& loc);
    ustring(const char* src, size_t count, locale& loc);
    ustring(const string& src, locale& loc, size_t pos = 0, size_t count = npos);
```

A constructor from `const char*` with a `locale` parameter is available. These constructors would probably perform a conversion if the locale is not for the same encoding as any of the ones implicitly selected by one of the character types, which basically pertains to UTF-8 and ASCII. If the implementation so chooses it can also implement a table lookup representation for the case of character sets like ISO/IEC 8859-1 (latin-1) which contain up to 256 Unicode code points. It would also be possible to implement 16 bit table lookup for encodings like UCS2, but as this is a subset of UTF-16 this seems unnecessary. Possibly there are other 9-16 bit encodings which can be handled by a table lookup. 

As there are encodings which are not reversible (such as shift-jis) it is impossible to retain the bidirectionality of iterators if an implementation would opt to convert such encodings on the fly.  There are also other drawbacks with such an implementation:

* Libraries like icu and iconv which can convert from/to any locale are not efficient if called for one code point at a time. Thus the iterator class would have to have a rather big buffer to amortise the overhead of calling the conversion function. 
* There is a risk is that the same string is converted multiple times if more iterators are created or one iterator is moved back and forth. 
* The virtual function call(s) required to handle an unbounded set of encodings is much worse than handling about 4 different encodings in the iterator. Branching out to four encodings can be done with two nested if statements and the branch target buffers of modern processors will usually make this at no-cost in tight loops. Not so for virtual calls.

Due to these drawbacks it doesn't seem reasonable to drop the bidirectionality just to accommodate implementations that may want to retain locale specific encodings. 

Note: The constructor taking a `std::string` and a `locale` is a special case, which suggests that maybe *char* is a better choice than *byte* for locale aware constructors anyway. The same can be said about loader/saver APIs (see below).

### What is the default encoding of a char string anyway?

To keep in sync with std::filesystem::path a char string must be interpreted as being in the current locale. I'm not sure if this means that it _always_ is in the locale of the underlying operating system (ensuring that filenames "work" when sent to 8 bit APIs) or if it follows the std::locale::global() setting. The Microsoft documentation at [](https://docs.microsoft.com/en-us/cpp/standard-library/path-class?view=msvc-170) suggests the former interpretation, and on Linux there is no difference, it is always UTF-8.

As the operating system interpretation of a char string can be any locale this means that constructors from char strings may have to set up a look up table to get the code points from the characters, or if the local encoding of the machine is not one char per code point even convert the incoming string on the fly.

This has the rather grave implication that even strings returned from innocuous functions like `std::to_string(int)` would have to be converted using iconv or something just because the operating system is set up for a locale that requires conversion. As the character array is copied anyway maybe a check whether all characters are ASCII (<128) could be implemented in the copy loop without too much extra cost. If no such characters are encountered all is fine, but if not the converter from the locale has to be called from the first non-ASCII character on, or something like that.

This merits further thought and discussion with the Unicode SIG.

### Literals

Literal suffix u for all built in prefixes are return ustrings which may be constructed without copying the contents of the literal. If this is implemented it is up to the implementation to select whether to avoid copying for all character types or to convert some subset of types to simplify iteration.

```C++
namespace literals::string_literals {
    inline ustring operator""u(const char* ptr, size_t sz);
    inline ustring operator""u(const wchar_t* ptr, size_t sz);
    inline ustring operator""u(const char8_t* ptr, size_t sz);
    inline ustring operator""u(const char16_t* ptr, size_t sz);
    inline ustring operator""u(const char32_t* ptr, size_t sz);
}
```

Note: These operators must be written separately, as a templated literal operator has another meaning than expected, it gets instantiated for each separate literal, not for the char types. [I may be wrong on this, maybe it works if the template parameter is typename, not auto].

### The view pseudo-constructor

The static member function view can be used to create viewing ustrings from non-literals. In this case the programmer guarantees that the data is available throughout the lifetime of the `ustring`, and furthermore that it will not change. If such data changes this is an UB condition as ustring is allowed to copy the data depending on its implementation. Iterators that access ustring data are also allowed to cache parts of the string for efficiency reasons even if it was not initially copied.

```C++
    template<character T> static ustring 
    view(const T*, std::size_t);
	template<character T> static ustring 
    view(const T*); 
    template<character T> static ustring 
    view(const basic_string<T>& original, size_t pos = 0, size_t count = npos);
    template<character T> static ustring 
    view(const basic_string_view<T>& original);
```

Again it is unclear if it would be better to have pos/size for `basic_string_view` too for a more orthogonal API.

For char data type there are view overloads taking a locale. This allows non-copying views to be created if the encoding of the locale allows this.

### ustring::filler

The ustring::filler class is an output iterator which creates a ustring from Unicode code points. When the sequence is complete it can be retrieved as a ustring using the rvalue-qualified cast operator or, equivalently, using the str() method, which is available in both lvalue and rvalue overloads. The lvalue overload sets the filler up for creating a new ustring. [Would it be possible to allow continuing to use the filler after calling str(), ensuring that the first retrieved string is a proper prefix of what ends up being the complete string. It is a bit unclear if it can be done efficiently for all feasible implementations].

### ustring::loader

To allow for piecewise construction from a sequence of buffers obtained by reading a file, receiving packets on a network or similar a special `ustring::loader` class is provided. This class builds an ustring from the data in the sequence of incoming buffers, not requiring that the data is broken up at code point boundaries. By implementing this functionality as a class members similar to mb_state are not required in the ustring class itself. 

```C++
class ustring::loader {
public:
    ustring_loader(locale& loc, size_t source_size = 0);

    bool append(const byte* buffer, size_t sz);
    bool is_complete() const { return m_complete; }

    ustring str() &&;
};
```

The constructor stores the relevant facet of the locale and if source_size is set it may pre-allocate a buffer for the result, using some measure of the resulting length, given the locale and the selected target encoding. It could be better to let the caller do the use_facet<T>() call on the locale to allow control over which internal representation the user wants the ustring to eventually hold. This is however cumbersome as you have to write something like `std::use_facet<std::codecvt<char32_t, char, std::mb_state>>(std::locale())` which is quite a mouthful to just indicate that an internal char32_t representation is requested. Unfortunately you can't template constructors if explicit template parameter is needed. It would be possible to template the entire loader class but that seems unnecessary. There could be some performance advantage though. Another option would be to have a `ustring:create_loader<T>(locale&, source_size);` which can do the use_facet call as a convenience. Some implementation issues may require the loader class to be templated anyway. This needs further elaboration.

The `append`() function adds a buffer's worth of data. It is free to resize some internal buffer as needed. It could also use separate ustrings for each buffer if the implementation of ustring handles concatenation by keeping copies. Note however that it would have to make sure that each ustring generated contains a complete set of code points, straddling code points are not supported in this case.

The `is_complete()` function returns true when the string contains a whole number of code points, and it is possible to extract the ustring by calling `str`().

Unfortunately the `codecvt` API is not friendly to this type of easy to use API as it requires the remaining bytes to be placed first in the buffer, causing an extra buffer copy or an extra (very short) call to `codecvt` with retained couple of bytes from the previous buffer and a few of the first bytes of the new buffer. A better solution would have been to retain the half-finished code point in the state to allow the entire source buffer to be consumed. Maybe this is the deficiency in codecvt that the Unicode SG is trying to remedy, I don't know.

The resulting ustring can only be retrieved once from the loader, as `str` has rvalue qualification. This guarantees that the returned ustring is indeed immutable, no further buffers can be added to the loader after a ustring has been retrieved from it. Adding buffers late could be defined to raise an exception, restarting the process from an empty state or just be UB. 

It is also possible that it could be allowed to do late additions but this requires the length to be stored in the ustring rather than the impl object, but this is required anyway for any implementation that reference counts the implementation and lets the result of substr share the data with the original. This remains to be seen. 

%Maybe **builder** is a better name than loader. On the other hand this class has not the same task as the builder class of other languages which are usually geared towards reducing the number of allocations when a string is created from many short fragments.


Access
------

The only way to access the contents of an ustring is via iterators. The regular `begin()` and `end()` functions return iterators. As some important representations don't have a fixed number of bytes per code point iterators are not random access or possible to subtract freely. It should be easy to provide `rbegin()` and `rend()`, returning iterator adapters. However this could interfere with preloading a code point into the iterator, as explained below. This would at least require a separate reverse_iterator class which is not just `std::reverese_iterator<ustring::iterator>` but that's ok with the standard. It could be that not even this is possible to implement but I would think so.

```C++
    iterator begin() const;
    iterator end() const;
    reverse_iterator iterator rbegin() const;
    reverse_iterator iterator rend() const;

```

Iterator class
---------

The nested class `ustring::iterator` allows const access on the code point level. At this point working on the grapheme cluster level has not been considered but it should be possible to implement for instance a function to increment on the grapheme cluster level, thus providing easy grouping of code points to clusters when needed.

```C++
class ustring::iterator {
public:
    iterator(const ustring& str, const byte* pos);

    char32_t operator*();

    iterator& operator++();
    iterator operator++(int);
    iterator& operator--();
    iterator operator--(int);

    strong_ordering operator<=>(const iterator& rhs) const;

    ptrdiff_t operator-(const iterator& rhs) const;

    iterator operator+(ptrdiff_t by) const;
    iterator& operator-=(ptrdiff_t by);
    iterator operator+(ptrdiff_t by) const;
    iterator& operator-=(ptrdiff_t by);

    ptrdiff_t index() const;
    
    void advance(ptrdiff_t by);
    size_t advance(const iterator& towards, size_t by);
    size_t advance(const iterator& to);
};
```

It may seem weird to include addition and subtraction by `ptrdiff_t` in a bidirectional iterator but as *some* encodings allow random access it would still be an advantage to have them even if they *sometimes* have linear time complexity. The same reasoning goes for the `operator-()` between two iterators. Note that with the *index* feature described below the range of cases where subtraction is quick is extended to all cases where the sign of the index is the same for both iterators being subtracted.

### reference type

A problem exists with the `reference` type of the iterator. According to the standard a proper *LegacyForwardIterator* `operator*()` must return a const T& (a const char32_t& in this case). This is problematic as the code point is constructed on the spot in `operator*()` if the internal representation is something else. Some implementations may opt to store the code point value as a member of the iterator and could potentially return a reference to it, but this has the adverse effect that doing the &i1 == &i2 comparison will always return false, even if the iterators i1 and i2 point at the same code point. I'm leaning towards returning char32_t anyway to make sure that you can't take the address of the returned value, thus departing slightly from the *LegacyBidirectionalIterator* concept. 

I also considered a proxy object which could "work" in the sense that comparisons as shown above would work. But the problem is the same as for `vector<bool>::operator*()`, i.e. that the cost of conversion to char32_t is not what you expect, which could affect overload resolution or even make some function calls that seem ok illegal. However, as ustring is immutable we don't have the worse problem of not being able to produce an assignable reference to pass to a function.

The proxy object solution makes optimizations harder and there is no real reason to compare the addresses of the references when you can compare the iterators themselves. It seems unlikely that standard library implementations would contain algorithm code that relies on comparing addresses of dereferenced iterators but it may well show up in user code (even template code where ustring would be a possible new template argument).

A proxy object with an *implicit* cast operator to char32_t would be one way of solving this, making the existence of a proxy object transparent to user code. Implicit cast operators is another proposal mainly intended to provide universal references.

### Index feature

A proposed feature of `ustring::iterator` is to keep track of the number of code points they have been moved from the beginning or end
of the ustring where all iterators originate. This simplifies counting code points and would allow quick subtraction of iterators as long as they were both created from the same end of the ustring even if the encoding is not random accessible. This feature has some time and space cost which means that it may be better to have a separate `counting_iterator` for this purpose, which inherits or aggregates the "dumber" regular iterator. The problem with having two iterator types is increased complexity and the question of which one begin() and end() returns, or if there are pairs of those functions.

The `index()` function returns the code point index, with iterators created from `end()` always returning negative numbers. Unfortunately it seems infeasible to let the `end()` iterator (which is after the last code point) have index 0 as in Python. This would be very confusing as a test for index() == 0 would only reveal that the iterator is at begin() *or* end(). As we don't implement slicing or random access with negative indices this is less of an issue than for a random access container.

The `advance()` member functions move the iterator by the given amount. As the size of the ustring is not easily obtainable to limit the argument of the first overload the second overload is available which stops the advancing if the `towards` iterator is hit. The direction of advancement is governed by first comparing the iterator itself with towards, which is always possible. This definition makes the function fool proof for providing an iterator on the wrong side of the current iterator. The third overload of `advance()` is present to mirror the overloads of `ranges::advance()`, but also as it provides a convenient way to move an iterator to the same code point as `to` but with the sign of the index value preserved. Example:

```C++
ustring myString = "Hej hopp";
auto jIter = myString.find("j");    // Index == 2
auto oIter = myString.rfind("o");   // Index == -4

// Quick or slow depending on encoding
auto distSlow = oIter - jIter;      

// Quick or slow depending on encoding
auto oFromStart = myString.begin().advance(oIter);

// Quick as both indices are from begin.
auto distQuick = oFromStart - jIter;                
```

### Are iterators to be safe for destruction of ustring?

Iterators must in some implementations store a reference to the ustring they were created for. It is unclear if this should be made
mandatory and in that case if the integrity of the underlying `ustring` should be guaranteed by having the iterator take a reference
count on the implementation. As we want to allow also implementations which don't reference count an implementation we opted to not
make iterators safe from destroying the underlying ustring, which is consistent with all other containers.

### Comparing iterators

As the underlying data is contiguous or consists of a set of contiguous areas two iterators can always be compared as this can be
done by comparing pointers even if the exact number of characters between the iterators is not known. In the case of a set of contiguous areas the comparison would first compare the area index.

One way of storing the area indices feasible for 64 bit implementations for the foreseeable future would be to store the area index as bits 57-62 of the pointer, as no widespread processors have a larger virtual address space than 57 bits. With the top bit lost as a sign bit this leaves room for up to 64 areas, which should be plenty. To handle cases where more than 64 parts are concatenated some logic would have to be implemented to coerce some or all areas to one when this happens. Implementations can take different approaches, and the very idea of creating areas at concatenation is just one option for implementation. The drawback with this type of implementation is that the area bits have to be set to the sign bit before all access, which could be costly. *In the first implementation the area numbers are bits in the pointers in ustring but extracted from the pointers in the iterator class, where the actual dereference of the pointer occurs.*

Utility member functions
-----------------

Some functionality is implemented as member functions for compatibility with basic_string and as it needs access to the private parts of the string.

```C++
bool empty() const;

pair<iterator, iterator> find_ends(const ustring& pattern) const;
pair<iterator, iterator> find_ends(const ustring& pattern, const iterator& after) const;
iterator find(const ustring& pattern) const;
iterator find(const ustring& pattern, const iterator& after) const;
pair<iterator, iterator> rfind_ends(const ustring& pattern) const;
pair<iterator, iterator> find_ends(const ustring& pattern, const iterator& before) const;
iterator rfind(const ustring& pattern) const;
iterator rfind(const ustring& pattern, const iterator& before) const;

bool contains(const ustring& pattern) const;
bool starts_with(const ustring& pattern) const;
bool ends_with(const ustring& pattern) const;

ustring substr(const iterator& start, const iterator& end) const;
ustring substr(const pair<iterator, iterator>& ends) const;
```
 While the lack of random access precludes `operator[]` or `at()` ustring still implements `find()` and `rfind()` as well as `starts_with()`,
`ends_with()` and `contains()`. It would be possible to implement `front()` and `back()` but these are pretty useless for strings, especially immutable strings.

To avoid having to redo the scan over the pattern there are versions of `find()` and `rfind()` that return pairs of
iterators delimiting the start and end of the part of the ustring that matches the pattern. Note that if the pattern and the ustring
have different encodings the number of bytes between the returned  iterators may not be the same as the byte count of the pattern.

`find()` and `rfind()` take an _iterator_ as the optional pos argument and return iterators, which allows tokenization, split and similar
tasks to be performed as efficiently as for random accessible strings.

The `find_ends()` and `rfind_ends()` functions' names can be discussed as well as the idea of returning the iterators as a pair. It would be more logical to return a span, but impossible as a span has an `operator[]` which can't be implemented. What we would need is a span between two bidirectional iterators, which may be possible to get by specializing span on the iterator category using CTAD or maybe more reasonably by implementing a separate ustring_span class, or intermediately a bidirectional_span class.

A `substr()` function taking two iterators (where the second defaults to `end()`) returns a ustring representing a subset of the
original string. While still being a complete ustring some implementations may use reference counting to reduce copying in this
case.

It would be possible to add a `size()` member function but this has the drawback that it could be linear in time for some encodings which have to look through the string to be able to know the number of code points. An advanced idea would be to let size() cache the result and that succeeding calls to `end()` would return iterators with index set to the size, thus allowing subtraction with iterators emanating from a `begin()` call. A drawback with this idea is that the size would have to be stored as an extra member in each ustring, even if it is not used. This suggests that there could be a `sized_ustring` class which provides this additional functionality and calculates the size on construction. As most constructors have to at least copy the bytes counting the code points is usually not a big extra cost. Adding an extra class is however quite a big effort.

The `span` class has two member functions `first()` and `last()` which complement `subspan()`to get the first or last N elements. This could be treated as a precedent for including functions corresponding to the traditional `left()` and `right()` of many string classes. Given that writing order varies in different languages first and last are better names. These are of course just shortcuts to the substr(i) and substr(0, i) we already love to hate.

```C++
ustring first(const iterator& upto) const;
ustring last(const iterator& from) const;
```



## Utility free functions

To make ustring easier to use a number of free functions are proposed. Note that the reasons for not having functions which need to know isspace and do tolower or toupper on characters for basic_string and basic_string_view are not present for ustring which works in code points. The fixed encoding specialization of basic_string would be able to accommodate these too, but assuming that somewhere there is a character in some encoding which changes byte count when made upper or lower case this would be less interesting to do in situ.

```C++
strong_ordering compare(const ustring& lhs, const ustring& rhs);
strong_ordering lexicographical_compare(const ustring& lhs, const ustring& rhs, locale& loc);
strong_ordering case_insensitive_compare(const ustring& lhs, const ustring& rhs, locale& loc);

ustring trim_front(const ustring& src);
ustring trim_back(const ustring& src);
ustring trim(const ustring& src);       // Trim both ends.

ustring tolower(const ustring& src, locale& loc);
ustring toupper(const ustring& src, locale& loc);
ustring capitalize(const ustring& src, locale& loc);

ustring insert(const ustring& source, 
               ustring::iterator start, 
               const ustring& replacement);
ustring replace(const ustring& source, 
                ustring::iterator start, 
                ustring::iterator end, 
                const ustring& replacement);
ustring replace(const ustring& source, 
                const pair<ustring::iterator, ustring::iterator>& ends,
                const ustring& replacement);
ustring replace(const ustring& source, const ustring& pattern, 
                const ustring& replacement,
                size_t max_count = numeric_limits<size_t>::max());

ustring erase(const ustring& source, ustring::iterator start, ustring::iterator end);
ustring erase(const ustring& source, const pair<ustring::iterator, ustring::iterator>& ends);

vector<ustring> split(const ustring& src, 
                      const ustring& delimiter, 
                      size_t max_count = numeric_limits<size_t>::max(),
                      bool trim = false, 
                      bool noempties = false);

ustring join(const vector<ustring>& parts, const ustring& delimiter);
```

Note that these functions are either comparing two ustrings on equal footing or returning an ustring.

While some languages like Python has member functions that return manipulated strings it is rather unintuitive for a immutable string class. Instead we provide some free functions to do these types of manipulations, which hopefully indicates that the result is returned (it can also be made [[nodiscard]]).

One could argue that `substr()` should also be a free function by this rule, but it is a member function to match other string classes mostly, but also as it would otherwise have to be a friend.

All the free functions are implemented through `ustring::find()`, `ustring::substr()` and `ustring::operator+()`. This means that with a reference counting and piece-handling implementation no copying of the character data is done by these functions. While this sounds great it may also reduce iteration performance if a lot of small pieces are concatenated by repeated calls to this type of functions (or operator+() in general). Implementations can implement policies to coerce small pieces into larger memory blocks and allocate extra storage to be able to do so.

Maybe there are split and join functionality in the ranges library that can be used sooner or later. Maybe the syntax for doing so is too hard to use for most programmers.

## Overloaded free functions

As ustring iterators have the peculiar feature that advance and distance operations can be quick or slow depending on the internal storage selected special overloads of at least the following free functions are required to make use of that performance optimization. These just call suitable methods in the iterators, maybe after cloning them.

```C++
size()
ssize()
next()
prev()
advance()
distance()
```

There could be more. Note that the corresponding customization points in the ranges:: namespace forwards to these functions by default (I assume). There is also a three parameter `ranges::advance()` overload which corresponds to the two parameter `advance()` of ustring::iterator in that its third parameter is a sentinel beyond which no further advancing occurs. This overload returns the number of steps that _could not_ be taken due to hitting the sentinel, which would be very impractical for ustring where you mainly want to measure the distance between iterators this way. 

**Rant:** Intuitively I think this is a mistake in the ranges::advance() specification, it would be more useful to return the number of steps actually taken also in this case, as you would normally have to write numeric_limits<size_t>::max() as the n parameter and then subtract the result from numeric_limits<size_t>::max() to get the number of steps taken.  

Extraction
----------

There are several ways to extract the contents of an `ustring`, which differ in performance and convenience.

### Conversion to basic_string

Just as for filesystem::path there are five access methods which return the ustring contents as different basic_string
specializations, after conversion from the current internal representation. For the benefit of code templated on a character type a template function called `basic_string()` is also included, just as for `std::filesystem::path`. This template function also allows for allocator and char traits class to be specified.

```C++
template<character T> std::basic_string<T> basic_string(T bad_char = '?') const;
std::string string(char bad_char = '?') const;
std::wstring wstring() const;
std::u8string u8string() const;
std::u16string u16string() const;
std::u32string u32string() const;
std::string string(locale& loc) const;
```

There is also a version of the `string()` function which takes a locale object and uses its codecvt facet to convert the data before returning it as a `std::string`.

### Accessing the internal representation

There is also a `data()` function to get a pointer to the internal representation of the string contents. This function is templated and will return nullptr if the internal representation does not match the template parameter. To aid in using `data()`  there is a function `encoding()` with an accompanying enum type.

To allow for piecewise storage it is possible that *all* of these data() specializations return nullptr for a given ustring, so portable code must include another method of extraction if nullptr is returned. In this case `encoding()` returns `encoding_t::other`.

There is also a universal `data()` overload which returns a byte*. The reason for selecting this type is that no predefined basic_string specialization can be constructed from it, preventing accidents if the explicit typename parameter of the templated `data()` is forgotten. This function returns nullptr if the ustring uses piecewise storage or is empty.

Along with the `data()` function there is a `bytes()` function which returns the number of bytes required for the internal representation data, and which returns npos if the ustring is using piecewise storage.

```C++
encoding_t encoding() const;
template<character T> const T* data() const;

const byte* data() const;
size_t bytes() const;
```

### Copying to user buffer

A third way to extract contents is to use a special copy method to which a buffer pointer and length is provided. This is similar to
the set of basic_string functions but is more efficient if a buffer is already available to store the string in. Another option would be
to use a basic_string instance as a safer buffer and call the method `fill()`. This is safer as the ustring method can resize the
basic_string to avoid overrun, when it notices that it is too short. The advantage is that the buffer is reused, only resized when needed. This can be important if for instance writing a file in UTF-8 from a vector of ustrings which may have different encodings. If the individual ustrings are of about the same length after conversion to UTF-8 the std::string used as buffer will only have to be reallocated a few times.

```C++
template<character T> 
size_t estimated_size(safety_margin margin = guaranteed) const; 

template<character T> 
size_t copy(T* dest, size_t count, T bad_char = '?') const;

template<character T, 
size_t SZ> span<T> copy(span<T, SZ> dest, T bad_char = '?') const;

template<character T> 
void fill(basic_string<T>& dest) const;

void fill(string& dest, locale& loc) const;
```

There is an additional overload for filling a pre-existing std::string using a certain locale.

### Using the ustring::saver class

A fourth way to extract data is piece by piece. This is useful if the string is very long and is to be written to a file or sent as
a stream of packets on a network. The ustring::saver class which contains the
state needed as well as the iterator to the next code point in the ustring. This makes the API nicer than that of
`codecvt::in()` and `codecvt::out()` functions with their long parameter lists. 

```C++
class ustring::saver {
public:
    enum result { ok, partial, incomplete, error };
    ustring_saver(locale& loc, const ustring& src);
    ustring_saver(ustring::encoding_t encoding, const ustring& src);

    size_t fill(byte* buffer, size_t sz, char32_t bad_char = '?');
    result fill_exact(byte* buffer, size_t& sz);
};
```



This problem is a bit easier than the ustring::loader as it can be defined that `fill()` returns somewhat less than sz if the next
code point can't fit the buffer. Only if `fill()` returns 0 is the conversion finished. This mostly requires one extra call to
`fill()` which returns 0 immediately. To handle the case that the ustring contains a character that can't be represented 

As an alternative `fill_exact()` can be called, which could be useful when a network protocol requires exactly sized packets (except
the last one) or when disk access is to be optimized by writing block size chunks. In this case the `result` type is returned: ok
means that the entire source string has been converted and sz may have been adjusted if ok was returned.

This API needs further polishing. A span and maybe a `std::string&` overload of the fill methods should be added. Maybe just one
`fill()` function with an extra bool exact flag is better. *However, as a general rule, it is better to have more names than flag
modes if it is apparent that those flags will always be given the values true or false at each call site in the source code. I think
mode parameters are often added to avoid bike shedding discussions about the names.*

## Interoperability with other parts of the library

To be accepted it must be easy to use `ustring` with other part of the C++ library such as iostreams, `std::string` based functions,
`std::filesystem::path`, `std::format` and others. 

### std::filesystem::path

If `std::filesystem::path` got a implicit constructor for ustring this would allow filenames stored in ustring to be used whenever a
path is required. Typically such places (such as `fstream::open()`) have path and string overloads but as long as string does not
have a `ustring` constructor this does not cause any ambiguity. Similarly `ustring` should have a constructor from
`std::filesystem::path` which may select to retain the same encoding as path uses internally.

### Functions available for std::string and/or std::wstring

As for functions dealing in `std::string` or `std::wstring`, such as `std::to_string` and the `stoi` group there are different
problems. 

For functions returning std::string but where the strings are known to contain ASCII only there could be significant overhead if a
`std::string` is first constructed and then converted to `ustring`. Even if the rvalue constructor could potentially take ownership
of the `std::string` and its implementation heap block this can't happen if the operating system encoding requires a call to a
conversion function, as the constructor does not know the origin of the `std::string`. This suggests that there should be a
`to_ustring()` function overload set parallel to the current to_string.

For functions taking a std::string as parameter adding a `.string()` at each call site is both tedious and inefficient, due to the
same reasons as for the return value case. Here it is however easier as overloads can be added taking `ustring`. However, this could
be a problem in that adding an overload to a function like `stoi()` would make calls with a string literal ambiguous, if ustring
would have an implicit constructor from const char*. To avoid this ustring constructors from character pointers are explicit. (This
also helps remind programmers to use the more efficient ustring literals).

### std::format()

Interoperability with `std::format`() has several aspects. Firstly the format string could be an ustring (often created using an
ustring literal, presumably). By convention this controls the type of the returned string. This does not seem to create any trouble,
really. Second, ustring values must be possible to format by putting them in the argument list of a format() call, without requiring
a ustring as the format string. This entails conversion, which for the char overload could fail. 

Currently `std::format()` is not templated on the format string type, instead there are only two function overloads, which take
format strings convertible to `string_view` and `wstring_view` respectively and return `std::string` and `std::wstring`. The type of
the format string parameter is unspecified which opens up to compile time format string validation, which we will likely get in
C++23. As std::format() is often used to create strings to present to a human reader the result strings will often be sent to
operating system or GUI components. This shows that an additional literal operator which creates a ustring with storage optimized
for the operating system the code is compiled for would be of interest. This could be spelled `""o` for optimized literal or
something like that. Given that the ustring implementation adapts its internal storage to the literal encoding this ensures that
when the ustring is later used to produce a operating system call parameter no conversion is needed.

It should be fairly straight-forward to implement a ustring based overload of std::format(). The overload would have to take a
ustring directly as the `""u` literals return a ustring rather than a CharT pointer for some CharT.

It is however a bit unclear why this would be a good thing. Probably the greatest advantage would be that it simplifies portability
where you today would want to use a char based format string as everything is UTF-8 anyway, and on Windows you would use a wide
format string if the result is to be displayed for instance in a Windows GUI which natively is UTF-16 (wchar_t is for UTF-16 on
Windows).

As for a ustring *formatter* specialization there seems to be no big hurdles. The formatting context provides a locale. Some
optimizations aside when locale matches internal storage the ustring can at least be copied to a buffer and from there to the
OutputIterator provided by the format_context. It is not very clear on CppReference but it seems that the formatter should have two
overloads of the format() function for a char and wchar_t format_context respectively, or a template that handles all character
types. From reading some of the source code of the fmt library it was deduced that the OutputIterator in fmt is not a regular output
iterator but provides access to a resizable buffer. Thanks to this the overhead of a normal back_inserter_iterator can be avoided.
Presuming that std::format has a similar implementation and as ustring will be part of the standard library a high performance
formatter should be fairly easy to achieve.

## Allocator support

It would be possible to make ustring a class template with the allocator as a template parameter. However, this is not proposed
initially, taking the cue from `std::filesystem::path` which also lacks allocator support.

Another aspect is allocator support for the constructors from other string types and the member functions returning such strings.
Again `std::filesystem::path` is used as a model and only the default allocator is supported. 

