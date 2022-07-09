/*

Test implementation of a ustring class for possible introduction into the C++ standard library.

* This implementation stores most incoming strings in their original representation, deferring conversion until the string contents
  is retrieved using iterators or extracted into another format.

* The implemenation also uses the possibility to refer to literals if the _u literal suffix is used (u
  also available if IS_STANDARDIZED is set, but currently generates warnings on some compilers).

* The implementation implements concatenation by referrring to different parts rather than copying them. The number of parts is
  limited to 64 and currently there is no mechanism to coerce the parts together if this limit is reached.

* For char bases "narrow" encodings an attempt is made to create a lookup table from char value to Unicode code point. If this
  succeeds the implementation retains this table in a global map and refers to it from each ustring created for that encoding. If
  no table can be created (i.e. if there are multibyte code points) the incoming string is converted to an UTF-8 ustring
  representation.

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


#pragma once

#include <cctype>
#include <cstdint>
#include <cstring>
#include <string>
#include <atomic>
#include <cassert>
#include <limits>
#include <vector>
#include <span>
#include <locale>
#include <map>
#include <iostream>

#if IS_STANDARDIZED

#define STD std
namespace std {

#else

#define STD stdx
namespace stdx {

using namespace std;

#endif

#ifndef HAS_NPOS
#define HAS_NPOS
    // A npos at namespace level allows checking for npos without caring about "which" npos to check against -- and it is shorter to write std::npos than std::string::npos.
    inline constexpr const size_t npos = static_cast<size_t>(-1);
#endif

    namespace detail {
    template <typename... Args>
            constexpr bool dependent_false = false;
    template <auto... Args>
            constexpr bool dependent_false_v = false;
    }


// type_trait to detect a character type, which is strangely missing from the current standard.
template<typename T> struct is_character : bool_constant<false> {};
template<> struct is_character<char> : bool_constant<true> {};
template<> struct is_character<wchar_t> : bool_constant<true> {};
template<> struct is_character<char8_t> : bool_constant<true> {};
template<> struct is_character<char16_t> : bool_constant<true> {};
template<> struct is_character<char32_t> : bool_constant<true> {};

template<typename T> constexpr bool is_character_v = is_character<T>::value;

template<typename T> concept character = is_character_v<T>;

namespace detail {
    template<typename I, typename E> class filler_impl;
}

class ustring {
public:
    using value_type = char32_t;
    using size_type = size_t;
    using difference_type = ptrdiff_t;
    using reference = char32_t;

    class iterator;
    using const_iterator = iterator;
    using reverse_iterator = reverse_iterator<iterator>;
    using const_reverse_iterator = reverse_iterator;

    template<character E> class filler;
    class loader;
    class saver;

    // Each ustring is conceptually encoded using one of the encodings corresponding to a char type. The narrow encoding
    // is the execution encoding of the compile, as specified on the compiler command line. If the ustring was constructed directly
    // from a ""u literal, a basic_string or a character pointer with or without length the encoding will retain the corresponding
    // encoding. In all other cases, including concatenation, the ustring may use the 'multiplart' encoding which means that it is not
    // possible to use data() to retrieve a pointer to the contents.
    enum encoding_t : uint8_t {
        utf8,           // type is char8_t, encoding is UTF-8
        utf16,          // type is char16_t, encoding is UTF-16
        utf32,          // type is char32_t, encoding is UTF-32
        wide,           // type is wchar_t, encoding is UTF-16 on Windows, UTF-32 elsewhere.
        execution,      // type is char, encoding is execution character set, which is convertible to Unicode by table lookup
        system,         // type is char, encoding is system character set, which is convertible to Unicode by table lookup
        single,         // type is char, constructed from some other locale with table lookup possibility than execution or system.
        multipart       // ustring is multipart, no direct access is possible.
    };

private:

    struct impl;

    // Extra pointers store 6 bits of extra data in bit 62 - 57 which are always equal for all known x64 and Arm8a processors due to
    // limitations in the pager (Arm8a has 15 usable bits actually). 
    // %%This should be reimplementd using an extra byte for the extra data for 32 bit architectures. Unfortunately this will expand to
    // 8 bytes due to alignment of 4 byte values, but maybe that's ok as it will make the soo areas the same size as with 64 bit pointers.
    template<typename EX, typename P> class extra_ptr {
    public:
        static_assert(sizeof(EX) <= sizeof(size_t));
        static const int max_extra = 63;

        extra_ptr(EX extra, const void* ptr) : m_data(size_t(ptr) & 0x81FF'FFFF'FFFF'FFFF | (size_t(extra) << 57)) {
            assert(size_t(extra) <= max_extra);
        }

        P* ptr() {
            if (m_data & 0x8000'0000'0000'0000)     // Make sure top byte has 6 bits equal to mask the storage of the current part index.
                return reinterpret_cast<P*>(m_data | 0xFE00'0000'0000'0000);
            else
                return reinterpret_cast<P*>(m_data & 0x01FF'FFFF'FFFF'FFFF);
        }
        const P* ptr() const { return const_cast<extra_ptr*>(this)->ptr(); }
        EX extra() const {
            return EX((m_data >> 57) & max_extra);
        }

    private:
        size_t m_data;
    };

    using part_ptr = extra_ptr<uint8_t, byte>;

    // Compressed mode class containing a two bit storage field, a three bit character encoding field and a table flag.
    class mode {
    public:
        enum storage_t : uint8_t {
            shared,     // Shared implementation block containing the refcount, length and character data.
            multi,      // Shared implementation block containing a number of concatenated ustring objects.
            soo,        // Characters stored inside the ustring object and deep copied on each copy.
            literal     // Characters retained in the original literal data.
        };

        mode() : mode(soo, single, false) {}
        mode(size_t v) : m_data(uint8_t(v) << 1) {}    // Used in mode_ptr.
        mode(storage_t storage, encoding_t encoding, bool table) : dummy(0), m_storage(storage), m_encoding(encoding), m_table(table), dummy2(0) {}

        storage_t storage() const { return m_storage; }
        encoding_t encoding() const { return m_encoding; }
        encoding_t normalized_encoding() const;  // Never return wide, return utf16 or utf32 depending on OS. Never return system or execution, instead return single (Which means that has_table() must be checked).

        bool is_shared() const { return storage() == shared || storage() == multi; }
        bool has_table() const { return m_table; }

        operator uint8_t() { return m_data >> 1; }
    private:
        union {
            uint8_t m_data;         // Note: low and high bits not usable as we must read the mode before knowing if it is embedded in a extra_pointer.
            struct {
                uint8_t dummy : 1;
                storage_t m_storage : 2;
                encoding_t m_encoding : 3;
                bool m_table : 1;
                uint8_t dummy2 : 1;
            };
        };
    };

    using table_ptr = extra_ptr<mode, char32_t>;
    using impl_ptr = extra_ptr<mode, impl>;

    template<encoding_t E> struct encoding_type_detail {
        static_assert(detail::dependent_false_v<E>, "Bad enum value to ecoding_type");         // Error to use base case
        using type = void;   // Silence Clang.
    };

public:
    // Bidirectional const iterator. When created from the end we can't reliably know if size can be calculated by subtraction.
    // Oddly, iterators know the extent of the underlying string. This allows advance() to stop at the end, thus providing a way to
    // calculate size. This is used for the multi storage mode where code points are not contiguous, and must be known to be able to step to the next/previous part at ends of one part.
    // At the same time allows iterator bounds checking.
    class iterator {
    public:
        using iterator_tag = bidirectional_iterator_tag;

        iterator(const ustring& str, part_ptr pos);

        char32_t operator*() { return m_current; }      // 0 at end, but there can also be embedded nul characters if the application puts any in there.

        iterator& operator++();
        iterator operator++(int);
        iterator& operator--();
        iterator operator--(int);

        // You can compare iterators derived from begin() to iterators derived from end() as comparison is by address.
        bool operator==(const iterator& rhs) const;
        strong_ordering operator<=>(const iterator& rhs) const;

        // There are options for operator- including: a) removing it, b) only allowing it if both iterators start out from the same
        // end, c) only allowing it if both iterators start out from the same end _or_ the encoding is fixed length, or d) let it take
        // time if it needs, using advance under the hood.
        ptrdiff_t operator-(const iterator& rhs) const;

        iterator operator+(ptrdiff_t by) const;
        iterator& operator+=(ptrdiff_t by);

        // Similar to operator+ but clamps to begin and end if by would leave us out of range. This can be used to implement
        // size and similar operations. Return false if either end was hit.
        void advance(ptrdiff_t by);
        size_t advance(const iterator& towards, size_t by);
        size_t advance(const iterator& to);

        // Iterators know their position in the string, counted from begin or end. Negative indices indicate counting from
        // the end, with -1 after the last character (unfortunately).
        ptrdiff_t index() const { return m_index; }

    private:
        friend class ustring;
        friend class saver;
        
        const ustring& str() const { return *m_string; }

        // Used by ustring's iterator based ctor.
        const byte* pos() const { return m_pos; }
        uint8_t part() const { return m_part; }
        part_ptr combined_pos() const { return part_ptr(m_part, m_pos); }

        void set_pos(const byte* pos) { m_pos = pos; }
        void set_part(uint8_t part) { m_part = part; }

        // This helper function returns the remaining steps to take in case the part ends.
        ptrdiff_t advance_in_part(ptrdiff_t by, const byte* beg);
        void load();
        void init_part();
        void init_size();

        const ustring* m_string;    // This offers most info we need, including end, table, impl. Also provides easy sanity checking for instance when subtracting iterators. (Check for same impl if mode is shared).
        const byte* m_pos;          // The current iterator position in bytes. For multi storage this is within the part indicated by m_part.
        const byte* m_end;          // To prevent reading outside the string we must check against end in load(). For m_multi this is also used in operator++. Decrementing is considered less common so m_begin is fecthed from m_string each time.
        ptrdiff_t m_index;          // To facilitate size and getting count from iterator subtraction (as long as none or both are from end). Negative numbers indicate iterator derived from end(), -1 means after last char.
        char32_t m_current;         // The current code point returned from operator*. operator++/-- sets the value.

        int8_t m_count;             // # bytes that last load consumed. Unfortunately I don't see a way that this extra member can be avoided, short of storing two positions.
        mode m_mode;                // To guide methods. For multi storage this is reloaded when the part number changes.
        uint8_t m_part;             // Part is extracted from m_pos for multi to speed up indexing.
        bool m_multi;               // Set for multi mode. As m_mode is for the current part this has to be stored separately.
    };

    template<character T> static constexpr encoding_t encoding_of = init_encoding_of<T>();
    template<encoding_t E> using encoding_type = typename encoding_type_detail<E>::type;

    ustring();

    // This uses soo or reference counting depending on src.m_mode.storage().
    ustring(const ustring& src);
    ustring(ustring&& src) noexcept;

    // Ctor from one char
    template<character T> ustring(T c);

    // Ctors from char + count.
    template<character T> ustring(size_t count, T c);

    // Constructors which _copy_ the literals, as these can not be assumed to not be pointers to buffers of changing data.
    // However, null termination is assumed, with respect to element size.
    template<character T> explicit ustring(const T* src);
    ustring(const char* src, const locale& loc);

    // Constructs with copy but does not use strlen.
    // Note that there are no templated array ctors as those would mostly cause unintended lengths when called with
    // C arrays of "sufficent length" used for legacy APIs. Instead let those arrays decay to pointers and call the above ctors
    // which use strlen.
    template<character T> ustring(const T* src, size_t sz);						// Interpreted as execution CS
    ustring(const char* src, size_t sz, const locale& loc);

    // These ctors copy the contents. Parallel ctors for rvalue references could be added, which as QoI could hold an appropriate
    // basic_string as a union member to save allocations/copying.
    template<character T, typename Tr = char_traits<T>, typename Al = allocator<T>>
        ustring(const basic_string<T, Tr, Al>& src, size_t pos = 0, size_t count = npos) : ustring(src.data() + pos, min(src.size() - pos, count)) {}
    template<character T, typename Tr = char_traits<T>, typename Al = allocator<T>>
        ustring(basic_string<T, Tr, Al>&& src) : ustring(src.data(), src.size()) {}           // Optimization not implemented yet.
    template<character T, typename Tr = char_traits<T>>
        ustring(basic_string_view<T, Tr> src, size_t pos = 0, size_t count = npos) : ustring(src.data() + pos, min(src.size() - pos, count)) {}

    // char string based ctors with an extra locale parameter.
    template<typename Tr = char_traits<char>, typename Al = allocator<char>>
        ustring(const basic_string<char, Tr, Al>& src, const locale& loc, size_t pos = 0, size_t count = npos) : ustring(src.data() + pos, min(src.size() - pos, count), loc) {}
    template<typename Tr = char_traits<char>, typename Al = allocator<char>>
        ustring(basic_string<char, Tr, Al>&& src, const locale& loc) : ustring(src.data(), src.size(), loc) {}
    template<typename Tr = char_traits<char>>
        ustring(basic_string_view<char, Tr> src, const locale& loc, size_t pos = 0, size_t count = npos) : ustring(src.data() + pos, min(src.size() - pos, count), loc) {}

    ~ustring() { unref(); }

    //--- operators ---

    ustring& operator=(const ustring& rhs);
    ustring& operator=(ustring&& rhs) noexcept;          // Note: As all ctors are implicit this covers assignment from basic_string<T> too.

    // These create multi implementations if needed. This happens if sum length is not soo or if encodings differ.
    friend ustring operator+(ustring&& lhs, ustring&& rhs);
    ustring& operator+=(const ustring& rhs);
    ustring& operator+=(ustring&& rhs);

    // Compares according to code point order, i.e. using compare()
    bool operator==(const ustring& rhs) const;
    strong_ordering operator<=>(const ustring& rhs) const;

    //--- methods ---

    // Pseudo constructors from string literals used by suffix u literals. Implementations may disable reference counting and
    // no heap storage needs to be allocated. Note that the char version implies _execution_ character set, not system. Also, if
    // it is not possible to get to unicode code points for the execution character set this will create a copy anyway. The
    // view() with locale likewise implies conversion unless a table can be created.
    template<character T> static ustring view(const T*, size_t sz);
    static ustring view(const char*, size_t sz, const locale& loc);
    template<character T> static ustring view(const T* src) { return view(src, len_helper(src)); }
    static ustring view(const char* src, const locale& loc) { return view(src, len_helper(src), loc); }

    // Views of lvalue basic_strings with pos/size to avoid having to mess around with view(str.data() + pos, cnt)
    template<character T, typename Tr = char_traits<T>, typename Al = allocator<T>>
        static ustring view(const basic_string<T, Tr, Al>& original, size_t pos = 0, size_t count = npos) { return view(original.data() + pos, count); }
    template<character T, typename Tr = char_traits<T>>
    static ustring view(const basic_string_view<T, Tr>& original, size_t pos = 0, size_t count = npos) { return view(original.data() + pos, count); }
 
    template<typename Tr = char_traits<char>, typename Al = allocator<char>>
    static ustring view(const basic_string<char, Tr, Al>& original, const locale& loc, size_t pos = 0, size_t count = npos) { return view(original.data() + pos, count. loc); }
    template<typename Tr = char_traits<char>>
    static ustring view(const basic_string_view<char, Tr>& original, const locale& loc, size_t pos = 0, size_t count = npos) { return view(original.data() + pos, count, loc); }

    bool empty() { return get_mode().storage() == mode::soo && m_soo.m_count == 0; }

    // Access.
    iterator begin() const { return iterator(*this, get_begin()); }
    iterator end() const { return iterator(*this, get_end()); }

    // Finding. Note: No complicated versions with pos arguments needed as it is cheap to make a substring from iterators.
    // TODO: Verify by testing usability.
    pair<iterator, iterator> find_ends(const ustring& pattern, const iterator& after) const;
    pair<iterator, iterator> find_ends(const ustring& pattern) const { return find_ends(pattern, begin()); }
    iterator find(const ustring& pattern, const iterator& after) const { return find_ends(pattern, after).first; }
    iterator find(const ustring& pattern) const { return find_ends(pattern).first; }

    pair<iterator, iterator> rfind_ends(const ustring& pattern, const iterator& before) const;
    pair<iterator, iterator> rfind_ends(const ustring& pattern) const { return rfind_ends(pattern, end()); }
    iterator rfind(const ustring& pattern, const iterator& before) const { return rfind_ends(pattern, before).first; }
    iterator rfind(const ustring& pattern) const { return rfind_ends(pattern).first; }

    // These should probably be overloaded with basic_string<T> versions to avoid having to
    // create an ustring from a (lvalue) basic_string first.
    bool contains(const ustring& pattern) const { return find(pattern) != end(); }
    bool starts_with(const ustring& pattern) const;
    bool ends_with(const ustring& pattern) const;

    ustring substr(const iterator& begin, const iterator& end) const;    // Create a substring. By combining with operator+ all kinds of erase, mid, left, right, replace etc. can be created.
    ustring substr(const pair<iterator, iterator>& ends) const { return substr(ends.first, ends.second); }
    ustring first(const iterator& upto) const { return substr(begin(), upto); }
    ustring last(const iterator & from) const { return substr(from, end()); }

    // Convert to basic_string by copying the data. This always works regardless of the internal encoding.
    template<character T, typename Tr = char_traits<T>, typename Al = allocator<T>> basic_string<T, Tr, Al> basic_string(T bad_char = '?') const;
    string string(char bad_char = '?') const { return basic_string<char>(bad_char); }
    wstring wstring() const { return basic_string<wchar_t>(); }
    u8string u8string() const { return basic_string<char8_t>(); }
    u16string u16string() const { return basic_string<char16_t>(); }
    u32string u32string() const { return basic_string<char32_t>(); }

	// Accessing the data in its stored encoding.
    encoding_t encoding() const;                 // Return encoding, but for a multi implementation with different encodings or a non-standard internal representation return encoding_t::other.

	template<character T> const T* data() const; // This checks that T is consistent with the current encoding and returns nullptr if not, or if storage is not contiguous.
	const byte* data() const;        			 // Generic data. encoding must be used to figure out what it means. Returns nullptr for other encoding.
	size_t bytes() const;						 // Number of raw bytes needed. Returns npos for other encoding.

    // Regardless of the encoding of the ustring contents it is always possible to retrieve it in all the encodings
    // corresponding to the different character types. The count parameter indicates the size of dest in Ts. If the entire ustring
    // can't fit in dest a whole number of code points is converted and start is set to point to the next code point.
    // The caller must check if pos == end() to know if the string ended, or try again and get a 0 return.
    // [We could add a second iterator end to control where to stop, but substr is costless so that's not necesssary].
    template<character T> size_t copy(T* dest, size_t count, iterator& start) const;
    size_t copy(char* dest, size_t count, iterator& start, char bad_char = '?') const;
    // Version which converts to the set locale while copying. 
    size_t copy(char* dest, size_t count, const locale& loc, iterator& start, char bad_char = '?') const;

    // Return estimated size needed for copy.
    template<character T> size_t estimated_size() const; 

    // Simplified version which stops when the dest buffer is full. If this happens it returns the size of the buffer and you don't
    // know if it overflowed or was an exact fit.
    template<character T> size_t copy(T* dest, size_t count) const;
    size_t copy(char* dest, size_t count, char bad_char = '?') const;
    size_t copy(char* dest, size_t count, const locale& loc, char bad_char = '?') const;

    // Versions of these which takes a span<char_type> are also provided. Note that the return type is always a span with dynamic
    // extent as the length of the ustring is always dynamic.
    template<character T, size_t SZ> span<T> copy(span<T, SZ> dest, iterator& start) const;
    template<size_t SZ> span<char> copy(span<char, SZ> dest, iterator& start, char bad_char = '?') const;
    template<size_t SZ> span<char> copy(span<char, SZ> dest, const locale& loc, iterator& start, char bad_char = '?') const;

    template<character T, size_t SZ> span<T> copy(span<T, SZ> dest) const;
    template<size_t SZ> span<char> copy(span<char, SZ> dest, char bad_char = '?') const;
    template<size_t SZ> span<char> copy(span<char, SZ> dest, const locale& loc, char bad_char = '?') const;

private:
    template<typename I, typename E> friend class detail::filler_impl;
    template<character T> static constexpr encoding_t init_encoding_of();
    static size_t len_helper(const char* ptr) { return strlen(ptr); }
    static size_t len_helper(const wchar_t* ptr) { return wcslen(ptr); }
    static size_t len_helper(const char8_t* ptr) { return strlen(reinterpret_cast<const char*>(ptr)); }
    static size_t len_helper(const char16_t* ptr);
    static size_t len_helper(const char32_t* ptr);

    mode get_mode() const { return m_soo.m_mode; }
    void set_mode(mode::storage_t storage, encoding_t encoding, bool table) { m_soo.m_mode = mode(storage, encoding, table); }
 
    part_ptr get_begin() const;
    part_ptr get_end() const;
    const char32_t* get_table(uint8_t part) const;
    const ustring& get_part(uint8_t part) const;
    ustring& get_part(uint8_t part);
    const impl& get_impl() const;
    impl& get_impl();

    byte* setup(size_t sz, encoding_t encoding, const char32_t* table = nullptr);
    template<typename T> T* setup(size_t count, encoding_t encoding = encoding_of<T>, const char32_t* table = nullptr) {
        return reinterpret_cast<T*>(setup(count * sizeof(T), encoding, table));
    }
    // Prevent forgetting encoding for char buffers.
    template<> char* setup<char>(size_t count, encoding_t encoding, const char32_t* table) { return reinterpret_cast<char*>(setup(count, encoding, table)); }

    void shrink_to(const void* end);
    void init(const void* src, size_t sz, encoding_t encoding);
    void init(const void* src, size_t sz, const char32_t* table, encoding_t encoding);

    static impl* make_multi_impl(int count);
    static impl* make_impl(size_t bytes);
    static impl* make_impl(const char32_t* table, size_t bytes);
    bool try_append(const ustring& rhs);
    bool try_prepend(const ustring& lhs);
    void unref();

    template<character T> size_t copy_part(T* dest, size_t count, iterator& start) const;
    size_t copy_part(char* dest, size_t count, iterator& start, char bad_char) const;

	union {
		struct {    // Long strings with shared data. m_start/m_end are needed for substrings. Also used for multi storage.
            const byte* m_begin;        // The start of the part of the shared string that this instance can access.
			const byte* m_end;          // The end position.
            impl_ptr m_impl;               // High byte contains mode, this must be anded off to get to the impl.
		} m_shared;
        struct {    // Long strings with shared data. m_start/m_end are needed for substrings. Also used for multi storage.
            part_ptr m_begin;           // The part number and pointer in that part that this ustring can access
            part_ptr m_end;             // The end position.
            impl_ptr m_impl;               // High byte contains mode, this must be anded off to get to the impl.
        } m_multi;
		struct {    // short string case. This union member used for execution encodings and utf encodings.
            uint8_t m_count;   		    // Number of valid bytes.
            byte m_data[22];
			mode m_mode;				// One byte mode info. If top 2 bits are 0 mode is shared. Thus it can be overlayed with m_end which always has c_block_bits top bits cleared.
		} m_soo;
        struct {    // This case is used for short strings which need a table lookup.
            uint8_t m_count;			// Number of valid bytes.
            byte m_data[15];            // Up to 15 bytes of raw data.
            table_ptr m_table;			// Table of mappings from 8 or 16 bit data to code points for "code page" local encodings. (High byte must be anded away.
        } m_soo_table;
        struct {    // Literal case. Encodings can only be execution or utf
            const byte* m_begin;
            const byte* m_end;
            table_ptr m_table;           // Table of mappings from 8 or 16 bit data to code points for "code page" local encodings. (High byte must be anded away.
        } m_literal;
	};
};

// Helper class used to build a ustring from buffers in any locale's narrow encoding. Useful when the entire source string is not
// available at one time.
// There should be a ctor which takes a ustring::encoding_t also to bypass the conversion using codecvt when we know that the
// encoding is one of the built in ones.
class ustring::loader {
public:
    loader(const locale& loc, size_t source_size = 0);

    bool append(const char* buffer, size_t sz);     // Return false if an illegal char was encountered in the input

    bool is_complete() const { return m_complete; }     // False if state is in the middle of a code point after append.

    // To preserve the immutability you can only move the actual string out once.
    ustring str()&&;

private:
    void reallocate(size_t sz);     // sz is the number of source bytes lacking.

    ustring m_str;
    locale m_locale;
    mbstate_t m_state{};

    size_t m_source_size = 0;
    size_t m_allocated_size = 0;
    size_t m_capacity_left = 0;
    size_t m_consumed_so_far = 0;
    byte* m_buffer = nullptr;
    bool m_complete = true;
};


// Helper class used to convert a ustring of any encoding to one or more external buffers of any locale supported encoding.
// There should be a ctor which takes a ustring::encoding_t also to bypass the conversion using codecvt when we know that the
// encoding is one of the built in ones.
class ustring::saver {
public:
    saver(const locale& loc, const ustring& src, char bad_char = '?');
    saver(const locale& loc, const ustring& src, const ustring::iterator& start, char bad_char = '?');

    enum safety_margin {
        minimal,                // Basically the length if everything turns out to be ASCII
        reasonable,             // With some margin for a reasonable mix of latin1 characters
        probable,               // With some more margin for a mixture of ucs2 characters
        guaranteed              // Guaranteed to fit the entire string. For instance 4x the ustring byte count, but in some cases it is known to be lower.
    };

    size_t estimated_size(safety_margin) const;        // Return an estimate of how many bytes will be needed for the entire ustring converted to loc, given different safety margins.

    // The return value 'partial' indicates that the entire src string has not been stored in buffers of this and preceeding fill
    // calls. error indicates conversion error as usual and ok means that the entire string has been converted. In both partial
    // and ok sz is changed to reflect how much of the buffer has been filled. For partial this could be a few bytes less than the
    // entire buffer if the result of converting one more code point would not fit the buffer. For ok return sz is set to indicate
    // where the converted data ends.
    codecvt_base::result fill(char* buffer, size_t& sz);

private:
    const ustring& m_source;
    ustring::iterator m_pos;
    size_t m_consumed;
    locale m_locale;
    mbstate_t m_state{};
    char m_bad_char;
};


// Literal operators
namespace literals::string_literals {
    // Note: Can't be made a template as that would be interpreted as a compile time literal operator.
    inline ustring operator""_u(const char* ptr, size_t sz);
    inline ustring operator""_u(const wchar_t* ptr, size_t sz);
    inline ustring operator""_u(const char8_t* ptr, size_t sz);
    inline ustring operator""_u(const char16_t* ptr, size_t sz);
    inline ustring operator""_u(const char32_t* ptr, size_t sz);

#ifdef IS_STANDARDIZED

    inline ustring operator""u(const char* ptr, size_t sz);
    inline ustring operator""u(const wchar_t* ptr, size_t sz);
    inline ustring operator""u(const char8_t* ptr, size_t sz);
    inline ustring operator""u(const char16_t* ptr, size_t sz);
    inline ustring operator""u(const char32_t* ptr, size_t sz);

#endif

}


inline ostream& operator<<(ostream& os, const ustring& src)
{
    ustring::saver s(os.getloc(), src);

    char buffer[1000];
    while (true) {
        size_t sz = 1000;
        auto res = s.fill(buffer, sz);
        os.write(buffer, sz);
        if (res != codecvt_base::partial)
            break;
    }

    return os;
}

// Free helper functions. As we are working in unicode code points these can be implemented for international use.

// Compare char32_t values. This gives some kind of ordering but not necessarily a lexicograpically correct ordering for a
// particular locale.
inline strong_ordering compare(const ustring& lhs, const ustring& rhs) { return lhs <=> rhs; }
strong_ordering lexicographical_compare(const ustring& lhs, const ustring& rhs, const locale& loc = locale());
strong_ordering case_insensitive_compare(const ustring& lhs, const ustring& rhs, const locale& loc = locale());

// Probably trimming does not need to know locale as whitespace unicode code point denotation should be locale indifferent.
ustring trim_front(const ustring& src);
ustring trim_back(const ustring& src);
ustring trim(const ustring& src);		// Trim both ends.

// Helpers for unicode code points. These are probably trivial if wchar_t is 32 bits as it just defers to iswspace but less so for
// 16 bit wchar_t unless all blanks are in the first unicode page. Unclear if we want to make this C function compatible, if so it
// may be called isuspace and there could be a complete set, including touupper and toulower for case conversion.
bool is_space(char32_t);

// May need locale, but unclear. Maybe there are different unicode code points which look the same in fonts if there are cases.
ustring tolower(const ustring& src, const locale& loc = locale(""));
ustring toupper(const ustring& src, const locale& loc = locale(""));
ustring capitalize(const ustring& src, const locale& loc = locale(""));


ustring insert(const ustring& source, ustring::iterator start, const ustring& addition);

ustring replace(const ustring& source, ustring::iterator start, ustring::iterator end, const ustring& replacement);
ustring replace(const ustring& source, pair<ustring::iterator, ustring::iterator> where, const ustring& replacement);
ustring replace(const ustring& source, const ustring& pattern, const ustring& replacement, size_t max_count = numeric_limits<size_t>::max());

ustring erase(const ustring& source, ustring::iterator start, ustring::iterator end);
ustring erase(const ustring& source, const pair<ustring::iterator, ustring::iterator>& ends);

// Split with some mode flags. Keeping flags at default ensures that the original string is recreated by join with the same
// delimiter.
vector<ustring> split(const ustring& src, const ustring& delimiter, size_t max_count = numeric_limits<size_t>::max(), bool trim = false, bool noempties = false);
ustring join(const vector<ustring>& parts, const ustring& delimiter);


//////////////// Impl struct must be defined before methods that use it. ////////////////

struct ustring::impl {
    // There must be a default ctor and dtor of any struct containing a union.
    impl() {}       // The different ustring ctors and other methods set my fields up, except m_refs.
    ~impl() {}      // Note: It is the ustring dtor (which knows the mode) that actually destroys valid m_strings elements

    atomic<uint32_t> m_refs = 1;        // Should be enough.
    union {
        byte m_data[1];
        struct {
            const char32_t* m_table;			// Table of mappings from 8 or 16 bit data to code points.
            byte m_data[1];			// C style tail.
        } m_table;
        struct {
            uint8_t m_count;      // Max is 63 as the part numbers are stored inside pointers.
            uint8_t m_capacity;  // May allocate some at a time in anticipation of further concatenations. Beware however that the string is immutable so this can only happen with refcount == 1 and rvalue lhs of op+.
            ustring m_strings[1]; // Strings are destroyed by last ustring owning this impl. Note: Not constructed as it is in a union.
        } m_multi;
    };
};


//////////////// Method implementations ////////////////

namespace detail {

    inline uint8_t decode(char32_t& dest, const char8_t* src)
    {
        if ((src[0] & char8_t(0x80)) == char8_t(0)) {
            dest = char32_t(src[0]);
            return 1;
        }
        else if ((src[0] & char8_t(0xe0)) == char8_t(0xc0)) {
            dest = (char32_t(src[0] & char8_t(0x1f)) <<  6) |
                   (char32_t(src[1] & char8_t(0x3f)) <<  0);
            return 2;
        }
        else if ((src[0] & char8_t(0xf0)) == char8_t(0xe0)) {
            dest = (char32_t(src[0] & char8_t(0x0f)) << 12) |
                   (char32_t(src[1] & char8_t(0x3f)) <<  6) |
                   (char32_t(src[2] & char8_t(0x3f)) <<  0);
            return 3;
        }
        else if ((src[0] & char8_t(0xf8)) == char8_t(0xf0) && (src[0] <= char8_t(0xf4))) {
            dest = (char32_t(src[0] & char8_t(0x07)) << 18) |
                   (char32_t(src[1] & char8_t(0x3f)) << 12) |
                   (char32_t(src[2] & char8_t(0x3f)) <<  6) |
                   (char32_t(src[3] & char8_t(0x3f)) <<  0);
            return 4;
        }

        throw std::runtime_error("Illegal UTF-8 code element combination");
    }

    inline uint8_t decode(char32_t& dest, const char16_t* src)
    {
        char32_t tmp = src[0];
        if (tmp >= 0xd800 && tmp < 0xe000) {   // Note: don't care which order the surrogates are or if they are actually different in the high bits.
            uint32_t next = src[1];
            if (next >= 0xd800 && next < 0xe000) {
                dest = (((tmp << 10) + next) & 0xFFFFF) + 0x10000;
                return 4;
            }
            else {
                throw std::runtime_error("Illegal UTF-16 code element combination");
            }
        }

        dest = tmp;
        return 2;
    }

    inline uint8_t decode(char32_t& dest, const char32_t* src)
    {
        dest = *src;
        return 4;
    }

    // For ASCII source only.
    inline uint8_t decode(char32_t& dest, const char* src)
    {
        assert((*src & 0x80) == 0);
        dest = *reinterpret_cast<const uint8_t*>(src);
        return 1;
    }

    // These internal methods must be defined before copy.
    inline bool encode(char8_t*& d, const char8_t* e, char32_t c)
    {
        if (c < 128) {
            if (d == e)
                return false;

            *d++ = char8_t(c);
        }
        else if (c < (1 << 11)) {
            if (d + 1 >= e)
                return false;

            d[0] = 0xC0 | (c >> 6);
            d[1] = 0x80 | (c & 0x3f);
            d += 2;
        }
        else if (c < (1 << 17)) {
            if (d + 2 >= e)
                return false;

            d[0] = 0xE0 | (c >> 12);
            d[1] = 0x80 | ((c >> 6) & 0x3f);
            d[2] = 0x80 | (c & 0x3f);
            d += 3;
        }
        else {
            if (d + 3 >= e)
                return false;

            d[0] = 0xF0 | ((c >> 18) & 7);          // Ignore upper 11 bits for now
            d[1] = 0x80 | ((c >> 12) & 0x3f);
            d[2] = 0x80 | ((c >> 6) & 0x3f);
            d[3] = 0x80 | (c & 0x3f);
            d += 3;
        }

        return true;
    }

    inline bool encode(char16_t*& d, const char16_t* e, char32_t c)
    {
        if (c < (1 << 16)) {
            if (d == e)
                return false;

            *d++ = char16_t(c);     // Ignore that c values in range 0xd800 - 0xe000 are illegal.
        }
        else {
            if (d + 1 >= e)
                return false;

            *d++ = 0xd800 | ((c >> 10) & 0x3ff);  // Ignore upper bytes
            *d++ = 0xdc00 | (c & 0x3ff);
        }

        return true;
    }

    inline bool encode(char32_t*& d, const char32_t* e, char32_t c)
    {
        if (d >= e)
            return false;

        *d++ = c;
        return true;
    }


    // ASCII only
    inline bool encode(char*& d, const char* e, char32_t c)
    {
        if (d >= e)
            return false;

        assert(c < 128);
        *d++ = char(c);
    }


    // Convert as little as possible at from. This is usually one code point, but if I == E it is one code element.
    template<character C> bool transcode(C*& to, const C* end, const C*& from)
    {
        if (to == end)
            return false;
        
        *to++ = *from++;
        return true;
    }

    // If character types are different use decode and encode.
    template<character T, character F> bool transcode(T*& to, const T* end, const F*& from)
    {
        char32_t tmp;
        from += decode(tmp, from) / sizeof(F);
        return encode(to, end, tmp);
    }


    // The default ustring representation when filling is typically the same as the E type for UTF-8 and UTF-16. For Windows wchar_t is
    // also UTF-16 but for Linux it is UTF-32 so to save space it is encoded to UTF-8. char always has UTF-8 as the target after
    // conversion, which means that it has to go via wchar_t but that is the problem of the converter.
    template<character E> struct default_representation {
        using type = E;
    };

    template<> struct default_representation<char> {
        using type = char8_t;
    };

    template<> struct default_representation<char32_t> {
        using type = char8_t;
    };

    template<size_t sz> struct wchar_encoding {};
    template<> struct wchar_encoding<2> { using type = char16_t; };
    template<> struct wchar_encoding<4> { using type = char8_t; };      // Use UTF-8 as the internal representation for wide strings on Linux.

    template<> struct default_representation<wchar_t> {
        using type = typename wchar_encoding<sizeof(wchar_t)>::type;
    };

    template<character E> using default_representation_t = detail::default_representation<E>::type;

    inline class TableManager {
    public:
        char32_t* get(const locale& loc) {
            auto i = m_tables.find(loc.name());
            if (i != m_tables.end())
                return i->second.get();

            // First time this locale name is used. Check if a table can be built by trying to convery 1 byte containing all values
            // from 1 to 255, presuming 0 is always the end marker. Unclear what happens if a value is outside the first 64k page
            // on windows, but by setting the destination buffer also to just one wchar_t any substitution pairs are excluded.
            auto& cvt = use_facet<codecvt<wchar_t, char, mbstate_t>>(loc);
            char32_t table[256];        // This is copied to the heap only if the table could be built successfully.
            table[0] = 0;
            for (int i = 1; i < 256; i++) {
                char c = char(i);
                mbstate_t state{};
                const char* from_next;
                wchar_t to;
                wchar_t* to_next;
                auto r = cvt.in(state, &c, &c + 1, from_next, &to, &to + 1, to_next);
                if (r != codecvt_base::ok) {
                    m_tables[loc.name()] = nullptr;
                    return nullptr;
                }

                table[i] = to;      // As there are no substitution pairs allowed in 1 to code element the 32 bit value is the 16 bit value.
            }

            // Table is ok. Copy it to heap array
            auto ptr = make_unique<char32_t[]>(256);
            auto ret = ptr.get();
            memcpy(ret, table, 256 * sizeof(char32_t));
            m_tables[loc.name()] = std::move(ptr);
            return ret;
        }

    private:
        map<string, unique_ptr<char32_t[]>> m_tables;
    } table_manager;

    inline ustring::encoding_t encoding_of_locale(const locale& loc)
    {
        if (loc == locale())
            return ustring::execution;
        else if (loc == locale(""))
            return ustring::system;
        else
            return ustring::single;
    }


} // namespace detail


// Specializations needed to be known before method implementations
template<> struct ustring::encoding_type_detail<ustring::system> {
    using type = char;
};
template<> struct ustring::encoding_type_detail<ustring::execution> {
    using type = char;
};
template<> struct ustring::encoding_type_detail<ustring::single> {
    using type = char;
};
template<> struct ustring::encoding_type_detail<ustring::wide> {
    using type = wchar_t;
};
template<> struct ustring::encoding_type_detail<ustring::utf8> {
    using type = char8_t;
};
template<> struct ustring::encoding_type_detail<ustring::utf16> {
    using type = char16_t;
};
template<> struct ustring::encoding_type_detail<ustring::utf32> {
    using type = char32_t;
};

// Function which (maybe) needs to be defined before any use of ustring::encoding_of in method implementations.
template<character T> constexpr ustring::encoding_t ustring::init_encoding_of()
{
    if constexpr(is_same_v<T, wchar_t>)
        return ustring::wide;
    else if constexpr(is_same_v<T, char8_t>)
        return ustring::utf8;
    else if constexpr(is_same_v<T, char16_t>)
        return ustring::utf16;
    else if constexpr(is_same_v<T, char32_t>)
        return ustring::utf32;
    else if constexpr(is_same_v<T, char>)
        static_assert(detail::dependent_false<T>, "Tried to use encoding_of for char. This is not possible as char has multiple encoding_t values");
    else
        static_assert(detail::dependent_false<T>,
                      "This implementation has another std::character type not implemented by ustring");
}


inline ustring::ustring()
{
    // Construct a zero length soo string.
    m_soo.m_mode = mode();
    m_soo.m_count = 0;
}

inline ustring::ustring(const ustring& src)
{
    // First copy the contents
    memcpy(this, &src, sizeof(ustring));

    if (get_mode().is_shared())
        get_impl().m_refs++;
}

inline ustring::ustring(ustring&& src) noexcept
{
    // First copy the contents
    memcpy(this, &src, sizeof(ustring));

    // Avoid any refcount decrementation in src's dtor
    src.m_soo.m_mode = mode();
    src.m_soo.m_count = 0;      // Make src look empty.
}

// Ctor from one repeated char
template<character T> ustring::ustring(size_t count, T c)
{
    T* ptr = reinterpret_cast<T*>(setup(count * sizeof(T), encoding_of<T>));
    fill(ptr, ptr + count, c);
}
template<> inline ustring::ustring(size_t count, char c) {
    // char overload is specialized as encoding_of<> is not defined for char.
    char* ptr = reinterpret_cast<char*>(setup(count, execution));
    fill(ptr, ptr + count, c);
}
template<character T> ustring::ustring(T c) : ustring(1, c) {}

template<character T> ustring::ustring(const T* src, size_t sz)
{
    init(src, sz * sizeof(T), encoding_of<T>);
}
template<> inline ustring::ustring(const char* src, size_t sz) : ustring(src, sz, locale("")) {}

template<character T> ustring::ustring(const T* src) : ustring(src, len_helper(src)) {}						// Interpreted as execution CS

inline ustring::ustring(const char* src, size_t sz, const locale& loc)
{
    auto table = detail::table_manager.get(loc);
    if (table != nullptr) {     // Soo check must make room for table
        init(src, sz, table, detail::encoding_of_locale(loc));
    }
    else {
        loader loader(loc, sz);
        loader.append(src, sz);
        *this = move(loader).str();
    }
}

inline ustring::ustring(const char* src, const locale& loc) : ustring(src, len_helper(src), loc) {}

inline ustring& ustring::operator=(const ustring& rhs)
{
    if (this == &rhs)
        return *this;

    if (get_mode().is_shared())
        unref();        // Unref previous impl.

    // Copy the contents
    memcpy(this, &rhs, sizeof(ustring));

    if (get_mode().is_shared())
        get_impl().m_refs++;

    return *this;
}

inline ustring& ustring::operator=(ustring&& rhs) noexcept
{
    if (this == &rhs)
        return *this;

    if (get_mode().is_shared())
        unref();        // Unref previous impl.

    // Copy the contents
    memcpy(this, &rhs, sizeof(ustring));

    // Avoid any refcount decrementation in src's dtor
    rhs.m_soo.m_mode = mode();
    rhs.m_soo.m_count = 0;      // Make src look empty.

    return *this;
}

// Implementation is for two rvalues. This means that if refcount == 1 in shared case we can change reuse the implementation of
// either if feasible.
inline ustring operator+(ustring&& lhs, ustring&& rhs)
{
    // Get the part count, i.e. 1 if not multi.
    auto partcount = [](const ustring& s) {
        if (s.get_mode().storage() != ustring::mode::multi)
            return 1;
        else
            return int(s.m_multi.m_end.extra() - s.m_multi.m_begin.extra()) + 1;
    };

    // NOTE: dest can be the same as simpl.m_strings in case of compressing a multi string, or it can be
    // separate in case of forming a new multi-impl.
    auto copy_active_parts = [](ustring dest[], const ustring& s) {
        if (s.get_mode().storage() != ustring::mode::multi) {
            *dest = s;
            return 1;
        }
        
        // Get the range of active parts in s
        auto& simpl = s.get_impl().m_multi;
        int begin_part = s.m_multi.m_begin.extra();
        int end_part = s.m_multi.m_end.extra();
        auto src = simpl.m_strings + begin_part;

        // Copy the active parts to dest, noting that there may be overlap in either direction.
        int count = end_part - begin_part + 1;
        if (dest < src)
            copy(src, src + count, dest);
        else if (dest > src)
            copy_backward(src, src + count, dest + count);

        // Adjust the first active part's begin to match s's begin.
        auto& bs = *src;
        if (bs.get_mode().storage() == ustring::mode::soo) {
            size_t begin_skip = s.m_multi.m_begin.ptr() - bs.m_soo.m_data;        // Bytes into first used part.
            assert(begin_skip < ustring::part_ptr::max_extra);
            if (begin_skip > 0) {
                // The first used part is partially used and in soo mode. Its contents must be moved down and its count decreased.
                dest->m_soo.m_count -= uint8_t(begin_skip);
                memcpy(dest->m_soo.m_data, dest->m_soo.m_data + begin_skip, dest->m_soo.m_count);
            }
        }
        else  // This includes m_literal too.
            dest->m_shared.m_begin = s.m_multi.m_begin.ptr();

        // Adjust the last active part's end to match s's end.
        auto& es = src[count - 1];
        auto& ed = dest[count - 1];
        if (es.get_mode().storage() == ustring::mode::soo) {
            size_t end_skip = es.m_soo.m_data + es.m_soo.m_count - s.m_multi.m_end.ptr();
            assert(end_skip < ustring::part_ptr::max_extra);
            ed.m_soo.m_count -= uint8_t(end_skip);
        }
        else  // This includes m_literal too.
            ed.m_shared.m_end = s.m_multi.m_end.ptr();

        return count;
    };

    auto update_ends = [](ustring& s) {
        assert(s.get_mode().storage() == ustring::mode::multi);
        auto& simpl = s.get_impl().m_multi;

        const ustring& first = simpl.m_strings[0];
        if (first.get_mode().storage() == ustring::mode::soo)
            s.m_multi.m_begin = ustring::part_ptr(0, first.m_soo.m_data);    // Now the begin is the actual beginning of part 0.
        else
            s.m_multi.m_begin = ustring::part_ptr(0, first.m_shared.m_begin);   // Just adjust the part number of begin to 0, keeping the offset within.

        const ustring& last = simpl.m_strings[simpl.m_count - 1];
        if (last.get_mode().storage() == ustring::mode::soo)
            s.m_multi.m_end = ustring::part_ptr(simpl.m_count - 1, last.m_soo.m_data + last.m_soo.m_count);    // Now the end is the actual end of last part
        else
            s.m_multi.m_end = ustring::part_ptr(simpl.m_count - 1, last.m_shared.m_end);      // Just adjust the part number of begin to 0, keeping the offset within.
    };


    // prune the parts of s which are not used, given begin/end. Also move the actual begin/end pointers to the remaining parts
    auto prune_parts = [&](ustring& s) {
        assert(s.get_mode().storage() == ustring::mode::multi);
        assert(s.get_impl().m_refs == 1);
        auto& simpl = s.get_impl().m_multi;

        simpl.m_count = copy_active_parts(simpl.m_strings, s);
        update_ends(s);
    };

    // Handle nops first
    if (lhs.empty())
        return move(rhs);

    if (rhs.empty())
        return move(lhs);
    
    // First attempt: Append rhs characters to lhs which must be soo and able to fit rhs contents, which must have same encoding.
    if (lhs.try_append(rhs))
        return lhs;

    // Seconds attempt: If lhs is a short literal prepending to a soo rhs can work.
    if (rhs.try_prepend(lhs))
        return rhs;

    // Third attempt: if lhs is uniquely owned multi-part and rhs fits in its spares, append the rhs parts.
    if (lhs.get_mode().storage() == ustring::mode::multi && lhs.get_impl().m_refs == 1) {
        prune_parts(lhs);
        auto& limpl = lhs.get_impl().m_multi;
        int rparts = partcount(rhs);
        if (rparts == 1 && limpl.m_strings[limpl.m_count - 1].try_append(rhs))     // First try appending to the last lhs part (not increasing lhs part count)
            return lhs;
        
        if (limpl.m_count + rparts <= limpl.m_capacity) {
            limpl.m_count += copy_active_parts(limpl.m_strings + limpl.m_count, rhs);
            update_ends(lhs);
            return lhs;
        }
    }

    // Fourth attempt: If rhs is uniquely owned multi-part and lhs fits in its spares, prepend the lhs parts
    if (rhs.get_mode().storage() == ustring::mode::multi && rhs.get_impl().m_refs == 1) {
        prune_parts(rhs);
        auto& rimpl = rhs.get_impl().m_multi;
        int lparts = partcount(lhs);
        if (lparts == 1 && rimpl.m_strings[0].try_prepend(lhs))     // First try prepending to the first rhs part (not increasing rhs part count)
            return rhs;

        if (rimpl.m_count + lparts <= rimpl.m_capacity) {
            copy_active_parts(rimpl.m_strings + lparts, rhs);
            copy_active_parts(rimpl.m_strings, lhs);
            rimpl.m_count += lparts;
            update_ends(rhs);
            return rhs;
        }
    }

    // The main method is to create a new multi-part implementation and just concatenate
    // lhs and rhs parts into it.
    int lparts = partcount(lhs);
    int rparts = partcount(rhs);

    // Create a separate ustring with enough multi parts to return.
    ustring::impl* ip = ustring::make_multi_impl(lparts + rparts + 3);
    ip->m_multi.m_count = copy_active_parts(ip->m_multi.m_strings, lhs);
    ip->m_multi.m_count += copy_active_parts(ip->m_multi.m_strings + ip->m_multi.m_count, rhs);

    ustring ret;
    ret.m_multi.m_impl = ustring::impl_ptr(ustring::mode(ustring::mode::multi, ustring::single, false), ip);
    update_ends(ret);
    return ret;
}

inline ustring operator+(const ustring& lhs, ustring&& rhs)
{
    return ustring(lhs) + move(rhs);
}

inline ustring operator+(ustring&& lhs, const ustring& rhs)
{
    return move(lhs) + ustring(rhs);
}

inline ustring operator+(const ustring& lhs, const ustring& rhs)
{
    return ustring(lhs) + ustring(rhs);
}

inline ustring& ustring::operator+=(const ustring& rhs)
{
    *this = move(*this) + rhs;
    return *this;
}

inline ustring& ustring::operator+=(ustring&& rhs)
{
    *this = move(*this) + move(rhs);
    return *this;
}


inline bool ustring::operator==(const ustring& rhs) const
{
    // TODO: Here we would benefit from a conditionally available size() which we could call if encoding allows it, returning false
    // if sizes differ.
    return operator<=>(rhs) == strong_ordering::equal;
}

inline strong_ordering ustring::operator<=>(const ustring& rhs) const
{
    iterator l = begin();
    iterator le = end();
    iterator r = rhs.begin();
    iterator re = rhs.end();
    while (l != le) {
        if (r == re || *l > *r)
            return strong_ordering::greater;
        if (*l < *r)
            return strong_ordering::less;
        ++l;
        ++r;
    }
    if (r == re)
        return strong_ordering::equal;
    else
        return strong_ordering::less;
}


template<character T> ustring ustring::view(const T* src, size_t sz)
{
    ustring ret;
    ret.m_literal.m_begin = reinterpret_cast<const byte*>(src);
    ret.m_literal.m_end = reinterpret_cast<const byte*>(src) + sz * sizeof(T);
    ret.m_literal.m_table = table_ptr(mode(mode::literal, encoding_of<T>, false), nullptr);
    return ret;
}

inline ustring ustring::view(const char* src, size_t sz, const locale& loc)
{
    const char32_t* table = detail::table_manager.get(loc);
    if (table == nullptr)
        return ustring(src, sz, loc);
    
    ustring ret;
    ret.m_literal.m_begin = reinterpret_cast<const byte*>(src);
    ret.m_literal.m_end = reinterpret_cast<const byte*>(src) + sz;
    ret.m_literal.m_table = table_ptr(mode(mode::literal, detail::encoding_of_locale(loc), table != nullptr), table);
    return ret;
}

template<> inline ustring ustring::view(const char* src, size_t sz) { return view(src, sz, locale("")); }


inline pair<ustring::iterator, ustring::iterator> ustring::find_ends(const ustring& pattern, const iterator& after) const
{
    iterator ret = after;

    iterator pb = pattern.begin();
    iterator pe = pattern.end();
    if (pb == pe)       // Empty pattern always succeeds immediately
        return make_pair(ret, ret);
    
    iterator e = end();
    while (true) {
        iterator i = ret;
        iterator p = pb;

        while (true) {
            if (i == e)
                return make_pair(e, e);       // Too little of string left for pattern to fit
            if (p == pe)
                return make_pair(ret, i);     // End of pattern reached without difference. Return start point in me.
            if (*i != *p)
                break;
            ++i;
            ++p;
        }

        ++ret;
    }

    // Compilers should know that a while (true) without break won't get here.
}

inline pair<ustring::iterator, ustring::iterator> ustring::rfind_ends(const ustring& pattern, const iterator& before) const
{
    iterator ret = before;

    iterator pb = pattern.begin();
    iterator pe = pattern.end();
    if (pb == pe)       // Empty pattern always succeeds immediately
        return make_pair(ret, ret);     // The zero length _start_ of the part of the string where match occurred is also end!

    iterator b = begin();   // Sentinel
    while (true) {
        iterator i = ret;
        iterator p = pe;

        while (true) {
            if (i == b)
                return make_pair(b, b);       // Too little of string left for pattern to fit, return begin.
            if (p == pb)
                return make_pair(i, ret);       // End of pattern reached without difference. Return start point in me.
            --i;
            --p;
            if (*i != *p)
                break;
        }

        --ret;
    }

    // Compilers should know that a while (true) without break won't get here.
}

inline bool ustring::starts_with(const ustring& pattern) const
{
    iterator p = pattern.begin();
    iterator pe = pattern.end();
    if (p == pe)       // Empty pattern always succeeds
        return true;

    iterator e = end();
    iterator i = begin();
    while (true) {
        if (i == e)
            return false;   // Pattern longer
        if (p == pe)
            return true;    // End of pattern reached without difference.
        if (*i != *p)
            return false;
        ++i;
        ++p;
    }
}

inline bool ustring::ends_with(const ustring& pattern) const
{
    iterator p = pattern.end();
    iterator pb = pattern.begin();
    if (p == pb)       // Empty pattern always succeeds
        return true;

    iterator i = end();
    iterator b = begin();
    while (true) {
        if (i == b)
            return false;   // Pattern longer
        if (p == pb)
            return true;    // End of pattern reached without difference.
        --i;
        --p;
        if (*i != *p)
            return false;
    }
}

inline ustring ustring::substr(const ustring::iterator& from, const ustring::iterator& to) const
{
    ustring ret;
    switch(get_mode().storage()) {
        case mode::soo:
            // For a soo string we must copy the selected characters.
            if (get_mode().has_table()) {
                ret.m_soo_table.m_count = uint8_t(to.pos() - from.pos());
                memcpy(ret.m_soo_table.m_data, from.pos(), m_soo_table.m_count);
                ret.m_soo_table.m_table = m_soo_table.m_table;
            }
            else {
                ret.m_soo.m_count = uint8_t(to.pos() - from.pos());
                memcpy(ret.m_soo.m_data, from.pos(), m_soo.m_count);
                ret.m_soo.m_mode = get_mode();
            }
            break;

        case mode::shared:
            ret.m_shared.m_begin = from.pos();
            ret.m_shared.m_end = to.pos();
            ret.m_shared.m_impl = m_shared.m_impl;  // Note: This includes the mode byte.
            ret.get_impl().m_refs++;
            break;

        case mode::multi:
            ret.m_multi.m_begin = from.combined_pos();
            ret.m_multi.m_end = to.combined_pos();
            ret.m_multi.m_impl = m_multi.m_impl;  // Note: This includes the mode byte.
            ret.get_impl().m_refs++;
            break;

        case mode::literal:
            ret.m_literal.m_begin = from.pos();
            ret.m_literal.m_end = to.pos();
            ret.m_literal.m_table = m_literal.m_table;  // Note: This includes the mode byte.
            break;
    }

    return ret;
}

template<character T, typename Tr, typename Al> basic_string<T, Tr, Al> ustring::basic_string(T bad_char) const
{
    size_t count = estimated_size<T>();
    std::basic_string<T, Tr, Al> ret(count, ' ');

    while (true) {
        size_t len = copy(ret.data(), count);
        if (len < count) {
            ret.resize(len);
            return ret;
        }

        count = count * 3 / 2;
        ret.resize(count);
    }
}

inline ustring::encoding_t ustring::encoding() const
{
    if (get_mode().storage() != mode::multi)
        return get_mode().encoding();

    return multipart;
}

namespace detail {

    inline constexpr ustring::encoding_t normalize(ustring::encoding_t src)
    {
        if (src != ustring::wide)
            return src;
        
        if constexpr (sizeof(wchar_t) == 2)
            return ustring::utf16;
        else
            return ustring::utf32;
    }


    inline bool equivalent(ustring::encoding_t lhs, ustring::encoding_t rhs)
    {
        return detail::normalize(lhs) == detail::normalize(rhs);
    }
}

inline ustring::encoding_t ustring::mode::normalized_encoding() const
{
    switch (m_encoding) {
    case ustring::wide:
        if constexpr (sizeof(wchar_t) == 2)
            return ustring::utf16;
        else
            return ustring::utf32;

    case single:
    case system:
    case execution:
        return single;

    default:
        return m_encoding;
    }
}

// This checks that T is consistent with the current encoding and returns nullptr if not, or if storage is not contiguous.
template<character T> const T* ustring::data() const
{
    auto enc = encoding_of<T>();
    if (!detail::equivalent(enc, encoding()))
        return nullptr;

    return reinterpret_cast<const T*>(get_begin());
}

inline const byte* ustring::data() const
{
    if (encoding() == multipart)
        return nullptr;

    return get_begin().ptr();
}

inline size_t ustring::bytes() const
{
    if (get_mode().storage() != ustring::mode::multi)
        return get_end().ptr() - get_begin().ptr();

    return npos;
}

// Return estimated size needed for copy.
template<character T> size_t ustring::estimated_size() const
{
    // This could be made more sophisticated, as a minimum taking care of the fixed width char and char32_t conversions which can
    // be done exactly, and maybe using some "typical" bytes per code point number for utf8 and utf16
    if (get_mode().storage() != mode::multi)
        return bytes();

    // Sum up all parts byte counts for the parts this ustring refers to, taking care of the partial first and last part usage.
    int part = m_multi.m_begin.extra();
    size_t ret = get_part(part).get_end().ptr() - m_multi.m_begin.ptr();
    int endpart = m_multi.m_end.extra();

    while (part < endpart - 1) {
        part++;
        ret += get_part(part).bytes();
    }

    ret += m_multi.m_end.ptr() - get_part(endpart).get_begin().ptr();

    return ret;
}


template<character C> size_t ustring::copy_part(C* dest, size_t count, iterator& start) const
{
    C* d= dest;
    C* e = d + count;
    const byte* end = get_end().ptr();
    auto loop = [&](auto& p) {
        while (reinterpret_cast<const byte*>(p) != end) {
            if (!detail::transcode(d, e, p))        // d has not been moved if transcode fails (which is due to d hitting end.
                break;
        }
    };

    const byte* p = start.pos();

    switch (get_mode().normalized_encoding()) {
     case utf8:
        loop(reinterpret_cast<const char8_t*&>(p));
        break;
        
    case utf16:
        loop(reinterpret_cast<const char16_t*&>(p));
        break;

    case utf32:
        loop(reinterpret_cast<const char32_t*&>(p));
        break;

    case single:
        if (get_mode().has_table()) {
            const char32_t* table = get_table(0);
            while (p != end) {
                if (!detail::encode(d, e, table[*reinterpret_cast<const uint8_t*>(p++)]))
                    break;
            }
        }
        else
            loop(reinterpret_cast<const char*&>(p));     // ASCII
        break;

    default:
        assert(false);      // Should not be returned from normalized_encoding()
    }

    start.set_pos(p);
    return d - dest;
}
inline size_t ustring::copy_part(char* dest, size_t count, iterator& start, char bad_char) const
{
    if (encoding() == single) {
        const byte* pos = start.pos();
        size_t bytes = min(count, size_t(get_end().ptr() - pos));
        memcpy(dest, pos, bytes);
        start.set_pos(pos + bytes);
        return bytes;
    }

    // Get code points from start and encode as ascii or by reverse table lookup at dest until dest is full or start is end.
    char* d = dest;
    char* e = dest + count;
    const byte* end = get_end().ptr();
    const char32_t* table = get_table(0);
    if (table == nullptr) {
        while (start.pos() != end) {
            if (d == e)
                break;

            char32_t cp = *start;
            if (cp > 127)       // Only ascii accepted.
                *d++ = bad_char;
            else
                *d++ = char(cp);

            ++start;
        }
    }
    else {
        while (start.pos() != end) {
            if (d == e)
                break;

            char32_t cp = *start;
            if (cp > 127) {
                *d = bad_char;                       // Presume it will not be found.
                for (int i = 128; i < 256; i++) {    // Look in the table to see if the code point cp is in its second half, first half still assumed to be ascii.
                    if (table[i] == cp) {
                        *d = char(i);
                        break;
                    }
                }
                d++;
            }
            else
                *d++ = char(cp);

            ++start;
        }
    }

    return d - dest;
}
template<> inline size_t ustring::copy_part(wchar_t* dest, size_t count, iterator& start) const
{
    if constexpr (sizeof(wchar_t) == 2)
        return copy_part(reinterpret_cast<char16_t*>(dest), count, start);
    else
        return copy_part(reinterpret_cast<char32_t*>(dest), count, start);
}

// Regardless of the encoding of the ustring it is always possible to retrieve its contents in one of the encodings
// corresponding to the different character types. The count parameter indicates the size of dest in Ts. If the entire ustring
// can't fit in dest a whole number of code points is converted and start is set to point to the next code point.
// The caller must check if start == end() to know if the string ended, or try again and get a 0 return.
// We could add a second iterator end to be able to copy up to a given iterator for symmetry.
template<character T> size_t ustring::copy(T* dest, size_t count, iterator& start) const
{
    assert(&start.str() == this);

    if (get_mode().storage() == mode::multi) {
        uint8_t part = start.part();
        uint8_t parts = get_impl().m_multi.m_count;
        size_t ret = 0;
        auto subStart = get_part(part).begin();
        subStart.set_pos(start.pos());
        while (part < parts) {
            size_t bytes = get_part(part).copy_part(dest, count, subStart);
            if (subStart.pos() < get_part(part).get_end().ptr()) {     // run out of dest inside the part
                start.set_pos(subStart.pos());
                start.set_part(part);
                return ret + bytes;
            }
            dest += bytes;
            count -= bytes;
            ret += bytes;
            part++;
            if (part == parts)
                break;

            subStart = get_part(part).begin();
        }

        start = end();      // Indicate total finish.
        return ret;
    }
    else
        return copy_part(dest, count, start);
}
inline size_t ustring::copy(char* dest, size_t count, iterator& start, char bad_char) const
{
    assert(&start.str() == this);

    if (get_mode().storage() == mode::multi) {
        uint8_t part = start.part();
        uint8_t parts = get_impl().m_multi.m_count;
        size_t ret = 0;
        auto subStart = get_part(part).begin();
        subStart.set_pos(start.pos());
        while (part < parts) {
            size_t bytes = get_part(part).copy_part(dest, count, subStart, bad_char);
            if (subStart.pos() < get_part(part).get_end().ptr()) {     // run out of dest inside the part
                start.set_pos(subStart.pos());
                start.set_part(part);
                return ret + bytes;
            }
            dest += bytes;
            count -= bytes;
            ret += bytes;
            part++;
            if (part == parts)
                break;

            subStart = get_part(part).begin();
        }

        start = end();      // Indicate total finish.
        return ret;
    }
    else
        return copy_part(dest, count, start, bad_char);
}


// Simplified version which stops when the dest buffer is full. If this happens it returns the size of the buffer and you don't
// know if it overflowed or was an exact fit.
template<character T> size_t ustring::copy(T* dest, size_t count) const
{
    iterator start = begin();
    return copy(dest, count, start);
}

inline size_t ustring::copy(char* dest, size_t count, char bad_char) const
{
    iterator start = begin();
    return copy(dest, count, start, bad_char);
}

inline size_t ustring::copy(char* dest, size_t count, const locale& loc, iterator& start, char bad_char) const
{
    saver s(loc, *this, bad_char);
    s.fill(dest, count);
    return size_t();
}

inline size_t ustring::copy(char* dest, size_t count, const locale& loc, char bad_char) const
{
    iterator start = begin();
    return copy(dest, count, loc, start, bad_char);
}


// Versions of these which takes a span<char_type> are also provided. Note that the return type is always a span with dynamic
// extent as the length of the ustring is always dynamic.
template<character T, size_t SZ> span<T> ustring::copy(span<T, SZ> dest, iterator& start) const
{
    return span<T>(dest.data(), copy(dest.data(), dest.size(), start));
}


template<character T, size_t SZ> span<T> ustring::copy(span<T, SZ> dest) const
{
    return span<T>(dest.data(), copy(dest.data(), dest.size()));
}

template<size_t SZ>
inline span<char> ustring::copy(span<char, SZ> dest, iterator& start, char bad_char) const
{
    return span<char>(dest.data(), copy(dest.data(), dest.size(), start, bad_char));
}

template<size_t SZ>
inline span<char> ustring::copy(span<char, SZ> dest, char bad_char) const
{
    return span<char>(dest.data(), copy(dest.data(), dest.size(), bad_char));
}

template<size_t SZ>
inline span<char> ustring::copy(span<char, SZ> dest, const locale& loc, iterator& start, char bad_char) const
{
    return span<char>(dest.data(), copy(dest.data(), dest.size(), loc, start, bad_char));
}

template<size_t SZ>
inline span<char> ustring::copy(span<char, SZ> dest, const locale& loc, char bad_char) const
{
    return span<char>(dest.data(), copy(dest.data(), dest.size(), loc, bad_char));
}



//////////////// iterator methods ////////////////


inline ustring::iterator::iterator(const ustring& str, part_ptr pos) : m_string(&str), m_index(npos) 
{
    mode m = str.get_mode();
    m_multi = m.storage() == mode::multi;
    if (m_multi) {
        m_part = pos.extra();
        m_pos = pos.ptr();
        init_part();
    }
    else {
        m_part = 0;         // Operator== checks this even for !m_multi to save time there
        m_pos = pos.ptr();
        m_end = str.get_end().ptr();
        m_mode = m;

        init_size();
    }
}


inline ustring::iterator& ustring::iterator::operator++() {        // Prefix
    assert(m_pos + m_count <= m_end);           // Check for out of range, as we can relatively easily.

    // Now add the bytes that were consumed when loading the previous code point. Saving that count in m_count allows m_pos
    // to point at the already loaded code point until we increment.
    m_pos += m_count;
    if (m_multi) {
        // Check if it is time to move to the next part.
        if (m_pos == m_end) {
            m_part++;
            m_pos = m_string->get_part(m_part).get_begin().ptr();

            init_part();
        }
        else
            load();
    }
    else
        load();

    return *this;
}

inline ustring::iterator ustring::iterator::operator++(int)
{      // Postfix
    iterator ret = *this;        // This copies all members, including the m_count.
    ++ret;
    return ret;
}

inline ustring::iterator& ustring::iterator::operator--()
{        // Prefix
    advance(-1);
    return *this;
}

inline ustring::iterator ustring::iterator::operator--(int)
{      // Postfix
    iterator ret = *this;        // This copies all members, including the m_count.
    --ret;
    return ret;
}

inline bool ustring::iterator::operator==(const iterator& rhs) const
{
    assert(m_string == rhs.m_string);       // Can only compare within same string, or compare two default constructed iterators

    return m_pos == rhs.m_pos && m_part == rhs.m_part;
}

inline strong_ordering ustring::iterator::operator<=>(const iterator& rhs) const
{
    strong_ordering po = m_part <=> rhs.m_part;
    if (po != strong_ordering::equal)
        return po;
    else
        return m_pos <=> m_end;
}

// You can't subtract iterators created from end to those created from begin as we don't know the exact size for all
// encodings.
inline ptrdiff_t ustring::iterator::operator-(const iterator& rhs) const
{
    if (m_index >= 0) {
        assert(rhs.m_index >= 0);
        return m_index - rhs.m_index;
    }
    else {
        assert(rhs.m_index < 0);            // Both iterators must count from beginning or end
        return rhs.m_index - m_index;
    }
}

inline ustring::iterator ustring::iterator::operator+(ptrdiff_t by) const
{
    iterator ret = *this;
    ret += by;
    return ret;
}

inline ustring::iterator& ustring::iterator::operator+=(ptrdiff_t by)
{
    advance(by);
    return *this;
}


inline void ustring::iterator::advance(ptrdiff_t by)
{
    if (m_multi) {
        // advance also between different parts, which may have different encodings.
        if (by > 0) {
            while (true) {
                by = advance_in_part(by, nullptr);
                if (by == 0)
                    return;

                if (m_part == m_string->get_end().extra())
                    throw runtime_error("advance out of bounds");

                m_part++;
                m_pos = m_string->get_part(m_part).get_begin().ptr();
                init_part();
            }
        }
        else if (by < 0) {
            while (true) {
                by  = advance_in_part(by, m_string->get_part(m_part).get_begin().ptr());
                if (by == 0)
                    return;

                if (m_part == 0)
                    throw runtime_error("advance out of bounds");

                m_part--;
                m_pos = m_string->get_part(m_part).get_end().ptr();
                init_part();
            }
        }
    }
    else
        advance_in_part(by, m_string->get_begin().ptr());


    assert(false);
}

inline size_t ustring::iterator::advance(const iterator& towards, size_t by)
{
    if (by == 0)
        return 0;
    
    if (towards < *this) {
        if (m_multi) {
            // advance also between different parts, which may have different encodings.
            while (true) {
                by = advance_in_part(by, nullptr);
                if (by == 0)
                    return by;

                if (m_part == m_string->get_end().extra())
                    return by - by;

                m_part++;
                m_pos = m_string->get_part(m_part).get_begin().ptr();
                init_part();
            }
        }
        else
            return advance_in_part(by, m_string->get_begin().ptr()) != 0;
    }
    else {
        if (m_multi) {
            while (true) {
                by  = advance_in_part(by, m_string->get_part(m_part).get_begin().ptr());
                if (by == 0)
                    return by;

                if (m_part == 0)
                    return false;

                m_part--;
                m_pos = m_string->get_part(m_part).get_end().ptr();
                init_part();
            }
        }
        else
            return advance_in_part(by, m_string->get_begin().ptr()) != 0;
    }

    assert(false);
    return false;   // MSVC could not detect that code above cover all cases.
}

inline size_t ustring::iterator::advance(const iterator& towards)
{
    return advance(towards, numeric_limits<size_t>::max());
}


//////////////// private iterator methods ////////////////

// This helper function returns the remaining steps to take
inline ptrdiff_t ustring::iterator::advance_in_part(ptrdiff_t by, const byte* beg)
{
    switch (m_mode.normalized_encoding()) {
    case single:
    case utf32: {
        bool positive = m_index >= 0;
        ptrdiff_t goal = m_index + by;

        // For all modes with fixed width we can just divide by m_count (which is always correctly set).
        ptrdiff_t size = (m_end - beg) / m_count;      // String size
        if (positive) {
            if (goal < 0) {
                m_index = 0;
                m_pos = beg;
                load();
                return -goal;
            }
            if (goal > size) {
                m_index = size;
                m_pos = m_end;
                return goal - m_index;
            }
        }
        else {
            if (goal >= -1) {
                m_index = -1;
                m_pos = m_end;
                return goal + 1;
            }
            if (goal < -1 - size) {
                m_index = -1 - size;
                m_pos = beg;
                load();
                return goal - m_index;
            }
        }

        m_pos += by * m_count;
        m_index = goal;
        load();
        return 0;
    }

    case utf8:
        // Code is different depending on the direction.
        if (by >= 0) {
            for (ptrdiff_t i = 0; i < by; i++) {
                if (m_pos >= m_end)
                    return by - i;

                if ((m_pos[0] & byte(0x80)) == byte(0))
                    m_pos += 1;
                else if ((m_pos[0] & byte(0xe0)) == byte(0xc0)) {
                    if (m_pos + 2 > m_end)
                        return false;
                    m_pos += 2;
                }
                else if ((m_pos[0] & byte(0xf0)) == byte(0xe0)) {
                    if (m_pos + 3 > m_end)
                        return false;
                    m_pos += 3;
                }
                else {
                    if (m_pos + 4 > m_end)
                        return false;
                    m_pos += 4;
                }
                m_index++;
            }

            return 0;
        }
        else {
            // Going back means iterating all C0-DF bytes and then skipping one.
            for (ptrdiff_t i = 0; i > by; i--) {
                while ((*m_pos & byte(0xC0)) == byte(0x80)) {
                    if (m_pos <= beg)   // Unfortunately have to check this for each byte.
                        return by - i;

                    m_pos--;
                }

                if (m_pos <= beg)   // Unfortunately have to check this for each byte.
                    return by - i;

                m_pos--;
                m_index--;
            }

            return 0;
        }

        break;

    case utf16: {
        if (by >= 0) {
            for (ptrdiff_t i = 0; i < by; i++) {
                if (m_pos + 2 > m_end)
                    return by - i;

                uint16_t lp = *reinterpret_cast<const uint16_t*>(m_pos);
                if (lp >= 0xD800 && lp < 0xE000) {      // Surrogate pair, or one surrogate.
                    if (m_pos + 4 > m_end)
                        return by - i;   // We must assume that if the last value is half a surrogate pair, something is wrong.

                    uint16_t hp = *reinterpret_cast<const uint16_t*>(m_pos + 2);
                    if (hp >= 0xD800 && hp < 0xE000)       // True surrogate pair, do an extra increment
                        m_pos += 2;
                }

                m_pos += 2,
                m_index++;
            }
        }
        else {
            for (ptrdiff_t i = 0; i > by; i--) {
                if (m_pos - 2 < beg)
                    return by - i;

                m_pos -= 2;
                uint16_t lp = *reinterpret_cast<const uint16_t*>(m_pos);
                if (lp >= 0xD800 && lp < 0xE000) {      // Surrogate pair, or one surrogate.
                    if (m_pos - 2 < beg)
                        return by - i;   // We must assume that if the first value is half a surrogate pair, something is wrong.

                    uint16_t hp = *reinterpret_cast<const uint16_t*>(m_pos - 2);
                    if (hp >= 0xD800 && hp < 0xE000)       // True surrogate pair, do an extra decrement
                        m_pos -= 2;
                }

                m_index--;
            }
        }
        break;

    default:
        break;
    }
    }

    assert(false);
    return 0;
}


inline void ustring::iterator::load()
{
    // To make sure we don't read outside memory we must check if we're at end before advancing. Note: Maybe it would be
    // better to not separate part from m_pos after all and instead load m_pos into a local var here, with the anding done
    // when loading it, and the same in advance of course.
    if (m_pos == m_end) {
        m_current = 0;
        return;
    }
    m_index++;

    switch ((m_mode.normalized_encoding())) {
    case single:
        if (m_mode.has_table())
            m_current = m_string->get_table(m_part)[*reinterpret_cast<const uint8_t*>(m_pos)];
        else
            m_current = *reinterpret_cast<const uint8_t*>(m_pos);
        break;

    case utf8:
        m_count = detail::decode(m_current, reinterpret_cast<const char8_t*>(m_pos));
        break;

    case utf16:
        m_count = detail::decode(m_current, reinterpret_cast<const char16_t*>(m_pos));
        break;

    case utf32:
        m_current = *reinterpret_cast<const uint32_t*>(m_pos);
        break;

    default:
        assert(false);  // Normalized encoding should not return anything else.
        break;
    }
}

inline void ustring::iterator::init_part()
{
    const ustring& ss = m_string->get_part(m_part);
    m_mode = ss.get_mode();
    assert(m_mode.storage() != mode::multi);       // Can't nest multi-parts, iterator can't store multi-level part numbers.

    part_ptr end = m_string->get_end();
    uint8_t end_part = end.extra();
    if (end_part == m_part)
        m_end = end.ptr();
    else
        m_end = ss.get_end().ptr();

    init_size();
}

inline void ustring::iterator::init_size()
{
    // For fixed size encodings set up the m_count once and for all.
    switch (m_mode.normalized_encoding()) {
        case single:
            m_count = 1;
            break;

        case utf32:
            m_count = 4;
            break;

        default:
            break;  // For all variable-length encodsing load sets up m_count each time.
    }

    load();     // Load is a nop if we're already at end. Instead it sets m_current to 0 in this case.
}


//////////////// private methods ////////////////

inline size_t ustring::len_helper(const char16_t* ptr) {
    if constexpr (sizeof(wchar_t) == sizeof(char16_t))
        return wcslen(reinterpret_cast<const wchar_t*>(ptr));
    else {
        auto e = ptr;
        while (*e++)
            ;
        return e - ptr;
    }
}

inline size_t ustring::len_helper(const char32_t* ptr) {
    if constexpr (sizeof(wchar_t) == sizeof(char32_t))
        return wcslen(reinterpret_cast<const wchar_t*>(ptr));
    else {
        auto e = ptr;
        while (*e++)
            ;
        return e - ptr;
    }
}

inline ustring::part_ptr ustring::get_begin() const {
    switch (get_mode().storage()) {
    case mode::multi:
        return part_ptr(0, m_shared.m_begin);    // Includes the part number

    case mode::shared:
        return part_ptr(0, m_shared.m_begin);    // Includes the part number

    case mode::soo:
        if (get_mode().has_table())
            return part_ptr(0, m_soo_table.m_data);
        else
            return part_ptr(0, m_soo.m_data);

    case mode::literal:
        return part_ptr(0, m_literal.m_begin);
    }

    assert(false);
    return part_ptr(0, nullptr);   // MSVC could not detect that switch cover all storage_t values.
}

inline ustring::part_ptr ustring::get_end() const {
    switch (get_mode().storage()) {
    case mode::multi:
        return m_multi.m_end;
    case mode::shared:
        return part_ptr(0, m_shared.m_end);

    case mode::soo:
        if (get_mode().has_table())
            return part_ptr(0, m_soo_table.m_data + m_soo_table.m_count);
        else
            return part_ptr(0, m_soo.m_data + m_soo.m_count);

    case mode::literal:
        return part_ptr(0, m_literal.m_end);
    }

    assert(false);
    return part_ptr(0, nullptr);   // MSVC could not detect that switch cover all storage_t values.
}

inline const char32_t* ustring::get_table(uint8_t part) const
{
    mode m = get_mode();
    if (m.storage() == mode::multi)
        return get_part(part).get_table(0);

    assert(part == 0);

    if (!m.has_table())
        return nullptr;

    switch (m.storage()) {
    case mode::shared:
        return get_impl().m_table.m_table;

    case mode::soo:
        return m_soo_table.m_table.ptr();

    case mode::literal:
        return m_literal.m_table.ptr();

    default:
        assert(false);
        return nullptr;   // MSVC and clang could not detect that multi is shaved off before the switch.
    }
}

inline const ustring& ustring::get_part(uint8_t part) const
{
    assert(get_mode().storage() == mode::multi);
    return get_impl().m_multi.m_strings[part];
}

inline ustring& ustring::get_part(uint8_t part)
{
    assert(get_mode().storage() == mode::multi);
    return get_impl().m_multi.m_strings[part];
}

inline const ustring::impl& ustring::get_impl() const {
    assert(get_mode().is_shared());
    return *m_shared.m_impl.ptr();
}
inline ustring::impl& ustring::get_impl() {
    assert(get_mode().is_shared());
    return *m_shared.m_impl.ptr();
}

inline byte* ustring::setup(size_t sz, encoding_t encoding, const char32_t* table)
{
    if (table == nullptr) {
        if (sz <= sizeof(m_soo.m_data)) {   // soo implementation without table
            m_soo.m_count = uint8_t(sz);
            m_soo.m_mode = mode(mode::soo, encoding, false);
            return m_soo.m_data;
        }
        else { // m_shared implementation without table.
            m_shared.m_impl = impl_ptr(mode(mode::shared, encoding, false), make_impl(sz));
            m_shared.m_begin = get_impl().m_data;
            m_shared.m_end = m_shared.m_begin + sz;
            return m_shared.m_impl.ptr()->m_data;
        }
    }
    else {
        if (sz <= sizeof(m_soo_table.m_data)) {
            // soo implemenation with table
            m_soo_table.m_table = table_ptr(mode(mode::soo, encoding, true), table);
            m_soo_table.m_count = uint8_t(sz);
            return m_soo_table.m_data;
        }
        else {
            // m_shared implementation with table.
            m_shared.m_impl = impl_ptr(mode(mode::shared, encoding, true), make_impl(table, sz));
            m_shared.m_begin = m_shared.m_impl.ptr()->m_table.m_data;
            m_shared.m_end = m_shared.m_begin + sz;
            return m_shared.m_impl.ptr()->m_table.m_data;
        }
    }
}

inline void ustring::shrink_to(const void* end)
{
    if (get_mode().storage() == mode::soo) {
        if (get_mode().has_table())
            m_soo_table.m_count = uint8_t(reinterpret_cast<const byte*>(end) - m_soo_table.m_data);
        else
            m_soo.m_count = uint8_t(reinterpret_cast<const byte*>(end) - m_soo.m_data);
    }
    else if (get_mode().storage() == mode::shared) {
        m_shared.m_end = reinterpret_cast<const byte*>(end);
    }
    else
        assert(false);      // Literals or multi can't be shrunk.
}

inline void ustring::init(const void* src, size_t sz, encoding_t encoding)
{
    memcpy(setup(sz, encoding), src, sz);
}


inline void ustring::init(const void* src, size_t sz, const char32_t* table, encoding_t encoding)
{
    memcpy(setup(sz, encoding, table), src, sz);
}

inline ustring::impl* ustring::make_impl(size_t bytes)
{
    byte* mem = new byte[bytes + sizeof(atomic<uint32_t>)];
    impl* ret = new(mem) impl;
    return ret;
}

inline ustring::impl* ustring::make_impl(const char32_t* table, size_t bytes)
{
    byte* mem = new byte[bytes + sizeof(atomic<uint32_t>) + sizeof(const char32_t*)];
    impl* ret = new(mem) impl;
    ret->m_table.m_table = table;
    return ret;
}

inline bool ustring::try_append(const ustring& rhs) {
    // Check if lhs + rhs fits into the soo storage of lhs
    mode lmode = get_mode();
    mode rmode = rhs.get_mode();

    auto same_table = [&] {
        if (lmode.has_table() != rmode.has_table())
            return false;
        
        if (!lmode.has_table())
            return true;
        
        return m_soo_table.m_table.ptr() == rhs.m_soo_table.m_table.ptr();
    };

    if (lmode.storage() == mode::soo && lmode.normalized_encoding() == rmode.normalized_encoding()) {
        // Different byte counts allowed depending on table mode of 'this'
        uint8_t spare;
        if (lmode.has_table())
            spare = sizeof(m_soo_table.m_data) - m_soo_table.m_count;
        else
            spare = sizeof(m_soo.m_data) - m_soo.m_count;

        if (rmode.storage() == mode::soo) {
            if (spare >= rhs.m_soo.m_count && same_table()) { // Append possible, and table equal (assuming each unique table has only one instance)
                memcpy(m_soo.m_data + m_soo.m_count, rhs.m_soo.m_data, rhs.m_soo.m_count);  // goto end of m_data and subtract spare to handle also m_soo_table case.
                m_soo.m_count += rhs.m_soo.m_count;
                return true;
            }
        }
        else if (rmode.storage() == mode::literal && same_table()) {
            ptrdiff_t rlen = rhs.m_literal.m_end - rhs.m_literal.m_begin;
            if (spare >= rlen) {
                memcpy(m_soo.m_data + m_soo.m_count, rhs.m_literal.m_begin, rlen);  // goto end of m_data and subtract spare to handle also m_soo_table case.
                m_soo.m_count += uint8_t(rlen);
                return true;
            }
        }
    }

    return false;
}

// If lhs is not literal this never works.
inline bool ustring::try_prepend(const ustring& lhs) {
    // Check if lhs + rhs fits into the soo storage of lhs
    mode rmode = get_mode();
    mode lmode = lhs.get_mode();

    auto same_table = [&] {
        if (lmode.has_table() != rmode.has_table())
            return false;

        if (!lmode.has_table())
            return true;

        return m_soo_table.m_table.ptr() == lhs.m_soo_table.m_table.ptr();
    };

    if (rmode.storage() == mode::soo && lmode.normalized_encoding() == rmode.normalized_encoding()) {
        // Different byte counts allowed depending on table mode of 'this'
        uint8_t spare;
        if (rmode.has_table())
            spare = sizeof(m_soo_table.m_data) - m_soo_table.m_count;
        else
            spare = sizeof(m_soo.m_data) - m_soo.m_count;

        if (lmode.storage() == mode::literal && same_table()) {
            ptrdiff_t llen = lhs.m_literal.m_end - lhs.m_literal.m_begin;
            if (spare >= llen) {
                copy_backward(m_soo.m_data, m_soo.m_data + m_soo.m_count, m_soo.m_data + m_soo.m_count + uint8_t(llen));
                memcpy(m_soo.m_data, lhs.m_literal.m_begin, llen);  // goto end of m_data and subtract spare to handle also m_soo_table case.
                m_soo.m_count += uint8_t(llen);
                return true;
            }
        }
    }

    return false;
}


inline ustring::impl* ustring::make_multi_impl(int count)
{
    assert(count <= part_ptr::max_extra);            // TODO: Merge strings by reallocation to reduce count enough.

    auto ip = make_impl(sizeof(impl) + (count - 1) * sizeof(ustring));
    ip->m_multi.m_capacity = count;
    ip->m_multi.m_count = 0;
    for (uint8_t i = 0; i < count; i++)
        new(&ip->m_multi.m_strings[i]) ustring;        // All ustrings are constructed.

    return ip;
}

// count is the total required count. Used when appending two multi strings.

inline void ustring::unref()
{
    if (!get_mode().is_shared())
        return;     // No external storage to remove

    auto& impl = get_impl();
    impl.m_refs--;
    if (impl.m_refs > 0)
        return;

    // Destroy the substrings of impl if mode is multi.
    if (get_mode().storage() == mode::multi) {
        for (int i = 0; i < impl.m_multi.m_count; i++)
            impl.m_multi.m_strings[i].~ustring();
    }

    // Get rid of the allocated memory
    delete[] reinterpret_cast<byte*>(&impl);
}


namespace detail {

    // Base case is used for combinations of char8_t, char16_t and char32_t which need transcoding but not codecvt calls.
    template<typename I, typename E> class filler_impl {
        static const size_t c_rawSize = 64 / sizeof(E); // Just a small buffer as we don't have to think about the codecvt::in overhead.
    public:
        filler_impl(size_t source_elements) : m_buf_ptr(m_buffer) {
            if (source_elements > 0) {
                // Crude guess, this can be improved, especially when E > I      
                setup(source_elements, std::max(22 / sizeof(I), source_elements / 10));
            }
            else
                setup(22 / sizeof(I), 256);
        }
        
        E& next() {
            if (m_buf_ptr == m_buffer + c_rawSize)
                flush(false);    // Including on first call!

            return *m_buf_ptr++;
        }

        ustring get_result() && {
            flush(true);
            if (m_buf_ptr != m_buffer)
                throw std::runtime_error("Retrieved result of ustring::filler when an incomplete code point is buffered");

            m_part.shrink_to(m_part_ptr);
            if (!m_str.empty()) {
                if (!m_part.empty()) {
                    m_str += m_part;
                }

                return move(m_str);
            }
            else
                return move(m_part);      // First buffer never overflowed.
        }        

    private:
        void flush(bool last) {
            const E* from = m_buffer;
            const E* end = m_buf_ptr;
            if (!last)
                 end -= 4 / sizeof(E);      // Don't continue into what could be an incomplete code point unless we're last

            while (from < end) { // Loop until m_buffer contains at most 4 / sizeof(E) code elements, or is empty in the last call.
                // First make sure that m_part can hold one code point.
                if (!transcode(m_part_ptr, m_part_end, from)) {
                    m_part.shrink_to(m_part_ptr);
                    m_str += m_part;
                    setup(m_next_size, m_next_size * 3 / 2);
                }
            }

            // Move the last unconverted code elements to the front of m_buffer and set m_buf_ptr after them
            E* to = m_buffer;
            while (from < m_buf_ptr)
                *to++ = *from++;
            m_buf_ptr = to;
        }

        void setup(size_t sz, size_t next) {
            m_part_ptr = m_part.setup<I>(sz);
            m_part_end = m_part_ptr + sz;
            m_next_size = next;
        }

        ustring m_str;
        ustring m_part;

        size_t m_next_size;
        I* m_part_ptr;
        I* m_part_end;

        // As the different encodings don't have a one to one relationship between code elements we need to intermediately store a
        // few code elements before transcoding. To make this more than 4 bytes amortizes the cost of moving the elements of the last to
        // the front of the buffer.
        E m_buffer[c_rawSize];
        E* m_buf_ptr;
    };

    // Simplified case which uses no intermediate buffering and stores each incoming code point as is. Still subdivides data into
    // parts as we may not know the length exactly, or at all from the onset.
    template<typename E> class filler_impl<E, E> {
    public:
        filler_impl(size_t source_elements) {
            if (source_elements > 0) {
                // Should be correct, but if not probably just a little spill over so set m_next_size
                // to 10% or at least the soo size.
                setup(source_elements, std::max(22 / sizeof(E), source_elements / 10));
            }
            else
                setup(22 / sizeof(E), 256);
        }
        
        E& next() {
            if (m_part_ptr == m_part_end)
                flush();    // Including on first call!

            return *m_part_ptr++;
        }

        ustring get_result() && {
            m_part.shrink_to(m_part_ptr);
            if (!m_str.empty()) {
                if (!m_part.empty()) {
                    m_str += m_part;
                }

                return move(m_str);
            }
            else
                return move(m_part);      // First buffer never overflowed.
        }        

    private:
        void flush() {
            m_str += m_part;
            setup(m_next_size, m_next_size * 3 / 2);
        }
        void setup(size_t sz, size_t next) {
            m_part_ptr = m_part.setup<E>(sz);
            m_part_end = m_part_ptr + sz;
            m_next_size = next;
        }

        ustring m_str;
        ustring m_part;

        size_t m_next_size;
        E* m_part_ptr;
        E* m_part_end;
    };


    // Specialization for char, I (where I is not char). If the encoding provided to the ctor can be converted to code points using a
    // simple look up table this implementation is as simple as the <E, E> implementation above. As this can't be determined at compile
    // time it has to be done using if on the existence of the table pointer in each flush. To reduce the number of if tests needed
    // the buffer is used also in this case.
    // Note: Only one of these per implementation will be instantiated, depending on the internal representation selected for narrow
    // external encodings, which is likely to be UTF-16 on Windows and UTF-8 on Linux.
    template<typename I> class filler_impl<I, char> {
        static const size_t c_rawSize = 1024;
    public:
        filler_impl(size_t source_elements) : filler_impl(source_elements, locale("")) {}      // Default to assuming the system locale. Not the global (Or what?)
        filler_impl(size_t source_elements, const locale& loc) : m_locale(loc), m_table(table_manager.get(loc)) {
            if (source_elements > 0) {
                // Should be correct, but if not probably just a little spill over so set m_next_size
                // to 10% or at least the soo size.
                setup(source_elements, std::max(soo_size(), source_elements / 10));
            }
            else
                setup(soo_size(), 256);
        }

        char& next() {
            if (m_pos == c_rawSize)
                flush();
            return m_buffer[m_pos++];
        }

        ustring get_result() && {
            flush();

            if (!m_str.empty()) {
                if (!m_part.empty()) {
                    m_part.shrink_to(m_part_ptr);
                    m_str += m_part;
                }

                return move(m_str);
            }
            else
                return move(m_part);      // First buffer never overflowed.
        }

    private:
        size_t soo_size() const {
            if (m_table == nullptr)
                return 22;
            else
                return 14;
        }

        void flush() {
            codecvt<I, char, mbstate_t> conv = use_facet<codecvt<wchar_t, char, mbstate_t>>(m_locale);

            char* from_next = m_buffer;    // This gets bumped if the current m_part is not large enough to hold the result and we have to loop back.
            char* from_end = m_buffer + m_pos;
            while (true) {
                if (m_part_ptr >= m_part_end - 4 / sizeof(I)) {
                    m_part.shrink_to(m_part_ptr);
                    m_str += m_part;
        
                    setup(m_next_size, m_next_size * 3 / 2);
                }

                I* to_next;
                auto res = conv.in(m_state, from_next, from_end, from_next, m_part.data<I>(), m_part_ptr, to_next);
                assert(res != std::codecvt_base::noconv);
                if (res == std::codecvt_base::error)
                    throw std::runtime_error("ustring::filler was given an illegal input string");

                m_part_ptr = to_next;
                size_t from_left = from_end - from_next;        // char chars not converted.
                if (from_left == 0) {     // Source contained complete code points, nothing more to do.
                    m_pos = 0;
                    break;
                }

                if (m_part_ptr >= m_part_end  - 4 / sizeof(I)) // Destination almost flled. Loop back to continue converting into the next part.
                    continue;

                if (res == std::codecvt_base::partial) {
                    // m_buffer ends with a partial code point. Must move that to start of m_buffer to get the rest.
                    if (m_pos < c_rawSize)
                        throw std::runtime_error("Tried to extract a ustring when the ustring::filler wasn't given a complete code point last");

                    // Move the (few) char characters not converted to the head of the buffer.
                    std::copy_n(from_next, from_left, m_buffer);
                    m_pos = uint16_t(from_left);
                }

                break;
            }
        }

        void setup(size_t sz, size_t next) {
            m_part_ptr = m_part.setup<I>(sz, m_table);
            m_part_end = m_part_ptr + sz;
            m_next_size = next;
        }

        ustring m_str;      // Multipart result string
        ustring m_part;     // Next part in a sequence of longer and longer parts

        size_t m_next_size;
        I* m_part_ptr;
        I* m_part_end;

        char m_buffer[c_rawSize];
        uint16_t m_pos;

        locale m_locale;
        mbstate_t m_state{};
        char32_t* m_table;      // If set it indicates a simpler flush to be done.
    };

}  // namespace detail


//////////////// ustring::filler methods and specializations ////////////////

// The filler class presents an output_iterator API for adding E characters to an internal representation depending on E.
// If E is char a constructor taking a locale object is available, else 'system' is assumed.
template<character E> class ustring::filler {
public:
    filler(size_t external_size = 0): m_impl(external_size) {}

    // ctors available only on char fillers, which specify an external encoding other than 'system'
    filler(const locale& locale, size_t external_size = 0) requires(is_same_v<E, char>) : m_impl(locale, external_size) {}

    E& operator*() { return m_impl.next(); }
    filler& operator++() { return *this; }
    filler& operator++(int) { return *this; }

    operator ustring() && { return move(m_impl).get_result(); }

private:
    detail::filler_impl<detail::default_representation_t<E>, E> m_impl;
};


//////////////// ustring::loader methods ////////////////

inline ustring::loader::loader(const locale& loc, size_t source_size) : m_source_size(source_size), m_locale(loc)
{
    assert((has_facet<codecvt<wchar_t, char, mbstate_t>>(m_locale)));

    if (source_size > 0) {
        // As an initial attempt, and as we don't know anything about the source encoding, assume same size as source.
        if constexpr (sizeof(wchar_t) == 2)
            m_buffer = m_str.setup(source_size, utf16);
        else
            m_buffer = m_str.setup(source_size, utf8);      // On linux do a double conversion resulting in utf8 which is mostly used there.

        m_capacity_left = source_size;
        m_allocated_size = source_size;
    }
}

inline bool ustring::loader::append(const char* buffer, size_t sz)
{
    mbstate_t ost{};        // used between sub-conversions if wchar_t is 32 bits.

    while (sz > 0) {
        reallocate(sz);

        // Actually perform the conversion using codecvt facet of m_locale
        if constexpr (sizeof(wchar_t) == 2) {
            auto& cvt = use_facet<codecvt<wchar_t, char, mbstate_t>>(m_locale);
            const char* from_next;
            wchar_t* to_next;
            auto result = cvt.in(m_state, buffer, buffer + sz, from_next, reinterpret_cast<wchar_t*>(m_buffer), reinterpret_cast<wchar_t*>(m_buffer) + m_capacity_left, to_next);
            size_t produced_bytes = reinterpret_cast<byte*>(to_next) - m_buffer;
            size_t consumed_bytes = from_next - buffer;
            sz -= consumed_bytes;
            m_consumed_so_far += consumed_bytes;
            m_buffer += produced_bytes;
            m_capacity_left -= produced_bytes;
            
            if (result == codecvt_base::noconv)
                assert(false);      // Unclear how to handle this. Does it mean that conversion is impossible or that we can just copy the buffers?
            if (result == codecvt_base::error)
                return false;       // No recovery possible in codecvt API
            m_complete = result == codecvt_base::ok;
        }
        else {
            auto& cvt = use_facet<codecvt<wchar_t, char, mbstate_t>>(m_locale);
            const char* from_next;
            wchar_t temp[1024];     // 4096 bytes on the stack.
            wchar_t* temp_next;
            auto result = cvt.in(m_state, buffer, buffer + sz, from_next, temp, temp + 1024, temp_next);
            size_t consumed_bytes = from_next - buffer;
            sz -= consumed_bytes;
            m_consumed_so_far += consumed_bytes;

            if (result == codecvt_base::noconv)
                assert(false);      // Unclear how to handle this. Does it mean that conversion is impossible or that we can just copy the buffers?
            if (result == codecvt_base::error)
                return false;       // No recovery possible in codecvt API
            m_complete = result == codecvt_base::ok;

            // Continue conversion to utf8, possibly reallocating it until all of temp has been converted.
            auto& to8 = use_facet<codecvt<char32_t, char8_t, mbstate_t>>(m_locale);
            char8_t* to_next;
            const char32_t* temp_final;
            while (true) {
                result = to8.out(ost, reinterpret_cast<const char32_t*>(temp), reinterpret_cast<const char32_t*>(temp_next), temp_final, reinterpret_cast<char8_t*>(m_buffer), reinterpret_cast<char8_t*>(m_buffer) + m_capacity_left, to_next);
                if (result == codecvt_base::noconv)
                    assert(false);      // Unclear how to handle this. Does it mean that conversion is impossible or that we can just copy the buffers?
                if (result == codecvt_base::error)
                    return false;       // No recovery possible in codecvt API

                size_t produced_bytes = to_next - reinterpret_cast<char8_t*>(m_buffer);
                m_buffer += produced_bytes;
                m_capacity_left -= produced_bytes;

                if (temp_final == reinterpret_cast<const char32_t*>(temp_next))        // The entire temporary buffer was consumed, so conversion of this temp buffer is done. Loop back to start working on the next temp buffer.
                    break;

                reallocate(sz + (reinterpret_cast<const char32_t*>(temp_next) - temp_final) * 2);    // Make room for 2 bytes per code point + the number of source bytes left.
                temp_next = const_cast<wchar_t*>(reinterpret_cast<const wchar_t*>(temp_final));
            }
        }
    }

    return true;
}

inline void ustring::loader::reallocate(size_t sz)
{
    if (m_capacity_left > 0)
        return;
    
    double ratio = double(m_consumed_so_far) / double(m_allocated_size);    // Number of source bytes per destination byte.

    // If have still consumed less than or equal to the initial source_size assume we won't be seeing more.
    if (m_consumed_so_far + sz < m_source_size)
        m_capacity_left = size_t(ratio * (m_source_size - m_consumed_so_far));
    else if (m_source_size == 0) {  // No source size was given, make next buffer 1.5 times the previous.
        if (m_allocated_size == 0)
            m_capacity_left = min(sz * 10, size_t(4096));   // First time allocate 4096 bytes unless sz is really small.
        else
            m_capacity_left = m_allocated_size * 3 / 2;
    }
    else        // We had an initial guess but has overran it. We can still use ratio, but we don't know anything about how much more will be presented.
        m_capacity_left = size_t(ratio * m_allocated_size * 3 / 2 + 1) & size_t(-2);  // Avoid odd number of bytes in case the internal storage is utf16 or cvt.in may never produce the last byte.

    ustring next;
    if constexpr (sizeof(wchar_t) == 2)
        m_buffer = next.setup(m_capacity_left, utf16);
    else
        m_buffer = next.setup(m_capacity_left, utf8);      // On linux do a double conversion resulting in utf8 which is mostly used there.

    m_allocated_size += m_capacity_left;
    m_str += next;
}

inline ustring ustring::loader::str() &&
{
    // Update the end pointer of str.
    auto set_end = [&](ustring& str) {
        switch (str.get_mode().storage()) {
        case ustring::mode::shared:
            str.m_shared.m_end = m_buffer;
            return;
        case ustring::mode::soo:
            if (str.get_mode().has_table())
                str.m_soo_table.m_count = uint8_t(m_buffer - str.m_soo_table.m_data);
            else
                str.m_soo.m_count = uint8_t(m_buffer - str.m_soo.m_data);
            return;

        default:
            assert(false);
        }
    };

    // Find last part if multi was created.
    if (m_str.get_mode().storage() == ustring::mode::multi) {
        uint8_t parts = m_str.get_impl().m_multi.m_count;
        m_str.m_multi.m_end = ustring::part_ptr(parts - 1, m_buffer);  // Isn't the end at begin of next part (with unspecified ptr)?
        set_end(m_str.get_part(parts - 1));
    }
    else
        set_end(m_str);

    return move(m_str);
}


//////////////// ustring::saver methods ////////////////

inline ustring::saver::saver(const locale& loc, const ustring& src, char bad_char) : m_source(src), m_pos(src.begin()), m_locale(loc), m_bad_char(bad_char)
{
}

inline ustring::saver::saver(const locale& loc, const ustring& src, const ustring::iterator& start, char bad_char) : m_source(src), m_pos(start), m_locale(loc), m_bad_char(bad_char)
{
}

inline size_t ustring::saver::estimated_size(safety_margin margin) const
{
    size_t ret = m_source.bytes();
    size_t sizes[4] = { 10, 11, 20, 40 };       // This can be improved by a lot.
    return ret * sizes[int(margin)] / 10;
}

inline codecvt_base::result ustring::saver::fill(char* buffer, size_t& sz)
{
    assert(sz >= 4);            // Buffer must be at least four bytes or we can get stuck not being able to convert even a single code point.
    
    auto& cvt = use_facet<codecvt<wchar_t, char, mbstate_t>>(m_locale);

    // First check if our internal storage is contiguous and compatible with wchar_t, depending on size of wchar_t.
    if (m_source.encoding() == ustring::wide || sizeof(wchar_t) == 2 && m_source.encoding() == ustring::utf16 || sizeof(wchar_t) == 4 && m_source.encoding() == ustring::utf32) {
        const wchar_t* start = reinterpret_cast<const wchar_t*>(m_pos.pos());
        const wchar_t* from_next;
        char* to_next;
        // PROBLEM: codecvt does not allow injecting bad_char when a code point can't be converted to char. Instead it returns
        // error. Maybe this can be solved by another loop, presuming the from_next and to_next are left before the code point that
        // could not be converted.
        auto result = cvt.out(m_state, start + m_consumed, reinterpret_cast<const wchar_t*>(m_source.get_end().ptr()), from_next, reinterpret_cast<char*>(buffer), reinterpret_cast<char*>(buffer) + sz, to_next);
        sz = to_next - buffer;

        if (result == codecvt_base::noconv)
            assert(false);      // Unclear how to handle this. Does it mean that conversion is impossible or that we can just copy the buffers?
        if (result == codecvt_base::error)
            return result;       // No recovery possible in codecvt API. Maybe we could add a m_bad_char to the output and then continue.

        m_pos.set_pos(reinterpret_cast<const byte*>(from_next));
        if (m_pos == m_source.end() && result == codecvt_base::ok)
            return codecvt_base::ok;
        else
            return codecvt_base::partial;
    }

    // If the internal storage is multi or if the encoding is not compatible with wchar_t use an intermediate buffer, which is
    // filled using copy.
    wchar_t temp[1024];
    size_t produced = 0;
    while (true) {
        const wchar_t* temp_end = temp + m_source.copy(temp, 1024, m_pos);
        const wchar_t* temp_next;
        char* to_next;
        auto result = cvt.out(m_state, temp, temp_end, temp_next, reinterpret_cast<char*>(buffer), reinterpret_cast<char*>(buffer) + sz, to_next);
        produced += to_next - buffer;
        buffer = to_next;

        if (result == codecvt_base::noconv)
            assert(false);      // Unclear how to handle this. Does it mean that conversion is impossible or that we can just copy the buffers?
        if (result == codecvt_base::error)
            return result;       // No recovery possible in codecvt API

        if (temp_next == temp_end && m_pos == m_source.end()) {
            sz = produced;
            return codecvt_base::ok;
        }

        // Destination buffer may not hold another converted code point, so return and ask for more buffer rather than looping back
        // and possibly get stuck.
        if (produced + 4 >= sz) {
            // Adjust m_pos, which is tricky if temp_next indicates that the entrire temp buffer was not consumed.
            if (m_pos != m_source.end() || result == codecvt_base::partial) {
                if (temp_next < temp_end) {
                    // Back up m_pos to re-convert last part of temp on next call. Unfortunately, if wchar_t is 2 bytes, i.e.
                    // utf16, we must count the number of surrogate pairs in the remaining part of temp to see what this count is.
                    if constexpr (sizeof(wchar_t) == 4)
                        m_pos.advance(temp_next - temp_end);
                    else {
                        const wchar_t* ptr = temp_next;
                        ptrdiff_t count = 0;
                        while (ptr < temp_end) {
                            wchar_t next = *ptr++;
                            if (next >= 0xD800 && next < 0xE000)
                                ptr++;
                            count++;
                        }

                        m_pos.advance(-count);      // Move m_pos from a position corresponding to temp_end to a position corresponding to temp_next.
                        // TODO: Time consumption can be halved, on average, by keeping the old m_pos around since before
                        // m_source.copy and move from there if temp_next is less than halfways.
                    }
                }
            }

            sz = produced;
            return codecvt_base::partial;
        }
    }
}


//////////////// Function implementations ////////////////

// Literal operators
namespace literals::string_literals {

    inline ustring operator""_u(const char* ptr, size_t sz) { return ustring::view(ptr, sz, locale()); }        // Literals use C locale as a placeholder for "execution" charset.
    inline ustring operator""_u(const wchar_t* ptr, size_t sz) { return ustring::view(ptr, sz); }
    inline ustring operator""_u(const char8_t* ptr, size_t sz) { return ustring::view(ptr, sz); }
    inline ustring operator""_u(const char16_t* ptr, size_t sz) { return ustring::view(ptr, sz); }
    inline ustring operator""_u(const char32_t* ptr, size_t sz) { return ustring::view(ptr, sz); }

#ifdef IS_STANDRADIZED

    inline ustring operator""u(const char* ptr, size_t sz) { return ustring::view(ptr, sz, locale()); }        // Literals use C locale as a placeholder for "execution" charset.
    inline ustring operator""u(const wchar_t* ptr, size_t sz) { return ustring::view(ptr, sz); }
    inline ustring operator""u(const char8_t* ptr, size_t sz) { return ustring::view(ptr, sz); }
    inline ustring operator""u(const char16_t* ptr, size_t sz) { return ustring::view(ptr, sz); }
    inline ustring operator""u(const char32_t* ptr, size_t sz) { return ustring::view(ptr, sz); }

#endif

}

strong_ordering lexicographical_compare(const ustring& lhs, const ustring& rhs, const locale& loc);
strong_ordering case_insensitive_compare(const ustring& lhs, const ustring& rhs, const locale& loc);


// Helpers for unicode code points. These are probably trivial if wchar_t is 32 bits as it just defers to iswspace but less so for
// 16 bit wchar_t unless all blanks are in the first unicode page. Unclear if we want to make this C function compatible, if so it
// may be called isuspace and there could be a complete set, including touupper and toulower for case conversion.
bool is_space(char32_t);

// Probably trimming does not need to know locale as whitespace unicode code point denotation should be locale indifferent.
inline ustring trim_front(const ustring& src)
{
    auto i = src.begin();
    auto e = src.end();
    while (i != e && is_space(*i))
        ++i;

    return src.substr(i, e);
}


inline ustring trim_back(const ustring& src)
{
    auto i = src.end();
    auto b = src.begin();
    while (i != b && is_space(*--i))
        ;

    return src.substr(b, i);
}


inline ustring trim(const ustring& src)	// Trim both ends.
{
    auto i = src.begin();
    auto e = src.end();
    while (i != e && is_space(*i))
        ++i;

    if (i == e)
        return ustring();
    
    while (is_space(*--e))
        ;

    return src.substr(i, e);
}

inline ustring tolower(const ustring& src, const locale& loc)
{
    auto& ct = use_facet<ctype<char32_t>>(loc);

    ustring::filler<char32_t> f;
    for (auto c : src)
        *f++ = ct.tolower(c);

    return move(f);
}

inline ustring toupper(const ustring& src, const locale& loc)
{
    auto& ct = use_facet<ctype<char32_t>>(loc);

    ustring::filler<char32_t> f;
    for (auto c : src)
        *f++ = ct.toupper(c);

    return move(f);
}
        
inline ustring capitalize(const ustring& src, const locale& loc)
{
    auto& ct = use_facet<ctype<char32_t>>(loc);

    ustring::filler<char32_t> f;
    auto iter = src.begin();
    if (iter == src.end())
        return src;

    *f++ = ct.toupper(*iter++);
    while (iter != src.end())
        *f++ = ct.tolower(*iter++);

    return move(f);
}


inline ustring insert(const ustring& source, ustring::iterator start, const ustring& addition)
{
    return replace(source, start, start, addition);
}


inline ustring replace(const ustring& source, ustring::iterator start, ustring::iterator end, const ustring& replacement)
{
    return source.first(start) + replacement + source.last(end);
}


inline ustring replace(const ustring& source, pair<ustring::iterator, ustring::iterator> where, const ustring& replacement)
{
    return replace(source, where.first, where.second, replacement);
}


inline ustring replace(const ustring& source, const ustring& pattern, const ustring& replacement, size_t max_count)
{
    ustring ret;
    auto prev = source.begin();
    auto ends = source.find_ends(pattern);
    while (ends.first != source.end() && max_count > 0) {
        ret += source.substr(prev, ends.first) + replacement;
        prev = ends.second;
        ends = source.find_ends(pattern, ends.second);      // Continue searching from after the previous find
        max_count--;
    }

    return ret + source.last(prev);
}

inline ustring erase(const ustring& source, ustring::iterator start, ustring::iterator end)
{
    return source.first(start) + source.last(end);
}

inline ustring erase(const ustring& source, const pair<ustring::iterator, ustring::iterator>& ends)
{
    return erase(source, ends.first, ends.second);
}


// Split with some mode flags. Keeping flags at default ensures that the original string is recreated by join with the same
// delimiter. 
inline vector<ustring> split(const ustring& src, const ustring& delimiter, size_t max_count, bool trim_parts, bool noempties)
{
    vector<ustring> ret;
    ustring rest = src;
    auto p = delimiter.begin();
    auto pe = delimiter.end();
    assert(pe != p);
    
    char32_t c = *p;
    ++p;
    
    for (int i = 0; i < max_count - 1; i++) {
        if (rest.empty())
            return ret;
        
        auto [next, next_end] = rest.find_ends(delimiter);
        ustring part = rest.first(next);       // Could be all of it
        if (trim_parts)
            part = trim(part);
        if (!noempties || !part.empty())
            ret.push_back(part);

        rest = rest.last(next_end);
    }

    // Count reached, rest must be appended.
    if (trim_parts)
        rest = trim(rest);
    if (!noempties || !rest.empty())
        ret.push_back(rest);

    return ret;
}


// Note: As long as parts have the same encoding as delimiter everything will end up in one long ustring without multi.
// If encodings differ those that don't have delimiter's encoding end up in separate parts unless this would yield too many parts,
// in which case further compression is done by transcoding everyhing to the delimiter's encoding, or if need be to the encoding of
// the first part able to encode all unicode code points.
//ustring join(const vector<ustring>& parts, const ustring& delimiter)
//{
//    auto compressed = join(&*parts.begin(), &*parts.end(), delimiter);
//    return ustring(&*compressed.begin(), &*compressed.end());
//}
//
}

