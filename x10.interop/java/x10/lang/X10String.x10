/*
 *  This file is part of the X10 project (http://x10-lang.org).
 *
 *  This file is licensed to You under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *      http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  (C) Copyright IBM Corporation 2006-2010.
 */

package x10.lang;

import x10.compiler.Native;
import x10.compiler.Inline;
import x10.compiler.NoInline;
import x10.compiler.NoReturn;
import x10.compiler.CompilerFlags;
import x10.util.Ordered;
import x10.util.ArrayList;
import x10.util.IndexedMemoryChunk;

/**
 * The String class represents character strings.
 * All string literals in X10 programs, such as "Hello", are instances of String.
 * Strings are immutable and cannot be changed after they are created.
 *
 * String provides a concatenation operator '+', methods for converting
 * instances of other types to strings (which invoke the
 * {@link x10.lang.Any#toString()} method), methods for examining individual
 * characters of the sequence, for searching strings, for comparing
 * strings, for extracting substrings, and for creating a copy of a string
 * with all characters translated to uppercase or to lowercase.  Case mapping
 * is defined in {@link x10.lang.Char}.
 */
public final class X10String implements (Int) => Char, Ordered[X10String], Comparable[X10String] {

    val content: IndexedMemoryChunk[Char]; // TODO: UTF-8

    /**
     * Default constructor.
     */
    public def this(): X10String {
        this.content = IndexedMemoryChunk.allocateUninitialized[Char](1);
        this.content(0) = '\0';
    }

    /**
     * Copy constructor.
     */
    public def this(s: X10String): X10String {
        this.content = s.content;
    }

    /**
     * Construct a String from an Array[Byte].
     */
    public def this(r:Array[Byte], offset:Int, length:Int): X10String { // TODO: UTF-8
        val content = IndexedMemoryChunk.allocateUninitialized[Char](length+1);
        for (i in 0..(length-1)) {
            content(i) = r(offset + i) as Char;
        }
        content(length) = '\0';
        this.content = content;
    }

    /**
     * Construct a String from an Array[Char].
     */
    public def this(r:Array[Char], offset:Int, length:Int): X10String { // TODO: UTF-8
        val content = IndexedMemoryChunk.allocateUninitialized[Char](length+1);
        for (i in 0..(length-1)) {
            content(i) = r(offset + i);
        }
        content(length) = '\0';
        this.content = content;
    }

    /**
     * Construct a String from an IndexedMemoryChunk[Char] (share).
     */
    private def this(r:IndexedMemoryChunk[Char]): X10String { // TODO: UTF-8
        this.content = r;
    }

    /**
     * Return true if the given entity is a String, and this String is equal
     * to the given entity.
     * @param x the given entity
     * @return true if this String is equal to the given entity.
     */
    public def equals(x:Any): Boolean {
        if (x == null) return false;
        if (x == this) return true; // short-circuit trivial equality
        if (!(x instanceof X10String)) return false;
        val that: X10String = x as X10String;
        if (this.content.length() != that.content.length()) return false; // short-circuit trivial dis-equality
        if (strncmp(this.content, 0, that.content, 0, this.length()) != 0)
            return false;
        return true;
    }

    // FIXME: Locale sensitivity
    /**
     * Returns true if this String is equal to the given String, ignoring case considerations.
     * @param that the given String
     * @return true if this String is equal to the given String ignoring case.
     */
    public def equalsIgnoreCase(that:X10String): Boolean {
        if (that == null) return false;
        if (that == this) return true; // short-circuit trivial equality
        if (this.content.length() != that.content.length()) return false; // short-circuit trivial dis-equality
        if (strncasecmp(this.content, 0, that.content, 0, this.length()) != 0)
            return false;
        return true;
    }

    /**
     * Returns a hash code for this String.
     * The hash code for a String object is computed as
     * <pre>
     * s(0).ord()*31^(n-1) + s(1).ord()*31^(n-2) + ... + s(n-1).ord()
     * </pre>
     * using integer arithmetic, where s(i) is the ith character of the string,
     * n is the length of the string, and ^ indicates exponentiation.
     * (The hash value of the empty string is zero.)
     * @return a hash code value for this String.
     */
    public def hashCode(): Int {
        var hc:Int = 0;
        var l:Int = length();
        val r = content;
        var k:Int = 0;
        for (; l > 0; k++, l--) {
            hc *= 31;
            hc += r(k).ord();
        }
        return hc;
    }


    /**
     * Returns this String.
     * @return the String itself.
     */
    public @Inline def toString(): X10String = this;


    /**
     * Returns the length of this String.
     * @return the length of this String.
     */
    public @Inline def length(): Int = this.content.length() - 1;

    /**
     * Returns the Char at the specified index in this String.
     * An index ranges from 0 to length()-1.
     * @param index the index of the Char
     * @return the Char at the specified (0-based) index of this String.
     * @see #charAt(Int)
     */
    public @Inline operator this(index: Int): Char = this.charAt(index);

    /**
     * Returns the Char at the specified index in this String.
     * An index ranges from 0 to length()-1.
     * @param index the index of the Char
     * @return the Char at the specified (0-based) index of this String.
     * @see #operator(Int)
     */
    public @Inline def charAt(index: Int): Char {
        val content_length = content.length() - 1;
        if (CompilerFlags.checkBounds() && index > content_length) {
            raiseStringIndexOutOfBoundsException(index, content_length);
        }
        return content(index);
    }

    private static @NoInline @NoReturn def raiseStringIndexOutOfBoundsException(index: Int, length: Int) {
        throw new StringIndexOutOfBoundsException("index = "+index+"; length = "+length);
    }

    /**
     * Converts this String to an Array of Chars.
     * @return an Array of Chars whose length is the length of this String and
     *         whose contents are initialized to contain the Chars in this String.
     * @see #bytes()
     */
    public def chars():Rail[Char] { // TODO: UTF-8
        val r = content;
        return new Array[Char](length(), (i:Int)=>r(i));
    }

    /**
     * Encodes this String into a sequence of Bytes using the platform's default charset.
     * @return the Array of Bytes representing this String in the default charset.
     * @see #chars()
     */
    public def bytes():Rail[Byte] { // TODO: UTF-8
        val r = content;
        return new Array[Byte](length(), (i:Int)=>r(i).ord() as Byte);
    }

    /**
     * Returns a new String that is a substring of this String.
     * The substring begins at the specified fromIndex and extends to the Char at index toIndex-1.
     * Thus the length of the substring is toIndex-fromIndex.
     * @param fromIndex the starting index, inclusive
     * @param toIndex the ending index, exclusive
     * @return the specified substring.
     */
    public def substring(fromIndex: Int, toIndex: Int): X10String {
        val content_length = content.length() - 1;
        if (CompilerFlags.checkBounds() && fromIndex < 0) {
            raiseStringIndexOutOfBoundsException(fromIndex, content_length);
        }
        if (CompilerFlags.checkBounds() && fromIndex > toIndex) {
            raiseStringIndexOutOfBoundsException(fromIndex, toIndex);
        }
        if (CompilerFlags.checkBounds() && toIndex > content_length) {
            raiseStringIndexOutOfBoundsException(toIndex, content_length);
        }
        val sz = toIndex - fromIndex;
        val r = content;
        val str = IndexedMemoryChunk.allocateUninitialized[Char](sz+1);
        for (i in 0..(sz-1)) {
            str(i) = r(fromIndex + i);
        }
        str(sz) = '\0';
        return new X10String(str);
    }

    /**
     * Returns a new String that is a substring of this String.
     * The substring begins at the specified fromIndex and extends to last Char in the String.
     * Thus the length of the substring is length()-fromIndex-1.
     * @param fromIndex the starting index, inclusive
     * @return the specified substring.
     */
    public @Inline def substring(fromIndex: Int): X10String = substring(fromIndex, this.length());

    /**
     * Returns the index within this String of the first occurrence of the specified Char ch.
     * If the Char ch occurs in this String, then the index of the first such occurrence is returned.
     * This index is the smallest value k such that:
     * <pre>
     * this(k) == ch
     * </pre>
     * is true.
     * If no such Char occurs in this String, then -1 is returned.
     * @param ch the given Char
     * @return the index of the first occurrence of the Char in this String, or -1 if the Char does not occur.
     * @see #indexOf(Char,Int)
     * @see #indexOf(String)
     * @see #lastIndexOf(Char)
     */
    public @Inline def indexOf(ch: Char): Int = indexOf(ch, 0);

    /**
     * Returns the index within this String of the first occurrence of the specified Char ch after
     * the given index i.  If the Char ch occurs in this String after the index i, then the index
     * of the first such occurrence is returned.
     * This index is the smallest value k&gt;=i such that:
     * <pre>
     * this(k) == ch
     * </pre>
     * is true.
     * If no such Char occurs in this String, then -1 is returned.
     * @param ch the given Char
     * @param i the given index
     * @return the index of the first occurrence of the Char in this String after the given index,
     *         or -1 if the Char does not occur.
     * @see #indexOf(Char)
     * @see #indexOf(String,Int)
     * @see #lastIndexOf(Char,Int)
     */
    public @Inline def indexOf(ch: Char, i: Int): Int = strnchr(content, i, content.length()-1, ch);

    private static def strnchr(haystack: IndexedMemoryChunk[Char], start: Int, end: Int, needle: Char): Int {
        val offset = (start < 0) ? 0 : start;
        for (i in offset..(end-1)) {
            if (haystack(i) == needle)
                return i;
        }
        return -1;
    }

    /**
     * Returns the index within this String of the first occurrence of the specified substring.
     * The Int returned is the smallest value k such that:
     * <pre>
     * this.substring(k, k+str.length()).equals(str)
     * </pre>
     * is true.
     * @param str the substring to search for
     * @return if the String argument occurs as a substring within this String,
     *         then the index of the first character of the first such substring
     *         is returned. If it does not occur as a substring, -1 is returned.
     * @see #indexOf(String,Int)
     * @see #indexOf(Char)
     * @see #lastIndexOf(String)
     */
    public @Inline def indexOf(str: X10String): Int = indexOf(str, 0);

    /**
     * Returns the index within this String of the first occurrence of the specified substring after
     * the given index i.
     * The Int returned is the smallest value k&gt;=i such that:
     * <pre>
     * this.substring(k, k+str.length()).equals(str)
     * </pre>
     * is true.
     * @param str the substring to search for
     * @param i the given index
     * @return if the String argument occurs as a substring within this String after the given index,
     *         then the index of the first character of the first such substring
     *         is returned. If it does not occur as a substring, -1 is returned.
     * @see #indexOf(String)
     * @see #indexOf(Char,Int)
     * @see #lastIndexOf(String,Int)
     */
    public @Inline def indexOf(str: X10String, i: Int): Int = strnstrn(content, i, content.length()-1, str.content);

    private static def strnstrn(haystack: IndexedMemoryChunk[Char], start: Int, end: Int, needle: IndexedMemoryChunk[Char]): Int {
        val offset = (start < 0) ? 0 : start;
        if (offset >= end) return -1;
        val needle_sz = needle.length()-1;
        val haystack_sz = end - offset;
        if (haystack_sz < needle_sz)
            return -1;
        for (i in offset..(end-needle_sz)) {
            if (strncmp(haystack, i, needle, 0, needle_sz) == 0)
                return i;
        }
        return -1;
    }

    private static def strncmp(left: IndexedMemoryChunk[Char], loff: Int, right: IndexedMemoryChunk[Char], roff: Int, len: Int): Int {
        for (i in 0..(len-1)) {
            val diff = left(loff + i) - right(roff + i);
            if (diff != 0)
                return diff;
        }
        return 0;
    }

    private static def strncasecmp(left: IndexedMemoryChunk[Char], loff: Int, right: IndexedMemoryChunk[Char], roff: Int, len: Int): Int {
        for (i in 0..(len-1)) {
            val diff = left(loff + i).toLowerCase() - right(roff + i).toLowerCase();
            if (diff != 0)
                return diff;
        }
        return 0;
    }

    /**
     * Returns the index within this String of the last occurrence of the specified Char ch.
     * If the Char ch occurs in this String, then the index of the last such occurrence is returned.
     * This index is the largest value k such that:
     * <pre>
     * this(k) == ch
     * </pre>
     * is true.
     * If no such Char occurs in this String, then -1 is returned.
     * The String is searched backwards starting at the last Char.
     * @param ch the given Char
     * @return the index of the last occurrence of the Char in this String, or -1 if the Char does not occur.
     * @see #lastIndexOf(Char,Int)
     * @see #lastIndexOf(String)
     * @see #indexOf(Char)
     */
    public @Inline def lastIndexOf(ch: Char): Int = lastIndexOf(ch, this.length()-1);

    /**
     * Returns the index within this String of the last occurrence of the specified Char ch before
     * the given index i.  If the Char ch occurs in this String before the index i, then the index
     * of the last such occurrence is returned.
     * This index is the largest value k&lt;=i such that:
     * <pre>
     * this(k) == ch
     * </pre>
     * is true.
     * If no such Char occurs in this String, then -1 is returned.
     * The String is searched backwards starting at index i.
     * @param ch the given Char
     * @param i the given index
     * @return the index of the last occurrence of the Char in this String before the given index,
     *         or -1 if the Char does not occur.
     * @see #lastIndexOf(Char)
     * @see #lastIndexOf(String,Int)
     * @see #indexOf(Char,Int)
     */
    public @Inline def lastIndexOf(ch: Char, i: Int): Int = strnrchr(content, 0, i+1, ch);

    private static def strnrchr(haystack: IndexedMemoryChunk[Char], start: Int, end: Int, needle: Char): Int {
        val endOffset = (end < 0) ? 0 : end;
        if (end > haystack.length()) return -1;
        for (i in (-endOffset+1)..(-start)) {
            if (haystack(-i) == needle)
                return -i;
        }
        return -1;
    }

    /**
     * Returns the index within this String of the rightmost occurrence of the specified substring.
     * The rightmost empty string "" is considered to occur at the index value this.length().
     * The returned index is the largest value k such that:
     * <pre>
     * this.substring(k, k+str.length()).equals(str)
     * </pre>
     * is true.
     * @param str the substring to search for
     * @return if the String argument occurs one or more times as a substring
     *         within this String, then the index of the first character of the
     *         last such substring is returned. If it does not occur as a
     *         substring, -1 is returned.
     * @see #lastIndexOf(String,Int)
     * @see #lastIndexOf(Char)
     * @see #indexOf(String)
     */
    public @Inline def lastIndexOf(str: X10String): Int = lastIndexOf(str, this.length()-1);

    /**
     * Returns the index within this String of the rightmost occurrence of the specified substring
     * before the given index i.
     * The rightmost empty string "" is considered to occur at the index value this.length().
     * The returned index is the largest value k&lt;=i such that:
     * <pre>
     * this.substring(k, k+str.length()).equals(str)
     * </pre>
     * is true.
     * @param str the substring to search for
     * @param i the given index
     * @return if the String argument occurs one or more times as a substring
     *         within this String before the given index, then the index of the first character of the
     *         last such substring is returned. If it does not occur as a
     *         substring, -1 is returned.
     * @see #lastIndexOf(String)
     * @see #lastIndexOf(Char,Int)
     * @see #indexOf(String,Int)
     */
    public def lastIndexOf(str: X10String, i: Int): Int = strnrstrn(content, 0, i+1, str.content);

    public static def strnrstrn(haystack: IndexedMemoryChunk[Char], start: Int, end: Int, needle: IndexedMemoryChunk[Char]) {
        val endOffset = (end < 0) ? 0 : end;
        if (end > haystack.length()) return -1;
        val needle_sz = needle.length()-1;
        val haystack_sz = endOffset - start;
        if (haystack_sz < needle_sz)
            return -1;
        for (i in (-endOffset+needle_sz)..(-start)) {
            if (strncmp(haystack, -i, needle, 0, needle_sz) == 0)
                return -i;
        }
        return -1;
    }


    /**
     * Splits this String around matches of the given string; 
     * unlike in Java the splitting String is treated as a simple String
     * to be matched character by character (as in indexOf), not as 
     * a regular expression.
     * Trailing empty strings are not included in the resulting Array.
     *
     * @param delim the String to use as a delimiter.
     * @return the Array of Strings computed by splitting this String around matches of the delimiter.
     */
    public def split(delim: X10String):Rail[X10String] {
        if (delim.equals("")) {
            return new Rail[X10String](this.length(), (i:Int)=>this.substring(i, i+1));
        }
        val ans = new ArrayList[X10String]();
        var pos:Int = 0;
        var nextMatch:Int = this.indexOf(delim, pos);
        while (nextMatch != -1) {
          ans.add(this.substring(pos, nextMatch));
          pos = nextMatch+delim.length();
          nextMatch = this.indexOf(delim, pos);
        }
        if (pos < this.length()) {
            ans.add(this.substring(pos, this.length()));
        }
        return ans.toArray();
    }


    /**
     * Returns a copy of the string with leading and trailing whitespace removed.
     * @return The new string with no leading/trailing whitespace.
     */
    public def trim(): X10String {
        val r = content;
        var start: Int = 0;
        var l: Int = content.length() - 1;
        var didSomething: Boolean = false;
        if (l==0) { return this; } // string is empty
        while (isws(r(start)) && l>0) { start++; l--; didSomething = true; }
        while (isws(r(start+l-1)) && l>0) { l--; didSomething = true; }
        if (!didSomething) { return this; }
        val trimmed: IndexedMemoryChunk[Char] = IndexedMemoryChunk.allocateUninitialized[Char](l+1);
        for (i in 0..(l-1)) {
            trimmed(i) = r(start+i);
        }
        trimmed(l) = '\0';
        return new X10String(trimmed);
    }

    // [DC] Java defines whitespace as any unicode codepoint <= U0020
    // ref: javadoc for java.lang.String.trim()
    private static def isws(x: Char): Boolean { return x.ord() <= 0x20; }


    /**
     * Returns the String representation of the given entity.
     * The representation is exactly the one returned by the toString() method of the entity.
     * @param v the given entity
     * @return a String representation of the given entity.
     */
    public static def valueOf[T](v: T): X10String {
        if (v == null) return "null";
        return v.toString();
    }


    /**
     * Returns a formatted String using the specified format String and arguments.
     * The only format specifiers supported at the moment are those common to Java's String.format() and C++'s printf.
     * If there are more arguments than format specifiers, the extra arguments are ignored.
     * The number of arguments is variable and may be zero.
     * The behaviour on a null argument depends on the conversion.
     * @param fmt the format String
     * @param args the arguments referenced by the format specifiers in the format string.
     * @return a formatted string.
     * TODO
     */
    @Native("java", "x10.core.String.format(#fmt,(Object[]) (#args).raw().value)")
    @Native("c++", "x10::lang::String::format(#fmt,#args)")
    public native static def format(fmt: X10String, args:Array[Any]): X10String;


    // FIXME: Locale sensitivity
    /**
     * Converts all of the Chars in this String to lower case.
     * @return this String, converted to lowercase.
     */
    public def toLowerCase(): X10String {
        val r = IndexedMemoryChunk.allocateUninitialized[Char](content.length());
        var all_lower: Boolean = true;
        for (i in 0..(content.length()-2)) {
            val c = content(i);
            if (!c.isLowerCase())
                all_lower = false;
            r(i) = c.toLowerCase();
        }
        if (all_lower) {
            r.deallocate();
            return this;
        }
        r(content.length()-1) = '\0';
        return new X10String(r);
    }

    // FIXME: Locale sensitivity
    /**
     * Converts all of the Chars in this String to upper case.
     * @return this String, converted to uppercase.
     */
    public def toUpperCase(): X10String {
        val r = IndexedMemoryChunk.allocateUninitialized[Char](content.length());
        var all_upper: Boolean = true;
        for (i in 0..(content.length()-2)) {
            val c = content(i);
            if (!c.isUpperCase())
                all_upper = false;
            r(i) = c.toUpperCase();
        }
        if (all_upper) {
            r.deallocate();
            return this;
        }
        r(content.length()-1) = '\0';
        return new X10String(r);
    }


    /**
     * Compares this String with another String lexicographically.
     * The result is a negative integer if this String lexicographically precedes the argument String.
     * The result is a positive integer if this String lexicographically follows the argument String.
     * The result is zero if the Strings are equal; compareTo returns 0 exactly when the equals(Any) method would return true.
     * <p/>
     * This method compares the Chars in this String and the argument String at all indexes from 0 to the length of the shorter of the two strings.
     * If the Chars at some index k are not equal, the method returns the difference in ordinal values of those Chars:
     * <pre>
     * this(k).ord() - arg(k).ord()
     * </pre>
     * If there is no index position at which the Chars differ, then the method returns the difference of the lengths of the two strings:
     * <pre>
     * this.length() - arg.length()
     * </pre>
     * @param arg the argument String
     * @return 0 if the argument String is equal to this String; a negative Int if this String is lexicographically less than the argument String; and a positive Int if this String is lexicographically greater than the argument String.
     */
    public def compareTo(arg: X10String): Int {
        if (arg == this) return 0; // short-circuit trivial equality
        val length_diff = this.content.length() - arg.content.length();
        if (length_diff != 0)
            return length_diff;
        val min_length = length_diff < 0 ? this.content.length()-1 : arg.content.length()-1;
        return strncmp(this.content, 0, arg.content, 0, min_length);
    }

    // FIXME: Locale sensitivity
    /**
     * Compares this String with another String lexicographically, ignoring case differences.
     * This method returns an integer whose sign is that of calling {@link #compareTo(String)}
     * with normalized versions of the Strings where case differences have been eliminated,
     * e.g., by calling s.toLowerCase().toUpperCase() on each String.
     * @param arg the argument String
     * @return a negative Int, zero, or a positive Int as the argument String is greater than, equal to, or less than this String, ignoring case considerations.
     */
    public def compareToIgnoreCase(arg: X10String): Int {
        if (arg == this) return 0; // short-circuit trivial equality
        val length_diff = this.content.length() - arg.content.length();
        if (length_diff != 0)
            return length_diff;
        val min_length = length_diff < 0 ? this.content.length()-1 : arg.content.length()-1;
        return strncasecmp(this.content, 0, arg.content, 0, min_length);
    }

    /**
     * Checks if this String has another String as its head.
     * @param arg The argument string.
     * @return true if the argument string appears at the head of this String.
     *         The method returns false otherwise.
     */
    public def startsWith(arg: X10String): Boolean {
        val len = arg.content.length()-1;
        if (len > this.content.length()-1)
            return false;
        return (strncmp(this.content, 0, arg.content, 0, len) == 0);
    }

    /**
     * Checks if this String has another String as its tail.
     * @param arg The argument string.
     * @return true if the argument string appears at the tail of this String.
     *         The method returns false otherwise.
     */
    public def endsWith(arg: X10String): Boolean {
        val len = arg.content.length()-1;
        if (len > this.content.length()-1)
            return false;
        val length_diff = this.content.length()-1 - len;
        return (strncmp(this.content, length_diff, arg.content, 0, len) == 0);
    }

    // FIXME: Locale sensitivity
    /**
     * A less-than operator.
     * Compares this String with another String and returns true if this String is
     * strictly before the other String in dictionary order.
     * @param x the other String
     * @return true if this String is strictly before the other String.
     */
    public @Inline operator this < (x:X10String): Boolean = this.compareTo(x) < 0;

    // FIXME: Locale sensitivity
    /**
     * A greater-than operator.
     * Compares this String with another String and returns true if this String is
     * strictly after the other String in dictionary order.
     * @param x the other String
     * @return true if this String is strictly after the other String.
     */
    public @Inline operator this > (x:X10String): Boolean = this.compareTo(x) > 0;

    // FIXME: Locale sensitivity
    /**
     * A less-than-or-equal-to operator.
     * Compares this String with another String and returns true if this String is
     * equal to the other String or is before it in dictionary order.
     * @param x the other String
     * @return true if this String is before or equal to the other String.
     */
    public @Inline operator this <= (x:X10String): Boolean = this.compareTo(x) <= 0;

    // FIXME: Locale sensitivity
    /**
     * A greater-than-or-equal-to operator.
     * Compares this String with another String and returns true if this String is
     * equal to the other String or is after it in dictionary order.
     * @param x the other String
     * @return true if this String is after or equal to the other String.
     */
    public @Inline operator this >= (x:X10String): Boolean = this.compareTo(x) >= 0;

    /**
     * A string concatenation operator.
     * Appends the given entity to this String by calling the entity's
     * {@link x10.lang.Any#toString()} method.
     * @param x the given String
     * @param y the given entity
     * @return the resulting String
     */
    public @Inline static operator[T] (x:X10String) + (y:T): X10String = x + X10String.valueOf(y);

    /**
     * A string concatenation operator.
     * Prepends the given entity to the given String by calling the entity's
     * {@link x10.lang.Any#toString()} method.
     * @param x the given entity
     * @param y the given String
     * @return the resulting String
     */
    public @Inline static operator[T] (x:T) + (y:X10String): X10String = X10String.valueOf(x) + y;

    /**
     * A string concatenation operator.
     * Appends the second String to the first String (disambiguation).
     * @param x the first String
     * @param y the second String
     * @return the resulting String
     */
    public static operator (x:X10String) + (y:X10String): X10String {
        val xc = x.content;
        val xl = xc.length()-1;
        val yc = y.content;
        val yl = yc.length()-1;
        val r = IndexedMemoryChunk.allocateUninitialized[Char](xl+yl+1);
        for (i in 0..(xl-1)) {
            r(i) = xc(i);
        }
        for (i in 0..(yl-1)) {
            r(xl+i) = yc(i);
        }
        r(xl+yl) = '\0';
        return new X10String(r);
    }
}

public type X10String(s:X10String) = X10String{self==s};
