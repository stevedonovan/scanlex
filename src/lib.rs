//! `scanlex` implements a simple _lexical scanner_.
//!
//! Tokens are returned by repeatedly calling the `get` method,
//! (which will return `Token::End` if no tokens are left)
//! or by iterating over the scanner.
//!
//! They represent numbers (stored as f64), characters, identifiers,
//! or single or double quoted strings. There is also `Token::Error` to
//! indicate a badly formed token.  This lexical scanner makes some
//! sensible assumptions, such as a number may not be directly followed
//! by a letter, etc. No attempt is made in this version to decode C-style
//! escape codes in strings.  All whitespace is ignored.
//!
//! ## Examples
//!
//! ```
//! use  scanlex::{Scanner,Token};
//! 
//! let mut scan = Scanner::new("iden 'string' * 10");
//! assert_eq!(scan.get(),Token::Iden("iden".to_string()));
//! assert_eq!(scan.get(),Token::Str("string".to_string()));
//! assert_eq!(scan.get(),Token::Char('*'));
//! assert_eq!(scan.get(),Token::Num(10.0));
//! assert_eq!(scan.get(),Token::End);
//! ```
//! 
//! The scanner struct implements iterator, so:
//!
//! ```
//! let v: Vec<_> = scanlex::Scanner::new("bonzo 42 dog (cat)")
//!     .filter_map(|t| t.as_iden()).collect();
//! assert_eq!(v,&["bonzo","dog","cat"]);
//! ```

use std::str::FromStr;
use std::error::Error;
use std::fmt;
use std::fmt::Display;
use std::io;

macro_rules! try_scan {
    ( $($v:ident : $value:expr),+ ) => (
       $(
        let $v = try!($value);
       )+
    );
}

/// a scanner error type
#[derive(Debug)]
#[derive(PartialEq)]
pub struct ScanError {
    details: String
}

impl Display for ScanError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,"{}",self.details)
    }
}

impl ScanError {
    /// create a new error
    pub fn new(msg: &str) -> ScanError { ScanError{details: msg.to_string()} }
}

impl Error for ScanError {
    fn description(&self) -> &str {
        &self.details
    }
}

impl From<io::Error> for ScanError {
    fn from(err: io::Error) -> ScanError {
        ScanError::new(err.description())
    }
}

/// Represents a token returned by `Scanner::get`
#[derive(Debug)]
#[derive(PartialEq)]
pub enum Token {
  /// a number, stored as double-precision float
  Num(f64),
  /// a quoted string
  Str(String),
  /// an identifier \a+[\a\d_]*
  Iden(String),
  /// a character (anything not recognized as any of the above
  Char(char),
  /// represents an error
  Error(String),
  /// end of stream
  End
}

impl Token {
    /// is this the end token?
    pub fn finished(&self) -> bool {
        match *self {
            Token::End => true,
            _ => false
        }
    }
    
    /// extract the number
    pub fn as_number(self) -> Option<f64> {
        match self { Token::Num(n) => Some(n), _ => None }
    }
    
    /// extract the string
    pub fn as_string(self) -> Option<String> {
        match self { Token::Str(s) => Some(s), _ => None }
    }
    
    /// extract the identifier
    pub fn as_iden(self) -> Option<String> {
        match self { Token::Iden(n) => Some(n), _ => None }
    }
    
    /// extract the character
    pub fn as_char(self) -> Option<char> {
        match self { Token::Char(n) => Some(n), _ => None }
    }
    
    /// extract the error
    pub fn as_error(self) -> Option<ScanError> {
        match self { Token::Error(n) => Some(ScanError::new(&n)), _ => None }
    }
    
    
}

/// a struct for lexical scanning of a string
pub struct Scanner <'a> {
    iter: ::std::str::Chars<'a>,
    ch: char,
    pub was_integer: bool,
    pub lineno: i32
}

fn expecting_chars(chars: &[char]) -> String {
    let mut res = String::new();
    for c in chars {
        res.push_str(&format!("'{}'",c));
        res.push(',')
    }
    res.pop();
    res        
}

impl<'a> Iterator for Scanner<'a> {
    type Item = Token;
    
    fn next(&mut self) -> Option<Token> {
        match self.get() {
        Token::End => None,
        t => Some(t)
        }
    }
}

impl<'a> Scanner<'a> {
    /// create a new scanner from a string slice.
    /// 
    /// Empty text is not a problem, but `get` will then
    /// return `Token::End`.
    pub fn new(s: &'a str) -> Scanner<'a> {
        let mut iter = s.chars();
        let mch = iter.next();
        Scanner { iter: iter, ch: match mch {Some(c) => c, None => '\0'}, was_integer: false, lineno: 1 }
    }
    
    fn expect_message(&self, t: &Token, msg: &str) -> ScanError {
        ScanError::new(&format!("line {}: {} expected, got {:?}",self.lineno,msg,t))        
    }
    
    fn error_msg(&self, msg: &str) -> String {
        format!("line {}: {}",self.lineno,msg)
    }
    
    /// skip any whitespace characters - return false if we're at the end.
    pub fn skip_whitespace(&mut self) -> bool {
        if self.ch.is_whitespace() {
            if self.ch == '\n' {
                 self.lineno += 1;
            }            
           while let Some(c) = self.iter.next() {
                if c == '\n' {
                     self.lineno += 1;
                }
                if ! c.is_whitespace() {
                     self.ch = c;
                     return true;
                }
            }
            // run of chars!
            self.ch = '\0';
        }
        if self.ch == '\0' {false} else {true}
    }
    
    /// look ahead at the next character
    pub fn peek(&self) -> char {
        self.ch
    }
    
    /// get the next character
    pub fn nextch(&mut self) -> char {
        let old_ch = self.ch;
        self.ch = match self.iter.next() {Some(c)=>c,None=>'\0'};
        old_ch
    }
    
    fn either_plus_or_minus(&self) -> char {
        if self.ch == '+' || self.ch == '-' {self.ch} else {'\0'}
    }
    
    fn is_digit(&self) -> bool {
        self.ch.is_digit(10)
    }    

    /// get the next token
    pub fn get(&mut self) -> Token {
        use self::Token::*;
        if ! self.skip_whitespace() { return End; }
        
        // a number starts with a digit or a sign
        let plusminus = self.either_plus_or_minus();
        if self.is_digit() || plusminus != '\0' {
            let mut s = String::new();
            if plusminus != '\0' {
                s.push(plusminus);
            }
            self.was_integer = false;
            let mut maybe_hex = self.ch == '0';
            if plusminus != '\0' || maybe_hex {
                // look ahead! Might be a number or just a char
                self.nextch();
                if maybe_hex { // after a '0'?
                    maybe_hex = self.ch == 'X' || self.ch == 'x';
                    if ! maybe_hex {
                        s.push('0');
                    }
                } else
                if ! self.is_digit() { // false alarm, wuz just a char...
                    return Char(plusminus);
                }
            }            
            // integer part
            if maybe_hex { // in hex...
                self.nextch(); // skip the 'x'
                self.take_while_into(&mut s,|c| c.is_digit(16));
                // yep, i64 does not fit into f64 over 2^53
                return match i64::from_str_radix(&s,16) {
                    Ok(n) => { self.was_integer = true; Num(n as f64)},
                    Err(e) => Error(self.error_msg(e.description()))
                }
            }
            self.take_digits_into(&mut s);
            // floating point part?
            if self.ch == '.'  || self.ch == 'e' || self.ch == 'E' {
                if self.ch == '.' {
                    self.take_digits_into(&mut s);
                }
                if self.ch == 'e' || self.ch == 'E' {
                    s.push(self.nextch());
                    let plusminus = self.either_plus_or_minus();
                    if self.is_digit() || plusminus != '\0' {
                        self.take_digits_into(&mut s);
                    }
                }
            } else {
                self.was_integer = true;
            }

            if self.ch.is_alphabetic() {
                return Error(self.error_msg("bad number: letter follows"));
            }
            return match f64::from_str(&s) {
                Ok(x) => Num(x),
                Err(e) => Error(self.error_msg(e.description()))
            }            
        } else
        if self.ch == '\'' || self.ch == '\"' {
            let endquote = self.ch;
            self.nextch(); // skip the opening quote
            let s = self.grab_while(|c| c != endquote);
            self.nextch();  // skip end quote
            Str(s)
        } else
        if self.ch.is_alphabetic() {
            let s = self.grab_while(|c| c.is_alphanumeric() || c == '_');
            Iden(s)
        } else {
            Char(self.nextch())
        }
    }
    
    /// collect chars matching the condition, returning a string
    /// ```
    /// let mut scan = scanlex::Scanner::new("hello + goodbye");
    /// assert_eq!(scan.grab_while(|c| c != '+'), "hello ");
    /// ```    
    pub fn grab_while<F>(&mut self, pred: F ) -> String
     where F: Fn(char) -> bool {
        let mut s = String::new();
        self.take_while_into(&mut s,pred);
        s
    }
    
    /// collect chars matching the condition into a given string
    pub fn take_while_into<F>(&mut self, s: &mut String, pred: F )
     where F: Fn(char) -> bool {
        if self.ch != '\0' { s.push(self.ch); }
        while let Some(c) = self.iter.next() {
            if ! pred(c) { self.ch = c; return; }
            s.push(c);
        }
        self.ch = '\0';
    }
    
    fn take_digits_into(&mut self, s: &mut String) {
        self.take_while_into(s, |c| c.is_digit(10));
    }
    
    /// skip chars while the condition is false
    ///
    /// ```
    /// let mut scan = scanlex::Scanner::new("hello and\nwelcome");
    /// scan.skip_until(|c| c == '\n');
    /// assert_eq!(scan.get_iden().unwrap(),"welcome");
    /// ```
    pub fn skip_until<F>(&mut self, pred: F ) -> bool
     where F: Fn(char) -> bool {
        while let Some(c) = self.iter.next() {
            if pred(c) { self.ch = c; return true; }
        }
        self.ch = '\0';
        false
    }
    
    /// collect the rest of the chars
    ///
    /// ```
    /// use scanlex::{Scanner,Token};
    ///
    /// let mut scan = Scanner::new("42 the answer");
    /// assert_eq!(scan.get(),Token::Num(42.0));
    /// assert_eq!(scan.take_rest()," the answer");
    /// ```    
    pub fn take_rest(&mut self) -> String {
        self.grab_while(|c| c != '\0')
    }
    
    /// collect until we match one of the chars
    pub fn take_until (&mut self, chars: &[char]) -> String {
        self.grab_while(|c| ! chars.contains(&c))        
    }
    
    /// get a String token, failing otherwise
    pub fn get_string(&mut self) -> Result<String,ScanError> {
        let t = self.get();
        if let Token::Str(s) = t {
            Ok(s)
        } else {
            Err(self.expect_message(&t,"string"))
        }
    }
    
    /// get an Identifier token, failing otherwise
    ///
    /// ```
    /// let mut scan = scanlex::Scanner::new("hello dolly");
    /// assert_eq!(scan.get_iden().unwrap(),"hello");
    /// ```
    pub fn get_iden(&mut self) -> Result<String,ScanError> {
        let t = self.get();
        if let Token::Iden(s) = t {
            Ok(s)
        } else {
            Err(self.expect_message(&t,"identifier"))
        }
    }
    
    /// get a float, failing otherwise
    ///
    /// ```
    /// let mut scan = scanlex::Scanner::new("(42)");
    /// scan.get(); // skip '('
    /// assert_eq!(scan.get_number().unwrap(),42.0);
    /// ```    
    pub fn get_number(&mut self) -> Result<f64,ScanError> {
        let t = self.get();
        if let Token::Num(x) = t {
            Ok(x)
        } else {
            Err(self.expect_message(&t,"number"))
        }
    }
    
    /// get a character, failing otherwise
    pub fn get_char(&mut self) -> Result<char,ScanError> {
        let t = self.get();
        if let Token::Char(x) = t {
            Ok(x)
        } else {
            Err(self.expect_message(&t,"char"))
        }
    }
    
    
    /// get an integer, failing otherwise
    pub fn get_integer(&mut self) -> Result<i32,ScanError> {
        let res = self.get_number();
        if let Err(e) = res { return Err(e); }
        let v = res.unwrap();
        Ok(v as i32)
    }
        
    
    /// get a Character token that must be one of the given chars
    pub fn get_ch_matching(&mut self, chars: &[char]) -> Result<char,ScanError> {
        let t = self.get();
        if let Token::Char(c) = t { 
            if chars.contains(&c) {
                Ok(c)
            } else {
                let s =  expecting_chars(chars);
                Err(ScanError::new(&format!("expected one of {}, got {}",s,c)))
            }
        } else {
            Err(self.expect_message(&t,"char"))
        }
    }
    
    /// skip each character in the string.
    pub fn skip_chars(&mut self, chars: &str) -> Result<(),ScanError> {
        for ch in chars.chars() {
            let c = try!(self.get_char());
            if c != ch {
                return Err(ScanError::new(&format!("expected '{}' got '{}'",ch,c)));
            }
        }
        Ok(())
    }
   
}

use std::io::prelude::*;

/// used to generate Scanner structs for each line
pub struct ScanLines<R: Read> {
    rdr: io::BufReader<R>,
    line: String
}

impl <'a, R: Read> ScanLines<R> {
    
    /// create a Scanner 'iterator' over all lines from a readable.
    /// This cannot be a proper `Iterator` because the lifetime constraint
    /// on `Scanner` cannot be satisfied. You need to use the explicit form:
    ///
    /// ```rust,ignore
    /// let mut iter = ScanLines::new(&f);
    /// while let Some(mut s) = iter.next() {
    ///     println!("{:?}",s.get());
    /// }
    /// ```
    pub fn new(f: R) -> ScanLines<R> {
        ScanLines {
            rdr: io::BufReader::new(f),
            line: String::new()
        }
    }
    

    /// call this to return a `Scanner` for the next line in the source.
    pub fn next(&'a mut self) -> Option<Scanner<'a>> {
        self.line.clear();
        let nbytes = self.rdr.read_line(&mut self.line).unwrap();
        if nbytes == 0 {
            return None;
        }
        Some(Scanner::new(&self.line))
    }        
    
}


#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn skipping() {
        // skipping
        let mut scan = Scanner::new("here we go\nand more *yay*");
        scan.skip_until(|c| c == '\n');
        assert_eq!(scan.get(),Token::Iden("and".to_string()));
        scan.skip_until(|c| c == '*');
        assert_eq!(scan.get(),Token::Char('*'));
        assert_eq!(scan.get(),Token::Iden("yay".to_string()));
    }

    #[test]
    fn getting()  {
        use Token::*;
        let mut scan = Scanner::new("'hello' 42 * / -10 24B 2.0e6 0xFF-\"yay\"");
        assert_eq!(scan.get_string().unwrap(), "hello");
        assert_eq!(scan.get_number().unwrap(), 42.0);
        assert_eq!(scan.get_ch_matching(&['*']).unwrap(),'*');
        assert_eq!(
            scan.get_ch_matching(&[',',':']).err().unwrap(),
            ScanError::new("expected one of ',',':', got /")
        );
        assert_eq!(scan.get(),Num(-10.0));
        assert_eq!(scan.get(),Error("line 1: bad number: letter follows".to_string()));
        assert_eq!(scan.get(),Iden("B".to_string()));
        assert_eq!(scan.get(),Num(2000000.0));
        assert_eq!(scan.get(),Num(255.0));
        assert_eq!(scan.get(),Char('-'));
        assert_eq!(scan.get(),Str("yay".to_string()));
    }
    
    fn try_scan_err() -> Result<(),ScanError> {
        let mut scan = Scanner::new("hello: 42");
        try_scan!{
            s: scan.get_iden(),
            ch: scan.get_char(),
            n: scan.get_integer()
        };
        assert_eq!(s,"hello");
        assert_eq!(ch,':');
        assert_eq!(n,42);
        Ok(())
    }

    #[test] 
    fn try_scan_test() {
        let _ = try_scan_err();
    }
    
    fn try_skip_chars(test: &str) -> Result<(),ScanError> {
        let mut scan = Scanner::new(test);
        try_scan! {
            __: scan.skip_chars("("),
            name: scan.get_iden(),
            __: scan.skip_chars(")="),
            num: scan.get_integer()
        };
        assert_eq!(name,"hello");
        assert_eq!(num,42);
        Ok(())
    }
    
    #[test]
    fn skip_chars() {
        let _ = try_skip_chars("(hello)=42");
        let _ = try_skip_chars(" ( hello ) =  42  ");
    }
    
    #[test]
    fn numbers() {
        let mut scan = Scanner::new("10 0.0 1.0e1 1e1");
        assert_eq!(scan.get_integer(),Ok(10));
        assert_eq!(scan.was_integer,true);
        assert_eq!(scan.get_number(),Ok(0.0));
        assert_eq!(scan.get_number(),Ok(10.0));
        assert_eq!(scan.get_number(),Ok(10.0));
        assert_eq!(scan.was_integer,false);
    }
    
    
}
