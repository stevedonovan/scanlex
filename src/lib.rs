//! `scanlex` implements a simple _lexical scanner_.
//!
//! Tokens are returned by repeatedly calling the `get` method,
//! (which will return `false` if no tokens are left)
//! or by iterating over the scanner.
use std::str::FromStr;
use std::error::Error;

macro_rules! try_scan {
    ( $($v:ident : $value:expr),+ ) => (
       $(
        let $v = try!($value);
       )+
    );
}

#[derive(Debug)]
#[derive(PartialEq)]
pub enum Token {
  Num(f64),
  Str(String),
  Iden(String),
  Char(char),
  Error(String),
  End
}

impl Token {
    pub fn finished(&self) -> bool {
        match *self {
            Token::End => true,
            _ => false
        }
    }
}

pub struct Scanner <'a> {
    iter: ::std::str::Chars<'a>,
    ch: char,
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
        Token::Error(_) => None,
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
        Scanner { iter: iter, ch: match mch {Some(c) => c, None => '\0'}, lineno: 1 }
    }
    
    pub fn expect_message(&self, t: &Token, msg: &str) -> String {
        format!("line {}: {} expected, got {:?}",self.lineno,msg,t)        
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
            let mut maybe_hex = self.ch == '0';
            if plusminus != '\0' || maybe_hex { // look ahead! 
                self.nextch();
                if maybe_hex {
                    if self.ch == 'X' || self.ch == 'x' {
                        maybe_hex = true;
                    } else
                    if ! self.is_digit() {
                        return Num(0.0);
                    }
                } else
                if ! self.is_digit() { // false alarm, wuz just a char...
                    return Char(plusminus);
                }
            }            
            let mut s = String::new();
            if plusminus != '\0' {
                s.push(plusminus);
            }
            // integer part
            if maybe_hex { // in hex...
                self.nextch(); // skip the 'x'
                self.take_while_into(&mut s,|c| c.is_digit(16));
                // yep, i64 does not fit into f64 over 2^53
                return match i64::from_str_radix(&s,16) {
                    Ok(n) => Num(n as f64),
                    Err(e) => Error(self.error_msg(e.description()))
                }
            }
            self.take_digits_into(&mut s);
            // floating point part?
            if self.ch == '.' {
                self.take_digits_into(&mut s);
                if self.ch == 'e' || self.ch == 'E' {
                    s.push(self.nextch());
                    let plusminus = self.either_plus_or_minus();
                    if self.is_digit() || plusminus != '\0' {
                        self.take_digits_into(&mut s);
                    }
                }
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
    pub fn skip_until<F>(&mut self, pred: F ) -> bool
     where F: Fn(char) -> bool {
        while let Some(c) = self.iter.next() {
            if pred(c) { self.ch = c; return true; }
        }
        self.ch = '\0';
        false
    }
    
    /// collect the rest of the chars in the iterator
    pub fn take_rest(&mut self) -> String {
        self.grab_while(|c| c != '\0')
    }
    
    /// collect until we match one of the chars
    pub fn take_until (&mut self, chars: &[char]) -> String {
        self.grab_while(|c| ! chars.contains(&c))        
    }
    
    /// get a String token, failing otherwise
    pub fn get_string(&mut self) -> Result<String,String> {
        let t = self.get();
		if let Token::Str(s) = t {
			Ok(s)
		} else {
			Err(self.expect_message(&t,"string"))
		}		
	}
    
    /// get an Identifier token, failing otherwise
    pub fn get_iden(&mut self) -> Result<String,String> {
        let t = self.get();
		if let Token::Iden(s) = t {
			Ok(s)
		} else {
			Err(self.expect_message(&t,"identifier"))
		}		
	}
	
    /// get a float, failing otherwise
    pub fn get_number(&mut self) -> Result<f64,String> {
        let t = self.get();
		if let Token::Num(x) = t {
			Ok(x)
		} else {
			Err(self.expect_message(&t,"number"))
		}		
	}
	
    /// get a float, failing otherwise
    pub fn get_char(&mut self) -> Result<char,String> {
        let t = self.get();
		if let Token::Char(x) = t {
			Ok(x)
		} else {
			Err(self.expect_message(&t,"char"))
		}		
	}
	
    
    /// get an integer, failing otherwise
    pub fn get_integer(&mut self) -> Result<i32,String> {
        let res = self.get_number();
        if let Err(e) = res { return Err(e); }
        let v = res.unwrap();
        Ok(v as i32)
	}
        
    
    /// get a Character token that must be one of the given chars
    pub fn get_ch_matching(&mut self, chars: &[char]) -> Result<char,String> {
        let t = self.get();
		if let Token::Char(c) = t { 
			if chars.contains(&c) {
				Ok(c)
			} else {
                let s =  expecting_chars(chars);
				Err(format!("expected one of {}, got {}",s,c))
			}
		} else {
			Err(self.expect_message(&t,"char"))
		}		
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
			"expected one of ',',':', got /"
		);
		assert_eq!(scan.get(),Num(-10.0));
		assert_eq!(scan.get(),Error("line 1: bad number: letter follows".to_string()));
		assert_eq!(scan.get(),Iden("B".to_string()));
		assert_eq!(scan.get(),Num(2000000.0));
		assert_eq!(scan.get(),Num(255.0));
		assert_eq!(scan.get(),Char('-'));
		assert_eq!(scan.get(),Str("yay".to_string()));
	}
	
	fn try_scan_err() -> Result<(),String> {
		let mut scan = Scanner::new("hello: 42");
		try_scan!{
			s: scan.get_iden(),
			ch: scan.get_char(),
			n: scan.get_integer()
		};
		assert_eq!(s,"hello".to_string());
		assert_eq!(ch,':');
		assert_eq!(n,42);     
		Ok(())
	}

	#[test]	
	fn try_scan_test() {		
		let _ = try_scan_err();
	}
	
	
}
