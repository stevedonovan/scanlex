`scanlex` implements a simple _lexical scanner_.

Tokens are returned by repeatedly calling the `get` method,
(which will return `Token::End` if no tokens are left)
or by iterating over the scanner. They represent numbers, characters, identifiers,
or single/double quoted strings. There is also `Token::Error` to
indicate a badly formed token.

This lexical scanner makes some
assumptions, such as a number may not be directly followed
by a letter, etc. No attempt is made in this version to decode C-style
escape codes in strings.  All whitespace is ignored. It's intended
for processing generic structured data, rather than code.

For example, the string "hello 'dolly' * 42" will be broken into four tokens:

  - an _identifier_ 'hello'
  - a quoted string 'dolly'
  - a character '*'
  - and a number 42
  

```rust
extern crate scanlex;
use scanlex::{Scanner,Token};

let mut scan = Scanner::new("iden 'string' * 10");
assert_eq!(scan.get(),Token::Iden("iden".to_string()));
assert_eq!(scan.get(),Token::Str("string".to_string()));
assert_eq!(scan.get(),Token::Char('*'));
assert_eq!(scan.get(),Token::Num(10.0));
assert_eq!(scan.get(),Token::End);
```

`Scanner` implements `Iterator`.  If you just wanted to extract the words from
a string, then calling `as_iden` repeatedly will do the trick, since it returns
`Option<String>`.

```rust
let v: Vec<_> = Scanner::new("bonzo 42 dog (cat)")
	.filter_map(|t| t.as_iden()).collect();
assert_eq!(v,&["bonzo","dog","cat"]);
```

By using `as_number` you can use this pattern to extract all the numbers out of a
document, ignoring all other structure.

Usually it's important _not_ to ignore structure. Say we have input strings that
look like this "(WORD) = NUMBER":

```
	scan.skip_chars("(")?;
	let word = scan.get_iden()?;
	scan.skip_chars(")=")?;
	let num = scan.get_number()?;
```

This needs to be appropriately wrapped up, because _any_ of these calls may fail!

A more serious example (taken from the tests) is parsing JSON:

```rust
fn scan_json(scan: &mut Scanner) -> Result<Value,ScanError> {
    use Value::*;
    match scan.get() {
    Token::Str(s) => Ok(Str(s)),
    Token::Num(x) => Ok(Num(x)),
    Token::End => Err(ScanError::new("unexpected end of input")),
    Token::Error(e) => Err(ScanError::new(&e)),
    Token::Iden(s) =>
        if s == "null"    {Ok(Null)}
        else if s == "true" {Ok(Bool(true))}
        else if s == "false" {Ok(Bool(false))}
        else {Err(ScanError::new(&format!("unknown identifier '{}' at line {}",s,scan.lineno)))},
    Token::Char(c) =>
        if c == '[' {
            let mut ja = Vec::new();
            let mut ch = c;
            while ch != ']' {
                let o = try!(scan_json(scan));
                ch = try!(scan.get_ch_matching(&[',',']']));
                ja.push(Box::new(o));
            }
            Ok(Arr(ja))
        } else
        if c == '{' {
            let mut jo = HashMap::new();
            let mut ch = c;
            while ch != '}' {
                let key = try!(scan.get_string());
                try!(scan.get_ch_matching(&[':']));
                let o = try!(scan_json(scan));
                ch = try!(scan.get_ch_matching(&[',','}']));
                jo.insert(key,Box::new(o));
            }
            Ok(Obj(jo))
        } else {
            Err(ScanError::new(&format!("bad char '{}'",c)))
        }
    }    
}

```

(This is of course an Illustrative Example. JSON is a solved problem.)


