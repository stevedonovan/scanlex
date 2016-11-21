extern crate scanlex;
use scanlex::{Scanner,Token};

use std::collections::HashMap;

type JsonArray = Vec<Box<Value>>;
type JsonObject = HashMap<String,Box<Value>>;


#[derive(Debug, Clone, PartialEq)]
pub enum Value {
   Str(String),
   Num(f64),
   Bool(bool),
   Arr(JsonArray),
   Obj(JsonObject),
   Null
}

fn scan_json(scan: &mut Scanner) -> Result<Value,String> {
    use Value::*;
    match scan.get() {
    Token::Str(s) => Ok(Str(s)),
    Token::Num(x) => Ok(Num(x)),
    Token::End => Err("unexpected end of input".to_string()),
    Token::Error(e) => Err(e),
    Token::Iden(s) =>
        if s == "null"    {Ok(Null)}
        else if s == "true" {Ok(Bool(true))}
        else if s == "false" {Ok(Bool(false))}
        else {Err(format!("unknown identifier '{}' at line {}",s,scan.lineno))},
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
            Err(format!("bad char '{}'",c))
        }
    }    
}

fn parse_json(txt: &str) -> String {
    let mut scan = Scanner::new(txt);
    let res = scan_json(&mut scan).expect("bad json");
    format!("{:?}",res)    
}

#[test]
fn array() {
	let s = parse_json("[10,20]");
	assert_eq!(&s,"Arr([Num(10), Num(20)])");
}

#[test]
fn array2() {
	let s = parse_json("[null,true]");
	assert_eq!(&s,"Arr([Null, Bool(true)])");
}

#[test]
fn map() {
	let s = parse_json("{'bonzo':10}");
	assert_eq!(&s,"Obj({\"bonzo\": Num(10)})");
}




