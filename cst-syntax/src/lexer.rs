#[cfg(test)]
mod test;

use crate::{
    error::{
        AmbiguousToken,
        BadChar,
        EmptyExponent,
        EmptyFrac,
        ExponentTooBig,
        ExponentTooSmall,
        UnexpectedToken,
    },
    token::{Token, TokenData, TokenPattern},
};
use cst_error::Emitter;
use cst_source::{Reader, Src};
use num::{BigInt, BigRational, Signed, ToPrimitive, Zero};
use std::rc::Rc;

#[derive(Debug, Clone, Copy)]
struct Base {
    digits: u8,
    exp_del: &'static str,
    min_exp: i32,
    max_exp: i32,
}

impl Base {
    const B16: Base =
        Base { digits: 16, exp_del: "p", max_exp: 255, min_exp: -268 };
    const B10: Base =
        Base { digits: 10, exp_del: "e", max_exp: 307, min_exp: -323 };
    const B8: Base =
        Base { digits: 8, exp_del: "e", max_exp: 341, min_exp: -358 };
    const B2: Base =
        Base { digits: 2, exp_del: "e", max_exp: 1023, min_exp: -1074 };
}

#[derive(Debug)]
pub struct Lexer<'emitter, 'diagnostics> {
    reader: Reader,
    tokens: Vec<Token>,
    pos: usize,
    err_emitter: &'emitter mut Emitter<'diagnostics>,
}

impl<'emitter, 'diagnostics> Lexer<'emitter, 'diagnostics> {
    pub fn new(
        src: Src,
        err_emitter: &'emitter mut Emitter<'diagnostics>,
    ) -> Self {
        let mut this = Self {
            reader: src.reader(),
            tokens: Vec::new(),
            pos: 0,
            err_emitter,
        };
        this.read_next();
        this
    }

    pub fn emitter(&mut self) -> &mut Emitter<'diagnostics> {
        self.err_emitter
    }

    pub fn is_eof(&self) -> bool {
        self.tokens.last().map_or(false, |tok| tok.data == TokenData::Eof)
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    pub fn src(&self) -> &Src {
        self.reader.src()
    }

    pub fn curr(&self) -> &Token {
        &self.tokens[self.pos]
    }

    pub fn next(&mut self) -> bool {
        if !self.is_eof() {
            self.pos += 1;
            if self.tokens.len() <= self.pos {
                self.read_next();
            }
            true
        } else {
            false
        }
    }

    pub fn prev(&mut self) -> bool {
        self.rollback(1) == 1
    }

    pub fn advance(&mut self, count: usize) -> usize {
        let mut advanced = count.min(self.tokens.len() - self.pos);
        self.pos += advanced;
        while advanced < count && self.next() {
            advanced += 1;
        }
        advanced
    }

    pub fn rollback(&mut self, count: usize) -> usize {
        let rolled = count.min(self.pos);
        self.pos -= rolled;
        rolled
    }

    pub fn check<P>(&mut self, pattern: P) -> bool
    where
        P: TokenPattern,
    {
        let token = self.curr();
        pattern.test(token)
    }

    pub fn expect<P>(&mut self, pattern: P) -> Option<Token>
    where
        P: TokenPattern,
    {
        let token = self.curr().clone();
        if pattern.test(&token) {
            self.next();
            Some(token)
        } else {
            self.err_emitter.emit(UnexpectedToken {
                found: token,
                expected: pattern.to_boxed_dyn(),
            });
            None
        }
    }

    fn read_next(&mut self) {
        while !self.try_read_next() {}
    }

    fn try_read_next(&mut self) -> bool {
        self.read_discardable();
        let read = self.read_eof()
            || self.read_number()
            || self.read_ident_like()
            || self.read_operator_like()
            || self.read_open_paren()
            || self.read_close_paren()
            || self.read_comma();
        if !read {
            self.reader.mark();
            self.reader.next();
            self.err_emitter.emit(BadChar { span: self.reader.span() });
        }
        read
    }

    fn read_discardable(&mut self) {
        while self.read_comment() || self.read_whitespace() {}
    }

    fn read_comment(&mut self) -> bool {
        self.read_multi_comment() || self.read_line_comment()
    }

    fn read_line_comment(&mut self) -> bool {
        if self.read_line_comment_start() {
            while !self.read_line_comment_end() {
                self.read_next();
            }
            true
        } else {
            false
        }
    }

    fn read_multi_comment(&mut self) -> bool {
        if self.read_multi_comment_start() {
            let mut count = 1;
            while count > 0 {
                if self.read_multi_comment_end() {
                    count -= 1;
                } else if self.read_multi_comment_start() {
                    count += 1;
                } else {
                    self.read_next();
                }
            }
            true
        } else {
            false
        }
    }

    fn read_line_comment_start(&mut self) -> bool {
        self.reader.expect("#")
    }

    fn read_multi_comment_start(&mut self) -> bool {
        self.reader.expect("{#")
    }

    fn read_line_comment_end(&mut self) -> bool {
        self.reader.is_eof() || self.reader.expect("\n")
    }

    fn read_multi_comment_end(&mut self) -> bool {
        self.reader.expect("#}")
    }

    fn read_whitespace(&mut self) -> bool {
        let mut skipped = false;
        while self
            .reader
            .curr()
            .map_or(false, |s| s.chars().all(char::is_whitespace))
        {
            self.reader.next();
            skipped = true;
        }
        skipped
    }

    fn read_eof(&mut self) -> bool {
        if self.reader.is_eof() {
            self.reader.mark();
            self.tokens
                .push(Token { data: TokenData::Eof, span: self.reader.span() });
            true
        } else {
            false
        }
    }

    fn read_ident_like(&mut self) -> bool {
        self.reader.mark();
        if self.is_ident_start() {
            self.reader.mark();
            self.reader.next();
            while self.is_ident_part() {
                self.reader.next();
            }
            self.read_if() || self.read_val() || self.read_ident()
        } else {
            false
        }
    }

    fn is_ident_start(&mut self) -> bool {
        self.reader
            .curr()
            .and_then(|s| s.chars().next())
            .map_or(false, |ch| ch.is_alphabetic() || ch == '_')
    }

    fn is_ident_part(&mut self) -> bool {
        self.is_ident_start()
            || self
                .reader
                .curr()
                .and_then(|s| s.chars().next())
                .map_or(false, char::is_numeric)
    }

    fn read_ident(&mut self) -> bool {
        self.tokens
            .push(Token { span: self.reader.span(), data: TokenData::Ident });
        true
    }

    fn read_if(&mut self) -> bool {
        self.read_keyword("if", TokenData::If)
    }

    fn read_val(&mut self) -> bool {
        self.read_keyword("val", TokenData::Val)
    }

    fn read_operator_like(&mut self) -> bool {
        self.reader.mark();
        while self.is_operator() {
            self.reader.next();
        }
        if self.reader.pos() != self.reader.marked() {
            self.read_thin_arrow()
                || self.read_fat_arrow()
                || self.read_equals()
                || self.read_operator()
        } else {
            false
        }
    }

    fn is_operator(&mut self) -> bool {
        self.reader.curr().map_or(false, |curr| match curr {
            "+" | "-" | "*" | "/" | "%" | ";" | "&" | "|" | "^" | "~" | "$"
            | "<" | ">" | "!" | "=" | "?" | ":" | "@" => true,
            _ => false,
        })
    }

    fn read_operator(&mut self) -> bool {
        self.tokens.push(Token {
            span: self.reader.span(),
            data: TokenData::Operator,
        });
        true
    }

    fn read_keyword(&mut self, contents: &str, data: TokenData) -> bool {
        if self.reader.span().as_str() == contents {
            self.tokens.push(Token { span: self.reader.span(), data });
            true
        } else {
            false
        }
    }

    fn read_thin_arrow(&mut self) -> bool {
        self.read_keyword("->", TokenData::ThinArrow)
    }

    fn read_fat_arrow(&mut self) -> bool {
        self.read_keyword("=>", TokenData::FatArrow)
    }

    fn read_equals(&mut self) -> bool {
        self.read_keyword("=", TokenData::Equals)
    }

    fn read_punctuation(&mut self, string: &str, data: TokenData) -> bool {
        self.reader.mark();
        if self.reader.expect(string) {
            self.tokens.push(Token { data, span: self.reader.span() });
            true
        } else {
            false
        }
    }

    fn read_open_paren(&mut self) -> bool {
        self.read_punctuation("(", TokenData::OpenParen)
    }

    fn read_close_paren(&mut self) -> bool {
        self.read_punctuation(")", TokenData::CloseParen)
    }

    fn read_comma(&mut self) -> bool {
        self.read_punctuation(",", TokenData::Comma)
    }

    fn read_number(&mut self) -> bool {
        self.reader.mark();
        let negative = self.read_negative();
        let maybe_base = self.read_base();
        let base = maybe_base.unwrap_or(Base::B10);
        match self.read_int_part(negative, base) {
            Some(int) => {
                if self.reader.curr() == Some(".")
                    || self.reader.curr() == Some(base.exp_del)
                {
                    self.read_float(base, int)
                } else {
                    self.read_int(int)
                }
            },
            None => {
                if negative && maybe_base.is_none() && self.read_operator() {
                    true
                } else {
                    self.reader
                        .rollback(self.reader.pos() - self.reader.marked());
                    false
                }
            },
        }
    }

    fn read_negative(&mut self) -> bool {
        self.reader.expect("~")
    }

    fn read_base(&mut self) -> Option<Base> {
        if self.reader.expect("0x") {
            Some(Base::B16)
        } else if self.reader.expect("0o") {
            Some(Base::B8)
        } else if self.reader.expect("0b") {
            Some(Base::B2)
        } else {
            None
        }
    }

    fn read_digit(&mut self, base: Base) -> Option<u8> {
        let mut iter = self.reader.curr()?.chars();
        let first = iter.next()?.to_lowercase().next()?;
        let ret = if iter.next().is_some() {
            None
        } else if first >= '0' && first <= '9' {
            Some(first as u8 - b'0').filter(|&digit| digit < base.digits)
        } else if first >= 'a' && first <= 'z' {
            Some(10 + first as u8 - b'a').filter(|&digit| digit < base.digits)
        } else {
            None
        };

        if ret.is_some() {
            self.reader.next();
        }
        ret
    }

    fn read_int_part(&mut self, negative: bool, base: Base) -> Option<BigInt> {
        let mut int = BigInt::zero();
        let mut read_smth = false;
        loop {
            match self.read_digit(base) {
                Some(digit) => {
                    int *= base.digits;
                    int += digit;
                    read_smth = true;
                },
                None if read_smth && self.reader.curr() == Some("_") => {
                    self.reader.next();
                },
                None => break,
            }
        }
        if negative {
            int = -int;
        }
        Some(int).filter(|_| read_smth)
    }

    fn read_int(&mut self, int: BigInt) -> bool {
        if self.is_ident_start() {
            self.err_emitter.emit(AmbiguousToken { span: self.reader.span() });
        }
        self.tokens.push(Token {
            span: self.reader.span(),
            data: TokenData::IntLiteral(Rc::new(int)),
        });
        true
    }

    fn read_float(&mut self, base: Base, int_part: BigInt) -> bool {
        let mut ratio = BigRational::from(int_part);
        let mut read_smth = false;

        if self.reader.curr() == Some(".") {
            self.reader.next();
            read_smth |= self.read_float_places(base, &mut ratio);
        }

        if self.reader.curr() == Some(base.exp_del) {
            self.reader.next();
            let read_exp = self.read_float_exponent(base, &mut ratio);
            read_smth |= read_exp;
            if read_smth && !read_exp {
                self.err_emitter
                    .emit(EmptyExponent { span: self.reader.span() })
            }
        }

        if !read_smth {
            self.err_emitter.emit(EmptyFrac { span: self.reader.span() })
        }

        if self.is_ident_start() {
            self.err_emitter.emit(AmbiguousToken { span: self.reader.span() });
        }
        self.tokens.push(Token {
            span: self.reader.span(),
            data: TokenData::FloatLiteral(Rc::new(ratio)),
        });
        true
    }

    fn read_float_places(
        &mut self,
        base: Base,
        ratio: &mut BigRational,
    ) -> bool {
        let mut read_smth = false;
        let big_base = BigInt::from(base.digits);
        let mut place = big_base.clone();
        loop {
            match self.read_digit(base) {
                Some(digit) => {
                    let big_digit = BigInt::from(if ratio.is_negative() {
                        -(digit as i8)
                    } else {
                        digit as i8
                    });

                    *ratio += BigRational::new(big_digit, place.clone());
                    read_smth = true;
                    place *= &big_base;
                },
                None if self.reader.curr() == Some("_") => {
                    self.reader.next();
                    read_smth = true;
                },
                None => break,
            }
        }
        read_smth
    }

    fn read_float_exponent(
        &mut self,
        base: Base,
        ratio: &mut BigRational,
    ) -> bool {
        let prev_mark = self.reader.marked();
        self.reader.mark();
        let negative = self.read_negative();
        if let Some(exp) = self.read_int_part(negative, base) {
            match exp.to_i32() {
                Some(actual_exp) if actual_exp < base.min_exp => self
                    .err_emitter
                    .emit(ExponentTooSmall { span: self.reader.span() }),
                Some(actual_exp) if actual_exp <= base.max_exp => {
                    let base_ratio =
                        BigRational::from(BigInt::from(base.digits));
                    *ratio *= base_ratio.pow(actual_exp);
                },
                _ => self
                    .err_emitter
                    .emit(ExponentTooBig { span: self.reader.span() }),
            }
            let count = self.reader.pos() - prev_mark;
            self.reader.rollback(count);
            self.reader.mark();
            self.reader.advance(count);
            true
        } else {
            false
        }
    }
}
