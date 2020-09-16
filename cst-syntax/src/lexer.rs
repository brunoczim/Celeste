use crate::{
    error::BadChar,
    token::{Token, TokenKind},
};
use cst_error::Emitter;
use cst_source::{Reader, Src};

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

    pub fn is_eof(&self) -> bool {
        self.reader.is_eof()
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    pub fn src(&self) -> &Src {
        self.reader.src()
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

    fn read_next(&mut self) {
        while !self.try_read_next() {}
    }

    fn try_read_next(&mut self) -> bool {
        self.read_discardable();
        let read = self.read_eof()
            || self.read_ident()
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
        if self.is_eof() {
            self.reader.mark();
            self.tokens
                .push(Token { kind: TokenKind::Eof, span: self.reader.span() });
            true
        } else {
            false
        }
    }

    fn read_ident(&mut self) -> bool {
        self.reader.mark();
        if self.read_ident_start() {
            true
        } else {
            false
        }
    }

    fn read_ident_start(&mut self) -> bool {
        if self.is_ident_start() {
            self.reader.next();
            while self.is_ident_part() {
                self.reader.next();
            }
            self.tokens.push(Token {
                kind: TokenKind::Ident,
                span: self.reader.span(),
            });
            true
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
                .map_or(false, |ch| ch.is_numeric() || ch == '-')
    }

    fn read_open_paren(&mut self) -> bool {
        self.reader.mark();
        if self.reader.expect("(") {
            self.tokens.push(Token {
                kind: TokenKind::OpenParen,
                span: self.reader.span(),
            });
            true
        } else {
            false
        }
    }

    fn read_close_paren(&mut self) -> bool {
        self.reader.mark();
        if self.reader.expect(")") {
            self.tokens.push(Token {
                kind: TokenKind::CloseParen,
                span: self.reader.span(),
            });
            true
        } else {
            false
        }
    }

    fn read_comma(&mut self) -> bool {
        self.reader.mark();
        if self.reader.expect(",") {
            self.tokens.push(Token {
                kind: TokenKind::Comma,
                span: self.reader.span(),
            });
            true
        } else {
            false
        }
    }
}
