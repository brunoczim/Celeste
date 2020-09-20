use crate::{lexer::Lexer, token::TokenKind};
use cst_error::Emitter;
use cst_source::Src;

#[test]
fn read_operator() {
    let mut err_emitter = Emitter::new();
    let src = Src::new("test.cst", "+ $$ >>= -");
    let mut lexer = Lexer::new(src, &mut err_emitter);
    assert_eq!(lexer.curr().kind, TokenKind::Operator);
    assert_eq!(lexer.curr().span.as_str(), "+");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::Operator);
    assert_eq!(lexer.curr().span.as_str(), "$$");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::Operator);
    assert_eq!(lexer.curr().span.as_str(), ">>=");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::Operator);
    assert_eq!(lexer.curr().span.as_str(), "-");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::Eof);
    assert_eq!(lexer.curr().span.as_str(), "");
    assert!(!lexer.next());
    assert!(!err_emitter.has_error());
}

#[test]
fn read_ident() {
    let mut err_emitter = Emitter::new();
    let src = Src::new("test.cst", "a bc cd_Ef");
    let mut lexer = Lexer::new(src, &mut err_emitter);
    assert_eq!(lexer.curr().kind, TokenKind::Ident);
    assert_eq!(lexer.curr().span.as_str(), "a");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::Ident);
    assert_eq!(lexer.curr().span.as_str(), "bc");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::Ident);
    assert_eq!(lexer.curr().span.as_str(), "cd_Ef");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::Eof);
    assert_eq!(lexer.curr().span.as_str(), "");
    assert!(!lexer.next());
    assert!(!err_emitter.has_error());
}

#[test]
fn read_punctuation() {
    let mut err_emitter = Emitter::new();
    let src = Src::new("test.cst", ",() , ( )");
    let mut lexer = Lexer::new(src, &mut err_emitter);
    assert_eq!(lexer.curr().kind, TokenKind::Comma);
    assert_eq!(lexer.curr().span.as_str(), ",");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::OpenParen);
    assert_eq!(lexer.curr().span.as_str(), "(");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::CloseParen);
    assert_eq!(lexer.curr().span.as_str(), ")");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::Comma);
    assert_eq!(lexer.curr().span.as_str(), ",");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::OpenParen);
    assert_eq!(lexer.curr().span.as_str(), "(");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::CloseParen);
    assert_eq!(lexer.curr().span.as_str(), ")");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::Eof);
    assert_eq!(lexer.curr().span.as_str(), "");
    assert!(!lexer.next());
    assert!(!err_emitter.has_error());
}

#[test]
fn read_keywords() {
    let mut err_emitter = Emitter::new();
    let src = Src::new("test.cst", "if = => ->");
    let mut lexer = Lexer::new(src, &mut err_emitter);
    assert_eq!(lexer.curr().kind, TokenKind::If);
    assert_eq!(lexer.curr().span.as_str(), "if");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::Equals);
    assert_eq!(lexer.curr().span.as_str(), "=");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::FatArrow);
    assert_eq!(lexer.curr().span.as_str(), "=>");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::ThinArrow);
    assert_eq!(lexer.curr().span.as_str(), "->");
    assert!(lexer.next());
    assert_eq!(lexer.curr().kind, TokenKind::Eof);
    assert_eq!(lexer.curr().span.as_str(), "");
    assert!(!lexer.next());
    assert!(!err_emitter.has_error());
}
