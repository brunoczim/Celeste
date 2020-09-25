use crate::{lexer::Lexer, token::TokenData};
use cst_error::Emitter;
use cst_source::Src;

#[test]
fn read_operator() {
    let mut err_emitter = Emitter::new();
    let src = Src::new("test.cst", "+ $$ >>= -");
    let mut lexer = Lexer::new(src, &mut err_emitter);
    assert_eq!(lexer.curr().data, TokenData::Operator);
    assert_eq!(lexer.curr().span.as_str(), "+");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::Operator);
    assert_eq!(lexer.curr().span.as_str(), "$$");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::Operator);
    assert_eq!(lexer.curr().span.as_str(), ">>=");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::Operator);
    assert_eq!(lexer.curr().span.as_str(), "-");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::Eof);
    assert_eq!(lexer.curr().span.as_str(), "");
    assert!(!lexer.next());
    assert!(!err_emitter.has_error());
}

#[test]
fn read_ident() {
    let mut err_emitter = Emitter::new();
    let src = Src::new("test.cst", "a bc\ncd_Ef");
    let mut lexer = Lexer::new(src, &mut err_emitter);
    assert_eq!(lexer.curr().data, TokenData::Ident);
    assert_eq!(lexer.curr().span.as_str(), "a");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::Ident);
    assert_eq!(lexer.curr().span.as_str(), "bc");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::Ident);
    assert_eq!(lexer.curr().span.as_str(), "cd_Ef");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::Eof);
    assert_eq!(lexer.curr().span.as_str(), "");
    assert!(!lexer.next());
    assert!(!err_emitter.has_error());
}

#[test]
fn read_punctuation() {
    let mut err_emitter = Emitter::new();
    let src = Src::new("test.cst", ",() ,\n  ( )");
    let mut lexer = Lexer::new(src, &mut err_emitter);
    assert_eq!(lexer.curr().data, TokenData::Comma);
    assert_eq!(lexer.curr().span.as_str(), ",");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::OpenParen);
    assert_eq!(lexer.curr().span.as_str(), "(");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::CloseParen);
    assert_eq!(lexer.curr().span.as_str(), ")");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::Comma);
    assert_eq!(lexer.curr().span.as_str(), ",");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::OpenParen);
    assert_eq!(lexer.curr().span.as_str(), "(");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::CloseParen);
    assert_eq!(lexer.curr().span.as_str(), ")");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::Eof);
    assert_eq!(lexer.curr().span.as_str(), "");
    assert!(!lexer.next());
    assert!(!err_emitter.has_error());
}

#[test]
fn read_keywords() {
    let mut err_emitter = Emitter::new();
    let src = Src::new("test.cst", "if = => ->");
    let mut lexer = Lexer::new(src, &mut err_emitter);
    assert_eq!(lexer.curr().data, TokenData::If);
    assert_eq!(lexer.curr().span.as_str(), "if");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::Equals);
    assert_eq!(lexer.curr().span.as_str(), "=");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::FatArrow);
    assert_eq!(lexer.curr().span.as_str(), "=>");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::ThinArrow);
    assert_eq!(lexer.curr().span.as_str(), "->");
    assert!(lexer.next());
    assert_eq!(lexer.curr().data, TokenData::Eof);
    assert_eq!(lexer.curr().span.as_str(), "");
    assert!(!lexer.next());
    assert!(!err_emitter.has_error());
}

#[test]
fn read_numbers() {
    let mut err_emitter = Emitter::new();
    let src = Src::new(
        "test.cst",
        "259 0xF0 ~259 ~0b11_01 259.25 0xF0.C8 ~259.25 ~0o21.24 259.25e23 \
         0xF0.C8p1A ~259.25e23 ~0b101.11e10 259e~2",
    );
    let mut lexer = Lexer::new(src, &mut err_emitter);

    assert_eq!(lexer.curr().data, TokenData::int(259));
    assert_eq!(lexer.curr().span.as_str(), "259");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::int(240));
    assert_eq!(lexer.curr().span.as_str(), "0xF0");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::int(-259));
    assert_eq!(lexer.curr().span.as_str(), "~259");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::int(-13));
    assert_eq!(lexer.curr().span.as_str(), "~0b11_01");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::float(25925, 100));
    assert_eq!(lexer.curr().span.as_str(), "259.25");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::float(0xF0C8, 0x100));
    assert_eq!(lexer.curr().span.as_str(), "0xF0.C8");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::float(-25925, 100));
    assert_eq!(lexer.curr().span.as_str(), "~259.25");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::float(-0o2124, 0o100));
    assert_eq!(lexer.curr().span.as_str(), "~0o21.24");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().data,
        TokenData::float(25925 * 10i128.pow(23), 100)
    );
    assert_eq!(lexer.curr().span.as_str(), "259.25e23");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().data,
        TokenData::float(0xF0C8 * 16i128.pow(0x1A), 0x100)
    );
    assert_eq!(lexer.curr().span.as_str(), "0xF0.C8p1A");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().data,
        TokenData::float(-25925 * 10i128.pow(23), 100),
    );
    assert_eq!(lexer.curr().span.as_str(), "~259.25e23");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::float(-0x17 * 2i128.pow(2), 0x4));
    assert_eq!(lexer.curr().span.as_str(), "~0b101.11e10");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::float(259, 100));
    assert_eq!(lexer.curr().span.as_str(), "259e~2");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::Eof);
    assert_eq!(lexer.curr().span.as_str(), "");
    assert!(!lexer.next());
    assert!(!err_emitter.has_error());
}

#[test]
fn errors() {
    let mut err_emitter = Emitter::new();
    let src = Src::new("test.cst", "25z … 25e5000 \n\n 0o25e~50000");
    let mut lexer = Lexer::new(src, &mut err_emitter);

    assert_eq!(lexer.curr().data, TokenData::int(25));
    assert_eq!(lexer.curr().span.as_str(), "25");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::Ident);
    assert_eq!(lexer.curr().span.as_str(), "z");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::float(25, 1),);
    assert_eq!(lexer.curr().span.as_str(), "25e5000");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::float(0o25, 1),);
    assert_eq!(lexer.curr().span.as_str(), "0o25e~50000");
    assert!(lexer.next());

    assert_eq!(lexer.curr().data, TokenData::Eof);
    assert_eq!(lexer.curr().span.as_str(), "");
    assert!(!lexer.next());
    assert!(err_emitter.has_error());

    eprintln!("{}", err_emitter);
}
