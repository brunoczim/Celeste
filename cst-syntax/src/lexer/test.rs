use crate::{lexer::Lexer, token::TokenKind};
use cst_error::Emitter;
use cst_source::Src;
use num::{BigInt, BigRational};

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
    let src = Src::new("test.cst", "a bc\ncd_Ef");
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
    let src = Src::new("test.cst", ",() ,\n  ( )");
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

#[test]
fn read_numbers() {
    let mut err_emitter = Emitter::new();
    let src = Src::new(
        "test.cst",
        "259 0xF0 ~259 ~0b11_01 259.25 0xF0.C8 ~259.25 ~0o21.24 259.25e23 \
         0xF0.C8p1A ~259.25e23 ~0b101.11e10 259e~2",
    );
    let mut lexer = Lexer::new(src, &mut err_emitter);

    assert_eq!(lexer.curr().kind, TokenKind::IntLiteral(BigInt::from(259)));
    assert_eq!(lexer.curr().span.as_str(), "259");
    assert!(lexer.next());

    assert_eq!(lexer.curr().kind, TokenKind::IntLiteral(BigInt::from(240)));
    assert_eq!(lexer.curr().span.as_str(), "0xF0");
    assert!(lexer.next());

    assert_eq!(lexer.curr().kind, TokenKind::IntLiteral(BigInt::from(-259)));
    assert_eq!(lexer.curr().span.as_str(), "~259");
    assert!(lexer.next());

    assert_eq!(lexer.curr().kind, TokenKind::IntLiteral(BigInt::from(-13)));
    assert_eq!(lexer.curr().span.as_str(), "~0b11_01");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().kind,
        TokenKind::FloatLiteral(BigRational::new(
            BigInt::from(25925),
            BigInt::from(100),
        ))
    );
    assert_eq!(lexer.curr().span.as_str(), "259.25");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().kind,
        TokenKind::FloatLiteral(BigRational::new(
            BigInt::from(0xF0C8),
            BigInt::from(0x100),
        ))
    );
    assert_eq!(lexer.curr().span.as_str(), "0xF0.C8");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().kind,
        TokenKind::FloatLiteral(BigRational::new(
            BigInt::from(-25925),
            BigInt::from(100),
        ))
    );
    assert_eq!(lexer.curr().span.as_str(), "~259.25");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().kind,
        TokenKind::FloatLiteral(BigRational::new(
            BigInt::from(-0o2124),
            BigInt::from(0o100),
        ))
    );
    assert_eq!(lexer.curr().span.as_str(), "~0o21.24");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().kind,
        TokenKind::FloatLiteral(
            BigRational::new(BigInt::from(25925), BigInt::from(100))
                * BigInt::from(10).pow(23)
        )
    );
    assert_eq!(lexer.curr().span.as_str(), "259.25e23");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().kind,
        TokenKind::FloatLiteral(
            BigRational::new(BigInt::from(0xF0C8), BigInt::from(0x100))
                * BigInt::from(16).pow(0x1A)
        )
    );
    assert_eq!(lexer.curr().span.as_str(), "0xF0.C8p1A");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().kind,
        TokenKind::FloatLiteral(
            BigRational::new(BigInt::from(-25925), BigInt::from(100))
                * BigInt::from(10).pow(23)
        )
    );
    assert_eq!(lexer.curr().span.as_str(), "~259.25e23");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().kind,
        TokenKind::FloatLiteral(
            BigRational::new(BigInt::from(-0x17), BigInt::from(0x4))
                * BigInt::from(2).pow(2)
        )
    );
    assert_eq!(lexer.curr().span.as_str(), "~0b101.11e10");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().kind,
        TokenKind::FloatLiteral(BigRational::new(
            BigInt::from(259),
            BigInt::from(100)
        ))
    );
    assert_eq!(lexer.curr().span.as_str(), "259e~2");
    assert!(lexer.next());

    assert_eq!(lexer.curr().kind, TokenKind::Eof);
    assert_eq!(lexer.curr().span.as_str(), "");
    assert!(!lexer.next());
    assert!(!err_emitter.has_error());
}

#[test]
fn errors() {
    let mut err_emitter = Emitter::new();
    let src = Src::new("test.cst", "25z … 25e5000 \n\n 0o25e~50000");
    let mut lexer = Lexer::new(src, &mut err_emitter);

    assert_eq!(lexer.curr().kind, TokenKind::IntLiteral(BigInt::from(25)));
    assert_eq!(lexer.curr().span.as_str(), "25");
    assert!(lexer.next());

    assert_eq!(lexer.curr().kind, TokenKind::Ident);
    assert_eq!(lexer.curr().span.as_str(), "z");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().kind,
        TokenKind::FloatLiteral(BigRational::from(BigInt::from(25)))
    );
    assert_eq!(lexer.curr().span.as_str(), "25e5000");
    assert!(lexer.next());

    assert_eq!(
        lexer.curr().kind,
        TokenKind::FloatLiteral(BigRational::from(BigInt::from(0o25)))
    );
    assert_eq!(lexer.curr().span.as_str(), "0o25e~50000");
    assert!(lexer.next());

    assert_eq!(lexer.curr().kind, TokenKind::Eof);
    assert_eq!(lexer.curr().span.as_str(), "");
    assert!(!lexer.next());
    assert!(err_emitter.has_error());

    eprintln!("{}", err_emitter);
}
