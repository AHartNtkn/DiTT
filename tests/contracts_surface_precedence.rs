mod common;

alpha_equiv_test!(
    projection_binds_tighter_than_application,
    r#"
module Prec.ProjAppA where
postulate A : Cat
postulate B : Cat
postulate f : A -> B
app (p : (A * A)) : B = f p.1
"#,
    r#"
module Prec.ProjAppB where
postulate A : Cat
postulate B : Cat
postulate f : A -> B
app (p : (A * A)) : B = f (p.1)
"#
);

alpha_equiv_test!(
    product_binds_tighter_than_arrow,
    r#"
module Prec.ProdArrowA where
postulate A : Cat
postulate B : Cat
postulate C : Cat
h : A * B -> C = \x. x
"#,
    r#"
module Prec.ProdArrowB where
postulate A : Cat
postulate B : Cat
postulate C : Cat
h : (A * B) -> C = \x. x
"#
);

alpha_equiv_test!(
    arrow_is_right_associative,
    r#"
module Prec.ArrowAssocA where
postulate A : Cat
postulate B : Cat
postulate C : Cat
k : A -> B -> C = \x. x
"#,
    r#"
module Prec.ArrowAssocB where
postulate A : Cat
postulate B : Cat
postulate C : Cat
k : A -> (B -> C) = \x. x
"#
);
