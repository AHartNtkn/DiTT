mod common;

alpha_equiv_test!(
    lambda_ascii_and_unicode_forms_are_equivalent,
    "module Surface.LambdaAscii where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n",
    "module Surface.LambdaUnicode where\npostulate C : Cat\nid : (x : C) -> C = λx. x\n"
);

alpha_equiv_test!(
    arrow_ascii_and_unicode_forms_are_equivalent,
    "module Surface.ArrowAscii where\npostulate C : Cat\npostulate D : Cat\nf : C -> D = \\x. x\n",
    "module Surface.ArrowUnicode where\npostulate C : Cat\npostulate D : Cat\nf : C → D = λx. x\n"
);

alpha_equiv_test!(
    product_ascii_and_unicode_forms_are_equivalent,
    "module Surface.ProductAscii where\npostulate A : Cat\npostulate B : Cat\nproj : (p : (A * B)) -> A = p.1\n",
    "module Surface.ProductUnicode where\npostulate A : Cat\npostulate B : Cat\nproj : (p : (A × B)) -> A = p.1\n"
);

alpha_equiv_test!(
    directed_hom_ascii_and_unicode_forms_are_equivalent,
    "module Surface.HomAscii where\npostulate C : Cat\nrefl_intro (x : C) : x ->[C] x = refl x\n",
    "module Surface.HomUnicode where\npostulate C : Cat\nrefl_intro (x : C) : x →[C] x = refl x\n"
);

alpha_equiv_test!(
    end_coend_ascii_and_unicode_forms_are_equivalent,
    "module Surface.EndAscii where\npostulate C : Cat\npostulate P : (x : C) -> Prop\nq : end (x : C). P x = q\nr : coend (x : C). P x = r\n",
    "module Surface.EndUnicode where\npostulate C : Cat\npostulate P : (x : C) -> Prop\nq : ∫ (x : C). P x = q\nr : ∫^ (x : C). P x = r\n"
);
