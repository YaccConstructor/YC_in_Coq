Definition FSA Vt Et := Vt -> Et -> Vt -> Prop.
Record RSA Tt Nt St := mkRSA {
	Aut: FSA St (Tt + Nt);
	Nu: Nt -> (St * St) -> Prop;
}.
Definition ISectFSA Vt Et (a b: FSA Vt Et): FSA Vt Et := fun (vb: Vt) (e: Et) (ve: Vt) => (a vb e ve) /\ (b vb e ve).
Context {Tt Nt St: Type}.
Context {x: RSA Tt Nt St}.
Check Aut Tt Nt St x.
Check mkRSA.
Definition ISectRSA {Tt Nt St} (a b: RSA Tt Nt St): RSA Tt Nt St := mkRSA Tt Nt St (ISectFSA St (Tt + Nt) (a.(Aut Tt Nt St)) (b.(Aut Tt Nt St))) (fun n p => (Nu Tt Nt St a) n p \/ (Nu Tt Nt St b) n p).
