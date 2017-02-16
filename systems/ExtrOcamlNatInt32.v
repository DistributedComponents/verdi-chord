Require Import Arith Even Div2 EqNat Euclid.
Require Import ExtrOcamlBasic.

Extract Inductive nat => int32 [ "0l" "Int32.succ" ]
 "(fun fO fS n -> if n=Int32.zero then fO () else fS (Int32.pred n))".

Extract Constant plus => "(+)".
Extract Constant pred => "fun n -> Pervasives.max 0l (n-1l)".
Extract Constant minus => "fun n m -> Pervasives.max 0 (n-m)".
Extract Constant mult => "( * )".
Extract Inlined Constant max => "Pervasives.max".
Extract Inlined Constant min => "Pervasives.min".
Extract Inlined Constant EqNat.beq_nat => "(=)".
Extract Inlined Constant EqNat.eq_nat_decide => "(=)".

Extract Inlined Constant Peano_dec.eq_nat_dec => "(=)".

Extract Constant Compare_dec.nat_compare =>
 "fun n m -> if n=m then Eq else if n<m then Lt else Gt".
Extract Inlined Constant Compare_dec.leb => "(<=)".
Extract Inlined Constant Compare_dec.le_lt_dec => "(<=)".
Extract Inlined Constant Compare_dec.lt_dec => "(<)".
Extract Constant Compare_dec.lt_eq_lt_dec =>
 "fun n m -> if n>m then None else Some (n<m)".

Extract Constant Even.even_odd_dec => "fun n -> Int32.rem n 2 = 0".
Extract Constant Div2.div2 => "fun n -> Int32.div n 2".

Extract Inductive Euclid.diveucl => "(int * int)" [ "" ].
Extract Constant Euclid.eucl_dev => "fun n m -> (m/n, m mod n)".
Extract Constant Euclid.quotient => "fun n m -> m/n".
Extract Constant Euclid.modulo => "fun n m -> Int32.rem m n".
