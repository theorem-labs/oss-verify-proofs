(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Footprint () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Footprint."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "2or"; "3Z"; "4covers"; "4heap_rg"; "4region"; "4rg_disj"; "4rg_hi"; "4rg_lo"; "4rg_wf"; "5add"; "5le"; "5of_nat"; "5pow"; "0a"; "0a1"]; ["0a2"; "0base"; "0cur"; "0cur'"; "0n"; "0n1"; "0n2"; "0r"; "0r'"; "0r1"; "0r2"; "6bv"; "6bv_unsigned"]]).
Record region : Type := Rg { rg_lo : Z; rg_hi : Z }.
Definition rg_wf (r : region) : Prop :=
0 <= rg_lo r /\ rg_lo r <= rg_hi r /\ rg_hi r <= 2 ^ 64.
Definition covers (r : region) (a : word) (n : nat) : Prop :=
rg_lo r <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= rg_hi r.
Definition rg_disj (r1 r2 : region) : Prop :=
rg_hi r1 <= rg_lo r2 \/ rg_hi r2 <= rg_lo r1.
Lemma rg_disj_sym : ltac2:(TCodec.tc2 tcn__Footprint ":'5&6r2r1%3221r3%5241p031pQF81pQD91").
Proof. intros r1 r2 [H|H]; [right|left]; exact H. Qed.
Lemma covers_mono : ltac2:(TCodec.tc2 tcn__Footprint "M'5'KyR0%211'0&3r4r2r1%43321&;&8%116r5%311%5231&7r6%211%316%:221%@348?p021p081p0?1pQ:E1pNG1pQBK1pQ@L1").
Proof. intros r r' a n [H1 H2] Hl Hh. split; lia. Qed.
Lemma covers_nowrap : ltac2:(TCodec.tc2 tcn__Footprint "M'5'KyR0%211'0&9r3%211&3r4r2%33251&;&:&L%12=6&<%11;%5231&=+2+R0%3221%;251p0=1p0B1pQ:F1pNH1pQ@L1").
Proof. intros r a n (_ & _ & Hhi) (_ & H). lia. Qed.
Lemma covers_disj : ltac2:(TCodec.tc2 tcn__Footprint "Q6'5'KyR0%211'0&6r6r5%3221&3r7r4%33251r3%53431'1&;&:&L%12A9&<%11?%5231%52E@%8221%51>%9231%;218%=241p0?1p0B1p0G1pQ>L1pQ2N1pQ<N1pQ0Q01pQFQ41pQDQ51").
Proof. intros r1 r2 a1 n1 a2 n2 [H|H] [H1 H2] [H3 H4]; [left|right]; lia. Qed.
Lemma covers_same_disj : ltac2:(TCodec.tc2 tcn__Footprint "Q='5'KyR0%211'0&3r5r4r3%43321r6r2%73241'1&;&:&L%12?7&<%11=%5231%52C>%8221%51?%9231%;218%=241r7%<2J1%;1C%?221%?2MI%B221%?1J%C231%E217%G241p0;1p0J1p0N1pQ>Q41pQ2Q61pQ<Q61pQ0Q81pQ@Q<1").
Proof. auto. Qed.
Definition stack_rg (sp : word) (below above : Z) : region :=
Rg (bv_unsigned sp - below) (bv_unsigned sp + above).
Definition seg_rg (lo hi : Z) : region := Rg lo hi.
Definition heap_rg (base : word) (cur : Z) : region :=
Rg (bv_unsigned base) (bv_unsigned base + cur).
Lemma heap_rg_bump : ltac2:(TCodec.tc2 tcn__Footprint "J'KyR0%211'2'0&;r4r3%3221&3&4r6r5%3221r2%63281r7%7215%931<;p041p0<1pQ:A1pND1pQ8D1pQ6E1pQ4G1").
Proof.
intros base cur cur' a n Hle H.
apply (covers_mono (heap_rg base cur)); [exact H | cbn; lia | cbn; lia].
Qed.
Definition layout_wf (rs : list region) : Prop :=
Forall rg_wf rs /\
forall i j, (i < j)%nat -> (j < length rs)%nat ->
rg_disj (nth i rs (Rg 0 0)) (nth j rs (Rg 0 0)).
