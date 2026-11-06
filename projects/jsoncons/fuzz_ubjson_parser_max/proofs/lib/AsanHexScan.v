(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Import ListNotations.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanHexScan () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "Corelib.Numbers.Cyclic.Int63.Uint63Axioms."; "Corelib.Strings.PrimString."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanHexScan.FPX_1."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1bool"; "1cons"; "1nat"; "1nil"; "1option"; "1true"; "2eq"; "2not"; "3N"; "4to_Z"; "5length"; "5string"; "6hex_byte_at"; "6segment_byte_at"; "7scanN"]; ["8add"; "8le"; "8lt"; "9div"; "9lt"; "9of_N"; "9to_N"; "0base"; "0fuel"; "0i"; "0n"; "0off"; "0s"; ":bv"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition byte_ok (s : PrimString.string) (off : N) : bool :=
match hex_byte_at s off with Some _ => true | None => false end.
Fixpoint scanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
match fuel with
| O => N.eqb n 0
| S f =>
if N.eqb n 0 then true
else if N.eqb n 1 then byte_ok s base
else let h := N.div2 n in (scanN s f base h && scanN s f (base + h) (n - h))%bool
end.
Lemma scanN_sound : ltac2:(TCodec.tc2 tcn__AsanHexScan "Q6&<'3'9'7'1&?r4r3r2r1%544321(6%93821&B%1257&8'5'My8%211%411&=r7&@r5%221A%5241(0%119%J3931%?11p0A1pQDN1p0E1pQFQ01pQ@Q11pQBQ31pQJQ51").
Proof.
intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [scanN] in H.
- apply N.eqb_eq in H. lia.
- destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
destruct (N.eqb_spec n 1) as [E1|Hn1].
+ subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_ok in H.
destruct (hex_byte_at s base); [discriminate|discriminate].
+ apply andb_prop in H as [H1 H2].
rewrite N.div2_div in *.
set (h := (n / 2)%N) in *.
destruct (N.lt_ge_cases i h) as [Hl|Hge].
* exact (IH _ _ H1 i Hl).
* specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.
Lemma segment_byte_at_some1 : ltac2:(TCodec.tc2 tcn__AsanHexScan "QD&<'9'7'1&?r3uR0wr2%544321(6%93821&A&F&C&:&;r4%211%411+2%7221%911%;2B1&D&E%11E%21:%4221&8'5'My8%211%411&>(2r6(4%11Q7%43Q831%621H(0%11:%Q:3:31%@11p0B1p0H1p0Q51pQHQ@1pQFQA1pQJQC1").
Proof.
intros s n off Hs Hn Hoff. cbn [segment_byte_at].
replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true
by (symmetry; apply N.ltb_lt; lia).
exact (scanN_sound s 64 0 n Hs off ltac:(lia)).
Qed.
End FPX_1.
