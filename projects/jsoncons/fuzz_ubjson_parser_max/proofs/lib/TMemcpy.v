(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import StrFun.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import TSTRW_tac.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__TMemcpy () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.TMemcpy."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.TMemcpy.Proofs."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2or"; "3firstn"; "3skipn"; "4Z"; "0F"; "0K"; "5le_bytes_to_word"]; ["6bvmap"; "6sext"; "0P"; "7CB"; "7cell"; "8evt"; "9mkR"; ":MS"; ";bytes_at"; "<rw_cells"; "=seg_rom"; "?INV"; ">memcpy_post"; ">rsegs"; "@add"; "@le"]; ["@lt"; "@modulo"; "@sub"; "@to_nat"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0bs"; "0fc"; "0gp"; "0junk"]; ["0m"; "0m1"; "0r"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"]; ["0sp"; "0src"; "AZ_to_bv"; "Abv"; "Abv_extract"; "Abv_unsigned"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0w"; "0x14"]; ["0x15"; "0x16"; "0x17"; "0x28"; "0x5"; "0x6"; "0x7"; "0xa1"; "0xa2"; "0xa3"; "0xa4"]]).
Definition rsegs := Plain.Plain_loaded_segments.
Definition memcpy_entry := 0xa9160%Z.
Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m'
/\ rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at rsegs m' (bv_unsigned a1) src.
Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
Notation S := (bv_unsigned a1).
Notation D := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.
Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
Notation ST pc mm x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 :=
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).
Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
bytes_at rsegs m1 S src /\ u8arr rsegs m1 D bs /\ copied src bs (Z.to_nat P) /\
munch W m m1 /\ wmono rsegs m m1.
Ltac open_inv H := destruct H as (SRC & DST & CP & MU & WM).
Ltac inv_tac :=
lazymatch goal with
| |- INV _ _ _ => split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
end.
Ltac fin :=
lazymatch goal with
| DST : u8arr _ ?m1 _ ?bs, CP : copied _ ?bs (Z.to_nat ?P) |- _ =>
let E := fresh "E" in
pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
apply rw_cells_of_u8arr in DST; rewrite LEN in DST
end;
finish2.
Tactic Notation "use" uconstr(L) :=
eapply L; first [ inv_tac | idtac ]; try (f_equal; lia); try lia;
try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
Lemma mc_a8c : ltac2:(TCodec.tc2 tcn__TMemcpy "S;'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215'8&N&Q1&R5%12F:+4%4221%62>1vQ6%62K1%:3C31&R2vQ5%:2O1r?%>221%52Q21%A3Q2G1vQ4%@2Q51r@%D221%;2Q81%G3Q8M1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ3Q721&G&Fr;r:r9r8r7r6vR:vR;vR<%:OQ0ONMR1R09LKQ9Q=Q7R28765JIHGFEDCBA4321+eUY0%QB2R?1(0%11R@rC&J%11Q9%C78H6G431%Q<3Q;E1p0Q>1p0QE1p0QM1p0R91p0R=1pU8RK1pU6RL1pU4RM1pU2RN1pU0RO1pU>S01pU<S11pU:S21pUDS31pU@S41pS6S51pQ6RN1pRJS01pS4S31").
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_2 by lia.
zstep. if_cases K2; zify_cond K2.
-
destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [exfalso; cbn in K2; lia|]; apply (proj1 (Z.nlt_ge _ _)) in Hl4.
window P 2%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat.
zstep. zstep. rewrite land_1.
zstep. if_cases K1; zify_cond K1.
+ zstep. fin.
+ window (P + 2)%Z 1%nat HW1.
ld1 HW1 0%nat. st1 HW1 0%nat. zstep. fin.
- destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [|exfalso; cbn in K2; lia].
zstep. rewrite land_1.
zstep. if_cases K1; zify_cond K1.
+ window P 1%nat HW. ld1 HW 0%nat. st1 HW 0%nat. zstep. fin.
+ zstep. fin.
Qed.
Lemma mc_a60 : ltac2:(TCodec.tc2 tcn__TMemcpy "S<'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215'8&N+4%22:1&Q1&R5%12H<%3215%7251vQ6%52L1%;3D31&R2vQ5%92Q01r?%?221%52Q31%B3Q3H1vQ4%?2Q61r@%E221%;2Q91%H3Q9N1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ3Q721&G&Fr;r:r9r8r7r6vR:vR;vR<%:OQ0ONMR2R19LKQ9Q=Q7R38765JIHGFEDCBA4321+eUWD%QB2R@1(0%11RArC&J%11Q9%C78H6G431%Q<3Q;E1p0Q>1p0QE1p0QM1p0R:1p0R>1pU8RL1pU6RM1pU4RN1pU2RO1pU0S01pU>S11pU<S21pU:S31pUDS41pU@S51pS6S61pQ6RO1pRJS11pS4S41").
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 4%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed.
Lemma mc_a58 : ltac2:(TCodec.tc2 tcn__TMemcpy "S;'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215'8&N&Q1&R5%12F:+8%4221%62>1vQ6%62K1%:3C31&R2vQ5%:2O1r?%>221%52Q21%A3Q2G1vQ4%@2Q51r@%D221%;2Q81%G3Q8M1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ3Q721&G&Fr;r:r9r8r7r6vR:vR;vR<%:OQ0ONMR1R09LKQ9Q=Q7R28765JIHGFEDCBA4321+eUW<%QB2R?1(0%11R@rC&J%11Q9%C78H6G431%Q<3Q;E1p0Q>1p0QE1p0QM1p0R91p0R=1pU8RK1pU6RL1pU4RM1pU2RN1pU0RO1pU>S01pU<S11pU:S21pUDS31pU@S41pS6S51pQ6RN1pRJS01pS4S31").
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- use (mc_a60 m1 bs P).
Qed.
Lemma mc_a0c : ltac2:(TCodec.tc2 tcn__TMemcpy "S<'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215'8&N+8%22:1&Q1&R5%12H<%3215%7251vQ6%52L1%;3D31&R2vQ5%92Q01r?%?221%52Q31%B3Q3H1vQ4%?2Q61r@%E221%;2Q91%H3Q9N1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ3Q721&G&Fr;r:r9r8r7r6vR:vR;vR<%:OQ0ONMR2R19LKQ9Q=Q7R38765JIHGFEDCBA4321+eUU0%QB2R@1(0%11RArC&J%11Q9%C78H6G431%Q<3Q;E1p0Q>1p0QE1p0QM1p0R:1p0R>1pU8RL1pU6RM1pU4RN1pU2RO1pU0S01pU>S11pU<S21pU:S31pUDS41pU@S51pS6S61pQ6RO1pRJS11pS4S41").
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 8%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat. zstep.
use (mc_a58 _ _ (P + 8)%Z).
Qed.
Lemma mc_734 : ltac2:(TCodec.tc2 tcn__TMemcpy "S;'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215'8&N&Q1&R5%12F:+8%4221%62>1vQ6%62K1%:3C31&R2vQ5%:2O1r?%>221%52Q21%A3Q2G1vQ4%@2Q51r@%D221%;2Q81%G3Q8M1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ3Q721&G&Fr;r:r9r8r7r6vR:vR;vR<%:OQ0ONMR1R09LKQ9Q=Q7R28765JIHGFEDCBA4321+eT^8%QB2R?1(0%11R@rC&J%11Q9%C78H6G431%Q<3Q;E1p0Q>1p0QE1p0QM1p0R91p0R=1pU8RK1pU6RL1pU4RM1pU2RN1pU0RO1pU>S01pU<S11pU:S21pUDS31pU@S41pS6S51pQ6RN1pRJS01pS4S31").
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a60 m1 bs P).
- zstep. use (mc_a8c m1 bs P).
Qed.
Lemma mc_a04 : ltac2:(TCodec.tc2 tcn__TMemcpy "S;'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215'8&N&Q1&R5%12F:+@%4221%62>1vQ6%62K1%:3C31&R2vQ5%:2O1r?%>221%52Q21%A3Q2G1vQ4%@2Q51r@%D221%;2Q81%G3Q8M1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ3Q721&G&Fr;r:r9r8r7r6vR:vR;vR<%:OQ0ONMR1R09LKQ9Q=Q7R28765JIHGFEDCBA4321+eUTH%QB2R?1(0%11R@rC&J%11Q9%C78H6G431%Q<3Q;E1p0Q>1p0QE1p0QM1p0R91p0R=1pU8RK1pU6RL1pU4RM1pU2RN1pU0RO1pU>S01pU<S11pU:S21pUDS31pU@S41pS6S51pQ6RN1pRJS01pS4S31").
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_734 m1 bs P).
- use (mc_a0c m1 bs P).
Qed.
Lemma mc_72c : ltac2:(TCodec.tc2 tcn__TMemcpy "S;'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215'8&N&Q1&R5%12F:+@%4221%62>1vQ6%62K1%:3C31&R2vQ5%:2O1r?%>221%52Q21%A3Q2G1vQ4%@2Q51r@%D221%;2Q81%G3Q8M1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ3Q721&G&Fr;r:r9r8r7r6vR:vR;vR<%:OQ0ONMR1R09LKQ9Q=Q7R28765JIHGFEDCBA4321+eT^0%QB2R?1(0%11R@rC&J%11Q9%C78H6G431%Q<3Q;E1p0Q>1p0QE1p0QM1p0R91p0R=1pU8RK1pU6RL1pU4RM1pU2RN1pU0RO1pU>S01pU<S11pU:S21pUDS31pU@S41pS6S51pQ6RN1pRJS01pS4S31").
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a0c m1 bs P).
- use (mc_734 m1 bs P).
Qed.
Lemma mc_978 : ltac2:(TCodec.tc2 tcn__TMemcpy "S<'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215'8&N+@%22:1&Q1&R5%12H<%3215%7251vQ6%52L1%;3D31&R2vQ5%92Q01r?%?221%52Q31%B3Q3H1vQ4%?2Q61r@%E221%;2Q91%H3Q9N1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ3Q721&G&Fr;r:r9r8r7r6vR:vR;vR<%:OQ0ONMR2R19LKQ9Q=Q7R38765JIHGFEDCBA4321+eUP<%QB2R@1(0%11RArC&J%11Q9%C78H6G431%Q<3Q;E1p0Q>1p0QE1p0QM1p0R:1p0R>1pU8RL1pU6RM1pU4RN1pU2RO1pU0S01pU>S11pU<S21pU:S31pUDS41pU@S51pS6S61pQ6RO1pRJS11pS4S41").
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 16%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat.
ld1 HW 8%nat. ld1 HW 9%nat. ld1 HW 10%nat. ld1 HW 11%nat.
st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat.
ld1 HW 12%nat. ld1 HW 13%nat. ld1 HW 14%nat. ld1 HW 15%nat.
zstep.
st1 HW 8%nat. st1 HW 9%nat. st1 HW 10%nat. st1 HW 11%nat.
zstep.
st1 HW 12%nat. st1 HW 13%nat. st1 HW 14%nat. st1 HW 15%nat.
zstep.
use (mc_a04 _ _ (P + 16)%Z).
Qed.
Lemma mc_848 : ltac2:(TCodec.tc2 tcn__TMemcpy "S;'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215'8&N&Q1&R5%12F:+8%4221%62>1vQ6%62K1%:3C31&R2vQ5%:2O1r?%>221%52Q21%A3Q2G1vQ4%@2Q51r@%D221%;2Q81%G3Q8M1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ3Q721&G&Fr;r:r9r8r7r6vR:vR;vR<%:OQ0ONMR1R09LKQ9Q=Q7R28765JIHGFEDCBA4321+eTfL%QB2R?1(0%11R@rC&J%11Q9%C78H6G431%Q<3Q;E1p0Q>1p0QE1p0QM1p0R91p0R=1pU8RK1pU6RL1pU4RM1pU2RN1pU0RO1pU>S01pU<S11pU:S21pUDS31pU@S41pS6S51pQ6RN1pRJS01pS4S31").
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- window P 4%nat HW. ld4 HW 0%nat q0. zstep. st4 HW 0%nat. zstep. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed.
Lemma mc_828 : ltac2:(TCodec.tc2 tcn__TMemcpy "SC'R3yR0%211'6y8%511%311p051'3%114'<&Kr?r>r=%43321&Oz%2215'8&N%1298&R5vQ6%22G1%63?41'7%;2:?&Q0+@%22B1%5241&R2vQ5%<2Q11rA%@221%52Q41%C3Q4J1%72Q64%E3Q6L1vQ4%D2Q91rC%H221%=2Q<1%K3Q<Q21&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ5Q?21&G&FrBr@r<r;r:r9r8vR:vR;vR<%;OQ1Q0ONR7R6R5MLQ::Q@98765KJIHGFEDCB4321+eTeL%QE2RD1(0%11RErF&J%11Q:%D78I6H431%Q=3Q<F1p0Q?1p0QF1p0QI1p0R11p0R81p0R@1p0RD1pU8S21pU6S31pU4S41pU2S51pU0S61pU>S71pU<S81pU:S91pUDS:1pUBS;1pU@S<1pS6S51pQ6S61pRJS81pS4S;1").
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
zstep. zstep. if_cases K8; zify_cond K8.
- use (mc_848 m1 bs P (Z_to_bv 64 r)).
- window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. st4 HW 0%nat. st4 HW 4%nat. zstep. zstep.
use (mc_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
Qed.
Lemma mc_7f8 : ltac2:(TCodec.tc2 tcn__TMemcpy "SD'4'R3yR0%211'6y8%511%311p051'3%114'<'8&Q3&Q2&R5vQ6%22?1r;%5221%711r>%:3F21&Kr=r<%33521&Oz%2215+@%A2>:%5221&R2&NvQ5%E2Q21r?%4221%62Q51%L3Q5C1r@%L2I1%:2Q91%Q03Q9G1vQ4%O2Q<1rA%>221%@2Q?1%Q63Q?M1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ7QJ21&G&F+?%Q=2R<1r:r9r8vR:vR;vR<%9OONMLR0QMQLKJQ8Q6Q<Q@7R365IHGFEDCBA@4321+eTd<%QF2RE1(0%11RFrD&J%11Q8%B78G6F431%Q;3Q:D1p0Q=1p0QD1p0QI1p0R21p0R61p0R:1p0R?1pU8S31pU6S41pU4S51pU2S61pU>S71pU<S81pU:S91pUDS:1pUBS;1pU@S<1pQ6S51pRJS71pS4S:1pNSC1").
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
window P 16%nat HW.
ld4 HW 0%nat q0. ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3.
zstep. zstep.
st4 HW 0%nat. st4 HW 4%nat. st4 HW 8%nat. st4 HW 12%nat.
zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z).
- use (mc_828 _ _ (P + 16)%Z (n - (P + 16))%Z).
Qed.
Lemma mc_7ec : ltac2:(TCodec.tc2 tcn__TMemcpy "S<'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321'7&Oz%2216&R5vQ6%22E1%62:1%8251'8&R2&NvQ5%92L1%321B%52N1%73NC1&Q2r?%22=1%:2Q31%<3Q3H1vQ4%C2Q61r@%>221%@2Q91%B3Q9N1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ7Q>21&G&Fr;r:r9r8r7r6vR:vR;vR<%:OQ0ONMR2R19LKQ9Q7Q=R38765JIHGFEDCBA4321+eTd0%QG2R@1(0%11RArC&J%11Q9%C78H6G431%Q<3Q;E1p0Q>1p0QE1p0QK1p0R41p0R>1pU8RL1pU6RM1pU4RN1pU2RO1pU0S01pU>S11pU<S21pU:S31pUDS41pUBS51pU@S61pQ6RO1pRJS11pS4S41").
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases K16; zify_cond K16.
- use (mc_828 m1 bs P (n - P)%Z).
- zstep. use (mc_7f8 (Z.to_nat (n - P)) m1 bs P).
Qed.
Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
Lemma mc_770 : ltac2:(TCodec.tc2 tcn__TMemcpy "T7'4'R3yR0%211'6y8%511%311p051'3%114'<'8&Q3&Q2&R5vQ6%22?1r;%5221%711r>%:3F21&Kr=r<%33521&O+2%2215+B%A2>:%5221&:u4&;r?%G219%I11vR1%53Q221%83Q371%N3Q0E1&R2&NvQ5%O2Q<1r@%4221+>%6221%82QA1%Q83QAO1rA%Q82Q51%<2QE1%Q<3QEQ31vQ4%Q;2QH1rB%@221%B2QK1%QB3QKQ91&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vQ@%DGCBA@?>=<;:98765432LQ8R5Q>1&G&F&AyQ0&R4w&?%11Q2%44RL351%736RM1+A%QF2RO1r:r9vR:vR;vR<%@OQ5Q4Q3Q2RBR?R>Q1Q0Q>QBQHR386RE5ONMLKJIHGF4321+eT`4%QN2S71(0%11S8rE&J%11Q>%I78M6L431%QA3Q@K1p0QC1p0QJ1p0QO1p0R:1p0RE1p0RI1p0RM1p0S21pU8SF1pU6SG1pU4SH1pU>SI1pU<SJ1pU:SK1pUDSL1pUBSM1pU@SN1pTNSH1pQ6SH1pRJSJ1pS4SM1pNT61").
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
window (P - 2)%Z 20%nat HW.
pose proof (window_sub src _ (P - 2)%Z 20 0 4 (P - 2)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 2%nat 4%nat ltac:(by_le 16%Z). st HW 6%nat 4%nat ltac:(by_le 16%Z).
st HW 10%nat 4%nat ltac:(by_le 16%Z). st HW 14%nat 4%nat ltac:(by_le 16%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ zstep. use (mc_978 _ _ (P + 16)%Z).
Qed.
Lemma mc_754 : ltac2:(TCodec.tc2 tcn__TMemcpy "SN'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215+Q0&Q2&R5vQ6%22F1%421<%9261'8&:u4&;&Q3r?%211vR1%53M21%83N71%:3KH1&R2&NvQ5%C2Q71r@%4221%62Q:1%B3Q:Q01rA%J2G1%:2Q>1%F3Q>Q41vQ4%M2QA1rB%>221%@2QD1%L3QDQ:1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vQ@%DGCBA@?>=<;:98765432LQ6QGQ<1&G&F&AyQ0&R4w&?%11Q2%44RE351%736RF1r;r:r9r8vR:vR;vR<%@OQ5Q4Q3Q2RCRBRAQ1Q0Q>QBQFR08765ONMLKJIHGF4321+eT_8%QL2S01(0%11S1rE&J%11Q>%I78M6L431%QA3Q@K1p0QC1p0QJ1p0QO1p0R81p0RD1p0RL1p0S01pU8S>1pU6S?1pU4S@1pU2SA1pU>SB1pU<SC1pU:SD1pUDSE1pUBSF1pU@SG1pTNSA1pQ6SA1pRJSC1pS4SF1").
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_770 (Z.to_nat (n - (P + 2))) _ _ (P + 2)%Z w). by_win HW 0%nat.
Qed.
Lemma mc_878 : ltac2:(TCodec.tc2 tcn__TMemcpy "T7'4'R3yR0%211'6y8%511%311p051'3%114'<'8&Q3&Q2&R5vQ6%22?1r;%5221%711r>%:3F21&Kr=r<%33521&O+1%2215+C%A2>:%5221&:u4&;r?%G219%I11vR1%53Q221%83Q371%N3Q0E1&R2&NvQ5%O2Q<1r@%4221+?%6221%82QA1%Q83QAO1rA%Q82Q51%<2QE1%Q<3QEQ31vQ4%Q;2QH1rB%@221%B2QK1%QB3QKQ91&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vQ@%DGCBA@?>=<;:98765432LQ8R5Q>1&G&F&AyQ0&R4w&?%11Q2%44RL351%736RM1+B%QF2RO1r:r9vR:vR;vR<%@OQ5Q4Q3Q2RBR?R>Q1Q0Q>QBQHR386RE5ONMLKJIHGF4321+eTh<%QN2S71(0%11S8rE&J%11Q>%I78M6L431%QA3Q@K1p0QC1p0QJ1p0QO1p0R:1p0RE1p0RI1p0RM1p0S21pU8SF1pU6SG1pU4SH1pU>SI1pU<SJ1pU:SK1pUDSL1pUBSM1pU@SN1pTNSH1pQ6SH1pRJSJ1pS4SM1pNT61").
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
window (P - 1)%Z 20%nat HW.
pose proof (window_sub src _ (P - 1)%Z 20 0 4 (P - 1)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 1%nat 4%nat ltac:(by_le 24%Z). st HW 5%nat 4%nat ltac:(by_le 24%Z).
st HW 9%nat 4%nat ltac:(by_le 24%Z). st HW 13%nat 4%nat ltac:(by_le 24%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ zstep. use (mc_978 _ _ (P + 16)%Z).
Qed.
Lemma mc_864 : ltac2:(TCodec.tc2 tcn__TMemcpy "SN'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215+Q0&Q2&R5vQ6%22F1%421<%9261'8&:u4&;&Q3r?%211vR1%53M21%83N71%:3KH1&R2&NvQ5%C2Q71r@%4221%62Q:1%B3Q:Q01rA%J2G1%:2Q>1%F3Q>Q41vQ4%M2QA1rB%>221%@2QD1%L3QDQ:1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vQ@%DGCBA@?>=<;:98765432LQ6QGQ<1&G&F&AyQ0&R4w&?%11Q2%44RE351%736RF1r;r:r9r8vR:vR;vR<%@OQ5Q4Q3Q2RCRBRAQ1Q0Q>QBQFR08765ONMLKJIHGF4321+eTgH%QL2S01(0%11S1rE&J%11Q>%I78M6L431%QA3Q@K1p0QC1p0QJ1p0QO1p0R81p0RD1p0RL1p0S01pU8S>1pU6S?1pU4S@1pU2SA1pU>SB1pU<SC1pU:SD1pUDSE1pUBSF1pU@SG1pTNSA1pQ6SA1pRJSC1pS4SF1").
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
st HW 0%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep. zstep.
use (mc_878 (Z.to_nat (n - (P + 1))) _ _ (P + 1)%Z w). by_win HW 0%nat.
Qed.
Lemma mc_90c : ltac2:(TCodec.tc2 tcn__TMemcpy "T7'4'R3yR0%211'6y8%511%311p051'3%114'<'8&Q3&Q2&R5vQ6%22?1r;%5221%711r>%:3F21&Kr=r<%33521&O+3%2215+A%A2>:%5221&:u4&;r?%G219%I11vR1%53Q221%83Q371%N3Q0E1&R2&NvQ5%O2Q<1r@%4221+=%6221%82QA1%Q83QAO1rA%Q82Q51%<2QE1%Q<3QEQ31vQ4%Q;2QH1rB%@221%B2QK1%QB3QKQ91&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vQ@%DGCBA@?>=<;:98765432LQ8R5Q>1&G&F&AyQ0&R4w&?%11Q2%44RL351%736RM1+@%QF2RO1r:r9vR:vR;vR<%@OQ5Q4Q3Q2RBR?R>Q1Q0Q>QBQHR386RE5ONMLKJIHGF4321+eTm0%QN2S71(0%11S8rE&J%11Q>%I78M6L431%QA3Q@K1p0QC1p0QJ1p0QO1p0R:1p0RE1p0RI1p0RM1p0S21pU8SF1pU6SG1pU4SH1pU>SI1pU<SJ1pU:SK1pUDSL1pUBSM1pU@SN1pTNSH1pQ6SH1pRJSJ1pS4SM1pNT61").
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
window (P - 3)%Z 20%nat HW.
pose proof (window_sub src _ (P - 3)%Z 20 0 4 (P - 3)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 3%nat 4%nat ltac:(by_le 8%Z). st HW 7%nat 4%nat ltac:(by_le 8%Z).
st HW 11%nat 4%nat ltac:(by_le 8%Z). st HW 15%nat 4%nat ltac:(by_le 8%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ use (mc_978 _ _ (P + 16)%Z).
Qed.
Lemma mc_8e8 : ltac2:(TCodec.tc2 tcn__TMemcpy "SN'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215+Q0&Q2&R5vQ6%22F1%421<%9261'8&:u4&;&Q3r?%211vR1%53M21%83N71%:3KH1&R2&NvQ5%C2Q71r@%4221%62Q:1%B3Q:Q01rA%J2G1%:2Q>1%F3Q>Q41vQ4%M2QA1rB%>221%@2QD1%L3QDQ:1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vQ@%DGCBA@?>=<;:98765432LQ6QGQ<1&G&F&AyQ0&R4w&?%11Q2%44RE351%736RF1r;r:r9r8vR:vR;vR<%@OQ5Q4Q3Q2RCRBRAQ1Q0Q>QBQFR08765ONMLKJIHGF4321+eTkL%QL2S01(0%11S1rE&J%11Q>%I78M6L431%QA3Q@K1p0QC1p0QJ1p0QO1p0R81p0RD1p0RL1p0S01pU8S>1pU6S?1pU4S@1pU2SA1pU>SB1pU<SC1pU:SD1pUDSE1pUBSF1pU@SG1pTNSA1pQ6SA1pRJSC1pS4SF1").
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z). st HW 2%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_90c (Z.to_nat (n - (P + 3))) _ _ (P + 3)%Z w). by_win HW 0%nat.
Qed.
Lemma mc_740 : ltac2:(TCodec.tc2 tcn__TMemcpy "S='R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321&Oz%2215+Q0&Q2&R5vQ6%22F1%421<%9261'8&R2&NvQ5%92M1r?%4221%62Q01%83Q0F1r@%@2=1%:2Q41%<3Q4J1vQ4%C2Q71rA%>221%@2Q:1%B3Q:Q01&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ7Q>21&G&Fr;r:r9r8r7vR:vR;vR<%9OONMLR3R2R1KJQ8Q6Q<Q@8765IHGFEDCBA@4321+eT^D%QF2R@1(0%11RArD&J%11Q8%B78G6F431%Q;3Q:D1p0Q=1p0QD1p0QI1p0R31p0R;1p0R?1pU8RM1pU6RN1pU4RO1pU2S01pU0S11pU>S21pU<S31pU:S41pUDS51pUBS61pU@S71pQ6S01pRJS21pS4S51").
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> -> ->; open_inv I.
window P 4%nat HW. ld4 HW 0%nat q0.
zstep. zstep. if_cases K3; zify_cond K3.
- use (mc_864 m1 bs P q0). by_win HW 0%nat.
- zstep. zstep. if_cases K2; zify_cond K2.
+ use (mc_8e8 m1 bs P q0). by_win HW 0%nat.
+ use (mc_754 m1 bs P q0). by_win HW 0%nat.
Qed.
Lemma mc_71c : ltac2:(TCodec.tc2 tcn__TMemcpy "S<'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321'7&Oz%2216&R5vQ6%22E1%62:1%8251'8&R2&NvQ5%92L1%321B%52N1%73NC1&Q2r?%22=1%:2Q31%<3Q3H1vQ4%C2Q61r@%>221%@2Q91%B3Q9N1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ7Q>21&G&Fr;r:r9r8r7r6vR:vR;vR<%:OQ0ONMR2R19LKQ9Q7Q=R38765JIHGFEDCBA4321+eT]@%QG2R@1(0%11RArC&J%11Q9%C78H6G431%Q<3Q;E1p0Q>1p0QE1p0QK1p0R41p0R>1pU8RL1pU6RM1pU4RN1pU2RO1pU0S01pU>S11pU<S21pU:S31pUDS41pUBS51pU@S61pQ6RO1pRJS11pS4S41").
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases K32; zify_cond K32.
- use (mc_740 m1 bs P).
- zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_978 m1 bs P).
+ use (mc_72c m1 bs P).
Qed.
Lemma mc_714 : ltac2:(TCodec.tc2 tcn__TMemcpy "S<'R3yR0%211'6y8%511%311p051'3%114'<&Kr>r=r<%43321'7&Oz%2216&R5vQ6%22E1%62:1%8251'8&R2&NvQ5%92L1%321B%52N1%73NC1&Q2r?%22=1%:2Q31%<3Q3H1vQ4%C2Q61r@%>221%@2Q91%B3Q9N1&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543MQ7Q>21&G&Fr;r:r9r8r7r6vR:vR;vR<%:OQ0ONMR2R19LKQ9Q7Q=R38765JIHGFEDCBA4321+eT]8%QG2R@1(0%11RArC&J%11Q9%C78H6G431%Q<3Q;E1p0Q>1p0QE1p0QK1p0R41p0R>1pU8RL1pU6RM1pU4RN1pU2RO1pU0S01pU>S11pU<S21pU:S31pUDS41pUBS51pU@S61pQ6RO1pRJS11pS4S41").
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_7ec m1 bs P).
- use (mc_71c m1 bs P).
Qed.
Lemma mc_6e4 : ltac2:(TCodec.tc2 tcn__TMemcpy "SI'4'R3yR0%211'6y8%511%311p051'3%114'<'8&Q3&Q2&R5vQ6%22?1r;%5221%711r>%:3F21&Kr=r<%33521'7&Oz%2216&Q0%128?%6231&R2&NvQ5%F2Q31%321A%52Q51%L3Q5@1r?%L2I1%92Q91%Q03Q9D1vQ4%O2Q<1r@%=221%?2Q?1%Q63Q?J1rA%A2?1+1%C221%E2QE1%Q<3QEQ01&E&M&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=vR1vQ@%EGDCBA@?>=<;:9876543Q3Q<R021&G&F%QA2RANr:r9r8vR:vR;vR<%8ONMLKR2R1R8JIQ=Q7Q;QAR5765HGFEDCBA@?4321+eT[H%QJ2RJ1(0%11RKrD&J%11Q7%A78F6E431%Q:3Q9C1p0Q<1p0QC1p0QJ1p0QO1p0R71p0R?1p0RD1pU8S81pU6S91pU4S:1pU>S;1pU<S<1pU:S=1pUFS>1pUDS?1pUBS@1pU@SA1pQ6S:1pRJS<1pS4S?1pNSH1").
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28 HK I HP -> -> -> ->; open_inv I.
window P 1%nat HW.
ld1 HW 0%nat. zstep. zstep. zstep. rewrite land_3.
st1 HW 0%nat. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_714 _ _ (P + 1)%Z).
- zstep. zstep. if_cases K1; zify_cond K1.
+ use (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z).
+ zstep. use (mc_714 _ _ (P + 1)%Z).
Qed.
Lemma memcpy_body : ltac2:(TCodec.tc2 tcn__TMemcpy "R?'3'R3y8%211%411&I&MvQ@&R5yR0vQ4%3221(1'D(C&Q3vQ6%9281%311r1%6221(5%119%;3:31%C4BA=1&HvQ5%C2B1vR1%44GF21&E&LvQCvR0vQ>vR=vQDvQEvQHvQIvQJvQKvQLvQMvQNvQOvQFvQGv=vQ=%CGBA@?>=<;:987654321Q8HQ2FQ;&G&FvR6vR7vR8vQ7vQ8vQ9vQ:vQ;vR9vR:vR;vR<%=OQ1Q0ON<;:MLQGQ7QA98765KJIHGFEDCB4321&R2+eT[0%22QK1(0%R51QM%211&J%11R3%G79J6I3R31%Q=3R5I1p0Q?1p0QE1pS0R:1").
Proof using AB LEN SEP.
intros junk DST0 SRC.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
pose proof (copied_0 src junk ltac:(rewrite (rw_cells_CB_length _ _ _ _ _ DST0); lia)) as CP.
change 0%nat with (Z.to_nat 0) in CP. clear DST0.
zstep. rewrite land_3. zstep. if_cases Ksal; zify_cond Ksal.
-
zstep. zstep. rewrite land_3. zstep. if_cases Kdal; zify_cond Kdal.
+ use (mc_71c m junk 0%Z).
+ use (mc_7ec m junk 0%Z).
- zstep. if_cases K0; zify_cond K0.
+ zstep. use (mc_714 m junk 0%Z).
+ zstep. zstep. zstep. use (mc_6e4 (Z.to_nat n) m junk 0%Z).
Qed.
End Proofs.
Lemma memcpy_spec : ltac2:(TCodec.tc2 tcn__TMemcpy "T>'R3yR0%211&@y5%2213yQ0%711'6y8%:11%311p0:1'3%114&H&Mr3&R5rJ%22C1r2%746521'8'4&2%12@9&Q3%118%63531&Ir5rM%?2Q01(1'D(CrK%D2Q51%<11%421G(5%117%93831%>4L=;1'9&O&NrL%O2Q@1%32A1rN%Q22QC1%7231%7225%921F%;231&E&LrQ8rQ7rQ6rQ5rQ1rQ0rGrFrErDrCrBrAr@r?r>r9r8rOr6r7%FGEDCBA@?>=<;:9876543MQ@21&G&FrQ4rQ3rQ2rIrHr=r<r;r:%:OQ1Q0ON987ML?Q9QLQ<QGR965KJIHGFEDCB4321&R2+eT[0%22RN1(0%11RO&J%11RC%C78I5H3E1%Q<3REE1p0Q>1p0QK1p0R;1p0RC1pS0RL1pT4RM1pS2S01pRLS61pLS91pTJS=1pTHS>1pTFS?1pTDS@1pS@SA1pS>SB1pT0SC1pSNSD1pSLSE1pSJSF1pSHSG1pSFSH1pSDSI1pSBSJ1pRHSK1pRFSL1pRDSM1pRBSN1pR@SO1pR>T01pR<T11pR:T21pS<T31pS:T41pTBT51pT@T61pT>T71pTLT81pRNT91pT2T:1pS8T;1").
Proof.
intros until junk. intros SRC LEN DST SEP.
eapply memcpy_body; try eassumption.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
