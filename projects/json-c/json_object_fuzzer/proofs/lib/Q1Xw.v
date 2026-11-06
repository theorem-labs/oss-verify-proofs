(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpzM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpzM.Mqg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo AP S : Z) (str : list Z) (slack : list byte).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Hypothesis APC : rw_cells asegs m AP [C8 (wz S)].
Hypothesis APLO : bv_unsigned sp <= AP.

Hypothesis STR : bytes_at asegs m S (zb str ++ b8 0 :: slack).
Hypothesis BYT : Forall (fun c => 0 < c < 256) str.
Hypothesis SZ : szone S (zlength str + 1).
Hypothesis SLEN : zlength str + 1 <= 2^40.
Hypothesis SEP : S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S.

Ltac pc_tail FRa DIR FRb ST MU WM :=
dir_L1 DIR;
run; call_memset DIR;
run; dir_L2 DIR;
run;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of FRa with rw_cells _ _ ?A ?ca => lazymatch type of DIR with rw_cells _ _ _ ?cd => lazymatch type of FRb with rw_cells _ _ _ ?cb =>
let FR := fresh "FR" in
assert (FR : rw_cells asegs mc A (ca ++ cd ++ cb))
by (apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FRa|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; cbn [cells_size csize Nat.add app];
[eapply rwc_eq; [exact DIR| lia] | eapply rwc_eq; [exact FRb| lia]]);
clear FRa DIR FRb; cbn [app] in FR;
release_frame FR ST (bv_unsigned sp)
end end end end;
apply evt_done; unfold rpost; do 16 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST| exact I].

Ltac pc_join FRa DIR FRb FMT ST MU WM :=
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?mc ?ro) =>
let r2 := QVsB.Mq1.tbl_getreg 2 in let r3 := QVsB.Mq1.tbl_getreg 3 in let r4 := QVsB.Mq1.tbl_getreg 4 in
let r8 := QVsB.Mq1.tbl_getreg 8 in let r9 := QVsB.Mq1.tbl_getreg 9 in
let r18 := QVsB.Mq1.tbl_getreg 18 in let r19 := QVsB.Mq1.tbl_getreg 19 in let r20 := QVsB.Mq1.tbl_getreg 20 in
let r21 := QVsB.Mq1.tbl_getreg 21 in let r22 := QVsB.Mq1.tbl_getreg 22 in let r23 := QVsB.Mq1.tbl_getreg 23 in
let r24 := QVsB.Mq1.tbl_getreg 24 in let r25 := QVsB.Mq1.tbl_getreg 25 in let r26 := QVsB.Mq1.tbl_getreg 26 in let r27 := QVsB.Mq1.tbl_getreg 27 in
lazymatch type of FRa with rw_cells _ mc ?A1 ?c1 =>
lazymatch type of FRb with rw_cells _ mc ?A2 ?c2 =>
lazymatch type of DIR with rw_cells _ mc ?A3 ?c3 =>
lazymatch type of FMT with ro_cells _ mc ?A4 ?c4 =>
lazymatch type of ST with stk _ mc ?l ?h =>
lazymatch type of MU with munch ?W ?m0 mc =>
eapply (evt_cut segs (fun ms' : machine_state => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
(m' : word -> option byte),
ms' = MS (mkR ra' r2 r3 r4 t0' t1' t2' r8 r9 a0' a1' a2' a3' a4' a5' a6' a7' r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3' t4' t5' t6')
F (Z_to_bv 64 343088) fc rv m' ro
/\ rw_cells segs m' A1 c1 /\ rw_cells segs m' A2 c2 /\ rw_cells segs m' A3 c3 /\ ro_cells segs m' A4 c4
/\ stk segs m' l h /\ munch W m0 m' /\ wmono segs m0 m' /\ mem_inv segs m') Q)
end end end end end end end.
Ltac pc_join_done := apply evt_done; do 17 eexists; split; [cbv delta [mkR]; reflexivity|];
repeat (split; [eassumption|]); eassumption.

Lemma printf_common_cannot_open :
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - PCOMMON_STACK, bv_unsigned sp)] lo m
(fun _ _ => True))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x1ef3c)  (wz AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
eapply evt_cut; [exact (printf_common_cannot_open_head ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo AP S str slack ISH0 MI ST CEIL LO APC APLO STR SZ)|].
clear MI ST APC. cbv beta.
intros ms' (m2 & junk1 & junk2 & x3 & x4 & -> & FRa & FRb & DIR & MI & APC & FMT & ST & MU & WM).
pose proof CEIL as CEIL'. idtac. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct ISH0 as (ASH & RC & SB).
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
pose proof (rw_cells_bound _ _ _ _ APC) as BAP. cbn in BAP.
assert (SNZ : 0 < S /\ S + (zlength str + 1) + 8 <= 2^47) by (unfold szone in SZ; idtac; lia).

set (BAh := bytes_at) in STR. change (boxed (szone S (zlength str + 1))) in SZ.
change (boxed (S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S)) in SEP.
unfold zlength in *.
run. call_strchr 0x1acf4 [67; 83].
run. call_strchr 0x1088e [99; 115; 91].
run. call_strchr 0x140d6 [115; 83].

run. unfold_cond. rewrite (unsigned_lit S) by lia. if_false.

run.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (bytes_at_transport asegs _ m mc _ _ STR MU ltac:(subst BAh; unfold boxed in SEP; cbn [disjoint_from]; rewrite length_app, zb_length; cbn [length]; lia)) as STRc end.
eapply evt_cut; [eapply istrlen_spec with (s := str) (t := slack); [exact STRc| exact BYT] |].
intros ms' <-. unfold zlength. fixret. clear STRc.

bstep. bstep. bstep. rewrite (unsigned_lit S), zb_lxor_ones by lia. ifF.

bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (ash_munch _ _ _ ASH MU WM ltac:(zforalls)) as ASHc;
pose proof (shadow_base_munch _ _ _ SB MU ltac:(rt_wzones)) as SBc;
pose proof (rt_consts_at_munch _ _ _ RC MU WM ltac:(rt_wzones)) as RCc end.
unfold boxed in SZ.
pc_join FRa DIR FRb FMT ST MU WM.
2:{ intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & FRa' & FRb' & DIR' & FMT' & ST' & MU' & WM' & MI').
clear FRa FRb DIR FMT ST MU WM MI. rename FRa' into FRa, FRb' into FRb, DIR' into DIR, FMT' into FMT, ST' into ST, MU' into MU, WM' into WM, MI' into MI.
pc_tail FRa DIR FRb ST MU WM. }
destruct (Z_le_gt_dec (Z.of_nat (length str) + 1) 64) as [N64|N65].
- unfold_cond. fold_lit_ux. replace (Z.of_nat (length str) + -64) with ((Z.of_nat (length str) + 1) + -65) by lia. rewrite u_nm65 by lia.
match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
replace c with false by (symmetry; apply (proj2 (Bool.negb_false_iff _)); apply Z.ltb_lt; clear - N64; lia) end.
cbv iota.
destruct (ash_szone_words _ _ _ ASHc SZ ltac:(lia)) as [W1 W2].
destruct SBc as [SB1 SB2]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in SB1, SB2.
bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep.
rewrite ?(unsigned_lit S), ?(unsigned_lit (S + (Z.of_nat (length str) + 1) + -1)) by lia.
replace (2147450880 + S ≫ 3) with (SH S) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (S + (Z.of_nat (length str) + 1) + -1) ≫ 3) with (SH (S + (Z.of_nat (length str) + 1) - 1))
by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH S /\ SH S <= SH (S + (Z.of_nat (length str) + 1) - 1) < 0x10007fff8000)
by (rewrite !SH_eq; clear - SNZ BS; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH S)), (unsigned_lit (SH (S + (Z.of_nat (length str) + 1) - 1))) by lia. rewrite !land_m8 by lia.
replace (SH S - SH S mod 8) with (8 * (SH S / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (S + (Z.of_nat (length str) + 1) - 1) - SH (S + (Z.of_nat (length str) + 1) - 1) mod 8)
with (8 * (SH (S + (Z.of_nat (length str) + 1) - 1) / 8)) by (Z.div_mod_to_equations; lia).
bstep. bstep. bstep. bstep.
pc_join_done.
- ifz. bstep. ifz. run.
pose proof (rt_mem_cells_of _ (shadow_base_munch _ _ _ SB MU ltac:(rt_wzones)) RCc) as RTM.
destruct (rng_ok_of_ash _ _ _ ASHc SZ ltac:(lia)) as (_ & _ & SOK & _ & _). specialize (SOK ltac:(lia)).
call_u rip_spec7; [exact RTM| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia| exact SOK| lia| lia| lia
| unfold szone in SZ; rewrite ?KHI_eq in *; clear - SZ SNZ; lia|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST end.
clear ASHc SBc RCc RTM SOK.
bstep.
pc_join_done.
Qed.
End S.
