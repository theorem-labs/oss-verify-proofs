(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qm.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1go.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hm X1nq.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.

Lemma u32arr_of_u8arr : forall segs m A bs k,
u8arr segs m A bs -> length bs = (4 * k)%nat ->
exists ws, length ws = k /\ u32arr segs m A ws.
Proof.
intros segs m A bs k [Hb Hw] HL.
destruct (bytes_are_f32 k bs HL) as (ws & Lw & E). rewrite cells_bytes_f32 in E.
exists ws. split; [exact Lw|]. split.
- rewrite E. exact Hb.
- rewrite Lw. replace (4 * Z.of_nat k)%Z with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.
Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof. intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws))%Z by lia. exact Hw. Qed.

Definition obox (ws : list word) : list cell := [CB 8000 (cells_bytes (f32 ws))].
Lemma obox_wf : forall ws, length ws = 2000%nat -> cells_wf (obox ws).
Proof. intros ws L. cbn. split; [|exact I]. rewrite cells_bytes_f32, u32s_length, L. reflexivity. Qed.
Lemma f32_box : forall m A ws, length ws = 2000%nat -> rw_cells rsegs m A (f32 ws) -> rw_cells rsegs m A (obox ws).
Proof.
intros m A ws L H. eapply rw_cells_recast; [exact H | apply obox_wf; exact L |].
cbn [obox cells_bytes cbytes app]. rewrite app_nil_r. reflexivity.
Qed.
Lemma f32_unbox : forall m A ws, rw_cells rsegs m A (obox ws) -> rw_cells rsegs m A (f32 ws).
Proof.
intros m A ws H. eapply rw_cells_recast; [exact H | apply cells_wf_f32 |].
cbn [obox cells_bytes cbytes app]. rewrite app_nil_r. reflexivity.
Qed.
Lemma obox_size : forall ws, Z.of_nat (cells_size (obox ws)) = 8000.
Proof. intros. vm_compute. reflexivity. Qed.
#[export] Hint Rewrite obox_size : chunk_sizes.
Lemma u32arr_of_obox : forall m A ws, rw_cells rsegs m A (obox ws) -> u32arr rsegs m A ws.
Proof. intros m A ws H. apply u32arr_of_f32. apply f32_unbox. exact H. Qed.

Lemma zbv_neq_offset : forall a b, 0 < b < 2^64 ->
negb (bv_eqb (Z_to_bv 64 (a + b)) (Z_to_bv 64 a)) = true.
Proof.
intros a b Hb. rewrite bv_eqb_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
destruct (Z.eqb_spec ((a + b) mod 2^64) (a mod 2^64)) as [E|NE]; [|reflexivity].
exfalso. assert (D : ((a + b) - a) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
replace (a + b - a) with b in D by lia. rewrite Z.mod_small in D by lia. lia.
Qed.

Section Loop.
Context {RCEIL : RunCeiling}.
Variables (OUT STEREO lo : Z) (m0 : mem).
Variables ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Hypothesis AOS : OUT + 8000 <= STEREO \/ STEREO + 24 <= OUT.
Hypothesis AOL : OUT + 8000 <= lo \/ bv_unsigned sp <= OUT.
Hypothesis ASL : STEREO + 24 <= lo \/ bv_unsigned sp <= STEREO.

Local Notation SREGS a1v a3v a4v :=
(mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OUT + -4)) a1v (Z_to_bv 64 STEREO) a3v a4v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

Ltac out_store idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with XB : rw_cells _ mc OUT (obox ?ws), LW : length ?ws = 2000%nat |- _ =>
pose proof (u32arr_store_ok rsegs mc OUT ws idx _ (u32arr_of_obox _ _ _ XB) ltac:(rewrite LW; lia) ltac:(f_equal; lia)) as SOK;
zstep;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
let LW2 := fresh "LW" in
assert (LW2 : length (upd ws (Z.to_nat idx) v) = 2000%nat) by (rewrite upd_length; exact LW);
pose proof (f32_box _ _ _ LW2
(f32_of_u32arr _ _ _ _ (u32arr_write rsegs mc OUT ws idx v (u32arr_of_obox _ _ _ XB) ltac:(rewrite LW; lia)))) as XB2;
match goal with |- context [write_to_mem mc ?a (le4 v)] =>
replace (write_to_mem mc a (le4 v)) with (write_to_mem mc (wa (OUT + 4 * idx)) (le4 v)) by (f_equal; f_equal; lia) end;
clear XB LW; store_done; try clear SOK; rename XB2 into XB; rename LW2 into LW
end
end end.

#[using="AOS"] Lemma stereo_loop : forall (k : nat) (i : Z) (ws : list word) (q0 q1 q2 q3 q4 q5 a4 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
Z.of_nat k = i -> 0 <= i < 1000 -> True ->
frm0 fc -> mem_inv rsegs m -> munch [(lo, bv_unsigned sp); (OUT, OUT + 8000); (STEREO, STEREO + 24)] m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m OUT (obox ws) -> length ws = 2000%nat ->
rw_cells rsegs m STEREO (f32 [q0; q1; q2; q3; q4; q5]) ->
evt rsegs (rspx_decode_stereo_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT STEREO lo m0)
(MS (SREGS (Z_to_bv 64 (OUT + 8 * i + 4)) (Z_to_bv 64 (OUT + 4 * i)) a4) G (Z_to_bv 64 0x1ca50) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i ws q0 q1 q2 q3 q4 q5 a4 G fc m Hk Hi Hi2 FRM MI MU WM ST XB LW XS;
pose proof (rw_cells_bound _ _ _ _ XB) as BA; rewrite obox_size in BA;
pose proof (rw_cells_bound _ _ _ _ XS) as BS; rewrite cells_size_f32 in BS; cbn [length] in BS;
rewrite !f32_cons, f32_nil in XS.
- assert (E0 : i = 0) by lia. clear Hk. subst i.
zstep. zstep.
pose proof (u32arr_read_nth rsegs m OUT ws 0 _ (u32arr_of_obox _ _ _ XB) ltac:(rewrite LW; lia) ltac:(f_equal; lia)) as RD. zstep. clear RD.
zstep. zstep. zstep. zstep. zstep.
out_store 0.
zstep. zstep. out_store 1.
zstep. zstep. zstep. Show. if_false_x. zstep.
lazymatch goal with XB : rw_cells _ ?mc OUT (obox ?ws2), XS : rw_cells _ _ STEREO [C4 ?a; C4 ?b; C4 ?c; C4 ?d; C4 ?e; C4 ?f] |- _ =>
pose proof (u8arr_of_u32arr _ _ _ _ (u32arr_of_obox _ _ _ XB)) as XO8;
change (rw_cells rsegs mc STEREO (f32 [a; b; c; d; e; f])) in XS;
pose proof (rw_cells_f32_CB rsegs _ _ _ XS) as XS24 end.
cbn [length Nat.mul Nat.add] in XS24.
apply evt_done. sf_eexists 20%nat. split; [reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [exact XO8|]. split; [rewrite u32s_length, LW; reflexivity| exact XS24].
- zstep. zstep.
pose proof (u32arr_read_nth rsegs m OUT ws i _ (u32arr_of_obox _ _ _ XB) ltac:(rewrite LW; lia) ltac:(f_equal; lia)) as RD. zstep. clear RD.
zstep. zstep. zstep. zstep. zstep.
out_store (2 * i).
zstep. zstep. out_store (2 * i + 1).
zstep. zstep. zstep.
replace (OUT + 8 * i + -4) with (OUT + -4 + 8 * i) by lia. rewrite (zbv_neq_offset (OUT + -4) (8 * i)) by lia. cbv iota.
replace (OUT + -4 + 8 * i) with (OUT + 8 * (i - 1) + 4) by lia. replace (OUT + 4 * i + -4) with (OUT + 4 * (i - 1)) by lia.
lazymatch goal with XS : rw_cells _ ?mc STEREO [C4 ?a; C4 ?b; C4 ?c; C4 ?d; C4 ?e; C4 ?f] |- _ =>
change (rw_cells rsegs mc STEREO (f32 [a; b; c; d; e; f])) in XS end.
eapply (IH (i - 1)); [lia | lia | exact I | assumption | assumption | assumption | assumption | assumption | exact XB | exact LW | eassumption].
Qed.
End Loop.

Lemma decode_stereo_proof {RCEIL : RunCeiling} : rspx_decode_stereo_stmt.
Proof.
unfold rspx_decode_stereo_stmt. cbv delta [X1gj.rsegs]. intros until m. intros OUT STEREO lo fs outb stb.
intros XO LO XS FS AOS AOL ASL ST CEIL LOW MI FRM -> -> ->.
unfold HOUT_BYTES in LO, AOS, AOL |- *. unfold DECODE_STEREO_STACK in LOW. unfold alloc_ceiling in CEIL. unfold wz, A_speex_decode_stereo.
pose proof (u8arr_bound _ _ _ _ XO) as BO.
pose proof (rw_cells_bound _ _ _ _ XS) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (munch_refl [(lo, bv_unsigned sp); (OUT, OUT + 8000); (STEREO, STEREO + 24)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
zstep. destruct (Z.eq_dec fs 0) as [F0|F1].
- subst fs. if_true_x. zstep.
apply evt_done. sf_eexists 20%nat. split; [reflexivity|].
split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
split; [exact XO|]. split; [exact LO| exact XS].
- if_false_x.
destruct (u32arr_of_u8arr rsegs m OUT outb 2000%nat XO ltac:(lia)) as (ws & Lws & XA). clear XO.
pose proof (f32_box _ _ _ Lws (f32_of_u32arr _ _ _ _ XA)) as XB. clear XA.
destruct (rw_cells_CB_f32 rsegs _ _ 6%nat _ XS) as (sw & Lsw & XS'); clear XS.
destruct sw as [|q0 [|q1 [|q2 [|q3 [|q4 [|q5 [|? ?]]]]]]]; cbn in Lsw; try lia. rewrite !f32_cons, f32_nil in XS'. rename XS' into XS.
do 26 zstep.
replace (OUT + -4 + Z.shiftl fs 3) with (OUT + 8 * (fs - 1) + 4) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
replace (OUT + -4 + Z.shiftl fs 2) with (OUT + 4 * (fs - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
lazymatch goal with XS : rw_cells _ ?mc STEREO [C4 ?a; C4 ?b; C4 ?c; C4 ?d; C4 ?e; C4 ?f] |- _ =>
change (rw_cells rsegs mc STEREO (f32 [a; b; c; d; e; f])) in XS end.
eapply (stereo_loop OUT STEREO lo m) with (k := Z.to_nat (fs - 1));
[ exact AOS | lia | lia | exact I | assumption | exact MI | exact MU | exact WM | exact ST | exact XB | exact Lws | exact XS ].
Qed.
