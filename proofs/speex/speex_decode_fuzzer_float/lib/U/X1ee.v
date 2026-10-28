(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1hm X1nq.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require X1cc.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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


Lemma land3_mod4 : forall v, Z.land v 3 = v mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?land3_mod4 in K; rewrite ?signed_lit_small in K by lia; [exfalso; lia | clear K].

Local Ltac transport_chunks segs m a bs ::=
let HB0 := fresh "HBta" in let HB1 := fresh "HBtb" in
first [ sf_store_chunk segs m a ltac:(fun A kn sz =>
assert (HB0 : (0 <= a)%Z) by lia;
assert (HB1 : (a + Z.of_nat (length bs) <= 2^64)%Z) by (simpl_sizes; slia);
transport_chunks_dj segs m a bs A kn sz HB0 HB1; clear HB0 HB1)
| transport_chunks_lean segs m a bs ].

Ltac ltb_fix := repeat match goal with |- context [?x <? ?y] =>
first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia)
| replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ] end.
Ltac ee_pos p := lazymatch p with xH => idtac | xO ?q => ee_pos q | xI ?q => ee_pos q end.
Ltac ee_zlit z := lazymatch z with Z0 => idtac | Zpos ?p => ee_pos p | Zneg ?p => ee_pos p end.
Ltac lit_fold := repeat match goal with |- context [Z_to_bv 64 ?e] =>
tryif ee_zlit e then fail else (tryif (match e with context [?x] => is_var x end) then fail else (let v := eval vm_compute in e in ee_zlit v; change e with v)) end.

Ltac nt := first [ if_false_x | ntk ].

Lemma sra30_i : forall i, 0 <= i < 640 -> bv_signed (Z_to_bv 64 (i * 8589934592)) ≫ 30 = 8 * i.
Proof.
intros i Hi. rewrite signed_lit_small by lia. rewrite Z.shiftr_div_pow2 by lia.
replace (i * 8589934592) with (8 * i * 2 ^ 30) by lia. rewrite Z.div_mul by (apply Z.pow_nonzero; lia). reflexivity.
Qed.
Lemma land_bit30 : forall i, 0 <= i < 2^30 -> Z.land i 1073741824 = 0.
Proof.
intros i Hi. assert (E : i = Z.land i (Z.ones 30)) by (rewrite Z.land_ones by lia; rewrite Z.mod_small; lia).
rewrite E, <- Z.land_assoc. change (Z.land (Z.ones 30) 1073741824) with 0. apply Z.land_0_r.
Qed.
Lemma shl2 : forall x, x ≪ 2 = 4 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. lia. Qed.
Lemma a6_entry : forall fs, 1 <= fs <= 640 -> bv_swrap 32 (Z.land (fs ≪ 1) 18446744073709551615 + -1) = 2 * (fs - 1) + 1.
Proof.
intros fs Hf. rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
rewrite Z.mod_small by lia. rewrite X1cc.swrap32_small by lia. lia.
Qed.
Lemma zbv_eqm : forall x y, x mod 2^64 = y mod 2^64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
intros x y E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). exact E.
Qed.
Ltac zeq := first [ lazymatch goal with |- ?x = ?x => reflexivity end
| f_equal; rewrite ?shl2, ?Z.shiftl_mul_pow2, ?X1cc.swrap32_small by lia; lia
| apply zbv_eqm; match goal with |- _ = ?y mod _ => rewrite <- (Z.mod_add y 1 (2^64)) by lia end; f_equal; lia ].



Section Loop.
Context {RCEIL : RunCeiling}.
Variables (OUT STEREO lo : Z) (m0 : mem).
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Hypothesis AOS : OUT + 8000 <= STEREO \/ STEREO + 24 <= OUT.
Hypothesis AOL : OUT + 8000 <= lo \/ bv_unsigned sp <= OUT.
Hypothesis ASL : STEREO + 24 <= lo \/ bv_unsigned sp <= STEREO.
Hypothesis LOW : lo <= bv_unsigned sp - 1024.
Hypothesis LO0 : 0 <= lo.
Hypothesis ON : 0 < OUT.
Hypothesis OM : OUT mod 4 = 0.
Hypothesis SN : 0 < STEREO.
Hypothesis SM : STEREO mod 4 = 0.

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

Lemma stereo_loop : forall (k : nat) (i : Z) (ws : list word) (q0 q1 q2 q3 q4 q5 : word) (fj : list byte)
(t0v t1v t2v s0v a1v a3v a4v a6v a7v t3v t4v t5v t6v : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
Z.of_nat k = i -> 0 <= i < 640 ->
t0v = Z_to_bv 64 1 -> t1v = Z_to_bv 64 i -> t2v = Z_to_bv 64 18446744065119617024 -> a1v = Z_to_bv 64 (i + 1073741824) ->
a3v = Z_to_bv 64 1 -> a4v = Z_to_bv 64 (i * 8589934592) -> a6v = Z_to_bv 64 (2 * i + 1) ->
a7v = Z_to_bv 64 (OUT + 4 * i) -> t3v = Z_to_bv 64 (OUT + 4 * i) ->
frm0 fc -> mem_inv rsegs m -> munch [(lo, bv_unsigned sp); (OUT, OUT + 8000); (STEREO, STEREO + 24)] m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (bv_unsigned sp + -16) -> rw_cells rsegs m (bv_unsigned sp + -16) [CB 8 fj; C8 s0] ->
rw_cells rsegs m OUT (obox ws) -> length ws = 2000%nat ->
rw_cells rsegs m STEREO [C4 q0; C4 q1; C4 q2; C4 q3; C4 q4; C4 q5] ->
evt rsegs (rspx_decode_stereo_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT STEREO lo m0)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0v t1v t2v s0v s1 (Z_to_bv 64 OUT) a1v (Z_to_bv 64 STEREO) a3v a4v
(Z_to_bv 64 1073741824) a6v a7v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4v t5v t6v) G (Z_to_bv 64 0x1d1c4) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i ws q0 q1 q2 q3 q4 q5 fj t0v t1v t2v s0v a1v a3v a4v a6v a7v t3v t4v t5v t6v G fc m
Hk Hi -> -> -> -> -> -> -> -> -> FRM MI MU WM ST FR XB LW XS;
pose proof (rw_cells_bound _ _ _ _ XB) as BA; rewrite obox_size in BA;
pose proof (rw_cells_bound _ _ _ _ XS) as BS; cbn [cells_size csize Nat.add] in BS;
pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp; change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rsp;
zstep; nt;
zstep; zstep; zstep; ltb_fix; lit_fold; zstep; nt;
zstep; nt;
zstep; zstep;
(pose proof (u32arr_read_nth rsegs m OUT ws i _ (u32arr_of_obox _ _ _ XB) ltac:(rewrite LW; lia) ltac:(f_equal; lia)) as RD); zstep; clear RD;
zstep; zstep; zstep; zstep;
zstep; nt;
zstep; rewrite (sra30_i i) by lia; zstep;
zstep; nt;
zstep; zstep; rewrite (land_bit30 i) by lia; zstep; zstep; zstep; ltb_fix; lit_fold;
zstep; nt;
zstep; zstep; rewrite shl2; zstep;
out_store (2 * i);
zstep; nt;
zstep; zstep; zstep; zstep; ltb_fix; lit_fold; zstep; nt;
zstep; zstep; out_store (2 * i + 1);
zstep; zstep; zstep; zstep; zstep; zstep; zstep.
- assert (E0 : i = 0) by lia. subst i. if_false_x. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
lazymatch goal with XB : rw_cells _ ?mc OUT (obox ?ws2), XS : rw_cells _ _ STEREO [C4 ?a; C4 ?b; C4 ?c; C4 ?d; C4 ?e; C4 ?f] |- _ =>
pose proof (u8arr_of_u32arr _ _ _ _ (u32arr_of_obox _ _ _ XB)) as XO8;
change (rw_cells rsegs mc STEREO (f32 [a; b; c; d; e; f])) in XS;
pose proof (rw_cells_f32_CB rsegs _ _ _ XS) as XS24 end.
cbn [length Nat.mul Nat.add] in XS24.
apply evt_done. sf_eexists 20%nat. split; [reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [exact XO8|]. split; [rewrite u32s_length, LW; reflexivity| exact XS24].
- if_true_x.
eapply (IH (i - 1)); try lia; try zeq; eassumption.
Qed.
End Loop.

Lemma decode_stereo_proof {RCEIL : RunCeiling} : rspx_decode_stereo_stmt.
Proof.
unfold rspx_decode_stereo_stmt. cbv delta [X1gj.rsegs]. intros until m. intros OUT STEREO lo fs outb stb.
intros XO LO XS FS AOS AOL ASL ST CEIL LOW MI FRM -> -> -> ON OM SN SM.
unfold HOUT_BYTES in LO, AOS, AOL |- *. unfold DECODE_STEREO_STACK in LOW. unfold alloc_ceiling in CEIL. unfold wz, A_speex_decode_stereo.
pose proof (u8arr_bound _ _ _ _ XO) as BO.
pose proof (rw_cells_bound _ _ _ _ XS) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rsp.
pose proof (munch_refl [(lo, bv_unsigned sp); (OUT, OUT + 8000); (STEREO, STEREO + 24)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
destruct (u32arr_of_u8arr rsegs m OUT outb 2000%nat XO ltac:(lia)) as (ws & Lws & XA). clear XO.
pose proof (f32_box _ _ _ Lws (f32_of_u32arr _ _ _ _ XA)) as XB. clear XA.
destruct (rw_cells_CB_f32 rsegs _ _ 6%nat _ XS) as (sw & Lsw & XS'); clear XS.
destruct sw as [|q0 [|q1 [|q2 [|q3 [|q4 [|q5 [|? ?]]]]]]]; cbn in Lsw; try lia. rewrite !f32_cons, f32_nil in XS'. rename XS' into XS.
carve_frame 16%nat ST.
zstep. zstep. zstep. ntk.
zstep. zstep. ntk.
zstep. rewrite (X1cc.swrap32_small (fs + -1)) by lia. zstep. ntk.
zstep. destruct (Z.eq_dec fs 0) as [F0|F1].
- subst fs. if_true_x. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
pose proof (u8arr_of_u32arr _ _ _ _ (u32arr_of_obox _ _ _ XB)) as XO8.
change (rw_cells rsegs m0 STEREO (f32 [q0; q1; q2; q3; q4; q5])) in XS.
pose proof (rw_cells_f32_CB rsegs _ _ _ XS) as XS24. cbn [length Nat.mul Nat.add] in XS24.
apply evt_done. sf_eexists 20%nat. split; [reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [exact XO8|]. split; [rewrite u32s_length, Lws; reflexivity| exact XS24].
- if_false_x. do 36 zstep.
rewrite land3_mod4, OM. ltb_fix. lit_fold. rewrite (a6_entry fs) by lia.
assert (LO0 : 0 <= lo) by lia.
eapply (stereo_loop OUT STEREO lo m) with (k := Z.to_nat (fs - 1)) (i := fs - 1).
all: first [ eassumption | zeq | lia ].
Qed.
