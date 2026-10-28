(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1mo.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Seg.
Context {RCEIL : RunCeiling}.
Variable k : nat.
Variable X : sbinv.
Hypothesis IH : sb_ihyps k X.
Local Notation S := (x_S X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation lo := (x_lo X). Local Notation a := (x_a X). Local Notation LBL := (x_LBL X).
Local Notation s0 := (x_s X). Local Notation b0 := (x_b0 X). Local Notation canary := (x_canary X). Local Notation st := (x_st X).
Local Notation sp := (x_sp X). Local Notation gp := (x_gp X). Local Notation tp := (x_tp X). Local Notation ra0 := (x_ra X).
Local Notation cs0 := (x_s0 X). Local Notation cs1 := (x_s1 X). Local Notation cs2 := (x_s2 X). Local Notation cs3 := (x_s3 X).
Local Notation cs4 := (x_s4 X). Local Notation cs5 := (x_s5 X). Local Notation cs6 := (x_s6 X). Local Notation cs7 := (x_s7 X).
Local Notation cs8 := (x_s8 X). Local Notation cs9 := (x_s9 X). Local Notation cs10 := (x_s10 X). Local Notation cs11 := (x_s11 X).
Local Notation F0 := (x_F X). Local Notation m0 := (x_m0 X).
Local Notation usp := (bv_unsigned (x_sp X)).

Definition at_END (ret : Z) (s : sbd_state bptr) (low : dec_state bptr) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (j : sb_junk) (ows : list word) (stb : list byte),
ms = MS (mkR ra0 sp gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) cs0 cs1 (Z_to_bv 64 ret) (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (ret_pc ra0) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s low b j ows stb /\ stk rsegs m lo usp /\ -2 <= ret <= 0.

Ltac rel1 FR tgt :=
lazymatch goal with STK : stk _ _ _ _ |- _ =>
eapply stk_release in FR; [ | exact STK | lia ]; clear STK;
lazymatch type of FR with stk _ _ _ ?hi =>
replace hi with tgt in FR by (rewrite ?cells_size_f32; cbn [cells_size csize Nat.add Nat.mul length]; lia) end;
rename FR into STK
end.

#[using="RCEIL k IH"] Lemma sbX : forall ret s low b ms, at_X X ret s low b ms -> evt rsegs (at_END ret s low b) ms.
Proof.
intros ret s low b ms AT.
first [ sf_destruct 27%nat AT as Fx fc m kk xra xsp xa0 xs1 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 j ows stb fr -> FRM CTX ST FRA RET | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xsp & xa0 & xs1 & xs2 & xs4 & xs5 & xs6 & xs7 & xs8 & xs9 & xs10 & xs11 & j & ows & stb & fr & -> & FRM & CTX & ST & FRA & RET) ].
open_ihyps IH. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof CTX as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ MI _ | sf_fb; destruct sfP_ as (_ & _ & MI & _) ].

zstep. zstep.
do 13 zstep.
do 6 zstep.
zstep. zstep.
rel1 FL (usp + -152). rel1 FV (usp + 0). replace (usp + 0) with usp in ST by lia.
apply evt_done. unfold at_END.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _). first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ].
split.
{ replace (Z_to_bv 64 usp) with sp by (symmetry; apply Z_to_bv_bv_unsigned). reflexivity. }
split; [exact FRM|]. split; [exact CTX|]. split; [exact ST| exact RET].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.
End Seg.
