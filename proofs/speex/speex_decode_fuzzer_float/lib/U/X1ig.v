(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1c6.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Seg.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Variable notify : list Z -> X1qx.M PState unit.
Variable STR_TOP : Z.
Variable X : nbinv ptr.
Hypothesis NH : nb_hyps notify STR_TOP X.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation ISV := (x_isv X). Local Notation lo := (x_lo X).
Local Notation st0 := (x_st0 X). Local Notation b0 := (x_b0 X).
Local Notation sp := (x_sp X). Local Notation gp := (x_gp X). Local Notation tp := (x_tp X). Local Notation ra0 := (x_ra X).
Local Notation cs0 := (x_s0 X). Local Notation cs1 := (x_s1 X). Local Notation cs2 := (x_s2 X). Local Notation cs3 := (x_s3 X).
Local Notation cs4 := (x_s4 X). Local Notation cs5 := (x_s5 X). Local Notation cs6 := (x_s6 X). Local Notation cs7 := (x_s7 X).
Local Notation cs8 := (x_s8 X). Local Notation cs9 := (x_s9 X). Local Notation cs10 := (x_s10 X). Local Notation cs11 := (x_s11 X).
Local Notation F0 := (x_F X). Local Notation m0 := (x_m0 X). Local Notation canary := (x_canary X).
Local Notation usp := (bv_unsigned (x_sp X)).
Local Notation NBREP := (nbstate_rep rsegs NB_MODE_PTR NB_SUBMODES_PTR A_speex_default_user_handler A_speex_std_stereo_request_handler).
Local Notation POST s := (nb_decode_post (x_serr X) (x_sspc X) ST OUT A D STEREO ISV lo canary ra0 sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 F0 m0 s).

Ltac rel1 FR tgt :=
lazymatch goal with STK : stk _ _ _ _ |- _ =>
eapply stk_release in FR; [ | exact STK | lia ]; clear STK;
lazymatch type of FR with stk _ _ _ ?hi =>
replace hi with tgt in FR by (rewrite ?cells_size_f32; cbn [cells_size csize Nat.add Nat.mul length]; lia) end;
rename FR into STK
end.

#[using="notify STR_TOP NH"] Lemma nbX : forall rr st b s ms, at_X X rr st b ms -> evt rsegs (POST s (rr, st, b) s) ms.
Proof.
intros rr st b s ms AT.
first [ sf_destruct 28%nat AT as Fx fc m k xra xa0 xs0 xs1 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 j ows iws sws fr -> FRM CTX FOK FRA JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs0 & xs1 & xs2 & xs3 & xs4 & xs6 & xs7 & xs8 & xs9 & xs10 & xs11 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & JEXC) ].
open_hyps NH.
first [ sf_destruct 20%nat CTX as MU WM MI STK PCS JOK CBS INV REP BOK BSZ XO Lows XI Liws XS Lsws TAB SERR SSPC | sf_fb; destruct CTX as (MU & WM & MI & STK & PCS & JOK & CBS & INV & REP & BOK & BSZ & XO & Lows & XI & Liws & XS & Lsws & TAB & SERR & SSPC) ].
pose proof PCS as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ PEXC _ | sf_fb; destruct sfP_ as (_ & _ & PEXC & _) ]. rewrite JEXC in PEXC.
open_frame FRA. open_fok FOK.
do 14 zstep.
do 12 zstep.
zstep. zstep.

rel1 FA (usp + -864). rel1 FL (usp + -776). rel1 FQ (usp + -736). rel1 FK (usp + -576). rel1 FE (usp + -416).
rel1 FI (usp + -256). rel1 FS (usp + -216). rel1 FP (usp + -200). rel1 FV (bv_unsigned (x_sp X)).
apply evt_done. unfold nb_decode_post. cbv beta iota zeta.
exists k. eexists. first [ unshelve sf_eexists 5%nat; [ exact (fc) | exact (m) | exact (ows) | exact (iws) | exact (sws) | ] | sf_fb; exists fc, m, ows, iws, sws ].
split; [reflexivity|].
repeat match goal with |- _ /\ _ => split end; try assumption.
-
unfold fs_kept, fs_regs. intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [ rewrite !reg_get_set; reflexivity | ]). contradiction.
-
unfold nbstate_rep. split; [exact (h_stal _ _ _ NH)|]. split; [lia|]. split; [exact INV|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply (proj2 (nb_pieces_iff rsegs _ _ _ _ _ _ _ _ _ JOK)). exact PCS.
- reflexivity.
Qed.
End Seg.
