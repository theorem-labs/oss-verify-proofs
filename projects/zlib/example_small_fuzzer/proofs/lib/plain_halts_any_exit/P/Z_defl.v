(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_defl_model.

Module Z_defl_kit.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_memset.InitMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz DeflateBlk FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* 1.4 (zl14-cmp): deflate's frame is 64 bytes (ra, s0..s6); s7 / s8 are never saved or written, flush lives in
   s6 (1.3.1: s4), and the temporaries are s2..s5. *)
Definition Z_DEFL_EPI : Z := 0x179a8.

Definition defl_frame (r : sregs) : list cell :=
  [C8 (r_s6 r); C8 (r_s5 r); C8 (r_s4 r); C8 (r_s3 r); C8 (r_s2 r); C8 (r_s1 r); C8 (r_s0 r); C8 (r_ra r)].

Definition defl_W (L : dlay) (rest0 : list byte) (lo : Z) (r : sregs) : list ivl :=
  [(lo, bv_unsigned (r_sp r)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Aw L, dl_Aw L + DS_WIN);
   (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_Ab L, dl_Ab L + DS_PEND);
   (dl_NO L, dl_NO L + Z.of_nat (length rest0))].

Record defl_ctx (L : dlay) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (me : mem) : Prop := mkDctx {
  dc_lo : lo <= bv_unsigned (r_sp r) - Z_DEFLATE_IN_STACK;
  dc_sp16 : bv_unsigned (r_sp r) mod 16 = 0;
  dc_lay : dlay_ok L;
  dc_bel : dlay_below L lo (bv_unsigned (r_sp r));
  dc_io : dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo;
  dc_relro : relro_clean me;
  dc_din : din me L inp }.

Definition DINV (L : dlay) (rest0 : list byte) (lo : Z) (r : sregs) (me : mem) (X : deflate_state) (m : mem) : Prop :=
  DREP m L X /\ dout m L rest0 (ds_strm X) /\ Box (length (cs_out_rev (ds_strm X)) <= length rest0)%nat
  /\ rw_cells psegs m (bv_unsigned (r_sp r) + -64) (defl_frame r)
  /\ stk psegs m lo (bv_unsigned (r_sp r) + -64)
  /\ munch (defl_W L rest0 lo r) me m /\ wmono psegs me m /\ mem_inv psegs m.

Definition deflR (L : dlay) (flush : Z) (r : sregs) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x28 x29 x30 x31 : word) : bvmap 5 word :=
  mkR x1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) x5 x6 x7 (wz (dl_As L)) (wz (dl_S L)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
      x21 x22 (wz flush) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) x28 x29 x30 x31.

Definition DKE (L : dlay) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (w : word) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 : word) (m' : mem),
    DINV L rest0 lo r me X m' ->
    evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 y10 y11 w y13 y14 y15 y16 y17 y18 y19 y20 y21 y22
                         (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz Z_DEFL_EPI) fc None m' (seg_rom psegs)).

Definition DK (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (pc : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31 : word) (m' : mem),
    DINV L rest0 lo r me X m' ->
    evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz (dl_S L)) (wz flush) y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                    F (wz pc) fc None m' (seg_rom psegs)).

Definition DKB (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31 : word) (m' : mem),
    DINV L rest0 lo r me X m' ->
    evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz (dl_S L)) (wz flush) (wz (ds_pending X)) (wz (ds_status X)) y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                    F (wz 0x16da4) fc None m' (seg_rom psegs)).

Definition DKH (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31 : word) (m' : mem),
    DINV L rest0 lo r me X m' ->
    evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz (dl_S L)) (wz flush) (wz (ds_pending X)) y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                    F (wz 0x16dc8) fc None m' (seg_rom psegs)).

Definition DKL (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31 : word) (m' : mem),
    DINV L rest0 lo r me X m' ->
    evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                    F (wz 0x1799c) fc None m' (seg_rom psegs)).

Definition defl_post_gen (r : sregs) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (dF : deflate_state) (w : word) (inp : list Z) (rest0 : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) w a1 a2 a3 a4 a5 a6 a7
                  (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
             F (ret_pc (r_ra r)) fc None m' (seg_rom psegs)
    /\ munch (defl_W L rest0 lo r) m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned (r_sp r))
    /\ DREP m' L dF /\ din m' L inp /\ dout m' L rest0 (ds_strm dF).

Ltac closed_br := let K := fresh "K" in if_cases K; try (exfalso; revert K; vm_compute; intros K; discriminate K); clear K.

(* the flush_pending length joins in x18 (s2), not x19 *)
Ltac join_x18 v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode ?Lt None (TNode ?A ?o2 (TNode (TNode (TNode TEmpty (Some _) TEmpty) ?o10 ?B) ?o6 ?C))) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut psegs (fun ms' => ms' = MS (TNode Lt None (TNode A o2 (TNode (TNode (TNode TEmpty (Some v) TEmpty) o10 B) o6 C))) F (wz pcj) fc None m rom))
  end.
Ltac join_x19 v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode (TNode (TNode ?A ?x3 (TNode (TNode TEmpty (Some _) TEmpty) ?x11 ?B)) ?x1 ?C) None ?D) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut psegs (fun ms' => ms' = MS (TNode (TNode (TNode A x3 (TNode (TNode TEmpty (Some v) TEmpty) x11 B)) x1 C) None D) F (wz pcj) fc None m rom))
  end.

Section DKIT.
Variables (L : dlay) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.

Lemma defl_din : forall m, munch (defl_W L rest0 lo r) me m -> din m L inp.
Proof.
  intros m MU. destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. unfold din in *.
  eapply bytes_at_transport; [exact DIN| exact MU|]. unfold defl_W. cbn [disjoint_from]. rewrite zb8_length.
  below_open BEL. pose proof IO as I0. io_open I0. unfold zlength in *.
  pose proof (io_is _ _ _ _ IO) as J1. pose proof (io_iw _ _ _ _ IO) as J2. pose proof (io_ip _ _ _ _ IO) as J3.
  pose proof (io_ih _ _ _ _ IO) as J4. pose proof (io_ib _ _ _ _ IO) as J5. pose proof (io_io _ _ _ _ IO) as J6.
  unfold apart, zlength in *. repeat split; lia.
Qed.

Lemma defl_relro : forall m, munch (defl_W L rest0 lo r) me m -> relro_clean m.
Proof.
  intros m MU. destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp.
  eapply relro_clean_munch; [exact RELRO| exact MU|]. unfold defl_W, RELRO_LO, RELRO_HI. cbn [disjoint_from].
  below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_s L LAY) as (_ & _ & _ & Is). pose proof (lo_w L LAY) as (_ & _ & _ & Iw). pose proof (lo_p L LAY) as (_ & _ & _ & Ip).
  pose proof (lo_h L LAY) as (_ & _ & _ & Ih). pose proof (lo_b L LAY) as (_ & _ & _ & Ib). pose proof (io_img _ _ _ _ IO) as Io.
  repeat split; lia.
Qed.

Lemma defl_epi : forall (dF : deflate_state) (w12 : word)
    (y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 : word) (m' : mem),
  DINV L rest0 lo r me dF m' ->
  evt psegs (defl_post_gen r F fc L dF w12 inp rest0 lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 y10 y11 w12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31)
        F (wz Z_DEFL_EPI) fc None m' (seg_rom psegs)).
Proof.
  intros until m'. intros (DR & DOUT & _ & FR & STK & MU & WM & MI). unfold defl_frame in FR. unfold Z_DEFL_EPI.
  pose proof (defl_din m' MU) as DIN.
  pose proof (dc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp.
  do 9 zs. release_frame FR STK (bv_unsigned (r_sp r)).
  zs. zs.
  apply evt_done. unfold defl_post_gen. do 14 eexists. exists m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
  split; [exact DR|]. split; [exact DIN| exact DOUT].
Qed.
End DKIT.

Definition Z_GOT_ERRMSG : Z := 0x290d0.
Definition Z_ERRMSG : Z := 0x28fb8.

Lemma errmsg_cells : forall m, relro_clean m ->
  rw_cells psegs m Z_GOT_ERRMSG [C8 (wz Z_ERRMSG)]
  /\ rw_cells psegs m Z_ERRMSG (map (fun p => C8 (wz p)) Z_ERRMSG_PTRS).
Proof.
  intros m RC. unfold relro_clean, RELRO_LO, RELRO_HI in RC. unfold Z_GOT_ERRMSG, Z_ERRMSG, Z_ERRMSG_PTRS. cbn [map].
  split.
  - pose (cs := [C8 (wz 0x28fb8)]).
    apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_memset.InitMem.rw_cells_recast psegs m 0x290d0 [CB 8 (cells_bytes cs)] cs).
    + apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_memset.InitMem.rw_cells_image0 psegs m 0x290d0 (cells_bytes cs)).
      * intros a Ha. apply RC. change (Z.of_nat (length (cells_bytes cs))) with 8 in Ha. lia.
      * vm_compute. reflexivity.
      * lia.
      * change (Z.of_nat (length (cells_bytes cs))) with 8. lia.
    + cbn. repeat split; exact I.
    + vm_compute. reflexivity.
    + reflexivity.
  - pose (cs := [C8 (wz 66570); C8 (wz 67068); C8 (wz 66444); C8 (wz 66694); C8 (wz 66549); C8 (wz 66317); C8 (wz 66761); C8 (wz 66748); C8 (wz 66947); C8 (wz 66444)]).
    apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_memset.InitMem.rw_cells_recast psegs m 0x28fb8 [CB 80 (cells_bytes cs)] cs).
    + apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_memset.InitMem.rw_cells_image0 psegs m 0x28fb8 (cells_bytes cs)).
      * intros a Ha. apply RC. change (Z.of_nat (length (cells_bytes cs))) with 80 in Ha. lia.
      * vm_compute. reflexivity.
      * lia.
      * change (Z.of_nat (length (cells_bytes cs))) with 80. lia.
    + cbn. repeat split; exact I.
    + vm_compute. reflexivity.
    + reflexivity.
Qed.

Definition Z_CFG6_FUNC : Z := 0x28f80.

Lemma cfg6_cell : forall m, relro_clean m -> rw_cells psegs m Z_CFG6_FUNC [C8 (wz Z_DEFLATE_SLOW)].
Proof.
  intros m RC. unfold relro_clean, RELRO_LO, RELRO_HI in RC. unfold Z_CFG6_FUNC, Z_DEFLATE_SLOW.
  pose (cs := [C8 (wz 0x194dc)]).
  apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_memset.InitMem.rw_cells_recast psegs m 0x28f80 [CB 8 (cells_bytes cs)] cs).
  + apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_memset.InitMem.rw_cells_image0 psegs m 0x28f80 (cells_bytes cs)).
    * intros a Ha. apply RC. change (Z.of_nat (length (cells_bytes cs))) with 8 in Ha. lia.
    * vm_compute. reflexivity.
    * lia.
    * change (Z.of_nat (length (cells_bytes cs))) with 8. lia.
  + cbn. repeat split; exact I.
  + vm_compute. reflexivity.
  + reflexivity.
Qed.
End Z_defl_kit.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_defl_path.

Module Z_defl_entry.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate FillWinModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section ENTRY.
Variables (L : dlay) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.

Lemma defl_entry : forall (Q : machine_state -> Prop) (d : deflate_state) (flush : Z)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  DREP me L d -> dout me L rest0 (ds_strm d) -> Box (length (cs_out_rev (ds_strm d)) <= length rest0)%nat ->
  stk psegs me lo (bv_unsigned (r_sp r)) -> mem_inv psegs me ->
  (ds_status d = 42 \/ ds_status d = 113 \/ ds_status d = 666) -> (flush = 0 \/ flush = 4) ->
  0 <= cs_avail_in (ds_strm d) <= 1 -> 0 <= cs_next_in (ds_strm d) <= zlength inp ->
  (ds_status d = 666 /\ flush <> 4 ->
   forall (y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 : word) (m' : mem),
     DINV L rest0 lo r me (fst (err_return d Z_STREAM_ERROR)) m' ->
     evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 y10 y11 (wz (-2)) y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 (r_s7 r) (r_s8 r)
                          (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz Z_DEFL_EPI) fc None m' (seg_rom psegs))) ->
  (~ (ds_status d = 666 /\ flush <> 4) ->
   forall (y1 y5 y6 y7 y9 y12 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
     DINV L rest0 lo r me d m' ->
     evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 (wz (dl_S L)) (wz flush) y12 (wz (ds_status d)) (wz (cs_avail_in (ds_strm d))) y15 y16 y17
                          (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x16ccc) fc None m' (seg_rom psegs))) ->
  evt psegs Q (MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) (wz (dl_S L)) (wz flush) a2 a3 a4 a5 a6 a7
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
                  F (wz Z_DEFLATE_PC) fc None me (seg_rom psegs)).
Proof.
  intros until t6. intros DR DOUT ROOM STK MI HST HFL RAI RNI KERR KOK.
  pose proof DR as DR0.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold Z_DEFLATE_PC. unfold Z_ZCALLOC, Z_ZCFREE in ZS.
  pose proof (munch_refl (defl_W L rest0 lo r) me) as MU. unfold defl_W in MU. pose proof (wmono_refl psegs me) as WM.
  pose proof (munch_refl [(lo, bv_unsigned (r_sp r))] me) as MUf. pose proof (wmono_refl psegs me) as WMf.
  zs. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [exfalso; lia|].
  zs. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [exfalso; lia|].
  zs. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [exfalso; lia|].
  carve_frame 64%nat STK.
  do 9 zs. name_mem mP.
  zs. zstep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia; [exfalso; lia|].
  zs. zstep. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia; [exfalso; lia|].
  assert (RST : 0 <= ds_status d < 1000) by lia.
  assert (RLP : relro_clean mP) by (apply (defl_relro L inp rest0 lo r me CTX); unfold defl_W; exact MU).
  destruct (errmsg_cells _ RLP) as [GOTE TABE]. unfold Z_GOT_ERRMSG in GOTE. unfold Z_ERRMSG, Z_ERRMSG_PTRS in TABE, GOTE. cbn [map] in TABE.
  assert (DRP : DREP mP L d).
  { apply (DREP_agree me mP L d DR0).
    - eapply ag_blocks_munch; [exact LAY1| exact MUf| exact WMf| | | | |]; cbn [disjoint_from]; slia.
    - apply (agree_on_of_munch [(lo, bv_unsigned (r_sp r))]); [exact MUf| exact WMf| lia| lia| cbn [disjoint_from]; slia]. }
  assert (DOUTP : dout mP L rest0 (ds_strm d)) by (apply (dout_munch _ me mP L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia).
  assert (C_AE4 : forall a14 a15 : word,
    evt psegs Q (MS (mkR (r_ra r) (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) t0 t1 t2 (wz (dl_As L)) (r_s1 r) (wz (dl_S L)) (wz flush) (wz (-2)) (wz (ds_status d)) a14 a15 a6 a7
                     (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6) F (wz 0x16c74) fc None mP (seg_rom psegs))).
  { intros a14 a15. pose proof (unbox _ ROOM) as RM0.
    zs. zstep. if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia; [exfalso; lia|].
    zs. zstep. if_cases KNO; zify_cond KNO; rewrite ?unsigned_lit in KNO by lia; [exfalso; lia|].
    zs. zstep.
    assert (C_B04 : forall a15' : word,
      evt psegs Q (MS (mkR (r_ra r) (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) t0 t1 t2 (wz (dl_As L)) (r_s1 r) (wz (dl_S L)) (wz flush) (wz (-2)) (wz (ds_status d)) (wz (cs_avail_in (ds_strm d))) a15' a6 a7
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6) F (wz 0x16c94) fc None mP (seg_rom psegs))).
    { intros a15'. zs. zstep.
      assert (SIP : DINV L rest0 lo r me d mP).
      { split; [exact DRP|]. split; [exact DOUTP|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
      if_cases KF4; zify_cond KF4; rewrite ?unsigned_lit in KF4 by lia.
      - eapply (KOK ltac:(lia)). exact SIP.
      - zs. zstep. if_cases KS6; zify_cond KS6; rewrite ?unsigned_lit in KS6 by lia.
        + eapply (KOK ltac:(lia)). exact SIP.
        +
          clear MUf WMf ZS GA. destruct DRP as [ZSP STP]. open_zs ZSP.
          pose proof (munch_refl [(dl_S L, dl_S L + 112)] mP) as MUg. pose proof (wmono_refl psegs mP) as WMg.
          zs. zs. zs. zs. name_mem mE. zs.
          eapply (KERR ltac:(lia)).
          split; [split|].
          { unfold err_return, Z_STREAM_ERROR, MSG_ERR. cbn [fst]. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont orb Z.sub Z.opp Z.add Z.pos_sub Pos.pred_double].
            do 4 eexists. unfold zs_call_cells, zs_priv_cells. cbn [app]. dsred. close_cells ZSP. }
          { apply DST_set_strm; [intros HB; exact HB|].
            apply (DST_agree mP mE L d STP). eapply ag_blocks_munch; [exact LAY1| exact MUg| exact WMg| | | | |]; cbn [disjoint_from]; slia. }
          { split; [unfold err_return; cbn [fst]; dsred; apply (dout_munch _ mP mE L rest0 _ DOUTP ROOM MUg WMg); cbn [disjoint_from]; slia|].
            split; [unfold err_return; cbn [fst]; dsred; exact ROOM|].
            split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. } }
    if_cases KAI; zify_cond KAI; rewrite ?unsigned_lit in KAI by lia.
    - apply C_B04.
    - zs. zstep. if_cases KNI; zify_cond KNI; rewrite ?unsigned_lit in KNI by lia; [exfalso; lia|]. apply C_B04. }
  clear KERR KOK.
  zs. zs. zs. zstep.
  destruct HST as [E|[E|E]]; rewrite E in *.
  -
    if_cases KS; zify_cond KS; [|exfalso; revert KS; vm_compute; intros KS; apply KS; reflexivity].
    zs. zstep. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia; [exfalso; lia|].
    zs. zstep. if_cases K7; zify_cond K7; rewrite ?unsigned_lit in K7 by lia; [|exfalso; lia].
    apply C_AE4.
  -
    if_cases KS; zify_cond KS; [exfalso; revert KS; vm_compute; intros KS; discriminate KS|].
    zs. zs. zs. zs. zstep.
    if_cases KM; zify_cond KM; [exfalso; revert KM; vm_compute; intros KM; discriminate KM|].
    apply C_AE4.
  -
    if_cases KS; zify_cond KS; [|exfalso; revert KS; vm_compute; intros KS; apply KS; reflexivity].
    zs. zstep. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia; [|exfalso; lia].
    apply C_AE4.
Qed.
End ENTRY.
End Z_defl_entry.


Module Z_defl_arms.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_memcpy.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflFast1 RefDeflFastM DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section ARMS.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.

Lemma defl_lf : forall (Q : machine_state -> Prop) (X : deflate_state),
  DKE L rest0 lo r F fc me Q (wz 0) (set_last_flush X (-1)) -> DKL L flush rest0 lo r F fc me Q X.
Proof.
  intros Q X HK. unfold DKL. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] m') as MUf. pose proof (wmono_refl psegs m') as WMf.
  zs. zs. zs. name_mem mA.
  tr_groups MUf WMf.
  eapply HK.
  split; [split|].
  - exact ZS.
  - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
  - split; [apply (dout_munch _ m' mA L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
    split; [exact ROOM|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma defl_buferr : forall (Q : machine_state -> Prop) (X : deflate_state) (pc : Z)
    (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 : word) (m : mem),
  pc = 0x16d84 \/ pc = 0x170f4 \/ pc = 0x16dbc ->
  DINV L rest0 lo r me X m ->
  DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return X Z_BUF_ERROR)) ->
  evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 (wz (dl_S L)) y11 y12 y13 y14 y15 y16 y17
                       y18 y19 y20 y21 y22 (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz pc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPC (DR & DOUT & ROOM & FR & STK & MU & WM & MI) HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  assert (RLP : relro_clean m) by (apply (defl_relro L inp rest0 lo r me CTX); exact MU).
  destruct (errmsg_cells _ RLP) as [GOTE TABE]. unfold Z_GOT_ERRMSG in GOTE. unfold Z_ERRMSG, Z_ERRMSG_PTRS in TABE, GOTE. cbn [map] in TABE.
  destruct DR as [ZS ST]. open_zs ZS. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold defl_frame in FR. unfold defl_W in MU.
  pose proof (munch_refl [(dl_S L, dl_S L + 112)] m) as MUg. pose proof (wmono_refl psegs m) as WMg.
  assert (FIN : forall mE, munch [(dl_S L, dl_S L + 112)] m mE -> wmono psegs m mE -> mem_inv psegs mE ->
            munch (defl_W L rest0 lo r) me mE -> wmono psegs me mE ->
            rw_cells psegs mE (bv_unsigned (r_sp r) + -64) (defl_frame r) -> stk psegs mE lo (bv_unsigned (r_sp r) + -64) ->
            dzs mE L (cset_msg (ds_strm X) (MSG_ERR Z_BUF_ERROR)) ->
            DINV L rest0 lo r me (fst (err_return X Z_BUF_ERROR)) mE).
  { intros mE MUg' WMg' MI' MU' WM' FR' STK' ZS'.
    split; [split|].
    - unfold err_return. cbn [fst]. dsred. exact ZS'.
    - apply DST_set_strm; [intros HB; exact HB|].
      apply (DST_agree m mE L X ST). eapply ag_blocks_munch; [exact (st_lay _ _ _ _ ST)| exact MUg'| exact WMg'| | | | |]; cbn [disjoint_from]; slia.
    - split; [unfold err_return; cbn [fst]; dsred; apply (dout_munch _ m mE L rest0 _ DOUT ROOM MUg' WMg'); cbn [disjoint_from]; slia|].
      split; [unfold err_return; cbn [fst]; dsred; exact ROOM|].
      split; [exact FR'|]. split; [exact STK'|]. split; [exact MU'|]. split; [exact WM'| exact MI']. }
  destruct HPC as [->|[->| ->]].
  - zs. zs. zs. zs. name_mem mE. zs. zs.
    eapply HK. apply FIN; [exact MUg| exact WMg| eassumption| exact MU| exact WM| exact FR| exact STK|].
    unfold Z_BUF_ERROR, MSG_ERR. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont orb Z.sub Z.opp Z.add Z.pos_sub Pos.pred_double].
    do 4 eexists. unfold zs_call_cells, zs_priv_cells. cbn [app]. dsred. close_cells ZS.
  - zs. zs. zs. zs. zs. name_mem mE. zs. zs.
    eapply HK. apply FIN; [exact MUg| exact WMg| eassumption| exact MU| exact WM| exact FR| exact STK|].
    unfold Z_BUF_ERROR, MSG_ERR. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont orb Z.sub Z.opp Z.add Z.pos_sub Pos.pred_double].
    do 4 eexists. unfold zs_call_cells, zs_priv_cells. cbn [app]. dsred. close_cells ZS.
  - zs. zs. zs. zs. zs. name_mem mE. zs. zs.
    eapply HK. apply FIN; [exact MUg| exact WMg| eassumption| exact MU| exact WM| exact FR| exact STK|].
    unfold Z_BUF_ERROR, MSG_ERR. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont orb Z.sub Z.opp Z.add Z.pos_sub Pos.pred_double].
    do 4 eexists. unfold zs_call_cells, zs_priv_cells. cbn [app]. dsred. close_cells ZS.
Qed.

End ARMS.
End Z_defl_arms.


Module Z_defl_pend.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_memcpy.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_arms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflFast1 RefDeflFastM DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section PEND.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HTFB : tr_flush_bits_stmt.

Lemma defl_pend : forall (Q : machine_state -> Prop) (d : deflate_state)
    (y1 y5 y6 y7 y9 y12 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  DINV L rest0 lo r me d m ->
  (flush = 0 \/ flush = 4) ->
  0 <= cs_avail_out (ds_strm d) < 2^31 -> 0 <= cs_avail_in (ds_strm d) <= 1 -> - 2 <= ds_last_flush d <= 5 ->
  0 <= ds_pending d <= 65536 -> ds_lit_bufsize d = 16384 ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> fp_ok (set_last_flush d flush)) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> 0 <= ds_status (flush_pending (set_last_flush d flush)) < 1000) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> Box (length (cs_out_rev (ds_strm (flush_pending (set_last_flush d flush)))) <= length rest0)%nat) ->
  (cs_avail_out (ds_strm d) = 0 -> DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return d Z_BUF_ERROR))) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> cs_avail_out (ds_strm (flush_pending (set_last_flush d flush))) = 0 ->
   DKL L flush rest0 lo r F fc me Q (flush_pending (set_last_flush d flush))) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> cs_avail_out (ds_strm (flush_pending (set_last_flush d flush))) <> 0 ->
   DKB L flush rest0 lo r F fc me Q (flush_pending (set_last_flush d flush))) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d = 0 -> rank_err d flush ->
   DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return (set_last_flush d flush) Z_BUF_ERROR))) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d = 0 -> ~ rank_err d flush -> DKB L flush rest0 lo r F fc me Q (set_last_flush d flush)) ->
  evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 (wz (dl_S L)) (wz flush) y12 (wz (ds_status d)) (wz (cs_avail_in (ds_strm d))) y15 y16 y17
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x16ccc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) HFL RAO RAI RLF RP LBS FPOK RST2 ROOMF KBUF KLF KB1 KRK KB0.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof DR as DR0.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold defl_frame in FR. unfold defl_W in MU.
  zs. zstep. if_cases KAO; zify_cond KAO; rewrite ?unsigned_lit in KAO by lia.
  -
    eapply (defl_buferr L inp rest0 lo r F fc me CTX Q d 0x16d84); [left; reflexivity| |apply KBUF; lia].
    split; [exact DR0|]. split; [exact DOUT|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI].
  - pose proof (munch_refl [(dl_As L, dl_As L + 212)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.
    zs. zs. zs. name_mem mA. zs. zs. zstep.
    tr_groups MUf WMf.
    remember (set_last_flush d flush) as s1 eqn:Es1.
    assert (ST1 : DST mA L s1).
    { rewrite Es1. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1]. }
    assert (DOUT1 : dout mA L rest0 (ds_strm s1)).
    { rewrite Es1. dsred. apply (dout_munch _ m mA L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia. }
    if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia.
    +
      assert (P0 : ds_pending d = 0) by lia.
      specialize (KRK ltac:(lia) P0). specialize (KB0 ltac:(lia) P0). clear KLF KB1 KBUF FPOK ROOMF RST2.
      assert (DI1 : DINV L rest0 lo r me s1 mA).
      { split; [split; [rewrite Es1; dsred; do 4 eexists; exact ZS| exact ST1]|]. split; [exact DOUT1|]. split; [rewrite Es1; dsred; exact ROOM|].
        split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
      assert (C_C1C : forall (a12 y14 y15 y16 : word), a12 = wz 0 -> ~ rank_err d flush ->
        evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz (dl_S L)) (wz (dl_S L)) (wz flush) a12 (wz (ds_status d)) y14 y15 y16 y17
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (wz flush) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x16da4) fc None mA (seg_rom psegs))).
      { intros a12 z14 z15 z16 -> NR. specialize (KB0 NR). unfold DKB, deflR in KB0.
        replace (wz 0) with (wz (ds_pending s1)) by (rewrite Es1; dsred; rewrite P0; reflexivity).
        replace (wz (ds_status d)) with (wz (ds_status s1)) by (rewrite Es1; reflexivity).
        eapply KB0. exact DI1. }
      clear KB0.
      zstep. if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by lia.
      *
        zs. zs. zstep. if_cases KF4; zify_cond KF4; rewrite ?unsigned_lit in KF4 by lia.
        -- apply C_C1C; [reflexivity|]. unfold rank_err, Z_FINISH. lia.
        -- assert (F0 : flush = 0) by lia. rewrite F0 in *.
           assert (HLF : ds_last_flush d = -2 \/ ds_last_flush d = -1 \/ ds_last_flush d = 0 \/ ds_last_flush d = 1 \/ ds_last_flush d = 2
                         \/ ds_last_flush d = 3 \/ ds_last_flush d = 4 \/ ds_last_flush d = 5) by lia.
           destruct HLF as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; do 11 zs; zstep; if_cases KR.
           1,3: clear KR; apply C_C1C; [reflexivity|]; unfold rank_err, RANK; rewrite E; cbn; lia.
           1,2: exfalso; revert KR; vm_compute; intros KR; discriminate KR.
           1,3,5,7,9,11: exfalso; revert KR; vm_compute; intros KR; discriminate KR.
           all: clear KR; eapply (defl_buferr L inp rest0 lo r F fc me CTX Q s1 0x170f4); [right; left; reflexivity| exact DI1| apply KRK; unfold rank_err, RANK, Z_FINISH; rewrite E; cbn; lia].
      * zs. apply C_C1C; [reflexivity|]. unfold rank_err. lia.
    +
      assert (PN0 : ds_pending d <> 0) by lia.
      specialize (FPOK ltac:(lia) PN0). specialize (ROOMF ltac:(lia) PN0). specialize (RST2 ltac:(lia) PN0).
      specialize (KLF ltac:(lia) PN0). specialize (KB1 ltac:(lia) PN0). clear KRK KB0 KBUF.
      destruct FPOK as [BI FPK]. rewrite Es1 in BI, FPK. change (ds_lit_bufsize (set_last_flush d flush)) with (ds_lit_bufsize d) in BI, FPK. rewrite LBS in BI, FPK.
      change (16384 * 4) with 65536 in BI, FPK. rewrite <- Es1 in BI, FPK. cbv zeta in FPK.
      pose proof (tr_flush_bits_strm' s1) as ES.
      pose proof (flush_pending_eq s1) as EF. cbv zeta in EF.
      destruct FPK as (RP1 & RPB & RPO0 & RPO1 & RTO).
      clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf.
      assert (ESS : ds_strm s1 = ds_strm d) by (rewrite Es1; reflexivity).
      rewrite ESS in ES, DOUT1. unfold dout in DOUT1.
      assert (OL0 : (length (cs_out_rev (ds_strm d)) <= length rest0)%nat) by (exact (unbox _ ROOM)).
      pose proof (outv_length rest0 (ds_strm d) OL0) as OL. clear OL0.
      assert (C_BEC : forall (X' : deflate_state) (a11 a12 y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31 : word) (m' : mem),
        X' = flush_pending s1 -> DINV L rest0 lo r me X' m' -> 0 <= cs_avail_out (ds_strm X') < 2^31 ->
        a11 = wz (cs_avail_out (ds_strm X')) -> a12 = wz (ds_pending X') ->
        evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz (dl_S L)) a11 a12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                        F (wz 0x16d70) fc None m' (seg_rom psegs))).
      { intros X' a11 a12 z1 z5 z6 z7 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 m' EX' DI' RAO' -> ->.
        unfold deflR. zs. zstep. if_cases KA'; zify_cond KA'; rewrite ?unsigned_lit in KA' by lia.
        - rewrite EX' in *. eapply (KLF ltac:(lia)). exact DI'.
        - pose proof DI' as DI0. destruct DI' as (DR' & _ & _ & FR' & STK' & _ & _ & MI').
          destruct DR' as [_ ST']. destruct ST' as [GA' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA'.
          rewrite EX' in *.
          zs. zs. zs. eapply (KB1 ltac:(lia)). exact DI0. }
      clear KLF KB1.
      zs. zs.
      call (HTFB L s1).
      1:{ exact ST1. } 1:{ eassumption. } 1:{ exact BI. } 1:{ exact RPB. } 1:{ reflexivity. }
      name_mem mC.
      remember (tr_flush_bits s1) as d1 eqn:Ed1.
      assert (EL : fp_len d1 = if cs_avail_out (ds_strm d) <? ds_pending d1 then cs_avail_out (ds_strm d) else ds_pending d1).
      { unfold fp_len. rewrite ES, wrap32_id by lia. reflexivity. }
      remember (fp_len d1) as flen eqn:Eflen. clear Eflen.
      destruct POST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSd LAYd]. open_A GA.
      pose proof (munch_refl [(dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] mC) as MUf.
      pose proof (wmono_refl psegs mC) as WMf.
      zs. zs. zs. zs. zstep.
      assert (FL : 0 <= flen /\ flen <= cs_avail_out (ds_strm d) /\ flen <= ds_pending d1) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm d)) (ds_pending d1)); lia).
      join_x18 (wz flen) 0x16d0c.
      { if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
        - assert (E : flen = ds_pending d1) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm d)) (ds_pending d1)); lia).
          rewrite E. apply evt_done. reflexivity.
        - assert (E : flen = cs_avail_out (ds_strm d)) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm d)) (ds_pending d1)); lia).
          rewrite E. zstep. apply evt_done. reflexivity. }
      intros ms' ->. clear EL.
      zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
      *
        assert (EX : flush_pending s1 = d1) by (rewrite EF; replace (flen =? 0) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
        assert (DI : DINV L rest0 lo r me d1 mC).
        { split; [split|].
          - rewrite ES. do 4 eexists. exact ZS.
          - constructor; [do 5 eexists; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                         | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENSd| exact LAYd].
          - split; [unfold dout; rewrite ES; exact DOUT1|]. split; [rewrite ES; exact ROOM|].
            split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
        eapply (C_BEC d1); [symmetry; exact EX| exact DI| rewrite ES; lia| rewrite ES; reflexivity| reflexivity].
      *
        replace (flen =? 0) with false in EF by (symmetry; apply Z.eqb_neq; lia).
        do 4 zstep. rewrite ?Z.mod_small by lia.
        remember (length (cs_out_rev (ds_strm d))) as k eqn:Ek.
        assert (KL : (k + Z.to_nat flen <= length rest0)%nat).
        { apply unbox in ROOMF. rewrite EF, fp_tail_out, cs_emit_out_len', ES, <- Ek, arr_slice_length' in ROOMF. lia. }
        pose proof (u8arr_sub_bytes _ (dl_Ab L) _ (Z.to_nat (ds_pending_out d1)) (Z.to_nat flen) Gpend ltac:(rewrite av8_length; lia)) as SRC.
        rewrite av8_slice in SRC by lia. rewrite Z2Nat.id in SRC by lia.
        assert (LSRC : length (map (Z_to_bv 8) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)) = Z.to_nat flen)
          by (rewrite length_map; apply arr_slice_length').
        destruct (u8arr_split3 _ (dl_NO L) _ k (Z.to_nat flen) DOUT1 ltac:(rewrite OL; lia)) as (O1 & O2 & O3). clear DOUT1.
        assert (LO1 : length (firstn k (outv rest0 (ds_strm d))) = k) by (rewrite length_firstn, OL; lia).
        assert (LO3 : length (skipn (k + Z.to_nat flen) (outv rest0 (ds_strm d))) = (length rest0 - (k + Z.to_nat flen))%nat) by (rewrite length_skipn, OL; lia).
        call (memcpy_Z (dl_NO L + Z.of_nat k) (dl_Ab L + ds_pending_out d1) flen).
        1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
        name_mem mD.
        pose proof (u8arr_join3k _ (dl_NO L) _ _ _ k (Z.to_nat flen) LO1 O1 PC O3) as OUT.
        fold (zb8 (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)) in OUT.
        rewrite <- (arr_slice_length' (ds_pending_buf d1) (ds_pending_out d1) flen) in OUT. rewrite Ek in OUT.
        rewrite <- outv_emit in OUT by (rewrite <- Ek, arr_slice_length'; exact KL).
        assert (OL' : length (outv rest0 (cs_emit (ds_strm d) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen))) = length rest0).
        { apply outv_length. rewrite cs_emit_out_len, arr_slice_length', <- Ek. lia. }
        clear O1 O3 PC POST SRC LSRC LO1 LO3.
        do 16 zs. zstep.
        if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
        --
          unfold fp_tail in EF. cbv zeta in EF. replace (ds_pending d1 - flen =? 0) with false in EF by (symmetry; apply Z.eqb_neq; lia).
          tr_groups MUf WMf.
          match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (DI : DINV L rest0 lo r me (flush_pending s1) mm) end.
          { split; [rewrite EF; split|split; [rewrite EF|split; [exact ROOMF|]]].
            - rewrite ES. eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
              rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek; close_cells ZS.
            - constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                           | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSd | exact LAYd].
            - unfold dout. rewrite ES; dsred; exact OUT.
            - split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
          eapply (C_BEC (flush_pending s1)); [reflexivity| exact DI| rewrite EF; dsred; rewrite ES; lia| rewrite EF; dsred; rewrite ES; reflexivity| rewrite EF; dsred; reflexivity].
        --
          do 3 zs.
          unfold fp_tail in EF. cbv zeta in EF. replace (ds_pending d1 - flen =? 0) with true in EF by (symmetry; apply Z.eqb_eq; lia).
          tr_groups MUf WMf.
          match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (DI : DINV L rest0 lo r me (flush_pending s1) mm) end.
          { split; [rewrite EF; split|split; [rewrite EF|split; [exact ROOMF|]]].
            - rewrite ES. eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
              rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek; close_cells ZS.
            - constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                           | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSd | exact LAYd].
            - unfold dout. rewrite ES; dsred; exact OUT.
            - split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
          eapply (C_BEC (flush_pending s1)); [reflexivity| exact DI| rewrite EF; dsred; rewrite ES; lia| rewrite EF; dsred; rewrite ES; reflexivity| rewrite EF; dsred; f_equal; lia].
Qed.
End PEND.
End Z_defl_pend.


Module Z_defl_put4.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_model.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate SendModel FillWinModel DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section PUT4.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.

Lemma defl_put4 : forall (Q : machine_state -> Prop) (X : deflate_state) (pc : Z)
    (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31 : word) (m : mem),
  pc = 0x16e8c \/ pc = 0x17b5c ->
  DINV L rest0 lo r me X m ->
  0 <= ds_pending X -> ds_pending X + 4 <= 65536 -> 0 <= cs_adler (ds_strm X) < 2^64 ->
  (forall (z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 : word) (m' : mem),
     DINV L rest0 lo r me (put_adler X) m' ->
     evt psegs Q (MS (deflR L flush r z1 z5 z6 z7 (wz (dl_S L)) z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31)
                     F (wz (pc + 112)) fc None m' (seg_rom psegs))) ->
  evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz (dl_S L)) (wz (cs_adler (ds_strm X))) y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                  F (wz pc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPC (DR & DOUT & ROOM & FR & STK & MU & WM & MI) RP0 RP4 RA HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA. open_pend Gpend. pose proof (ln_pend _ LENS) as Lpend.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + 65536)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.
  remember (cs_adler (ds_strm X)) as a eqn:Ea.
  assert (R3 : 0 <= Z.shiftr a 24 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (R2 : 0 <= Z.shiftr a 16 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (R1 : 0 <= Z.shiftr a 8 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  destruct HPC as [-> | ->].
  - do 6 zs.
    pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8)) ltac:(rewrite unsigned_lit by lia; exact (adler_b3 a RA)).
    do 6 zs.
    pb_store Gpend (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8))) 65536 (dl_Ab L) (ds_pending X + 1)
      (wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255)) ltac:(rewrite unsigned_lit by lia; exact (adler_b2 a RA)).
    do 7 zs.
    pb_store Gpend (arr_set (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8))) (ds_pending X + 1) (wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255)))
      65536 (dl_Ab L) (ds_pending X + 1 + 1) (wrap8 (Z.shiftr (Z.land a 65535) 8)) ltac:(rewrite unsigned_lit by lia; exact (adler_b1 a RA)).
    do 5 zs.
    pb_store Gpend (arr_set (arr_set (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8))) (ds_pending X + 1) (wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255)))
                     (ds_pending X + 1 + 1) (wrap8 (Z.shiftr (Z.land a 65535) 8)))
      65536 (dl_Ab L) (ds_pending X + 1 + 1 + 1) (wrap8 (Z.land (Z.land a 65535) 255)) ltac:(rewrite unsigned_lit by lia; exact (adler_b0 a RA)).
    name_mem mB. tr_groups MUf WMf.
    eapply HK.
    split; [split|].
    + unfold put_adler, putShortMSB, put_byte. dsred. rewrite Ea in ZS. do 4 eexists. exact ZS.
    + unfold put_adler, putShortMSB, put_byte. rewrite <- Ea.
      constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| unfold dpend; dsred; exact Gpend| close_lens_set LENS | exact LAY1].
    + split; [unfold put_adler, putShortMSB, put_byte; dsred; apply (dout_munch _ m mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
      split; [unfold put_adler, putShortMSB, put_byte; dsred; exact ROOM|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
  - do 6 zs.
    pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8)) ltac:(rewrite unsigned_lit by lia; exact (adler_b3 a RA)).
    do 6 zs.
    pb_store Gpend (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8))) 65536 (dl_Ab L) (ds_pending X + 1)
      (wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255)) ltac:(rewrite unsigned_lit by lia; exact (adler_b2 a RA)).
    do 7 zs.
    pb_store Gpend (arr_set (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8))) (ds_pending X + 1) (wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255)))
      65536 (dl_Ab L) (ds_pending X + 1 + 1) (wrap8 (Z.shiftr (Z.land a 65535) 8)) ltac:(rewrite unsigned_lit by lia; exact (adler_b1 a RA)).
    do 5 zs.
    pb_store Gpend (arr_set (arr_set (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8))) (ds_pending X + 1) (wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255)))
                     (ds_pending X + 1 + 1) (wrap8 (Z.shiftr (Z.land a 65535) 8)))
      65536 (dl_Ab L) (ds_pending X + 1 + 1 + 1) (wrap8 (Z.land (Z.land a 65535) 255)) ltac:(rewrite unsigned_lit by lia; exact (adler_b0 a RA)).
    name_mem mB. tr_groups MUf WMf.
    eapply HK.
    split; [split|].
    + unfold put_adler, putShortMSB, put_byte. dsred. rewrite Ea in ZS. do 4 eexists. exact ZS.
    + unfold put_adler, putShortMSB, put_byte. rewrite <- Ea.
      constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| unfold dpend; dsred; exact Gpend| close_lens_set LENS | exact LAY1].
    + split; [unfold put_adler, putShortMSB, put_byte; dsred; apply (dout_munch _ m mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
      split; [unfold put_adler, putShortMSB, put_byte; dsred; exact ROOM|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.
End PUT4.
End Z_defl_put4.

Module Z_defl_hdr.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_model.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_flushpend Z_adler32.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_arms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_put4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_flushpend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_adler32.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate SendModel FillWinModel DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section HDR.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.

Lemma defl_disp : forall (Q : machine_state -> Prop) (X : deflate_state),
  (ds_status X = 42 \/ ds_status X = 113 \/ ds_status X = 666) -> 0 <= cs_avail_in (ds_strm X) <= 1 ->
  (ds_status X = 42 -> DKH L flush rest0 lo r F fc me Q X) ->
  (ds_status X = 113 -> DK L flush rest0 lo r F fc me Q 0x178c8 X) ->
  (ds_status X = 666 -> cs_avail_in (ds_strm X) = 0 -> DK L flush rest0 lo r F fc me Q 0x178d0 X) ->
  (ds_status X = 666 -> cs_avail_in (ds_strm X) <> 0 -> DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return X Z_BUF_ERROR))) ->
  DKB L flush rest0 lo r F fc me Q X.
Proof.
  intros Q X HST RAI KH K90 K98 KERR. unfold DKB. intros until m'. intros DI.
  unfold deflR.
  destruct HST as [E|[E|E]].
  - specialize (KH E). clear K90 K98 KERR. rewrite E. zs. zstep. closed_br.
    unfold DKH, deflR in KH. eapply KH. exact DI.
  - specialize (K90 E). clear KH K98 KERR. rewrite E. zs. zstep. closed_br.
    zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs.
    unfold DK, deflR in K90. eapply K90. exact DI.
  - specialize (K98 E). specialize (KERR E). clear KH K90. rewrite E. zs. zstep. closed_br.
    zs. zstep. closed_br.
    pose proof DI as DI0. destruct DI as (DR & _). destruct DR as [ZS _]. open_zs ZS.
    zs. zstep. if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by lia.
    + unfold DK, deflR in K98. eapply (K98 ltac:(lia)). exact DI0.
    + eapply (defl_buferr L inp rest0 lo r F fc me CTX Q X 0x16dbc); [right; right; reflexivity| exact DI0| apply KERR; lia].
Qed.

Hypothesis HTFB : tr_flush_bits_stmt.

Lemma defl_hdr : forall (Q : machine_state -> Prop) (X : deflate_state),
  ds_wrap X = 1 -> ds_w_bits X = 15 -> ds_level X = 6 -> ds_strategy X = 0 ->
  0 <= ds_strstart X < 2^31 -> 0 <= ds_pending X -> ds_pending X + 6 <= 65536 -> ds_lit_bufsize X = 16384 ->
  0 <= cs_adler (ds_strm X) < 2^64 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  fp_ok (zhdr_st X) -> ds_status (flush_pending (zhdr_st X)) = 113 -> 0 <= ds_pending (flush_pending (zhdr_st X)) < 2^64 ->
  Box (length (cs_out_rev (ds_strm (flush_pending (zhdr_st X)))) <= length rest0)%nat ->
  (ds_pending (flush_pending (zhdr_st X)) <> 0 -> DKL L flush rest0 lo r F fc me Q (flush_pending (zhdr_st X))) ->
  (ds_pending (flush_pending (zhdr_st X)) = 0 -> DK L flush rest0 lo r F fc me Q 0x178c8 (flush_pending (zhdr_st X))) ->
  DKH L flush rest0 lo r F fc me Q X.
Proof.
  intros Q X WR WB LV SG RSS RP0 RP6 LBS RAD RAO FPOK STF RPF ROOMF KL K90.
  unfold DKH. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof (zhdr_eq X WB LV SG) as EH. cbv zeta in EH.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA. open_pend Gpend. pose proof (ln_pend _ LENS) as Lpend.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + 65536)] m') as MUf. pose proof (wmono_refl psegs m') as WMf.
  assert (RW : - 2^31 <= ds_wrap X < 2^31) by lia. assert (RWB : - 2^31 <= ds_w_bits X < 2^31) by lia.
  assert (RLV : - 2^31 <= ds_level X < 2^31) by lia. assert (RSG : - 2^31 <= ds_strategy X < 2^31) by lia.
  zs. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [exfalso; lia|]. clear K1.
  zs. zs. zs. rewrite WB, SG. zs. zs. zs. zs. zstep. closed_br.
  zs. rewrite LV. zs. zstep. closed_br. zs. zstep. closed_br. zstep. closed_br. zs. zs. zs.
  assert (C_D74 : forall (s3 : deflate_state) (z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 : word) (mm : mem),
    zhdr_st X = set_status (set_strm s3 (cset_adler (ds_strm s3) adler32_init)) BUSY_STATE ->
    ds_lit_bufsize s3 = 16384 -> ds_strm s3 = ds_strm X ->
    DINV L rest0 lo r me s3 mm ->
    evt psegs Q (MS (deflR L flush r z1 z5 z6 z7 (wz (dl_S L)) z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31)
                    F (wz 0x16efc) fc None mm (seg_rom psegs))).
  { clear GA Gpend ZS FR STK MU WM MUf WMf DOUT ROOM GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS Lpend.
    intros s3 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 mm EH3 LBS3 ES3 (DR3 & DOUT3 & ROOM3 & FR3 & STK3 & MU3 & WM3 & MI3).
    destruct DR3 as [ZS3 ST3]. destruct ST3 as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS3 LAY3].
    open_zs ZS3. open_A GA.
    unfold deflR. unfold defl_frame in FR3. unfold defl_W in MU3.
    pose proof (munch_refl [(dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212)] mm) as MUf. pose proof (wmono_refl psegs mm) as WMf.
    do 5 zs.
    call (adler32_null_spec).
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ eassumption. }
    do 5 zs.
    name_mem mC. tr_groups MUf WMf.
    assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
    assert (DRH : DREP mC L (zhdr_st X)).
    { rewrite EH3. split.
      - dsred. do 4 eexists. unfold zs_call_cells, zs_priv_cells, adler32_init. cbn [app]. dsred. close_cells ZS3.
      - constructor; [do 5 eexists; unfold dsA_cells, BUSY_STATE; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS3 | exact LAY3]. }
    assert (DOH : dout mC L rest0 (ds_strm (zhdr_st X))).
    { rewrite EH3. dsred. apply (dout_munch _ mm mC L rest0 _ DOUT3 ROOM3 MUf WMf); cbn [disjoint_from]; slia. }
    clear ZS3 GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf.
    call (flush_pending_spec HTFB L (zhdr_st X) rest0 (zlength inp) lo).
    1:{ exact DRH. } 1:{ exact DOH. } 1:{ eassumption. } 1:{ rewrite ESP. exact STK3. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
    1:{ exact IO. } 1:{ exact FPOK. } 1:{ rewrite EH3. dsred. rewrite LBS3. reflexivity. } 1:{ rewrite EH3. dsred. rewrite ES3. exact RAO. }
    1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. }
    name_mem mD.
    lazymatch goal with H : stk psegs mD _ _ |- _ => rename H into STKF end. rewrite ESP in STKF.
    lazymatch goal with H : DREP mD L _ |- _ => rename H into DRF end.
    lazymatch goal with H : dout mD L _ _ |- _ => rename H into DOF end.
    assert (DIF : DINV L rest0 lo r me (flush_pending (zhdr_st X)) mD).
    { split; [exact DRF|]. split; [exact DOF|]. split; [exact ROOMF|]. split; [exact FR3|]. split; [exact STKF|]. split; [exact MU3|]. split; [exact WM3| eassumption]. }
    destruct DRF as [_ STF']. destruct STF' as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
    assert (RSTF : - 2^31 <= ds_status (flush_pending (zhdr_st X)) < 2^31) by lia.
    zs. zstep. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia.
    - unfold DKL, deflR in KL. eapply (KL ltac:(lia)). exact DIF.
    - zs. rewrite STF. zs. zs.
      zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs.
      unfold DK, deflR in K90. eapply (K90 ltac:(lia)). exact DIF. }
  do 5 zs.
  destruct (Z.eq_dec (ds_strstart X) 0) as [SS0|SSN].
  - replace (ds_strstart X =? 0) with true in EH by (symmetry; apply Z.eqb_eq; exact SS0).
    rewrite SS0. do 6 zs. change (Z.b2z (0 <? 0)) with 0. zs.
    pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_pending X) (wrap8 120) ltac:(vm_compute; reflexivity).
    do 18 zs.
    pb_store Gpend (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 120)) 65536 (dl_Ab L) (ds_pending X + 1) (wrap8 156) ltac:(vm_compute; reflexivity).
    zs. rewrite SS0. zstep. closed_br.
    name_mem mB. tr_groups MUf WMf.
    eapply (C_D74 (put_byte (put_byte X 120) 156)); [exact EH| exact LBS| reflexivity|].
    split; [split|].
    + unfold put_byte. dsred. do 4 eexists. exact ZS.
    + unfold put_byte.
      constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| unfold dpend; dsred; exact Gpend| close_lens_set LENS | exact LAY1].
    + split; [unfold put_byte; dsred; apply (dout_munch _ m' mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
      split; [unfold put_byte; dsred; exact ROOM|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
  - replace (ds_strstart X =? 0) with false in EH by (symmetry; apply Z.eqb_neq; exact SSN).
    do 6 zs. replace (0 <? ds_strstart X) with true by (symmetry; apply Z.ltb_lt; lia). change (Z.b2z true) with 1. zs.
    pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_pending X) (wrap8 120) ltac:(vm_compute; reflexivity).
    do 18 zs.
    pb_store Gpend (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 120)) 65536 (dl_Ab L) (ds_pending X + 1) (wrap8 187) ltac:(vm_compute; reflexivity).
    zs. zstep. if_cases KDI; zify_cond KDI; rewrite ?unsigned_lit in KDI by lia; [exfalso; lia|]. clear KDI.
    zs.
    name_mem mB. tr_groups MUf WMf.
    eapply (defl_put4 L flush inp rest0 lo r F fc me CTX Q (put_byte (put_byte X 120) 187) 0x16e8c); [left; reflexivity| | | | |].
    + split; [split|].
      * unfold put_byte. dsred. do 4 eexists. exact ZS.
      * unfold put_byte.
        constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| unfold dpend; dsred; exact Gpend| close_lens_set LENS | exact LAY1].
      * split; [unfold put_byte; dsred; apply (dout_munch _ m' mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
        split; [unfold put_byte; dsred; exact ROOM|].
        split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
    + unfold put_byte; dsred. lia.
    + unfold put_byte; dsred. lia.
    + unfold put_byte; dsred. exact RAD.
    + intros z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 mm DI4.
      eapply (C_D74 (put_adler (put_byte (put_byte X 120) 187))); [exact EH| unfold put_adler, putShortMSB, put_byte; dsred; exact LBS| reflexivity| exact DI4].
Qed.
End HDR.
End Z_defl_hdr.


Module Z_defl_blocks.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_model.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflSlow6 DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section BLOCKS.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HSLOW : deflate_slow_stmt.

Lemma defl_run : forall (Q : machine_state -> Prop) (X : deflate_state),
  (flush = 0 \/ flush = 4) -> ds_level X = 6 -> ds_strategy X = 0 ->
  din_tie inp X -> slow_safe X flush ->
  ds_w_size X = 32768 -> ds_hash_size X = 32768 -> ds_lit_bufsize X = 16384 -> ds_insert X = 0 -> ds_wrap X = 1 ->  (* 1.4: was <> 2; deflate_slow needs wrap <> 0 *)
  cs_avail_in (ds_strm X) <= 1 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  snd (deflate_slow X flush) <> block_done ->
  0 <= cs_avail_out (ds_strm (blk_s2 X flush)) < 2^31 ->
  Box (length (cs_out_rev (ds_strm (fst (deflate_slow X flush)))) <= length rest0)%nat ->
  (snd (deflate_slow X flush) = need_more \/ snd (deflate_slow X flush) = finish_started ->
   cs_avail_out (ds_strm (blk_s2 X flush)) = 0 -> DKL L flush rest0 lo r F fc me Q (blk_s2 X flush)) ->
  (snd (deflate_slow X flush) = need_more \/ snd (deflate_slow X flush) = finish_started ->
   cs_avail_out (ds_strm (blk_s2 X flush)) <> 0 -> DKE L rest0 lo r F fc me Q (wz 0) (blk_s2 X flush)) ->
  (snd (deflate_slow X flush) = finish_done -> DK L flush rest0 lo r F fc me Q 0x17a50 (blk_s2 X flush)) ->
  DK L flush rest0 lo r F fc me Q 0x178d8 X.
Proof.
  intros Q X HFL LV SG TIE SAFE WS HS LBS INS WR RAI RAO NBD RAO2 ROOMF KNM0 KNM1 KFD.
  unfold DK. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI). rename m' into m.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp.
  assert (RL : relro_clean m) by (apply (defl_relro L inp rest0 lo r me CTX); exact MU).
  pose proof (cfg6_cell m RL) as CFG. unfold Z_CFG6_FUNC, Z_DEFLATE_SLOW in CFG.
  assert (DINm : din m L inp) by (apply (defl_din L inp rest0 lo r me CTX); exact MU).
  pose proof DR as DR0. destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  assert (RLV : - 2^31 <= ds_level X < 2^31) by lia. assert (RSG : - 2^31 <= ds_strategy X < 2^31) by lia.
  zs. rewrite LV. zstep. closed_br. zs. rewrite SG. zs. zstep. closed_br. zs. zstep. closed_br.
  do 6 zs.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
  clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend CFG.
  zs.
  call (HSLOW L X flush inp rest0 lo).
  1:{ exact DR0. } 1:{ exact DINm. } 1:{ exact TIE. } 1:{ exact DOUT. } 1:{ exact MI. } 1:{ exact RL. } 1:{ rewrite ESP. exact STK. }
  1:{ rewrite ESP. unfold Z_SLOW_STACK. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact IO. } 1:{ exact SAFE. } 1:{ exact HFL. } 1:{ exact WS. } 1:{ exact HS. } 1:{ exact LBS. } 1:{ exact INS. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  1:{ exact RAI. } 1:{ exact RAO. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem mA.
  lazymatch goal with H : stk psegs mA _ _ |- _ => rename H into STKA end. rewrite ESP in STKA.
  lazymatch goal with H : DREP mA L _ |- _ => rename H into DRA end.
  lazymatch goal with H : dout mA L _ _ |- _ => rename H into DOA end.
  assert (C_85C : forall (s2 : deflate_state) (z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 : word) (mm : mem),
    DINV L rest0 lo r me s2 mm -> 0 <= cs_avail_out (ds_strm s2) < 2^31 ->
    (cs_avail_out (ds_strm s2) = 0 -> DKL L flush rest0 lo r F fc me Q s2) ->
    (cs_avail_out (ds_strm s2) <> 0 -> DKE L rest0 lo r F fc me Q (wz 0) s2) ->
    evt psegs Q (MS (deflR L flush r z1 z5 z6 z7 (wz (dl_S L)) z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31)
                    F (wz 0x17994) fc None mm (seg_rom psegs))).
  { intros s2 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 mm DI2 RA2 K0 K1.
    pose proof DI2 as DI0. destruct DI2 as (DR2 & _). destruct DR2 as [ZS2 _]. open_zs ZS2.
    unfold deflR. zs. zstep. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia.
    - zs. zs. eapply (K1 ltac:(lia)). exact DI0.
    - unfold DKL, deflR in K0. eapply (K0 ltac:(lia)). exact DI0. }
  unfold blk_s2 in *.
  destruct (deflate_slow X flush) as [X1 b] eqn:EDS. cbn [fst snd] in DRA, DOA, KNM0, KNM1, KFD, NBD, RAO2, ROOMF |- *.
  assert (DIA : DINV L rest0 lo r me X1 mA).
  { split; [exact DRA|]. split; [exact DOA|]. split; [exact ROOMF|]. split; [exact FR|]. split; [exact STKA|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  destruct b; cbn [bs_code block_state_eqb orb] in KNM0, KNM1, KFD, RAO2 |- *.
  -
    do 4 zs. zstep. closed_br. zs. zstep. closed_br.
    eapply (C_85C X1); [exact DIA| exact RAO2| apply KNM0; left; reflexivity| apply KNM1; left; reflexivity].
  - exfalso. apply NBD. reflexivity.
  -
    destruct DRA as [ZSA STA]. destruct STA as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSA LAYA]. open_A GA.
    pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
    do 4 zs. zstep. closed_br. zs. zs. name_mem mB.
    tr_groups MUf WMf.
    assert (DIB : DINV L rest0 lo r me (set_status X1 FINISH_STATE) mB).
    { split; [split|].
      - exact ZSA.
      - constructor; [do 5 eexists; unfold dsA_cells, FINISH_STATE; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSA | exact LAYA].
      - split; [dsred; apply (dout_munch _ mA mB L rest0 _ DOA ROOMF MUf WMf); cbn [disjoint_from]; slia|].
        split; [exact ROOMF|]. split; [exact FR|]. split; [exact STKA|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    zs. zstep. closed_br.
    eapply (C_85C (set_status X1 FINISH_STATE)); [exact DIB| exact RAO2| apply KNM0; right; reflexivity| apply KNM1; right; reflexivity].
  -
    destruct DRA as [ZSA STA]. destruct STA as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSA LAYA]. open_A GA.
    pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
    do 4 zs. zstep. closed_br. zs. zs. name_mem mB.
    tr_groups MUf WMf.
    assert (DIB : DINV L rest0 lo r me (set_status X1 FINISH_STATE) mB).
    { split; [split|].
      - exact ZSA.
      - constructor; [do 5 eexists; unfold dsA_cells, FINISH_STATE; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSA | exact LAYA].
      - split; [dsred; apply (dout_munch _ mA mB L rest0 _ DOA ROOMF MUf WMf); cbn [disjoint_from]; slia|].
        split; [exact ROOMF|]. split; [exact FR|]. split; [exact STKA|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    zs. zstep. closed_br. zs. zs. zstep. closed_br.
    unfold DK, deflR in KFD. eapply (KFD eq_refl). exact DIB.
Qed.

Lemma defl_blk98 : forall (Q : machine_state -> Prop) (X : deflate_state),
  (flush = 0 \/ flush = 4) -> cs_avail_in (ds_strm X) = 0 -> 0 <= ds_lookahead X < 2^31 -> 0 <= ds_status X < 1000 ->
  (negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)) = true -> DK L flush rest0 lo r F fc me Q 0x178d8 X) ->
  (negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)) = false -> flush = 0 -> DKE L rest0 lo r F fc me Q (wz 0) X) ->
  (negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)) = false -> flush <> 0 -> DK L flush rest0 lo r F fc me Q 0x17a50 X) ->
  DK L flush rest0 lo r F fc me Q 0x178d0 X.
Proof.
  intros Q X HFL AI0 RLA RST KRUN KOK KFIN. unfold DK. intros until m'. intros DI.
  pose proof DI as DI0. destruct DI as (DR & _). destruct DR as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
  unfold deflR. unfold Z_NO_FLUSH, FINISH_STATE in *.
  zs. zstep. if_cases KLA; zify_cond KLA; rewrite ?unsigned_lit in KLA by lia.
  -
    replace (ds_lookahead X =? 0) with true in * by (symmetry; apply Z.eqb_eq; lia). cbn [negb orb] in *.
    zstep. if_cases KF0; zify_cond KF0; rewrite ?unsigned_lit in KF0 by lia.
    + assert (F0 : flush = 0) by lia. replace (flush =? 0) with true in * by (symmetry; apply Z.eqb_eq; lia). cbn [negb andb] in *.
      zs. zs. eapply (KOK eq_refl F0). exact DI0.
    + assert (F4 : flush <> 0) by lia. replace (flush =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb] in *.
      zs. zs. zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia.
      * replace (ds_status X =? 666) with false in * by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in *.
        unfold DK, deflR in KRUN. eapply (KRUN eq_refl). exact DI0.
      * replace (ds_status X =? 666) with true in * by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in *.
        zs. unfold DK, deflR in KFIN. eapply (KFIN eq_refl F4). exact DI0.
  - replace (ds_lookahead X =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb] in *.
    unfold DK, deflR in KRUN. eapply (KRUN eq_refl). exact DI0.
Qed.

Lemma defl_blk90 : forall (Q : machine_state -> Prop) (X : deflate_state),
  0 <= cs_avail_in (ds_strm X) <= 1 ->
  (cs_avail_in (ds_strm X) <> 0 -> DK L flush rest0 lo r F fc me Q 0x178d8 X) ->
  (cs_avail_in (ds_strm X) = 0 -> DK L flush rest0 lo r F fc me Q 0x178d0 X) ->
  DK L flush rest0 lo r F fc me Q 0x178c8 X.
Proof.
  intros Q X RAI KRUN K98. unfold DK. intros until m'. intros DI.
  pose proof DI as DI0. destruct DI as (DR & _). destruct DR as [ZS _]. open_zs ZS.
  unfold deflR. zs. zstep. if_cases KAI; zify_cond KAI; rewrite ?unsigned_lit in KAI by lia.
  - unfold DK, deflR in KRUN. eapply (KRUN ltac:(lia)). exact DI0.
  - unfold DK, deflR in K98. eapply (K98 ltac:(lia)). exact DI0.
Qed.
End BLOCKS.
End Z_defl_blocks.


Module Z_defl_fin.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_model.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_flushpend.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_put4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_flushpend.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate SendModel FillWinModel DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section FIN.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HTFB : tr_flush_bits_stmt.

Lemma defl_fin : forall (Q : machine_state -> Prop) (X : deflate_state),
  (flush = 0 \/ flush = 4) -> - 2 <= ds_wrap X <= 2 -> ds_wrap X <> 2 ->
  (flush = 4 -> 0 < ds_wrap X ->
   0 <= ds_pending X /\ ds_pending X + 4 <= 65536 /\ 0 <= cs_adler (ds_strm X) < 2^64 /\ ds_lit_bufsize X = 16384
   /\ 0 <= cs_avail_out (ds_strm X) < 2^31 /\ fp_ok (put_adler X)
   /\ ds_wrap (flush_pending (put_adler X)) = ds_wrap X /\ 0 <= ds_pending (flush_pending (put_adler X)) < 2^64
   /\ Box (length (cs_out_rev (ds_strm (flush_pending (put_adler X)))) <= length rest0)%nat) ->
  (flush <> 4 -> DKE L rest0 lo r F fc me Q (wz 0) X) ->
  (flush = 4 -> ds_wrap X <= 0 -> DKE L rest0 lo r F fc me Q (wz 1) X) ->
  (flush = 4 -> 0 < ds_wrap X -> ds_pending (flush_pending (put_adler X)) = 0 ->
   DKE L rest0 lo r F fc me Q (wz 1) (set_wrap (flush_pending (put_adler X)) (- ds_wrap (flush_pending (put_adler X))))) ->
  (flush = 4 -> 0 < ds_wrap X -> ds_pending (flush_pending (put_adler X)) <> 0 ->
   DKE L rest0 lo r F fc me Q (wz 0) (set_wrap (flush_pending (put_adler X)) (- ds_wrap (flush_pending (put_adler X))))) ->
  DK L flush rest0 lo r F fc me Q 0x17a50 X.
Proof.
  intros Q X HFL RW W2 TRL KOK KEND KT1 KT0. unfold DK. intros until m'. intros DI.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  unfold deflR.
  zs. zstep. if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia.
  -
    assert (F4 : flush = 4) by lia. specialize (KEND F4). specialize (KT1 F4). specialize (KT0 F4). specialize (TRL F4). clear KOK.
    pose proof DI as DI0. destruct DI as (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
    destruct DR as [ZS ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY1]. open_zs ZS. open_A GA.
    lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
    assert (HW : ds_wrap X = -2 \/ ds_wrap X = -1 \/ ds_wrap X = 0 \/ ds_wrap X = 1) by lia.
    zs.
    destruct HW as [EW|[EW|[EW|EW]]]; rewrite EW; zstep; closed_br.
    1,2,3: zs; zs; eapply (KEND ltac:(lia)); exact DI0.
    assert (WP : 0 < ds_wrap X) by lia. specialize (KT1 WP). specialize (KT0 WP). destruct (TRL WP) as (RP0 & RP4 & RAD & LBS & RAO & FPOK & EWR & RPF & ROOMF).
    clear KEND TRL.
    zs. zs. zstep. closed_br.
    clear GA ZS.
    assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
    eapply (defl_put4 L flush inp rest0 lo r F fc me CTX Q X 0x17b5c); [right; reflexivity| exact DI0| exact RP0| exact RP4| exact RAD|].
    intros z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 mm (DR4 & DOUT4 & ROOM4 & FR4 & STK4 & MU4 & WM4 & MI4).
    change (wz (97116 + 112)) with (wz 97228). unfold deflR. unfold defl_frame in FR4. unfold defl_W in MU4.
    zs.
    call (flush_pending_spec HTFB L (put_adler X) rest0 (zlength inp) lo).
    1:{ exact DR4. } 1:{ exact DOUT4. } 1:{ exact MI4. } 1:{ rewrite ESP. exact STK4. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
    1:{ exact IO. } 1:{ exact FPOK. } 1:{ unfold put_adler, putShortMSB, put_byte. dsred. rewrite LBS. reflexivity. }
    1:{ unfold put_adler, putShortMSB, put_byte. dsred. exact RAO. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. }
    name_mem mD.
    lazymatch goal with H : stk psegs mD _ _ |- _ => rename H into STKF end. rewrite ESP in STKF.
    lazymatch goal with H : DREP mD L _ |- _ => rename H into DRF end.
    lazymatch goal with H : dout mD L _ _ |- _ => rename H into DOF end.
    revert DRF DOF EWR RPF ROOMF KT1 KT0. generalize (flush_pending (put_adler X)). intros s2 DRF DOF EWR RPF ROOMF KT1 KT0.
    destruct DRF as [ZSF STF]. destruct STF as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSF LAYF]. open_A GA.
    pose proof (munch_refl [(dl_As L, dl_As L + 212)] mD) as MUf. pose proof (wmono_refl psegs mD) as WMf.
    assert (RW2 : - 2^31 <= ds_wrap s2 < 2^31) by lia.
    zs. rewrite EWR, EW. zstep. closed_br. zs. zs. name_mem mE. zs.
    tr_groups MUf WMf.
    assert (DIE : DINV L rest0 lo r me (set_wrap s2 (- ds_wrap s2)) mE).
    { split; [split|].
      - exact ZSF.
      - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSF | exact LAYF].
      - split; [dsred; apply (dout_munch _ mD mE L rest0 _ DOF ROOMF MUf WMf); cbn [disjoint_from]; slia|].
        split; [exact ROOMF|]. split; [exact FR4|]. split; [exact STKF|]. split; [exact MU4|]. split; [exact WM4| eassumption]. }
    destruct (Z.eq_dec (ds_pending s2) 0) as [P0|PN].
    + rewrite P0. zs. zs. eapply (KT1 P0). exact DIE.
    + zs. replace (ds_pending s2 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). change (Z.b2z false) with 0.
      zs. eapply (KT0 PN). exact DIE.
  - zs. zs. eapply (KOK ltac:(lia)). exact DI.
Qed.
End FIN.
End Z_defl_fin.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_path OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_entry OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_arms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_pend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_hdr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_blocks OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl.Z_defl_fin.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflSlow6 DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition deflate_in_stmt : Prop :=
  forall (L : dlay) (d : deflate_state) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L d -> din m L inp -> dout m L rest0 (ds_strm d) -> mem_inv psegs m -> relro_clean m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_DEFLATE_IN_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) -> dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
  defl_path inp flush (deflate_core d flush) d ->
  (length (cs_out_rev (ds_strm (fst (deflate_core d flush)))) <= length rest0)%nat ->
  a0 = wz (dl_S L) -> a1 = wz flush ->
  evt psegs (deflate_in_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (fst (deflate_core d flush)) (snd (deflate_core d flush)) inp rest0 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_DEFLATE_PC) fc None m (seg_rom psegs)).

Section ASM.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HSLOW : deflate_slow_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : flush = 0 \/ flush = 4.
Variables (R : deflate_state * Z) (Q : machine_state -> Prop).
Hypothesis EXIT : forall X rc, R = (X, rc) -> DKE L rest0 lo r F fc me Q (wz rc) X.
Hypothesis ROOMR : (length (cs_out_rev (ds_strm (fst R))) <= length rest0)%nat.

Lemma room_of_ole : forall X, ole R X -> Box (length (cs_out_rev (ds_strm X)) <= length rest0)%nat.
Proof. intros X [OL _]. apply box. lia. Qed.

Lemma asm_lf : forall X, R = (set_last_flush X (-1), 0) -> DKL L flush rest0 lo r F fc me Q X.
Proof. intros X ER. apply (defl_lf L flush inp rest0 lo r F fc me CTX). exact (EXIT _ _ ER). Qed.

Lemma asm_fin : forall X, fin_path flush R X -> DK L flush rest0 lo r F fc me Q 0x17a50 X.
Proof.
  intros X (OL & RW & W2 & E0 & E1 & TR).
  apply (defl_fin L flush inp rest0 lo r F fc me CTX HTFB Q X HFL RW W2).
  - intros F4 WP. destruct (TR F4 WP) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & _).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
    split; [exact A7|]. split; [exact A8|]. exact (room_of_ole _ A9).
  - intros F4. exact (EXIT _ _ (E0 F4)).
  - intros F4 WN. exact (EXIT _ _ (E1 F4 WN)).
  - intros F4 WP P0. destruct (TR F4 WP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & T1 & _). exact (EXIT _ _ (T1 P0)).
  - intros F4 WP PN. destruct (TR F4 WP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T0). exact (EXIT _ _ (T0 PN)).
Qed.

Lemma asm_run : forall X, blocks_path inp flush R X -> blk_cond X flush = true -> DK L flush rest0 lo r F fc me Q 0x178d8 X.
Proof.
  intros X (OL & RAI & RLA & RST & PT & _) HC.
  destruct (PT HC) as (LV & SG & TIE & SAFE & WS & HS & LBS & INS & W2 & RAO & NBD & RAO2 & OL1 & E0 & E1 & KF).
  apply (defl_run L flush inp rest0 lo r F fc me CTX HSLOW Q X HFL LV SG TIE SAFE WS HS LBS INS W2 (proj2 RAI) RAO NBD RAO2 (room_of_ole _ OL1)).
  - intros Hb A0. exact (asm_lf _ (E0 Hb A0)).
  - intros Hb AN. exact (EXIT _ _ (E1 Hb AN)).
  - intros Hb. exact (asm_fin _ (KF Hb)).
Qed.

Lemma asm_blk98 : forall X, blocks_path inp flush R X -> cs_avail_in (ds_strm X) = 0 -> DK L flush rest0 lo r F fc me Q 0x178d0 X.
Proof.
  intros X BP A0. pose proof BP as (OL & RAI & RLA & RST & PT & PF).
  assert (EC : blk_cond X flush = negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)))
    by (unfold blk_cond; rewrite A0; reflexivity).
  apply (defl_blk98 L flush rest0 lo r F fc me Q X HFL A0 RLA RST).
  - intros C. apply (asm_run X BP). rewrite EC. exact C.
  - intros C F0. destruct (PF ltac:(rewrite EC; exact C)) as (_ & _ & _ & E0 & _). exact (EXIT _ _ (E0 ltac:(lia))).
  - intros C FN. apply asm_fin. apply PF. rewrite EC. exact C.
Qed.

Lemma asm_blk90 : forall X, blocks_path inp flush R X -> DK L flush rest0 lo r F fc me Q 0x178c8 X.
Proof.
  intros X BP. pose proof BP as (OL & RAI & _).
  apply (defl_blk90 L flush rest0 lo r F fc me Q X RAI).
  - intros AN. apply (asm_run X BP). unfold blk_cond.
    replace (cs_avail_in (ds_strm X) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AN). reflexivity.
  - intros A0. exact (asm_blk98 X BP A0).
Qed.

Lemma asm_body : forall X, body_path inp flush R X -> DKB L flush rest0 lo r F fc me Q X.
Proof.
  intros X (OL & HST & RAI & EERR & B98 & B90 & HDR).
  apply (defl_disp L flush inp rest0 lo r F fc me CTX Q X HST RAI).
  - intros E42. pose proof (HDR E42) as HH. cbv zeta in HH.
    destruct HH as (W1 & WB & LV & SG & RSS & RP0 & RP6 & LBS & RAD & RAO & FPOK & ST5 & RP5 & OL5 & E5 & B5).
    apply (defl_hdr L flush inp rest0 lo r F fc me CTX HTFB Q X W1 WB LV SG RSS RP0 RP6 LBS RAD RAO FPOK ST5 RP5 (room_of_ole _ OL5)).
    + intros PN. exact (asm_lf _ (E5 PN)).
    + intros P0. exact (asm_blk90 _ (B5 P0)).
  - intros E113. exact (asm_blk90 _ (B90 E113)).
  - intros E666 A0. exact (asm_blk98 _ (B98 E666 A0) A0).
  - intros E666 AN. exact (EXIT _ _ (EERR E666 AN)).
Qed.

Lemma asm_top : forall (d : deflate_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  defl_path inp flush R d -> DREP me L d -> dout me L rest0 (ds_strm d) -> stk psegs me lo (bv_unsigned (r_sp r)) -> mem_inv psegs me ->
  evt psegs Q (MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) (wz (dl_S L)) (wz flush) a2 a3 a4 a5 a6 a7
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
                  F (wz Z_DEFLATE_PC) fc None me (seg_rom psegs)).
Proof.
  intros until t6. intros PATH DR DOUT STK MI. cbv zeta in PATH. destruct PATH as (OL & HST & RAI & RNI & PERR & POK).
  apply (defl_entry L inp rest0 lo r F fc me CTX Q d flush t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 DR DOUT (room_of_ole _ OL) STK MI HST HFL RAI RNI).
  - intros C. exact (EXIT _ _ (PERR C)).
  - intros NE. destruct (POK NE) as (RAO & RLF & RP & LBS & EBUF & PGO).
    intros y1 y5 y6 y7 y9 y12 y15 y16 y17 y28 y29 y30 y31 m' DI.
    apply (defl_pend L flush inp rest0 lo r F fc me CTX HTFB Q d y1 y5 y6 y7 y9 y12 y15 y16 y17 y28 y29 y30 y31 m' DI HFL RAO RAI RLF RP LBS).
    + intros AN PN. exact (proj1 (proj1 (PGO AN) PN)).
    + intros AN PN. exact (proj1 (proj2 (proj1 (PGO AN) PN))).
    + intros AN PN. exact (room_of_ole _ (proj1 (proj2 (proj2 (proj1 (PGO AN) PN))))).
    + intros A0. exact (EXIT _ _ (EBUF A0)).
    + intros AN PN A2. exact (asm_lf _ (proj1 (proj2 (proj2 (proj2 (proj1 (PGO AN) PN)))) A2)).
    + intros AN PN A2. exact (asm_body _ (proj2 (proj2 (proj2 (proj2 (proj1 (PGO AN) PN)))) A2)).
    + intros AN P0 RK. exact (EXIT _ _ (proj1 (proj2 (PGO AN) P0) RK)).
    + intros AN P0 NRK. exact (asm_body _ (proj2 (proj2 (PGO AN) P0) NRK)).
Qed.
End ASM.

Section DEFL.
Hypothesis HSLOW : deflate_slow_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.

Theorem deflate_in_spec : deflate_in_stmt.
Proof.
  unfold deflate_in_stmt. intros until m. intros DR DIN DOUT MI RL STK LO SP16 BEL IO HFL PATH ROOM -> ->.
  set (r := mkSR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  assert (CTX : defl_ctx L inp rest0 lo r m).
  { constructor; [exact LO| exact SP16| exact (st_lay _ _ _ _ (proj2 DR))| exact BEL| exact IO| exact RL| exact DIN]. }
  revert PATH ROOM. generalize (deflate_core d flush). intros R PATH ROOM.
  assert (EXIT : forall X rc, R = (X, rc) ->
            DKE L rest0 lo r F fc m (deflate_in_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (fst R) (snd R) inp rest0 lo m) (wz rc) X).
  { intros X rc ER. subst R. cbn [fst snd]. unfold DKE.
    intros y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 m' DI.
    eapply evt_mono; [exact (defl_epi L inp rest0 lo r F fc m CTX X (wz rc) y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 m' DI)|].
    intros ms' P. unfold deflate_in_post. rewrite Z_to_bv_mod64. exact P. }
  exact (asm_top L flush inp rest0 lo r F fc m CTX HSLOW HTFB HFL R _ EXIT ROOM d t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 PATH DR DOUT STK MI).
Qed.
End DEFL.
