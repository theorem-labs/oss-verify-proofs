(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz DeflateBlk FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* 1.4 (zl14-cmp): deflate's frame is 64 bytes (ra, s0..s6); s7 / s8 are never saved or written, flush lives in
   s6 (1.3.1: s4), and the temporaries are s2..s5. *)
Definition Z_DEFL_EPI : Z := 0x17c7c.

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
                    F (wz 0x17078) fc None m' (seg_rom psegs)).

Definition DKH (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31 : word) (m' : mem),
    DINV L rest0 lo r me X m' ->
    evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz (dl_S L)) (wz flush) (wz (ds_pending X)) y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                    F (wz 0x1709c) fc None m' (seg_rom psegs)).

Definition DKL (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31 : word) (m' : mem),
    DINV L rest0 lo r me X m' ->
    evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                    F (wz 0x17c70) fc None m' (seg_rom psegs)).

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

Definition Z_GOT_ERRMSG : Z := 0x293f0.
Definition Z_ERRMSG : Z := 0x292d8.

Lemma errmsg_cells : forall m, relro_clean m ->
  rw_cells psegs m Z_GOT_ERRMSG [C8 (wz Z_ERRMSG)]
  /\ rw_cells psegs m Z_ERRMSG (map (fun p => C8 (wz p)) Z_ERRMSG_PTRS).
Proof.
  intros m RC. unfold relro_clean, RELRO_LO, RELRO_HI in RC. unfold Z_GOT_ERRMSG, Z_ERRMSG, Z_ERRMSG_PTRS. cbn [map].
  split.
  - pose (cs := [C8 (wz 0x292d8)]).
    apply (InitMem.rw_cells_recast psegs m 0x293f0 [CB 8 (cells_bytes cs)] cs).
    + apply (InitMem.rw_cells_image0 psegs m 0x293f0 (cells_bytes cs)).
      * intros a Ha. apply RC. change (Z.of_nat (length (cells_bytes cs))) with 8 in Ha. lia.
      * vm_compute. reflexivity.
      * lia.
      * change (Z.of_nat (length (cells_bytes cs))) with 8. lia.
    + cbn. repeat split; exact I.
    + vm_compute. reflexivity.
    + reflexivity.
  - pose (cs := [C8 (wz 66651); C8 (wz 67163); C8 (wz 66447); C8 (wz 66797); C8 (wz 66568); C8 (wz 66304); C8 (wz 66880); C8 (wz 66867); C8 (wz 67058); C8 (wz 66447)]).
    apply (InitMem.rw_cells_recast psegs m 0x292d8 [CB 80 (cells_bytes cs)] cs).
    + apply (InitMem.rw_cells_image0 psegs m 0x292d8 (cells_bytes cs)).
      * intros a Ha. apply RC. change (Z.of_nat (length (cells_bytes cs))) with 80 in Ha. lia.
      * vm_compute. reflexivity.
      * lia.
      * change (Z.of_nat (length (cells_bytes cs))) with 80. lia.
    + cbn. repeat split; exact I.
    + vm_compute. reflexivity.
    + reflexivity.
Qed.

Definition Z_CFG6_FUNC : Z := 0x292a0.

