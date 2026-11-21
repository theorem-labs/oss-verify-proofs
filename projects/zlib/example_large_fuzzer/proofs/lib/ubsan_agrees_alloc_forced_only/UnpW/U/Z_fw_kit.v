(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_slow_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_defl_iface Z_fw_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Definition Z_FW_EPI : Z := 0x16e10.
Definition Z_FW_HIGH : Z := 0x16d6c.
Definition Z_FW_READ : Z := 0x16bb8.
Definition Z_FW_TAIL : Z := 0x16c14.
Definition Z_FW_SLIDE : Z := 0x16a94.
Definition fw_frame (j0 : list byte) (r : sregs) : list cell :=
  [CB 8 j0; C8 (r_s9 r); C8 (r_s8 r); C8 (r_s7 r); C8 (r_s6 r); C8 (r_s5 r); C8 (r_s4 r); C8 (r_s3 r); C8 (r_s2 r); C8 (r_s1 r); C8 (r_s0 r); C8 (r_ra r)].
Definition fw_W (L : dlay) (lo : Z) (r : sregs) : list ivl :=
  [(lo, bv_unsigned (r_sp r)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Aw L, dl_Aw L + DS_WIN);
   (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD)].
Record fw_ctx (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (me : mem) : Prop := mkFWctx {
  fc_lo : lo <= bv_unsigned (r_sp r) - Z_FILLWIN_STACK;
  fc_sp16 : bv_unsigned (r_sp r) mod 16 = 0;
  fc_lay : dlay_ok L;
  fc_bel : dlay_below L lo (bv_unsigned (r_sp r));
  fc_io : dio_sep L (zlength inp) nout lo;
  fc_din : din me L inp }.
Definition FWINV (L : dlay) (inp : list Z) (lo : Z) (r : sregs) (me : mem) (X : deflate_state) (m : mem) : Prop :=
  DREP m L X /\ din m L inp
  /\ (exists j0, rw_cells usegs m (bv_unsigned (r_sp r) + -96) (fw_frame j0 r))
  /\ stk usegs m lo (bv_unsigned (r_sp r) + -96)
  /\ munch (fw_W L lo r) me m /\ wmono usegs me m /\ mem_inv usegs m.
Definition fw_post_gen (r : sregs) (F : bvmap 5 word) (fc : bv 32) (L : dlay) (dF : deflate_state) (inp : list Z) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) a0 a1 a2 a3 a4 a5 a6 a7
                  (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
             F (ret_pc (r_ra r)) fc None m' (seg_rom usegs)
    /\ munch (fw_W L lo r) m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned (r_sp r))
    /\ DREP m' L dF /\ din m' L inp.
Section KIT.
Variables (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : fw_ctx L inp nout lo r me.
Lemma fw_din : forall m, munch (fw_W L lo r) me m -> din m L inp.
Proof.
  intros m MU. destruct CTX as [LOsp SP16 LAY BEL IO DIN]. unfold Z_FILLWIN_STACK in LOsp. unfold din in *.
  eapply bytes_at_transport; [exact DIN| exact MU|]. unfold fw_W. cbn [disjoint_from]. rewrite zb8_length.
  below_open BEL. pose proof IO as I0. io_open I0. unfold zlength in *.
  pose proof (io_is _ _ _ _ IO) as J1. pose proof (io_iw _ _ _ _ IO) as J2. pose proof (io_ip _ _ _ _ IO) as J3.
  pose proof (io_ih _ _ _ _ IO) as J4. pose proof (io_ib _ _ _ _ IO) as J5.
  unfold apart, zlength in *. repeat split; lia.
Qed.
Lemma fw_epi : forall (dF : deflate_state)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 : word) (m' : mem),
  FWINV L inp lo r me dF m' ->
  evt usegs (fw_post_gen r F fc L dF inp lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24
             y25 (r_s10 r) (r_s11 r) y28 y29 y30 y31)
        F (wz Z_FW_EPI) fc None m' (seg_rom usegs)).
Proof.
  intros until m'. intros (DR & DIN & (j0 & FR) & STK & MU & WM & MI). unfold fw_frame in FR. unfold Z_FW_EPI.
  pose proof (fc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_FILLWIN_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 12 zs. release_frame FR STK (bv_unsigned (r_sp r)). zs.
  apply evt_done. unfold fw_post_gen. do 15 eexists. exists m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [exact DR| exact DIN].
Qed.
End KIT.
