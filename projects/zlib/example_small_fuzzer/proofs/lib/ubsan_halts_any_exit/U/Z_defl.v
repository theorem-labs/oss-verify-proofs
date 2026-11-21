(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_defl_model.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit.

Module Z_defl_kit.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz DeflateBlk FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_DEFL_EPI : Z := 0x17e14.
Definition Z_DEFL_LF : Z := 0x17e08.
Definition Z_DEFL_TRAP : Z := 0x18110.
Definition Z_DEFL_DISP : Z := 0x1703c.
Definition Z_PUTSHORTMSB : Z := 0x181f0.

(* 1.4 UBSan: deflate no longer saves s6 (never written); its frame slot sp+0 stays the carve's 8 junk bytes j0 *)
Definition defl_frame (j0 : list byte) (r : sregs) : list cell :=
  [CB 8 j0; C8 (r_s5 r); C8 (r_s4 r); C8 (r_s3 r); C8 (r_s2 r); C8 (r_s1 r); C8 (r_s0 r); C8 (r_ra r)].

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
  /\ (exists j0, rw_cells usegs m (bv_unsigned (r_sp r) + -64) (defl_frame j0 r))
  /\ stk usegs m lo (bv_unsigned (r_sp r) + -64)
  /\ munch (defl_W L rest0 lo r) me m /\ wmono usegs me m /\ mem_inv usegs m.

Definition deflR (L : dlay) (flush : Z) (r : sregs) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) : bvmap 5 word :=
  mkR x1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) x5 x6 x7 (wz (dl_As L)) (wz (dl_S L)) x10 x11 x12 x13 x14 x15 x16 x17 (wz flush)
      (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) x28 x29 x30 x31.

Definition DKE (L : dlay) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (w : word) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word) (m' : mem),
    DINV L rest0 lo r me X m' ->
    evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 y10 y11 w y13 y14 y15 y16 y17 y18
                         (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz Z_DEFL_EPI) fc None m' (seg_rom usegs)).

Definition DK (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (pc : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    DINV L rest0 lo r me X m' ->
    evt usegs Q (MS (deflR L flush r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31)
                    F (wz pc) fc None m' (seg_rom usegs)).

Definition DKB (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y12 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    DINV L rest0 lo r me X m' ->
    evt usegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz (dl_S L)) (wz flush) y12 (wz (ds_status X)) y14 y15 y16 y17 y28 y29 y30 y31)
                    F (wz Z_DEFL_DISP) fc None m' (seg_rom usegs)).

Definition DKL (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  DK L flush rest0 lo r F fc me Q Z_DEFL_LF X.

Definition DKS (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (pc : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    DINV L rest0 lo r me X m' ->
    evt usegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz (dl_S L)) (wz flush) y12 y13 y14 y15 y16 y17 y28 y29 y30 y31)
                    F (wz pc) fc None m' (seg_rom usegs)).

Definition defl_post_gen (r : sregs) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (dF : deflate_state) (w : word) (inp : list Z) (rest0 : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) w a1 a2 a3 a4 a5 a6 a7
                  (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
             F (ret_pc (r_ra r)) fc None m' (seg_rom usegs)
    /\ munch (defl_W L rest0 lo r) m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned (r_sp r))
    /\ DREP m' L dF /\ din m' L inp /\ dout m' L rest0 (ds_strm dF).

Ltac closed_br := let K := fresh "K" in if_cases K; try (exfalso; revert K; vm_compute; intros K; discriminate K); clear K.


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
    (y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word) (m' : mem),
  DINV L rest0 lo r me dF m' ->
  evt usegs (defl_post_gen r F fc L dF w12 inp rest0 lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 y10 y11 w12 y13 y14 y15 y16 y17 y18 (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31)
        F (wz Z_DEFL_EPI) fc None m' (seg_rom usegs)).
Proof.
  intros until m'. intros (DR & DOUT & _ & (j0 & FR) & STK & MU & WM & MI). unfold defl_frame in FR. unfold Z_DEFL_EPI.
  pose proof (defl_din m' MU) as DIN.
  pose proof (dc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 9 zs. release_frame FR STK (bv_unsigned (r_sp r)). zs.
  apply evt_done. unfold defl_post_gen. do 14 eexists. exists m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
  split; [exact DR|]. split; [exact DIN| exact DOUT].
Qed.

Lemma defl_lf : forall (flush : Z) (Q : machine_state -> Prop) (X : deflate_state),
  DKE L rest0 lo r F fc me Q (wz 0) (set_last_flush X (-1)) -> DKL L flush rest0 lo r F fc me Q X.
Proof.
  intros flush Q X HK. unfold DKL, DK. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1]. open_A GA.
  unfold deflR, Z_DEFL_LF. unfold defl_frame in FR. unfold defl_W in MU.
  name_mem mA. pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zstep. zstep. zs. name_mem mB.
  tr_groups MUf WMf.
  unfold DKE, Z_DEFL_EPI in HK. eapply HK.
  split; [split|].
  - exact ZS.
  - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.
End DKIT.


Lemma rw_cells_read_lo2 : forall m A cs k v a,
  rw_cells usegs m A cs -> cell_at cs k = Some (C8 v) -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes usegs m a 2 = Some (le2 v).
Proof.
  intros m A cs k v a [[Hwf Hb] _] Hc ->.
  destruct (cell_at_split _ _ _ (C8 v) Hc) as (pre & post & E & Hsz & _). subst cs.
  apply cells_wf_app in Hwf. destruct Hwf as [Wpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
  rewrite (bytes_at_ov_read usegs m A _ k 2 Hb).
  2:{ rewrite !length_app, length_le8, (cells_bytes_length pre Wpre). lia. }
  rewrite skipn_app, skipn_all2 by (rewrite (cells_bytes_length pre Wpre); lia).
  rewrite (cells_bytes_length pre Wpre), Hsz, Nat.sub_diag. cbn [app]. rewrite skipn_O.
  rewrite firstn_app, length_le8. change (2 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r. reflexivity.
Qed.
Ltac rd_lo2 H kn :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let c := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs kn) in
      lazymatch c with
      | Some (C8 ?v) =>
          let k := eval vm_compute in (Z.of_nat kn) in
          let RD := fresh "RD" in
          pose proof (rw_cells_read_lo2 m A cs kn v (wa (A + k)) H ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as RD
      end
  end.

Lemma swrap32_mod32 : forall z, bv_swrap 32 z mod 2^32 = z mod 2^32.
Proof.
  intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.pow Z.mul].
  Z.div_mod_to_equations. lia.
Qed.

Definition Z_GOT_ERRMSG : Z := 0x2c048.
Definition Z_ERRMSG : Z := 0x2bf30.

Lemma errmsg_cells : forall m, relro_clean m ->
  rw_cells usegs m Z_GOT_ERRMSG [C8 (wz Z_ERRMSG)]
  /\ rw_cells usegs m Z_ERRMSG (map (fun p => C8 (wz p)) Z_ERRMSG_PTRS).
Proof.
  intros m RC. unfold relro_clean, RELRO_LO, RELRO_HI in RC. unfold Z_GOT_ERRMSG, Z_ERRMSG, Z_ERRMSG_PTRS. cbn [map].
  split.
  - pose (cs := [C8 (wz 0x2bf30)]).
    apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_recast usegs m 0x2c048 [CB 8 (cells_bytes cs)] cs).
    + apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_image0 usegs m 0x2c048 (cells_bytes cs)).
      * intros a Ha. apply RC. change (Z.of_nat (length (cells_bytes cs))) with 8 in Ha. lia.
      * vm_compute. reflexivity.
      * lia.
      * change (Z.of_nat (length (cells_bytes cs))) with 8. lia.
    + cbn. repeat split; exact I.
    + vm_compute. reflexivity.
    + reflexivity.
  - pose (cs := [C8 (wz 66570); C8 (wz 67068); C8 (wz 66444); C8 (wz 66694); C8 (wz 66549); C8 (wz 66317); C8 (wz 66761); C8 (wz 66748); C8 (wz 66947); C8 (wz 66444)]).
    apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_recast usegs m 0x2bf30 [CB 80 (cells_bytes cs)] cs).
    + apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_image0 usegs m 0x2bf30 (cells_bytes cs)).
      * intros a Ha. apply RC. change (Z.of_nat (length (cells_bytes cs))) with 80 in Ha. lia.
      * vm_compute. reflexivity.
      * lia.
      * change (Z.of_nat (length (cells_bytes cs))) with 80. lia.
    + cbn. repeat split; exact I.
    + vm_compute. reflexivity.
    + reflexivity.
Qed.

Definition Z_CFG_TABLE : Z := 0x2be90.
Definition Z_CFG6_FUNC : Z := 0x2bef8.

Lemma cfg6_cell : forall m, relro_clean m -> rw_cells usegs m Z_CFG6_FUNC [C8 (wz Z_DEFLATE_SLOW)].
Proof.
  intros m RC. unfold relro_clean, RELRO_LO, RELRO_HI in RC. unfold Z_CFG6_FUNC, Z_DEFLATE_SLOW.
  pose (cs := [C8 (wz 0x19c58)]).
  apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_recast usegs m 0x2bef8 [CB 8 (cells_bytes cs)] cs).
  + apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_image0 usegs m 0x2bef8 (cells_bytes cs)).
    * intros a Ha. apply RC. change (Z.of_nat (length (cells_bytes cs))) with 8 in Ha. lia.
    * vm_compute. reflexivity.
    * lia.
    * change (Z.of_nat (length (cells_bytes cs))) with 8. lia.
  + cbn. repeat split; exact I.
  + vm_compute. reflexivity.
  + reflexivity.
Qed.
End Z_defl_kit.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_defl_path.

Module Z_defl_entry.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate FillWinModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel.
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
  stk usegs me lo (bv_unsigned (r_sp r)) -> mem_inv usegs me ->
  (ds_status d = 42 \/ ds_status d = 113 \/ ds_status d = 666) -> (flush = 0 \/ flush = 4) ->
  0 <= cs_avail_in (ds_strm d) <= 1 -> 0 <= cs_next_in (ds_strm d) <= zlength inp ->
  (ds_status d = 666 /\ flush <> 4 ->
   forall (y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word) (m' : mem),
     DINV L rest0 lo r me (fst (err_return d Z_STREAM_ERROR)) m' ->
     evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 y10 y11 (wz (-2)) y13 y14 y15 y16 y17 y18
                          (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz Z_DEFL_EPI) fc None m' (seg_rom usegs))) ->
  (~ (ds_status d = 666 /\ flush <> 4) ->
   forall (y1 y5 y6 y7 y12 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
     DINV L rest0 lo r me d m' ->
     evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz (dl_S L)) (wz (dl_S L)) (wz flush) y12 (wz (ds_status d)) (wz (cs_avail_in (ds_strm d))) y15 y16 y17
                          (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x16fd8) fc None m' (seg_rom usegs))) ->
  evt usegs Q (MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) (wz (dl_S L)) (wz flush) a2 a3 a4 a5 a6 a7
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
                  F (wz Z_DEFLATE_PC) fc None me (seg_rom usegs)).
Proof.
  intros until t6. intros DR DOUT ROOM STK MI HST HFL RAI RNI KERR KOK.
  pose proof DR as DR0.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs. pose proof (lo_S _ LAY) as BKS.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold Z_DEFLATE_PC. unfold Z_ZCALLOC, Z_ZCFREE in ZS. unfold Z_DEFL_EPI in KERR.
  pose proof (munch_refl (defl_W L rest0 lo r) me) as MU. unfold defl_W in MU. pose proof (wmono_refl usegs me) as WM.
  pose proof (munch_refl [(lo, bv_unsigned (r_sp r))] me) as MUf. pose proof (wmono_refl usegs me) as WMf.
  carve_frame 64%nat STK.
  do 8 zs. name_mem mP.
  assert (RST : 0 <= ds_status d < 1000) by lia.
  assert (RLP : relro_clean mP) by (apply (defl_relro L inp rest0 lo r me CTX); unfold defl_W; exact MU).
  destruct (errmsg_cells _ RLP) as [GOTE TABE]. unfold Z_GOT_ERRMSG in GOTE. unfold Z_ERRMSG, Z_ERRMSG_PTRS in TABE, GOTE. cbn [map] in TABE.
  assert (DRP : DREP mP L d).
  { apply (DREP_agree me mP L d DR0).
    - eapply ag_blocks_munch; [exact LAY1| exact MUf| exact WMf| | | | |]; cbn [disjoint_from]; slia.
    - apply (agree_on_of_munch [(lo, bv_unsigned (r_sp r))]); [exact MUf| exact WMf| lia| lia| cbn [disjoint_from]; slia]. }
  assert (DOUTP : dout mP L rest0 (ds_strm d)) by (apply (dout_munch _ me mP L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia).
  zstep. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [exfalso; lia|].
  zstep. al8 (dl_S L). gT.
  zs. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [exfalso; lia|].
  zs. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [exfalso; lia|].
  zs. zstep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia; [exfalso; lia|].
  zstep. al8 (dl_As L). gT.
  zs. zstep. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia; [exfalso; lia|].
  zs.
  assert (C_DD4 : forall a14 a15 : word,
    evt usegs Q (MS (mkR (r_ra r) (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) t0 t1 t2 (wz (dl_As L)) (r_s1 r) (wz (dl_S L)) (wz flush) (wz (-2)) (wz (ds_status d)) a14 a15 a6 a7
                     (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6) F (wz 0x16f70) fc None mP (seg_rom usegs))).
  { intros a14 a15. pose proof (unbox _ ROOM) as RM0.
    zstep. zstep. if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia; [exfalso; lia|].
    zs. zstep. zstep. if_cases KNO; zify_cond KNO; rewrite ?unsigned_lit in KNO by lia; [exfalso; lia|].
    zs. zstep.
    assert (C_DF8 : forall a15' : word,
      evt usegs Q (MS (mkR (r_ra r) (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) t0 t1 t2 (wz (dl_As L)) (wz (dl_S L)) (wz (dl_S L)) (wz flush) (wz (-2)) (wz (ds_status d)) (wz (cs_avail_in (ds_strm d))) a15' a6 a7
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6) F (wz 0x16f94) fc None mP (seg_rom usegs))).
    { intros a15'. zstep. zstep.
      assert (SIP : DINV L rest0 lo r me d mP).
      { split; [exact DRP|]. split; [exact DOUTP|]. split; [exact ROOM|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
      if_cases KF4; zify_cond KF4; rewrite ?unsigned_lit in KF4 by lia.
      - eapply (KOK ltac:(lia)). exact SIP.
      - zstep. zstep. if_cases KS6; zify_cond KS6; rewrite ?unsigned_lit in KS6 by lia.
        + eapply (KOK ltac:(lia)). exact SIP.
        +
          clear MUf WMf ZS GA. destruct DRP as [ZSP STP]. open_zs ZSP.
          pose proof (munch_refl [(dl_S L, dl_S L + 112)] mP) as MUg. pose proof (wmono_refl usegs mP) as WMg.
          zstep. zs. zstep. gT. zs. zs. name_mem mE. zstep.
          eapply (KERR ltac:(lia)).
          split; [split|].
          { unfold err_return, Z_STREAM_ERROR, MSG_ERR. cbn [fst]. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont orb Z.sub Z.opp Z.add Z.pos_sub Pos.pred_double].
            do 4 eexists. unfold zs_call_cells, zs_priv_cells. cbn [app]. dsred. close_cells ZSP. }
          { apply DST_set_strm; [intros HB; exact HB|].
            apply (DST_agree mP mE L d STP). eapply ag_blocks_munch; [exact LAY1| exact MUg| exact WMg| | | | |]; cbn [disjoint_from]; slia. }
          { split; [unfold err_return; cbn [fst]; dsred; apply (dout_munch _ mP mE L rest0 _ DOUTP ROOM MUg WMg); cbn [disjoint_from]; slia|].
            split; [unfold err_return; cbn [fst]; dsred; exact ROOM|].
            split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. } }
    if_cases KAI; zify_cond KAI; rewrite ?unsigned_lit in KAI by lia.
    - apply C_DF8.
    - zs. zstep. if_cases KNI; zify_cond KNI; rewrite ?unsigned_lit in KNI by lia; [exfalso; lia|]. apply C_DF8. }
  clear KERR KOK.
  zstep. zstep. zstep.
  destruct HST as [E|[E|E]]; rewrite E in *.
  -
    if_cases KS; zify_cond KS; [|exfalso; revert KS; vm_compute; intros KS; apply KS; reflexivity].
    zstep. zstep. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia; [exfalso; lia|].
    zstep. zstep. if_cases K7; zify_cond K7; rewrite ?unsigned_lit in K7 by lia; [|exfalso; lia].
    apply C_DD4.
  -
    if_cases KS; zify_cond KS; [exfalso; revert KS; vm_compute; intros KS; discriminate KS|].
    zstep. zs. zstep. zstep. zstep.
    if_cases KM; zify_cond KM; [exfalso; revert KM; vm_compute; intros KM; discriminate KM|].
    apply C_DD4.
  -
    if_cases KS; zify_cond KS; [|exfalso; revert KS; vm_compute; intros KS; apply KS; reflexivity].
    zstep. zstep. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia; [|exfalso; lia].
    apply C_DD4.
Qed.
End ENTRY.
End Z_defl_entry.


Module Z_defl_arms.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate FillWinModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section ARMS.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.

Lemma defl_buferr : forall (Q : machine_state -> Prop) (X : deflate_state) (pc : Z)
    (y1 y5 y6 y7 y8 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word) (m : mem),
  pc = 0x17014 \/ pc = 0x17054 \/ pc = 0x17414 ->
  DINV L rest0 lo r me X m ->
  DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return X Z_BUF_ERROR)) ->
  evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 (wz (dl_S L)) (wz (dl_S L)) y11 y12 y13 y14 y15 y16 y17
                       y18 (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz pc) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPC (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI) HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  assert (RLP : relro_clean m) by (apply (defl_relro L inp rest0 lo r me CTX); exact MU).
  destruct (errmsg_cells _ RLP) as [GOTE TABE]. unfold Z_GOT_ERRMSG in GOTE. unfold Z_ERRMSG, Z_ERRMSG_PTRS in TABE, GOTE. cbn [map] in TABE.
  destruct DR as [ZS ST]. open_zs ZS. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold defl_frame in FR. unfold defl_W in MU. unfold DKE, Z_DEFL_EPI in HK.
  pose proof (munch_refl [(dl_S L, dl_S L + 112)] m) as MUg. pose proof (wmono_refl usegs m) as WMg.
  assert (FIN : forall mE, munch [(dl_S L, dl_S L + 112)] m mE -> wmono usegs m mE -> mem_inv usegs mE ->
            munch (defl_W L rest0 lo r) me mE -> wmono usegs me mE ->
            rw_cells usegs mE (bv_unsigned (r_sp r) + -64) (defl_frame j0 r) -> stk usegs mE lo (bv_unsigned (r_sp r) + -64) ->
            dzs mE L (cset_msg (ds_strm X) (MSG_ERR Z_BUF_ERROR)) ->
            DINV L rest0 lo r me (fst (err_return X Z_BUF_ERROR)) mE).
  { intros mE MUg' WMg' MI' MU' WM' FR' STK' ZS'.
    split; [split|].
    - unfold err_return. cbn [fst]. dsred. exact ZS'.
    - apply DST_set_strm; [intros HB; exact HB|].
      apply (DST_agree m mE L X ST). eapply ag_blocks_munch; [exact (st_lay _ _ _ _ ST)| exact MUg'| exact WMg'| | | | |]; cbn [disjoint_from]; slia.
    - split; [unfold err_return; cbn [fst]; dsred; apply (dout_munch _ m mE L rest0 _ DOUT ROOM MUg' WMg'); cbn [disjoint_from]; slia|].
      split; [unfold err_return; cbn [fst]; dsred; exact ROOM|].
      split; [eexists; exact FR'|]. split; [exact STK'|]. split; [exact MU'|]. split; [exact WM'| exact MI']. }
  assert (TAIL : forall (z11 z12 : word),
    evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 (wz (dl_S L)) (wz 0x2bf30) z11 z12 y13 y14 y15 y16 y17
                     y18 (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x1701c) fc None m (seg_rom usegs))).
  { intros z11 z12. zstep. gT. zs. zs. name_mem mE. zstep. zstep.
    eapply HK. apply FIN; [exact MUg| exact WMg| eassumption| exact MU| exact WM| exact FR| exact STK|].
    unfold Z_BUF_ERROR, MSG_ERR. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont orb Z.sub Z.opp Z.add Z.pos_sub Pos.pred_double].
    do 4 eexists. unfold zs_call_cells, zs_priv_cells. cbn [app]. dsred. close_cells ZS. }
  destruct HPC as [->|[->| ->]].
  - zstep. zs. apply TAIL.
  - zstep. zs. zstep. apply TAIL.
  - zstep. zs. zstep. apply TAIL.
Qed.
End ARMS.
End Z_defl_arms.


Module Z_defl_pend.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_flushpend.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_flushpend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_arms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate FillWinModel DeflateSafe RefDeflFastM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma fp_avail_out : forall s, 0 <= cs_avail_out (ds_strm s) ->
  0 <= cs_avail_out (ds_strm (flush_pending s)) <= cs_avail_out (ds_strm s).
Proof.
  intros s RA. rewrite flush_pending_eq. cbv zeta. pose proof (tr_flush_bits_strm' s) as ES.
  assert (EL : 0 <= fp_len (tr_flush_bits s) <= cs_avail_out (ds_strm s)).
  { unfold fp_len. rewrite ES. pose proof (wrap32_range (ds_pending (tr_flush_bits s))).
    destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) (wrap32 (ds_pending (tr_flush_bits s)))); lia. }
  destruct (fp_len (tr_flush_bits s) =? 0); [rewrite ES; lia|].
  unfold fp_tail. cbv zeta.
  assert (EA : forall c l v w, cs_avail_out (cset_total_out (cset_avail_out (cs_emit c l) v) w) = v) by (intros [] l v w; reflexivity).
  destruct (_ - _ =? 0); dsred; rewrite ?EA, ?ES; lia.
Qed.

Section PEND.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HTFB : tr_flush_bits_stmt.

Lemma defl_pend : forall (Q : machine_state -> Prop) (d : deflate_state)
    (y1 y5 y6 y7 y12 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  DINV L rest0 lo r me d m ->
  (flush = 0 \/ flush = 4) ->
  0 <= cs_avail_out (ds_strm d) < 2^31 -> 0 <= cs_avail_in (ds_strm d) <= 1 -> - 2 <= ds_last_flush d <= 5 ->
  0 <= ds_pending d <= 65536 -> ds_lit_bufsize d = 16384 -> 0 <= ds_status d < 1000 ->
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
  evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz (dl_S L)) (wz (dl_S L)) (wz flush) y12 (wz (ds_status d)) (wz (cs_avail_in (ds_strm d))) y15 y16 y17
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x16fd8) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI) HFL RAO RAI RLF RP LBS RST FPOK RST2 ROOMF KBUF KLF KB1 KRK KB0.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof DR as DR0.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold defl_frame in FR. unfold defl_W in MU. unfold DKL, DK, Z_DEFL_LF, deflR in KLF. unfold DKB, Z_DEFL_DISP, deflR in KB1, KB0.
  zs. zstep. if_cases KAO; zify_cond KAO; rewrite ?unsigned_lit in KAO by lia.
  -
    eapply (defl_buferr L inp rest0 lo r F fc me CTX Q d 0x17014); [left; reflexivity| |apply KBUF; lia].
    split; [exact DR0|]. split; [exact DOUT|]. split; [exact ROOM|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI].
  - pose proof (munch_refl [(dl_As L, dl_As L + 212)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
    zs. zs. zs. name_mem mA. zstep. zstep.
    tr_groups MUf WMf.
    remember (set_last_flush d flush) as s1 eqn:Es1.
    assert (ST1 : DST mA L s1).
    { rewrite Es1. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1]. }
    assert (DOUT1 : dout mA L rest0 (ds_strm s1)).
    { rewrite Es1. dsred. apply (dout_munch _ m mA L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia. }
    assert (DI1 : DINV L rest0 lo r me s1 mA).
    { split; [split; [rewrite Es1; dsred; do 4 eexists; exact ZS| exact ST1]|]. split; [exact DOUT1|]. split; [rewrite Es1; dsred; exact ROOM|].
      split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia.
    +
      assert (P0 : ds_pending d = 0) by lia.
      specialize (KRK ltac:(lia) P0). specialize (KB0 ltac:(lia) P0). clear KLF KB1 KBUF FPOK ROOMF RST2.
      assert (C_DISP : forall (a12 a14 a15 : word), ~ rank_err d flush ->
        evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz (dl_S L)) (wz (dl_S L)) (wz flush) a12 (wz (ds_status d)) a14 a15 y16 y17
                       (wz flush) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x1703c) fc None mA (seg_rom usegs))).
      { intros a12 a14 a15 NR. specialize (KB0 NR).
        replace (wz (ds_status d)) with (wz (ds_status s1)) by (rewrite Es1; reflexivity).
        eapply KB0. exact DI1. }
      clear KB0.
      zstep. if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by lia.
      *
        assert (HLF : ds_last_flush d = -2 \/ ds_last_flush d = -1 \/ ds_last_flush d = 0 \/ ds_last_flush d = 1 \/ ds_last_flush d = 2
                      \/ ds_last_flush d = 3 \/ ds_last_flush d = 4 \/ ds_last_flush d = 5) by lia.
        destruct HFL as [F0|F4]; rewrite ?F0, ?F4 in *;
          destruct HLF as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E;
          do 3 zstep; closed_br; do 7 zstep; closed_br; do 2 zstep; closed_br;
          try (do 8 zstep; closed_br).
        1,2: apply C_DISP; unfold rank_err, RANK; rewrite E; cbn; lia.
        1-6: eapply (defl_buferr L inp rest0 lo r F fc me CTX Q s1 0x17414); [right; right; reflexivity| exact DI1| apply KRK; unfold rank_err, RANK, Z_FINISH; rewrite E; cbn; lia].
        all: apply C_DISP; unfold rank_err, Z_FINISH; lia.
      * apply C_DISP. unfold rank_err. lia.
    +
      assert (PN0 : ds_pending d <> 0) by lia.
      specialize (FPOK ltac:(lia) PN0). specialize (ROOMF ltac:(lia) PN0). specialize (RST2 ltac:(lia) PN0).
      specialize (KLF ltac:(lia) PN0). specialize (KB1 ltac:(lia) PN0). clear KRK KB0 KBUF.
      assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
      assert (ESS : ds_strm s1 = ds_strm d) by (rewrite Es1; reflexivity).
      assert (LB1 : ds_lit_bufsize s1 * 4 = 65536) by (rewrite Es1; dsred; lia).
      assert (RAO1 : 0 <= cs_avail_out (ds_strm s1) < 2^31) by (rewrite ESS; lia).
      assert (DR1 : DREP mA L s1) by exact (proj1 DI1).
      clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf ZS ST1.
      zstep. zstep.
      call (flush_pending_spec HTFB L s1 rest0 (zlength inp) lo).
      1:{ exact DR1. } 1:{ exact DOUT1. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. }
      1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ exact IO. }
      1:{ exact FPOK. } 1:{ exact LB1. } 1:{ exact RAO1. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. }
      name_mem mC.
      lazymatch goal with H : stk usegs mC lo _ |- _ => rewrite ?ESP in H; rename H into STKC end.
      lazymatch goal with H : DREP mC L _ |- _ => rename H into DRC end.
      lazymatch goal with H : dout mC L rest0 _ |- _ => rename H into DOUTC end.
      lazymatch goal with H : mem_inv usegs mC |- _ => rename H into MIC end.
      assert (DIC : DINV L rest0 lo r me (flush_pending s1) mC).
      { split; [exact DRC|]. split; [exact DOUTC|]. split; [exact ROOMF|]. split; [eexists; exact FR|]. split; [exact STKC|]. split; [exact MU|]. split; [exact WM| exact MIC]. }
      remember (flush_pending s1) as X' eqn:EX'.
      pose proof DRC as DRC0. destruct DRC as [ZS' ST']. open_zs ZS'. destruct ST' as [GA' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA'.
      assert (RAO' : 0 <= cs_avail_out (ds_strm X') < 2^31) by (rewrite EX'; pose proof (fp_avail_out s1 ltac:(lia)); lia).
      zs. zstep. if_cases KA'; zify_cond KA'; rewrite ?unsigned_lit in KA' by lia.
      * eapply (KLF ltac:(lia)). exact DIC.
      * zstep. zs. zstep. zstep. eapply (KB1 ltac:(lia)). exact DIC.
Qed.
End PEND.
End Z_defl_pend.


Module Z_putmsb.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_slow_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_PUTSHORTMSB : Z := 0x181f0.

Definition putmsb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (X : deflate_state) (b : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + DS_PEND)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ DREP m' L (putShortMSB X b).

Lemma mod_mod_le : forall x j k, 0 <= j <= k -> (x mod 2^k) mod 2^j = x mod 2^j.
Proof.
  intros x j k Hjk. replace (2^k) with (2^j * 2^(k-j)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm (2^j)), Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
Lemma msb_b1 : forall b bb, 0 <= b < 2^32 -> bb mod 2^32 = b ->
  bv_unsigned (wz (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bb mod 18446744073709551616)) 8))) mod 2^8 = wrap8 (Z.shiftr b 8) mod 2^8.
Proof.
  intros b bb Hb Hbb. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. change 18446744073709551616 with (2^64). change 4294967296 with (2^32).
  rewrite mod_mod_le by lia. rewrite Hbb.
  assert (RS : 0 <= Z.shiftr b 8 < 2^24) by (rewrite Z.shiftr_div_pow2 by lia; change (2^8) with 256; change (2^24) with 16777216; Z.div_mod_to_equations; lia).
  rewrite bv_swrap32_id by lia. rewrite unsigned_lit by lia. rewrite wrap8_mod, Z.mod_mod by lia. reflexivity.
Qed.
Lemma msb_b0 : forall b bb, 0 <= b < 2^32 -> bb mod 2^32 = b -> bv_unsigned (wz bb) mod 2^8 = wrap8 (Z.land b 255) mod 2^8.
Proof.
  intros b bb Hb Hbb. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. unfold wrap8.
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. rewrite !Z.mod_mod by lia.
  rewrite <- Hbb. change 18446744073709551616 with (2^64). rewrite !mod_mod_le by lia. reflexivity.
Qed.

Lemma putShortMSB_spec : forall (L : dlay) (X : deflate_state) (b bb lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L X -> mem_inv usegs m -> dlay_below L lo (bv_unsigned sp) -> lo <= bv_unsigned sp ->
  0 <= ds_pending X -> ds_pending X + 2 <= 65536 -> 0 <= b < 2^32 -> bb mod 2^32 = b ->
  a0 = wz (dl_As L) -> a1 = wz bb ->
  evt usegs (putmsb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L X b m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_PUTSHORTMSB) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros DR MI BEL LOSP RP0 RP2 Rb Rbb -> ->. unfold Z_PUTSHORTMSB. below_open BEL.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY].
  open_A GA. open_pend Gpend. pose proof (ln_pend _ LENS) as Lpend.
  lay_open LAY. pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs. pose proof (lo_b _ LAY) as BKb. unfold blk_ok in BKb.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + 65536)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. al8 (dl_As L). gF.
  zs. zs. zstep. zstep. zs. gF. zstep. zstep. zstep. gX. gF.
  zstep.
  pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_pending X) (wrap8 (Z.shiftr b 8)) ltac:(exact (msb_b1 b bb Rb Rbb)).
  zs. zs. zstep. zstep. zs. gF. zstep. zstep. zstep. gX. gF.
  pb_store Gpend (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr b 8))) 65536 (dl_Ab L) (ds_pending X + 1) (wrap8 (Z.land b 255)) ltac:(exact (msb_b0 b bb Rb Rbb)).
  zstep. name_mem mB.
  tr_groups MU WM.
  apply evt_done. unfold putmsb_post. do 15 eexists. exists mB.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split.
  - unfold putShortMSB, put_byte. dsred. exact ZS.
  - unfold putShortMSB, put_byte.
    constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| unfold dpend; dsred; exact Gpend| close_lens_set LENS | exact LAY].
Qed.
End Z_putmsb.

Module Z_defl_hdr.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_defl_model.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_flushpend Z_adler32 Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_arms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_putmsb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_flushpend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_adler32 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate SendModel FillWinModel DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section HDR.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.

Lemma defl_disp : forall (Q : machine_state -> Prop) (X : deflate_state),
  (ds_status X = 42 \/ ds_status X = 113 \/ ds_status X = 666) -> 0 <= cs_avail_in (ds_strm X) <= 1 ->
  (ds_status X = 42 -> DKS L flush rest0 lo r F fc me Q 0x17060 X) ->
  (ds_status X = 113 -> DK L flush rest0 lo r F fc me Q 0x17d18 X) ->
  (ds_status X = 666 -> cs_avail_in (ds_strm X) = 0 -> DKS L flush rest0 lo r F fc me Q 0x17d28 X) ->
  (ds_status X = 666 -> cs_avail_in (ds_strm X) <> 0 -> DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return X Z_BUF_ERROR))) ->
  DKB L flush rest0 lo r F fc me Q X.
Proof.
  intros Q X HST RAI KH K90 K98 KERR. unfold DKB. intros until m'. intros DI.
  unfold deflR, Z_DEFL_DISP.
  destruct HST as [E|[E|E]].
  - specialize (KH E). clear K90 K98 KERR. rewrite E. zs. zstep. closed_br.
    unfold DKS, deflR in KH. eapply KH. exact DI.
  - specialize (K90 E). clear KH K98 KERR. rewrite E. zs. zstep. closed_br.
    zs. zstep. closed_br.
    zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zstep.
    unfold DK, deflR in K90. eapply K90. exact DI.
  - specialize (K98 E). specialize (KERR E). clear KH K90. rewrite E. zs. zstep. closed_br.
    zs. zstep. closed_br.
    pose proof DI as DI0. destruct DI as (DR & _). destruct DR as [ZS _]. open_zs ZS.
    zs. zstep. if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by lia.
    + unfold DKS, deflR in K98. eapply (K98 ltac:(lia)). exact DI0.
    + eapply (defl_buferr L inp rest0 lo r F fc me CTX Q X 0x17054); [right; left; reflexivity| exact DI0| apply KERR; lia].
Qed.

Hypothesis HTFB : tr_flush_bits_stmt.

Lemma defl_hdr : forall (Q : machine_state -> Prop) (X : deflate_state),
  ds_wrap X = 1 -> ds_w_bits X = 15 -> ds_level X = 6 -> ds_strategy X = 0 ->
  0 <= ds_strstart X < 2^31 -> 0 <= ds_pending X -> ds_pending X + 6 <= 65536 -> ds_lit_bufsize X = 16384 ->
  0 <= cs_adler (ds_strm X) < 2^64 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  fp_ok (zhdr_st X) -> ds_status (flush_pending (zhdr_st X)) = 113 -> 0 <= ds_pending (flush_pending (zhdr_st X)) < 2^64 ->
  Box (length (cs_out_rev (ds_strm (flush_pending (zhdr_st X)))) <= length rest0)%nat ->
  (ds_pending (flush_pending (zhdr_st X)) <> 0 -> DKL L flush rest0 lo r F fc me Q (flush_pending (zhdr_st X))) ->
  (ds_pending (flush_pending (zhdr_st X)) = 0 -> DK L flush rest0 lo r F fc me Q 0x17d18 (flush_pending (zhdr_st X))) ->
  DKS L flush rest0 lo r F fc me Q 0x17060 X.
Proof.
  intros Q X WR WB LV SG RSS RP0 RP6 LBS RAD RAO FPOK STF RPF ROOMF KL K90.
  unfold DKS. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (zhdr_eq X WB LV SG) as EH. cbv zeta in EH.
  pose proof DR as DR0.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + 65536)] m') as MUf. pose proof (wmono_refl usegs m') as WMf.
  assert (RW : - 2^31 <= ds_wrap X < 2^31) by lia. assert (RWB : - 2^31 <= ds_w_bits X < 2^31) by lia.
  assert (RLV : - 2^31 <= ds_level X < 2^31) by lia. assert (RSG : - 2^31 <= ds_strategy X < 2^31) by lia.
  zs. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [exfalso; lia|]. clear K1.
  zs. zs. zs. rewrite WB, SG. zs. zs. zs. zs. zstep. closed_br.
  zs. rewrite LV. zs. zstep. closed_br. zs. zstep. closed_br. zstep. closed_br. zs. zstep.
  zstep. zs.
  assert (C_F7C : forall (s3 : deflate_state) (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word) (mm : mem),
    zhdr_st X = set_status (set_strm s3 (cset_adler (ds_strm s3) adler32_init)) BUSY_STATE ->
    ds_lit_bufsize s3 = 16384 -> ds_strm s3 = ds_strm X ->
    DINV L rest0 lo r me s3 mm ->
    evt usegs Q (MS (deflR L flush r z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31)
                    F (wz 0x17118) fc None mm (seg_rom usegs))).
  { clear GA FR STK MU WM MUf WMf DOUT ROOM GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS DR0 EH.
    intros s3 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 mm EH3 LBS3 ES3 (DR3 & DOUT3 & ROOM3 & (j3 & FR3) & STK3 & MU3 & WM3 & MI3).
    destruct DR3 as [ZS3 ST3]. destruct ST3 as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS3 LAY3].
    open_zs ZS3. open_A GA.
    unfold deflR. unfold defl_frame in FR3. unfold defl_W in MU3.
    do 3 zs. zstep.
    remember (wz (bv_unsigned (r_sp r) + -64)) as spw eqn:Espw.
    pose proof (munch_refl [(lo, bv_unsigned spw); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212)] mm) as MUf. pose proof (wmono_refl usegs mm) as WMf.
    call (adler32_null_spec lo 0 0).
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI3. } 1:{ rewrite ESP. exact STK3. } 1:{ rewrite ESP. unfold ADLER32_FRAME. lia. }
    lazymatch goal with H : stk usegs _ lo (bv_unsigned spw) |- _ => rewrite ESP in H; rename H into STKA end.
    lazymatch goal with H : mem_inv usegs _ |- _ => rename H into MIA end.
    subst spw.
    do 5 zs.
    name_mem mC. tr_groups MUf WMf.
    assert (DRH : DREP mC L (zhdr_st X)).
    { rewrite EH3. split.
      - dsred. do 4 eexists. unfold zs_call_cells, zs_priv_cells, adler32_init. cbn [app]. dsred. close_cells ZS3.
      - constructor; [do 5 eexists; unfold dsA_cells, BUSY_STATE; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS3 | exact LAY3]. }
    assert (DOH : dout mC L rest0 (ds_strm (zhdr_st X))).
    { rewrite EH3. dsred. apply (dout_munch _ mm mC L rest0 _ DOUT3 ROOM3 MUf WMf); cbn [disjoint_from]; slia. }
    clear ZS3 GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf.
    call (flush_pending_spec HTFB L (zhdr_st X) rest0 (zlength inp) lo).
    1:{ exact DRH. } 1:{ exact DOH. } 1:{ exact MIA. } 1:{ rewrite ESP. exact STKA. } 1:{ rewrite ESP. lia. } 1:{ unfold dlay_below. rewrite ESP. lia. }
    1:{ exact IO. } 1:{ exact FPOK. } 1:{ rewrite EH3. dsred. rewrite LBS3. reflexivity. } 1:{ rewrite EH3. dsred. rewrite ES3. exact RAO. }
    1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. }
    name_mem mD.
    lazymatch goal with H : stk usegs mD _ _ |- _ => rewrite ?ESP in H; rename H into STKF end.
    lazymatch goal with H : DREP mD L _ |- _ => rename H into DRF end.
    lazymatch goal with H : dout mD L _ _ |- _ => rename H into DOF end.
    lazymatch goal with H : mem_inv usegs mD |- _ => rename H into MIF end.
    assert (DIF : DINV L rest0 lo r me (flush_pending (zhdr_st X)) mD).
    { split; [exact DRF|]. split; [exact DOF|]. split; [exact ROOMF|]. split; [eexists; exact FR3|]. split; [exact STKF|]. split; [exact MU3|]. split; [exact WM3| exact MIF]. }
    destruct DRF as [_ STF']. destruct STF' as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
    assert (RSTF : - 2^31 <= ds_status (flush_pending (zhdr_st X)) < 2^31) by lia.
    zs. zstep. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia.
    - unfold DKL, DK, Z_DEFL_LF, deflR in KL. eapply (KL ltac:(lia)). exact DIF.
    - zs. rewrite STF. zs.
      zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zstep.
      unfold DK, deflR in K90. eapply (K90 ltac:(lia)). exact DIF. }
  assert (X1F : forall Y b, ds_strstart (putShortMSB Y b) = ds_strstart Y /\ ds_pending (putShortMSB Y b) = ds_pending Y + 1 + 1
                            /\ ds_strm (putShortMSB Y b) = ds_strm Y /\ ds_lit_bufsize (putShortMSB Y b) = ds_lit_bufsize Y).
  { intros Y b. unfold putShortMSB, put_byte. dsred. repeat split; reflexivity. }
  destruct (Z.eq_dec (ds_strstart X) 0) as [SS0|SSN].
  - replace (ds_strstart X =? 0) with true in EH by (symmetry; apply Z.eqb_eq; exact SS0).
    rewrite SS0. do 3 zs. zstep. change (Z.b2z (0 <? 0)) with 0. do 14 zs. zs. zstep.
    clear GA.
    call (putShortMSB_spec L X 30876 30876 lo).
    1:{ exact DR0. } 1:{ exact MI. } 1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mB.
    lazymatch goal with H : DREP mB L _ |- _ => rename H into DR1 end.
    lazymatch goal with H : mem_inv usegs mB |- _ => rename H into MI1 end.
    remember (putShortMSB X 30876) as X1 eqn:EX1.
    destruct (X1F X 30876) as (S1 & P1 & T1 & B1). rewrite <- EX1 in S1, P1, T1, B1. rewrite SS0 in S1.
    pose proof DR1 as DR1'. destruct DR1' as [_ ST1]. destruct ST1 as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
    assert (RSS1 : - 2^31 <= ds_strstart X1 < 2^31) by lia.
    zs. rewrite S1. zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia; [| exfalso; lia]. clear KS GA.
    eapply (C_F7C X1); [rewrite EH, EX1; reflexivity| rewrite B1; exact LBS| exact T1|].
    split; [exact DR1|]. split; [rewrite T1; apply (dout_munch _ m' mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
    split; [rewrite T1; exact ROOM|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI1].
  - replace (ds_strstart X =? 0) with false in EH by (symmetry; apply Z.eqb_neq; exact SSN).
    do 3 zs. zstep. replace (0 <? ds_strstart X) with true by (symmetry; apply Z.ltb_lt; lia). change (Z.b2z true) with 1.
    do 14 zs. zs. zstep.
    clear GA.
    call (putShortMSB_spec L X 30907 30907 lo).
    1:{ exact DR0. } 1:{ exact MI. } 1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mB.
    lazymatch goal with H : DREP mB L _ |- _ => rename H into DR1 end.
    lazymatch goal with H : mem_inv usegs mB |- _ => rename H into MI1 end.
    remember (putShortMSB X 30907) as X1 eqn:EX1.
    destruct (X1F X 30907) as (S1 & P1 & T1 & B1). rewrite <- EX1 in S1, P1, T1, B1.
    pose proof DR1 as DR1'. destruct DR1' as [ZS1 ST1]. destruct ST1 as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA. open_zs ZS1.
    assert (RSS1 : - 2^31 <= ds_strstart X1 < 2^31) by lia.
    assert (RAD1 : 0 <= cs_adler (ds_strm X1) < 2^64) by (rewrite T1; exact RAD).
    zs. rewrite S1. zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia; [exfalso; lia|]. clear KS.
    zs. zstep. zstep. zs. zstep. rewrite T1. clear GA ZS1.
    call (putShortMSB_spec L X1 (wrap32 (Z.shiftr (cs_adler (ds_strm X)) 16)) (bv_swrap 32 (Z.shiftr (cs_adler (ds_strm X)) 16 + 0)) lo).
    1:{ exact DR1. } 1:{ exact MI1. } 1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ lia. } 1:{ lia. }
    1:{ apply wrap32_range. } 1:{ rewrite swrap32_mod32, Z.add_0_r, wrap32_mod. reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mB2.
    lazymatch goal with H : DREP mB2 L _ |- _ => rename H into DR2 end.
    lazymatch goal with H : mem_inv usegs mB2 |- _ => rename H into MI2 end.
    remember (putShortMSB X1 (wrap32 (Z.shiftr (cs_adler (ds_strm X)) 16))) as X2 eqn:EX2.
    destruct (X1F X1 (wrap32 (Z.shiftr (cs_adler (ds_strm X)) 16))) as (S2 & P2 & T2 & B2). rewrite <- EX2 in S2, P2, T2, B2.
    pose proof DR2 as DR2'. destruct DR2' as [ZS2 _]. open_zs ZS2. rewrite T2, T1 in ZS2.
    rd_lo2 ZS2 96%nat. zstep. zs. zstep. unfold zx16. clear ZS2 RD.
    call (putShortMSB_spec L X2 (Z.land (cs_adler (ds_strm X)) 65535) (bv_unsigned (wz (cs_adler (ds_strm X))) mod 2^16) lo).
    1:{ exact DR2. } 1:{ exact MI2. } 1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ lia. } 1:{ lia. }
    1:{ change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (cs_adler (ds_strm X)) (2^16) ltac:(lia)). lia. }
    1:{ rewrite unsigned_lit by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
        apply Z.mod_small. pose proof (Z.mod_pos_bound (cs_adler (ds_strm X)) (2^16) ltac:(lia)). lia. }
    1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mB3.
    lazymatch goal with H : DREP mB3 L _ |- _ => rename H into DR3 end.
    lazymatch goal with H : mem_inv usegs mB3 |- _ => rename H into MI3 end.
    remember (putShortMSB X2 (Z.land (cs_adler (ds_strm X)) 65535)) as X3 eqn:EX3.
    destruct (X1F X2 (Z.land (cs_adler (ds_strm X)) 65535)) as (S3 & P3 & T3 & B3). rewrite <- EX3 in S3, P3, T3, B3.
    assert (EQ3 : X3 = put_adler (put_byte (put_byte X 120) 187)).
    { rewrite EX3, EX2, EX1. unfold put_adler. cbv zeta.
      change (cs_adler (ds_strm (put_byte (put_byte X 120) 187))) with (cs_adler (ds_strm X)).
      change (putShortMSB X 30907) with (put_byte (put_byte X 120) 187). reflexivity. }
    eapply (C_F7C X3); [rewrite EH, <- EQ3; reflexivity| rewrite B3, B2, B1; exact LBS| rewrite T3, T2; exact T1|].
    split; [exact DR3|]. split; [rewrite T3, T2, T1; apply (dout_munch _ m' mB3 L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
    split; [rewrite T3, T2, T1; exact ROOM|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI3].
Qed.
End HDR.
End Z_defl_hdr.


Module Z_defl_blocks.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_defl_model.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflSlow6 DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe.
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
  din_tie inp X -> slow_safe X flush -> Z_defl_iface.sbs_ok (lz_fuel X) X flush -> slow_fe X flush ->
  ds_w_size X = 32768 -> ds_hash_size X = 32768 -> ds_lit_bufsize X = 16384 -> ds_insert X = 0 -> ds_wrap X = 1 ->  (* 1.4: was <> 2; deflate_slow needs wrap <> 0 *)
  cs_avail_in (ds_strm X) <= 1 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  snd (deflate_slow X flush) <> block_done ->
  0 <= cs_avail_out (ds_strm (blk_s2 X flush)) < 2^31 ->
  Box (length (cs_out_rev (ds_strm (fst (deflate_slow X flush)))) <= length rest0)%nat ->
  (snd (deflate_slow X flush) = need_more \/ snd (deflate_slow X flush) = finish_started ->
   cs_avail_out (ds_strm (blk_s2 X flush)) = 0 -> DKL L flush rest0 lo r F fc me Q (blk_s2 X flush)) ->
  (snd (deflate_slow X flush) = need_more \/ snd (deflate_slow X flush) = finish_started ->
   cs_avail_out (ds_strm (blk_s2 X flush)) <> 0 -> DKE L rest0 lo r F fc me Q (wz 0) (blk_s2 X flush)) ->
  (snd (deflate_slow X flush) = finish_done -> DKS L flush rest0 lo r F fc me Q 0x17ed8 (blk_s2 X flush)) ->
  DK L flush rest0 lo r F fc me Q 0x17d30 X.
Proof.
  intros Q X HFL LV SG TIE SAFE SBS SFE WS HS LBS INS WR RAI RAO NBD RAO2 ROOMF KNM0 KNM1 KFD.
  unfold DK. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI). rename m' into m.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp.
  assert (RL : relro_clean m) by (apply (defl_relro L inp rest0 lo r me CTX); exact MU).
  pose proof (cfg6_cell m RL) as CFG. unfold Z_CFG6_FUNC, Z_DEFLATE_SLOW in CFG.
  assert (DINm : din m L inp) by (apply (defl_din L inp rest0 lo r me CTX); exact MU).
  pose proof DR as DR0. destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  assert (RLV : - 2^31 <= ds_level X < 2^31) by lia. assert (RSG : - 2^31 <= ds_strategy X < 2^31) by lia.
  zs. rewrite LV. zstep. closed_br. zs. rewrite SG. zs. zstep. closed_br. zs. zstep. closed_br.
  zs. zstep. closed_br. zs. zs. zs. zs. zstep. closed_br. zs. zs. zs. zs.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
  clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend CFG.
  zs.
  call (HSLOW L X flush inp rest0 lo).
  1:{ exact DR0. } 1:{ exact DINm. } 1:{ exact TIE. } 1:{ exact DOUT. } 1:{ exact MI. } 1:{ exact RL. } 1:{ rewrite ESP. exact STK. }
  1:{ rewrite ESP. unfold Z_SLOW_STACK. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact IO. } 1:{ exact SAFE. } 1:{ exact HFL. } 1:{ exact WS. } 1:{ exact HS. } 1:{ exact LBS. } 1:{ exact INS. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  1:{ exact RAI. } 1:{ exact RAO. } 1:{ exact (unbox _ ROOMF). } 1:{ exact SBS. } 1:{ exact SFE. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem mA.
  lazymatch goal with H : stk usegs mA _ _ |- _ => rewrite ?ESP in H; rename H into STKA end.
  lazymatch goal with H : DREP mA L _ |- _ => rename H into DRA end.
  lazymatch goal with H : dout mA L _ _ |- _ => rename H into DOA end.
  lazymatch goal with H : mem_inv usegs mA |- _ => rename H into MIA end.
  assert (C_C90 : forall (s2 : deflate_state) (z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word) (mm : mem),
    DINV L rest0 lo r me s2 mm -> 0 <= cs_avail_out (ds_strm s2) < 2^31 ->
    (cs_avail_out (ds_strm s2) = 0 -> DKL L flush rest0 lo r F fc me Q s2) ->
    (cs_avail_out (ds_strm s2) <> 0 -> DKE L rest0 lo r F fc me Q (wz 0) s2) ->
    evt usegs Q (MS (deflR L flush r z1 z5 z6 z7 (wz (dl_S L)) z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31)
                    F (wz 0x17e00) fc None mm (seg_rom usegs))).
  { intros s2 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 mm DI2 RA2 K0 K1.
    pose proof DI2 as DI0. destruct DI2 as (DR2 & _). destruct DR2 as [ZS2 _]. open_zs ZS2.
    unfold deflR. zs. zstep. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia.
    - zs. zstep. unfold DKE, Z_DEFL_EPI in K1. eapply (K1 ltac:(lia)). exact DI0.
    - unfold DKL, DK, Z_DEFL_LF, deflR in K0. eapply (K0 ltac:(lia)). exact DI0. }
  unfold blk_s2 in *.
  destruct (deflate_slow X flush) as [X1 b] eqn:EDS. cbn [fst snd] in DRA, DOA, KNM0, KNM1, KFD, NBD, RAO2, ROOMF |- *.
  assert (DIA : DINV L rest0 lo r me X1 mA).
  { split; [exact DRA|]. split; [exact DOA|]. split; [exact ROOMF|]. split; [eexists; exact FR|]. split; [exact STKA|]. split; [exact MU|]. split; [exact WM| exact MIA]. }
  destruct b; cbn [bs_code block_state_eqb orb] in KNM0, KNM1, KFD, RAO2 |- *.
  -
    do 4 zs. zstep. closed_br. zs. zstep. closed_br.
    eapply (C_C90 X1); [exact DIA| exact RAO2| apply KNM0; left; reflexivity| apply KNM1; left; reflexivity].
  - exfalso. apply NBD. reflexivity.
  -
    destruct DRA as [ZSA STA]. destruct STA as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSA LAYA]. open_A GA.
    pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
    do 4 zs. zstep. closed_br. zs. zs. name_mem mB.
    tr_groups MUf WMf.
    assert (DIB : DINV L rest0 lo r me (set_status X1 FINISH_STATE) mB).
    { split; [split|].
      - exact ZSA.
      - constructor; [do 5 eexists; unfold dsA_cells, FINISH_STATE; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSA | exact LAYA].
      - split; [dsred; apply (dout_munch _ mA mB L rest0 _ DOA ROOMF MUf WMf); cbn [disjoint_from]; slia|].
        split; [exact ROOMF|]. split; [eexists; exact FR|]. split; [exact STKA|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    zs. zstep. closed_br.
    eapply (C_C90 (set_status X1 FINISH_STATE)); [exact DIB| exact RAO2| apply KNM0; right; reflexivity| apply KNM1; right; reflexivity].
  -
    destruct DRA as [ZSA STA]. destruct STA as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSA LAYA]. open_A GA.
    pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
    do 4 zs. zstep. closed_br. zs. zs. name_mem mB.
    tr_groups MUf WMf.
    assert (DIB : DINV L rest0 lo r me (set_status X1 FINISH_STATE) mB).
    { split; [split|].
      - exact ZSA.
      - constructor; [do 5 eexists; unfold dsA_cells, FINISH_STATE; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSA | exact LAYA].
      - split; [dsred; apply (dout_munch _ mA mB L rest0 _ DOA ROOMF MUf WMf); cbn [disjoint_from]; slia|].
        split; [exact ROOMF|]. split; [eexists; exact FR|]. split; [exact STKA|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    zs. zstep. closed_br. zs. zs. zstep. closed_br.
    unfold DKS, deflR in KFD. eapply (KFD eq_refl). exact DIB.
Qed.

Lemma defl_blk98 : forall (Q : machine_state -> Prop) (X : deflate_state),
  (flush = 0 \/ flush = 4) -> cs_avail_in (ds_strm X) = 0 -> 0 <= ds_lookahead X < 2^31 -> 0 <= ds_status X < 1000 ->
  (negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)) = true -> DK L flush rest0 lo r F fc me Q 0x17d30 X) ->
  (negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)) = false -> flush = 0 -> DKE L rest0 lo r F fc me Q (wz 0) X) ->
  (negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)) = false -> flush <> 0 -> DKS L flush rest0 lo r F fc me Q 0x17ed8 X) ->
  DKS L flush rest0 lo r F fc me Q 0x17d28 X.
Proof.
  intros Q X HFL AI0 RLA RST KRUN KOK KFIN. unfold DKS. intros until m'. intros DI.
  pose proof DI as DI0. destruct DI as (DR & _). destruct DR as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
  unfold deflR. unfold Z_NO_FLUSH, FINISH_STATE in *.
  assert (RSTs : - 2^31 <= ds_status X < 2^31) by lia.
  zs. zstep. if_cases KLA; zify_cond KLA; rewrite ?unsigned_lit in KLA by lia.
  -
    replace (ds_lookahead X =? 0) with true in * by (symmetry; apply Z.eqb_eq; lia). cbn [negb orb] in *.
    zstep. if_cases KF0; zify_cond KF0; rewrite ?unsigned_lit in KF0 by lia.
    + assert (F0 : flush = 0) by lia. replace (flush =? 0) with true in * by (symmetry; apply Z.eqb_eq; lia). cbn [negb andb] in *.
      zs. zstep. unfold DKE, Z_DEFL_EPI in KOK. eapply (KOK eq_refl F0). exact DI0.
    + assert (F4 : flush <> 0) by lia. replace (flush =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb] in *.
      zs. zs. zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia.
      * replace (ds_status X =? 666) with false in * by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in *.
        unfold DK, deflR in KRUN. eapply (KRUN eq_refl). exact DI0.
      * replace (ds_status X =? 666) with true in * by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in *.
        zstep. unfold DKS, deflR in KFIN. eapply (KFIN eq_refl F4). exact DI0.
  - replace (ds_lookahead X =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb] in *.
    unfold DK, deflR in KRUN. eapply (KRUN eq_refl). exact DI0.
Qed.

Lemma defl_blk90 : forall (Q : machine_state -> Prop) (X : deflate_state),
  0 <= cs_avail_in (ds_strm X) <= 1 ->
  (cs_avail_in (ds_strm X) <> 0 -> DK L flush rest0 lo r F fc me Q 0x17d30 X) ->
  (cs_avail_in (ds_strm X) = 0 -> DKS L flush rest0 lo r F fc me Q 0x17d28 X) ->
  DK L flush rest0 lo r F fc me Q 0x17d18 X.
Proof.
  intros Q X RAI KRUN K98. unfold DK. intros until m'. intros DI.
  pose proof DI as DI0. destruct DI as (DR & _). destruct DR as [ZS _]. open_zs ZS.
  unfold deflR. zstep. zs. zstep. zstep. if_cases KAI; zify_cond KAI; rewrite ?unsigned_lit in KAI by lia.
  - unfold DK, deflR in KRUN. eapply (KRUN ltac:(lia)). exact DI0.
  - unfold DKS, deflR in K98. eapply (K98 ltac:(lia)). exact DI0.
Qed.
End BLOCKS.
End Z_defl_blocks.


Module Z_defl_fin.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_defl_model.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_flushpend Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_putmsb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_flushpend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate SendModel FillWinModel DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe.
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
  DKS L flush rest0 lo r F fc me Q 0x17ed8 X.
Proof.
  intros Q X HFL RW W2 TRL KOK KEND KT1 KT0. unfold DKS. intros until m'. intros DI.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold deflR. unfold DKE, Z_DEFL_EPI in KOK, KEND, KT1, KT0.
  zs. zstep. if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia.
  -
    assert (F4 : flush = 4) by lia. specialize (KEND F4). specialize (KT1 F4). specialize (KT0 F4). specialize (TRL F4). clear KOK KF.
    pose proof DI as DI0. destruct DI as (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
    pose proof DR as DR0. destruct DR as [ZS ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY1]. open_zs ZS. open_A GA.
    lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
    unfold defl_frame in FR. unfold defl_W in MU.
    assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
    assert (HW : ds_wrap X = -2 \/ ds_wrap X = -1 \/ ds_wrap X = 0 \/ ds_wrap X = 1) by lia.
    assert (RWs : - 2^31 <= ds_wrap X < 2^31) by lia.
    zs.
    destruct HW as [EW|[EW|[EW|EW]]]; rewrite EW; zstep; closed_br.
    1,2,3: zs; zstep; eapply (KEND ltac:(lia)); exact DI0.
    assert (WP : 0 < ds_wrap X) by lia. specialize (KT1 WP). specialize (KT0 WP). destruct (TRL WP) as (RP0 & RP4 & RAD & LBS & RAO & FPOK & EWR & RPF & ROOMF).
    clear KEND TRL.
    pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + 65536)] m') as MUf. pose proof (wmono_refl usegs m') as WMf.
    zs. zs. zstep. closed_br. zstep. zstep. zs. zstep.
    clear GA ZS.
    assert (X1F : forall Y b, ds_pending (putShortMSB Y b) = ds_pending Y + 1 + 1 /\ ds_strm (putShortMSB Y b) = ds_strm Y
                              /\ ds_lit_bufsize (putShortMSB Y b) = ds_lit_bufsize Y /\ ds_wrap (putShortMSB Y b) = ds_wrap Y).
    { intros Y b. unfold putShortMSB, put_byte. dsred. repeat split; reflexivity. }
    call (putShortMSB_spec L X (wrap32 (Z.shiftr (cs_adler (ds_strm X)) 16)) (bv_swrap 32 (Z.shiftr (cs_adler (ds_strm X)) 16 + 0)) lo).
    1:{ exact DR0. } 1:{ exact MI. } 1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ lia. } 1:{ lia. }
    1:{ apply wrap32_range. } 1:{ rewrite swrap32_mod32, Z.add_0_r, wrap32_mod. reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mB.
    lazymatch goal with H : DREP mB L _ |- _ => rename H into DR1 end.
    lazymatch goal with H : mem_inv usegs mB |- _ => rename H into MI1 end.
    remember (putShortMSB X (wrap32 (Z.shiftr (cs_adler (ds_strm X)) 16))) as X1 eqn:EX1.
    destruct (X1F X (wrap32 (Z.shiftr (cs_adler (ds_strm X)) 16))) as (P1 & T1 & B1 & W1). rewrite <- EX1 in P1, T1, B1, W1.
    pose proof DR1 as DR1'. destruct DR1' as [ZS1 _]. open_zs ZS1. rewrite T1 in ZS1.
    rd_lo2 ZS1 96%nat. zstep. zs. zstep. unfold zx16. clear ZS1 RD.
    call (putShortMSB_spec L X1 (Z.land (cs_adler (ds_strm X)) 65535) (bv_unsigned (wz (cs_adler (ds_strm X))) mod 2^16) lo).
    1:{ exact DR1. } 1:{ exact MI1. } 1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ lia. } 1:{ lia. }
    1:{ change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (cs_adler (ds_strm X)) (2^16) ltac:(lia)). lia. }
    1:{ rewrite unsigned_lit by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
        apply Z.mod_small. pose proof (Z.mod_pos_bound (cs_adler (ds_strm X)) (2^16) ltac:(lia)). lia. }
    1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mB2.
    lazymatch goal with H : DREP mB2 L _ |- _ => rename H into DR2 end.
    lazymatch goal with H : mem_inv usegs mB2 |- _ => rename H into MI2 end.
    assert (EPA : putShortMSB X1 (Z.land (cs_adler (ds_strm X)) 65535) = put_adler X) by (rewrite EX1; reflexivity).
    rewrite EPA in DR2.
    destruct (X1F X1 (Z.land (cs_adler (ds_strm X)) 65535)) as (P2 & T2 & B2 & Wr2). rewrite EPA in P2, T2, B2, Wr2.
    assert (DOUT2 : dout mB2 L rest0 (ds_strm (put_adler X))).
    { rewrite T2, T1. apply (dout_munch _ m' mB2 L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia. }
    clear MUf WMf DR0 DR1 EX1 X1F.
    zs. zstep.
    call (flush_pending_spec HTFB L (put_adler X) rest0 (zlength inp) lo).
    1:{ exact DR2. } 1:{ exact DOUT2. } 1:{ exact MI2. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
    1:{ exact IO. } 1:{ exact FPOK. } 1:{ rewrite B2, B1, LBS. reflexivity. }
    1:{ rewrite T2, T1. exact RAO. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. }
    name_mem mD.
    lazymatch goal with H : stk usegs mD _ _ |- _ => rewrite ?ESP in H; rename H into STKF end.
    lazymatch goal with H : DREP mD L _ |- _ => rename H into DRF end.
    lazymatch goal with H : dout mD L _ _ |- _ => rename H into DOF end.
    lazymatch goal with H : mem_inv usegs mD |- _ => rename H into MIF end.
    clear P2 T2 B2 Wr2 P1 T1 B1 W1 EPA DR2 DOUT2.
    revert DRF DOF EWR RPF ROOMF KT1 KT0. generalize (flush_pending (put_adler X)). intros s2 DRF DOF EWR RPF ROOMF KT1 KT0.
    destruct DRF as [ZSF STF]. destruct STF as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSF LAYF]. open_A GA.
    pose proof (munch_refl [(dl_As L, dl_As L + 212)] mD) as MUf. pose proof (wmono_refl usegs mD) as WMf.
    assert (RW2 : - 2^31 <= ds_wrap s2 < 2^31) by lia.
    zs. rewrite EWR, EW. zstep. closed_br. zs. zs. name_mem mE.
    tr_groups MUf WMf.
    assert (DIE : DINV L rest0 lo r me (set_wrap s2 (- ds_wrap s2)) mE).
    { split; [split|].
      - exact ZSF.
      - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSF | exact LAYF].
      - split; [dsred; apply (dout_munch _ mD mE L rest0 _ DOF ROOMF MUf WMf); cbn [disjoint_from]; slia|].
        split; [exact ROOMF|]. split; [eexists; exact FR|]. split; [exact STKF|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    zs.
    destruct (Z.eq_dec (ds_pending s2) 0) as [P0|PN].
    + rewrite P0. zstep. change (Z.b2z (0 <? 1)) with 1. zstep. eapply (KT1 P0). exact DIE.
    + zstep. replace (ds_pending s2 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). change (Z.b2z false) with 0.
      zstep. eapply (KT0 PN). exact DIE.
  - zs. zstep. eapply (KOK ltac:(lia)). exact DI.
Qed.
End FIN.
End Z_defl_fin.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_path OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_entry OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_arms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_pend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_hdr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_blocks OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl.Z_defl_fin.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflSlow6 DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition deflate_in_stmt : Prop :=
  forall (L : dlay) (d : deflate_state) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L d -> din m L inp -> dout m L rest0 (ds_strm d) -> mem_inv usegs m -> relro_clean m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_DEFLATE_IN_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) -> dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
  defl_path inp flush (deflate_core d flush) d ->
  (length (cs_out_rev (ds_strm (fst (deflate_core d flush)))) <= length rest0)%nat ->
  a0 = wz (dl_S L) -> a1 = wz flush ->
  evt usegs (deflate_in_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (fst (deflate_core d flush)) (snd (deflate_core d flush)) inp rest0 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_DEFLATE_PC) fc None m (seg_rom usegs)).

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
Proof. intros X ER. apply (defl_lf L inp rest0 lo r F fc me CTX flush). exact (EXIT _ _ ER). Qed.

Lemma asm_fin : forall X, fin_path flush R X -> DKS L flush rest0 lo r F fc me Q 0x17ed8 X.
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

Lemma asm_run : forall X, blocks_path inp flush R X -> blk_cond X flush = true -> DK L flush rest0 lo r F fc me Q 0x17d30 X.
Proof.
  intros X (OL & RAI & RLA & RST & PT & _) HC.
  destruct (PT HC) as (LV & SG & TIE & SAFE & SBS & SFE & WS & HS & LBS & INS & W2 & RAO & NBD & RAO2 & OL1 & E0 & E1 & KF).
  apply (defl_run L flush inp rest0 lo r F fc me CTX HSLOW Q X HFL LV SG TIE SAFE SBS SFE WS HS LBS INS W2 (proj2 RAI) RAO NBD RAO2 (room_of_ole _ OL1)).
  - intros Hb A0. exact (asm_lf _ (E0 Hb A0)).
  - intros Hb AN. exact (EXIT _ _ (E1 Hb AN)).
  - intros Hb. exact (asm_fin _ (KF Hb)).
Qed.

Lemma asm_blk98 : forall X, blocks_path inp flush R X -> cs_avail_in (ds_strm X) = 0 -> DKS L flush rest0 lo r F fc me Q 0x17d28 X.
Proof.
  intros X BP A0. pose proof BP as (OL & RAI & RLA & RST & PT & PF).
  assert (EC : blk_cond X flush = negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)))
    by (unfold blk_cond; rewrite A0; reflexivity).
  apply (defl_blk98 L flush rest0 lo r F fc me Q X HFL A0 RLA RST).
  - intros C. apply (asm_run X BP). rewrite EC. exact C.
  - intros C F0. destruct (PF ltac:(rewrite EC; exact C)) as (_ & _ & _ & E0 & _). exact (EXIT _ _ (E0 ltac:(lia))).
  - intros C FN. apply asm_fin. apply PF. rewrite EC. exact C.
Qed.

Lemma asm_blk90 : forall X, blocks_path inp flush R X -> DK L flush rest0 lo r F fc me Q 0x17d18 X.
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
  defl_path inp flush R d -> DREP me L d -> dout me L rest0 (ds_strm d) -> stk usegs me lo (bv_unsigned (r_sp r)) -> mem_inv usegs me ->
  evt usegs Q (MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) (wz (dl_S L)) (wz flush) a2 a3 a4 a5 a6 a7
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
                  F (wz Z_DEFLATE_PC) fc None me (seg_rom usegs)).
Proof.
  intros until t6. intros PATH DR DOUT STK MI. cbv zeta in PATH. destruct PATH as (OL & HST & RAI & RNI & PERR & POK).
  apply (defl_entry L inp rest0 lo r F fc me CTX Q d flush t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 DR DOUT (room_of_ole _ OL) STK MI HST HFL RAI RNI).
  - intros C. exact (EXIT _ _ (PERR C)).
  - intros NE. destruct (POK NE) as (RAO & RLF & RP & LBS & EBUF & PGO).
    assert (RST : 0 <= ds_status d < 1000) by lia.
    intros y1 y5 y6 y7 y12 y15 y16 y17 y28 y29 y30 y31 m' DI.
    apply (defl_pend L flush inp rest0 lo r F fc me CTX HTFB Q d y1 y5 y6 y7 y12 y15 y16 y17 y28 y29 y30 y31 m' DI HFL RAO RAI RLF RP LBS RST).
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
    intros y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 m' DI.
    eapply evt_mono; [exact (defl_epi L inp rest0 lo r F fc m CTX X (wz rc) y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 m' DI)|].
    intros ms' P. unfold deflate_in_post. rewrite Z_to_bv_mod64. exact P. }
  exact (asm_top L flush inp rest0 lo r F fc m CTX HSLOW HTFB HFL R _ EXIT ROOM d t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 PATH DR DOUT STK MI).
Qed.
End DEFL.
