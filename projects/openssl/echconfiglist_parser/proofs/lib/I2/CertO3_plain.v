(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX CellsX Arr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import InitMem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_SR ECH_Img ECH_Xpres ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C2_stmt ECH_C3_stmt ECH_C4_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom I2Canon I2Mach I2Image I2Run I2Inv I2NodeLib
  I2NodeM I2Start I2Top I2Cert I2CertE I2ImgPlain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require GenO3s0_plain GenO3s1_plain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Definition S_O3 (save : Z) : ssrc :=
  SSrc [(4, RATP); (10, save)]
       [(A_malloc_impl, le8Z P_CRYPTO_malloc ++ le8Z P_CRYPTO_realloc ++ le8Z P_CRYPTO_free);
        (A_mem_inited, [1]);
        (RGOT_SSP, le8Z RSSP_GUARD);
        (A_stopped, [0; 0; 0; 0]);
        (A_base_once, le4Z 2 ++ le4Z 1);
        (A_destructor_key, le4Z 1 ++ le4Z (2 ^ 32 - 1));
        (A_td_tsd, le8Z A_tsd_main);
        (A_keys, le8Z P_nodtor ++ le8Z P_init_thread_destructor ++ le8Z P_nodtor);
        (A_next_key, le4Z 2);
        (A_key_lock, le8Z 0);
        (A_td_cancelbuf, le8Z 0)]
       [(RO_LO, RO_HI); (RELRO_LO, RGOT_SSP); (RGOT_SSP + 8, RELRO_HI);
        (A_err_string_once, A_defctx_inited); (A_tevent_once, A_tevent_once + 16);
        (A_load_strings_once, A_load_strings_once + 8); (A_optsdone, A_optsdone + 8);
        (A_td_tsd_used, A_td_tsd_used + 1); (A_keys + 24, A_keys + 32); (A_key_lock + 8, A_key_lock + 16);
        (A_tsd_main + 8, A_tsd_main + 16); (A_tsd_main + 24, A_tsd_main + 32)]
       [(RERRNO, 4, 30%uint63); (RSSP_GUARD, 8, 32%uint63); (A_optsdone_lock, 8, 31%uint63)].

(* [comment removed for export] *)
Definition xregs_of3 (errv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (i : Z) : word :=
  nth (Z.to_nat i) [errv; ra; sp; gp; tp; t0; t1; t2; s0; s1; a0; a1; a2; a3; a4; a5; a6; a7; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] w0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma chk0_K : K_ok GenO3s0_plain.K = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_roc : K_roc_ok GenO3s0_plain.K = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_code_some : match build_code rsegs GenO3s0_plain.pcs with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_code : code_ok rsegs GenO3s0_plain.code.
Proof.
  unfold GenO3s0_plain.code_. pose proof chk0_code_some as Hs.
  destruct (build_code rsegs GenO3s0_plain.pcs) as [C|] eqn:E; [|discriminate Hs]. exact (build_code_ok rsegs GenO3s0_plain.pcs C E).
Qed.
Lemma chk0_run : i2_check IM GenO3s0_plain.code GenO3s0_plain.K GenO3s0_plain.fuel GenO3s0_plain.st0 GenO3s0_plain.X = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_shape : start_shape_ok GenO3s0_plain.K IMX GenO3s0_plain.st0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_ho : ho_check2 IMX GenO3s0_plain.facts0 GenO3s0_plain.d0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_tags : forallb (fact_tags_lt GenO3s0_plain.n0) GenO3s0_plain.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_facts : forallb (fact_ok GenO3s0_plain.K GenO3s0_plain.d0 (S_O3 0)) GenO3s0_plain.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_xw : xw_in GenO3s0_plain.K ERR_X = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma chk1_K : K_ok GenO3s1_plain.K = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk1_roc : K_roc_ok GenO3s1_plain.K = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk1_code_some : match build_code rsegs GenO3s1_plain.pcs with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk1_code : code_ok rsegs GenO3s1_plain.code.
Proof.
  unfold GenO3s1_plain.code_. pose proof chk1_code_some as Hs.
  destruct (build_code rsegs GenO3s1_plain.pcs) as [C|] eqn:E; [|discriminate Hs]. exact (build_code_ok rsegs GenO3s1_plain.pcs C E).
Qed.
Lemma chk1_run : i2_check IM GenO3s1_plain.code GenO3s1_plain.K GenO3s1_plain.fuel GenO3s1_plain.st0 GenO3s1_plain.X = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk1_shape : start_shape_ok GenO3s1_plain.K IMX GenO3s1_plain.st0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk1_ho : ho_check2 IMX GenO3s1_plain.facts0 GenO3s1_plain.d0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk1_tags : forallb (fact_tags_lt GenO3s1_plain.n0) GenO3s1_plain.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk1_facts : forallb (fact_ok GenO3s1_plain.K GenO3s1_plain.d0 (S_O3 1)) GenO3s1_plain.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk1_xw : xw_in GenO3s1_plain.K ERR_X = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Section C.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HHx : heap_sr_hyps_x H.
  Let HH : heap_sr_hyps H := proj1 HHx.

  (* [comment removed for export] *)
  Lemma S_O3_holds : forall (x : Z -> word) m s LB (errv : word) (cx : ctxinfo) (save : Z),
    hs_RHEAP H s LB m -> x 4 = Z_to_bv 64 RATP -> x 10 = Z_to_bv 64 save -> IMPL_mem m -> MEMFLAG m 1 -> mem_inv rsegs m -> relro_lib m ->
    ERR_fresh_core m -> CTX_keys m -> CTX_statics m cx -> rw_cells rsegs m RERRNO [C4 errv] ->
    ssrc_holds (S_O3 save) x [(30%uint63, errv); (32%uint63, wz (hs_canary H)); (31%uint63, wz (cx_olock cx))] m.
  Proof.
    intros x m s LB errv cx save Hheap Htp Ha0 Himpl Hmf Hinv Hrelro Hfresh Hkeys Hctx Herr.
    pose proof HHx as (_ & _ & _ & _ & Hst & _). destruct (Hst _ _ _ Hheap) as (_ & Hgot & _ & Hcan).
    destruct Hfresh as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    destruct Hkeys as (K1 & K2 & K3).
    destruct Hctx as (Cs1 & Cs2 & Cs3 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10 & Cs11 & Cs12).
    unfold ssrc_holds, S_O3. cbn [s_cregs s_vals s_clear s_words fst snd].
    split; [|split; [|split]].
    - constructor; [exact Htp | constructor; [exact Ha0 | constructor]].
    - constructor. { eapply schunk_of_rw_cells; [exact Himpl|]. vm_compute. reflexivity. }
      constructor.
      { destruct Hmf as (fb & Hrw & Hfb & _). intros i Hi. destruct i as [|i]; [|cbn in Hi; slia]. cbn [nth].
        destruct Hrw as [[_ (_ & _ & HB)] _]. cbn [cells_bytes cbytes app length] in HB. rewrite (HB 0%nat ltac:(slia)). cbn [nth_error].
        f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hfb. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Hgot|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Cs8|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Cs10|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Cs6|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Cs4|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Cs12|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact K1|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact K2|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact K3|]. vm_compute. reflexivity. }
      constructor.
    - unfold relro_lib in Hrelro.
      unfold RO_LO, RO_HI, RELRO_LO, RELRO_HI, RGOT_SSP, A_err_string_once, A_defctx_inited, A_tevent_once, A_load_strings_once, A_optsdone,
        A_td_tsd_used, A_keys, A_key_lock, A_tsd_main in *.
      unfold none_on in *.
      constructor. { intros a Ha. cbn in Ha. apply mem_inv_ro_none; [exact Hinv | slia | slia]. }
      constructor. { intros a Ha. cbn in Ha. apply Hrelro; slia. }
      constructor. { intros a Ha. cbn in Ha. apply Hrelro; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F1; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F2; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F3; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F4; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F5; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F6; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F7; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F8; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F9; slia. }
      constructor.
    - constructor; [exact (sword_of_C4 m RERRNO errv Herr)|]. constructor; [exact (sword_of_C8 m RSSP_GUARD _ Hcan) |].
      constructor; [|constructor].
      exact (sword_of_C8 m A_optsdone_lock _ (proj1 (proj1 (rw_cells_app rsegs m A_optsdone_lock [C8 (wz (cx_olock cx))] [C8 (wz (cx_ilock cx))]) Cs11))).
  Qed.

  Theorem egs_fresh_cert : egs_fresh_stmt H.
  Proof.
    unfold egs_fresh_stmt, egs_stmt_for.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB cx save lo B errv
           Ha0 Hsave Hs01 Hheap Hkrel Hby Hcnt Hbig Haux HB Hsp16 Hstk Hhl Hlo Herr Hinv Htp Hmf Himpl Hgot Hrelro Herrph Herrx Hbelow Hctx Hra.
    change (blocks_ERRST errst_zero) with (@nil block) in *. cbn [app] in Hheap, Hby, Hcnt, Hbig.
    cbn [errph_bytes errph_cnt errph_big errph_stack ERRPH CTXPH] in Hby, Hcnt, Hbig, Hlo, Herrph, Hctx.
    unfold ERRINIT_BYTES, ERRINIT_CNT, ERRINIT_BIG, ERRINIT_STACK, FR_ossl_err_get_state_int, RREALLOC_STACK, RMALLOC_STACK in Hby, Hcnt, Hbig, Hlo.
    destruct Herrph as [Hfresh Hkeys]. destruct Hctx as [Hstat Hblk].
    set (x := xregs_of3 errv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
    set (W := [(30%uint63, errv); (32%uint63, wz (hs_canary H)); (31%uint63, wz (cx_olock cx))]).
    pose proof HHx as (_ & _ & _ & Hrx & _ & _).
    destruct (Hrx _ _ Haux) as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & sec & _ & _ & _ & _ & HBav & Hav & _).
    assert (HB64 : B < 2 ^ 64) by (clear - HBav Hav; slia).
    assert (Hsp63 : bv_unsigned (x 2) < 2 ^ 63) by (clear - HBav Hav HB; change (x 2) with sp; slia).
    clear HBav Hav av x3 x4 x5 x16 x6 x11 x12 x23 rnd sec Hrx.
    change (bv_unsigned sp) with (bv_unsigned (x 2)) in HB, Hsp16, Hstk, Hlo.
    assert (Etp : x 4 = Z_to_bv 64 RATP) by exact Htp.
    assert (Eerr : bv_unsigned tp + -164 = RERRNO).
    { rewrite Htp, Z_to_bv_unsigned. vm_compute. reflexivity. }
    rewrite Eerr in Herr.
    assert (Hlo' : lo <= bv_unsigned (x 2) - (48 + (1024 + (64 + 8192)))) by (clear - Hlo; slia).
    change (x 10 = Z_to_bv 64 save) in Ha0.
    destruct (Hs01 eq_refl) as [Es | Es]; rewrite Es in Ha0 |- *; clear Es Hsave Hs01.
    + (* [comment removed for export] *)
      assert (Ea0 : x 10 = Z_to_bv 64 0) by exact Ha0.
      assert (Cc : to_Z (c_cost GenO3s0_plain.K) <= 2 ^ 16) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cn : to_Z (c_cnt GenO3s0_plain.K) <= 1600) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cb : to_Z (c_big GenO3s0_plain.K) <= 2) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cs : to_Z (c_stack GenO3s0_plain.K) = 48 + (1024 + (64 + 8192))) by (vm_compute; reflexivity).
      assert (Hby' : lb_bytes LB + to_Z (c_cost GenO3s0_plain.K) <= hs_LIVE_MAX H) by (clear - Hby Cc; slia).
      assert (Hcnt' : Z.of_nat (length LB) + to_Z (c_cnt GenO3s0_plain.K) <= hs_LIVE_CNT_MAX H) by (clear - Hcnt Cn; slia).
      assert (Hbig' : lb_big LB + to_Z (c_big GenO3s0_plain.K) <= hs_LIVE_BIG_MAX H) by (clear - Hbig Cb; slia).
      assert (Hlo'' : lo <= bv_unsigned (x 2) - to_Z (c_stack GenO3s0_plain.K)) by (clear - Hlo' Cs; slia).
      pose proof (start_Rn GenO3s0_plain.K GenO3s0_plain.d0 (S_O3 0) x W F fc m lo chk0_K
                    (S_O3_holds x m s LB errv cx 0 Hheap Etp Ea0 Himpl Hmf Hinv Hrelro Hfresh Hkeys Hstat Herr)
                    Hstk (conj Hhl Hlo'') Hsp63 Hsp16 IMX GenO3s0_plain.facts0 GenO3s0_plain.n0 IMX_ok IMX_wr_ok chk0_ho chk0_tags chk0_facts) as HRn.
      pose proof (i2_certificate H IMX GenO3s0_plain.K GenO3s0_plain.code chk0_K HHx IMX_ok IMX_wr_ok chk0_code (ro_const_intro H GenO3s0_plain.K HHx chk0_roc)
                    GenO3s0_plain.fuel GenO3s0_plain.st0 GenO3s0_plain.X [] (rho_of GenO3s0_plain.K GenO3s0_plain.d0 x W) x F fc m mo s LB lo B chk0_run chk0_shape eq_refl (List.NoDup_nil _) (Forall_nil _)
                    HRn eq_refl eq_refl Hheap Hkrel Hby' Hcnt' Hbig'
                    Haux HB HB64 Hstk Hhl Hlo'' Hsp16 Herr Hinv) as HC.
      clear HRn.
      match goal with |- hs_SR _ _ ?c => match type of HC with hs_SR _ _ ?c' => replace c with c' by reflexivity end end.
      apply (sr_mono H HH _ _ _ HC). clear HC.
      (* [comment removed for export] *)
      intros k (rho' & st' & ms1 & s' & LB' & G' & Ek & X1 & Hfin & HXR & HXC & HXB & Hsz & Hes).
      set (Q := I2E _ _ _ _ _ _ _ _ _ _ _) in X1.
      assert (HG0 : q_G0 Q = []) by reflexivity.
      assert (HQ : q_rho0 Q = rho_of GenO3s0_plain.K GenO3s0_plain.d0 x W) by reflexivity.
      pose proof (post_magree H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0) as MAG. cbn [q_m0 Q] in MAG.
      pose proof (post_magree_block H IMX GenO3s0_plain.K chk0_K Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0) as MAGB. cbn [q_m0 q_LB0 Q] in MAGB.
      pose proof (post_rw_cells rho' ms1 G' GenO3s0_plain.X HXC) as RWC.
      pose proof (post_blk_rw_cells H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s0_plain.X X1 Hsz HXB) as RWB.
      pose proof (post_blk_arr H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s0_plain.X X1 Hsz HXB) as RWA.
      set (m1 := ms_mem ms1) in *.
      (* [comment removed for export] *)
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_plain.X HXC (of_Z (A_tsd_main + 24)) 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g0 & Hg0 & Rtsd3).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_plain.X HXC (of_Z (A_tsd_main + 8)) 4%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g4 & Hg4 & Rtsd1).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_plain.X HXC (of_Z (A_tevent_once + 8)) 5%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g5 & Hg5 & Rtev).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_plain.X HXC (of_Z (A_err_string_once + 8)) 10%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g10 & Hg10 & Resl).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_plain.X HXC (of_Z (A_err_string_once + 16)) 11%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g11 & Hg11 & Resh).
      destruct (post_blk_ptr0 H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s0_plain.X X1 Hsz HXB 0%uint63 g0 24%uint63 1%uint63 Hg0 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s0_plain.X Hsz _ _ Hg0))); vm_compute; discriminate)) as (g1 & Hg1 & Rmkey).
      destruct (post_blk_ptr0 H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s0_plain.X X1 Hsz HXB 1%uint63 g1 24%uint63 2%uint63 Hg1 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s0_plain.X Hsz _ _ Hg1))); vm_compute; discriminate)) as (g2 & Hg2 & Rsa).
      destruct (post_blk_ptr0 H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s0_plain.X X1 Hsz HXB 2%uint63 g2 0%uint63 3%uint63 Hg2 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s0_plain.X Hsz _ _ Hg2))); vm_compute; discriminate)) as (g3 & Hg3 & Rnodes).
      change (to_Z 0%uint63) with 0 in Rnodes. rewrite Z.add_0_r in Rnodes.
      destruct (blk_of_LBN G' GenO3s0_plain.X Hsz _ _ Hg0) as (In0 & _ & Sz0). destruct (blk_of_LBN G' GenO3s0_plain.X Hsz _ _ Hg1) as (In1 & _ & Sz1).
      destruct (blk_of_LBN G' GenO3s0_plain.X Hsz _ _ Hg2) as (In2 & _ & Sz2). destruct (blk_of_LBN G' GenO3s0_plain.X Hsz _ _ Hg3) as (In3 & _ & Sz3).
      destruct (blk_of_LBN G' GenO3s0_plain.X Hsz _ _ Hg4) as (In4 & _ & Sz4).
      change (nth (Z.to_nat (to_Z 0%uint63)) (x_sizes GenO3s0_plain.X) 0%uint63) with 72%uint63 in Sz0.
      change (nth (Z.to_nat (to_Z 1%uint63)) (x_sizes GenO3s0_plain.X) 0%uint63) with 32%uint63 in Sz1.
      change (nth (Z.to_nat (to_Z 2%uint63)) (x_sizes GenO3s0_plain.X) 0%uint63) with 128%uint63 in Sz2.
      change (nth (Z.to_nat (to_Z 3%uint63)) (x_sizes GenO3s0_plain.X) 0%uint63) with 904%uint63 in Sz3.
      change (nth (Z.to_nat (to_Z 4%uint63)) (x_sizes GenO3s0_plain.X) 0%uint63) with 8%uint63 in Sz4.
      destruct (post_errno H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1) as [errv0 Herr0].
      (* [comment removed for export] *)
      assert (AGR : forall A n, unw_range GenO3s0_plain.K A n = true -> forall cs, Z.of_nat (cells_size cs) = n -> rw_cells rsegs m A cs -> rw_cells rsegs m1 A cs).
      { intros A n Hu cs Hn Hrw. apply (rw_cells_agree (in_range A n) m m1 A cs (MAG A n Hu) Hrw). rewrite Hn. exact (fun a h => h). }
      (* [comment removed for export] *)
      exists (rv rho' (i_F st') 5), (rv rho' (i_F st') 6), (rv rho' (i_F st') 7),
             (rv rho' (i_F st') 11), (rv rho' (i_F st') 12), (rv rho' (i_F st') 13), (rv rho' (i_F st') 14),
             (rv rho' (i_F st') 15), (rv rho' (i_F st') 16), (rv rho' (i_F st') 17),
             (rv rho' (i_F st') 28), (rv rho' (i_F st') 29), (rv rho' (i_F st') 30), (rv rho' (i_F st') 31),
             m1, errv0, s', (LBN G'),
             (mkEC (gblock g0) (gblock g1) (gblock g2) (gblock g3) (gblock g4) (g_addr g10) (g_addr g11) (g_addr g5)).
      assert (Hn0 : forall t : int, (t <? GenO3s0_plain.n0)%uint63 = true -> to_Z t < to_Z (q_n0 Q)) by (intros t Ht; exact (i_ltb_lt _ _ Ht)).
      pose proof (fun kk t r => xreg_entry H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s0_plain.X X1 HXR GenO3s0_plain.d0 x W kk t r HQ) as XE.
      cbn [ec_mkey ec_sa ec_nodes ec_es ec_hands ec_eslock ec_eshash ec_tevreg].
      split.
      { rewrite Ek, (post_regs H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1).
        change (q_F Q) with F. change (q_fc Q) with fc. replace (q_rho0 Q (c_tra GenO3s0_plain.K)) with ra by reflexivity. fold m1.
        rewrite <- (XE 1%uint63 2%uint63 1%uint63 eq_refl eq_refl (Hn0 2%uint63 eq_refl) eq_refl : rv rho' (i_F st') 1 = ra).
        rewrite <- (xreg_sp H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s0_plain.X X1 HXR GenO3s0_plain.d0 x W HQ eq_refl eq_refl : rv rho' (i_F st') 2 = sp).
        rewrite <- (XE 3%uint63 3%uint63 3%uint63 eq_refl eq_refl (Hn0 3%uint63 eq_refl) eq_refl : rv rho' (i_F st') 3 = gp).
        assert (E4 : rv rho' (i_F st') 4 = tp).
        { rewrite (xreg_W st' rho' G' GenO3s0_plain.X HXR 4%uint63 _ eq_refl : rv rho' (i_F st') 4 = _), Htp. apply bv_eq. vm_compute. reflexivity. }
        rewrite <- E4.
        rewrite <- (XE 8%uint63 7%uint63 8%uint63 eq_refl eq_refl (Hn0 7%uint63 eq_refl) eq_refl : rv rho' (i_F st') 8 = s0).
        rewrite <- (XE 9%uint63 8%uint63 9%uint63 eq_refl eq_refl (Hn0 8%uint63 eq_refl) eq_refl : rv rho' (i_F st') 9 = s1).
        assert (E10 : rv rho' (i_F st') 10 = Z_to_bv 64 (blk_addr (gblock g3))).
        { destruct (xreg_New st' rho' G' GenO3s0_plain.X HXR 10%uint63 3%uint63 0%uint63 eq_refl) as (g3' & Hg3' & E).
          rewrite Hg3 in Hg3'. injection Hg3' as <-. change (to_Z 10%uint63) with 10 in E. rewrite E, Z.add_0_r. reflexivity. }
        rewrite <- E10.
        rewrite <- (XE 18%uint63 16%uint63 18%uint63 eq_refl eq_refl (Hn0 16%uint63 eq_refl) eq_refl : rv rho' (i_F st') 18 = s2).
        rewrite <- (XE 19%uint63 17%uint63 19%uint63 eq_refl eq_refl (Hn0 17%uint63 eq_refl) eq_refl : rv rho' (i_F st') 19 = s3).
        rewrite <- (XE 20%uint63 18%uint63 20%uint63 eq_refl eq_refl (Hn0 18%uint63 eq_refl) eq_refl : rv rho' (i_F st') 20 = s4).
        rewrite <- (XE 21%uint63 19%uint63 21%uint63 eq_refl eq_refl (Hn0 19%uint63 eq_refl) eq_refl : rv rho' (i_F st') 21 = s5).
        rewrite <- (XE 22%uint63 20%uint63 22%uint63 eq_refl eq_refl (Hn0 20%uint63 eq_refl) eq_refl : rv rho' (i_F st') 22 = s6).
        rewrite <- (XE 23%uint63 21%uint63 23%uint63 eq_refl eq_refl (Hn0 21%uint63 eq_refl) eq_refl : rv rho' (i_F st') 23 = s7).
        rewrite <- (XE 24%uint63 22%uint63 24%uint63 eq_refl eq_refl (Hn0 22%uint63 eq_refl) eq_refl : rv rho' (i_F st') 24 = s8).
        rewrite <- (XE 25%uint63 23%uint63 25%uint63 eq_refl eq_refl (Hn0 23%uint63 eq_refl) eq_refl : rv rho' (i_F st') 25 = s9).
        rewrite <- (XE 26%uint63 24%uint63 26%uint63 eq_refl eq_refl (Hn0 24%uint63 eq_refl) eq_refl : rv rho' (i_F st') 26 = s10).
        rewrite <- (XE 27%uint63 25%uint63 27%uint63 eq_refl eq_refl (Hn0 25%uint63 eq_refl) eq_refl : rv rho' (i_F st') 27 = s11).
        reflexivity. }
      split; [exact (post_mpres H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
      split.
      { (* [comment removed for export] *)
        split; [exact (post_krel H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
        split; [exact (post_inv H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
        split; [exact (post_stk H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
        split; [exact (post_auxv H IMX GenO3s0_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
        split; [cbn [app]; exact (post_heap H IMX GenO3s0_plain.K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0)|].
        split.
        { destruct Hmf as (fb & Hrw & Hfb & H01). exists fb. split; [|split; [exact Hfb | exact H01]].
          apply (AGR A_mem_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Hrw]. }
        split; [apply (AGR A_malloc_impl 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Himpl]|].
        split; [apply (AGR A_got_CRYPTO_malloc 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Hgot]|].
        intros a Ha Hg. unfold relro_lib in Hrelro.
        destruct (Z_lt_ge_dec a RGOT_SSP) as [Hlt|Hge].
        - rewrite (proj1 (MAG RELRO_LO (RGOT_SSP - RELRO_LO) ltac:(vm_compute; reflexivity) a ltac:(unfold RELRO_LO, RELRO_HI, RGOT_SSP in *; slia)
                            ltac:(unfold in_range, RELRO_LO, RELRO_HI, RGOT_SSP in *; slia))). exact (Hrelro a Ha Hg).
        - rewrite (proj1 (MAG (RGOT_SSP + 8) (RELRO_HI - RGOT_SSP - 8) ltac:(vm_compute; reflexivity) a ltac:(unfold RELRO_LO, RELRO_HI, RGOT_SSP in *; slia)
                            ltac:(unfold in_range, RELRO_LO, RELRO_HI, RGOT_SSP in *; slia))). exact (Hrelro a Ha Hg). }
      split; [rewrite Eerr; exact Herr0|].
      split; [intros Hne; exfalso; exact (Hne eq_refl)|].
      split.
      { (* [comment removed for export] *)
        cbn [errph_delta chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands].
        split; [rewrite (LBN_length G' GenO3s0_plain.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        split; [rewrite (LBN_bytes G' GenO3s0_plain.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        split; [rewrite (LBN_big G' GenO3s0_plain.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        repeat constructor; assumption. }
      pose proof In0 as In0g. pose proof In1 as In1g. pose proof In2 as In2g. pose proof In3 as In3g. pose proof In4 as In4g.
      unfold gblock in In0, In1, In2, In3, In4.
      rewrite Sz0 in In0. rewrite Sz1 in In1. rewrite Sz2 in In2. rewrite Sz3 in In3. rewrite Sz4 in In4.
      split.
      { (* [comment removed for export] *)
        cbn [ERRPH]. unfold ERR_statics, ERR_chain. cbn [ec_mkey ec_sa ec_nodes ec_es ec_hands ec_eslock ec_eshash ec_tevreg chain_blocks].
        unfold gblock. cbn [blk_addr blk_size fst snd]. rewrite Sz0, Sz1, Sz2, Sz3, Sz4.
        change (to_Z 72%uint63) with 72. change (to_Z 32%uint63) with 32. change (to_Z 128%uint63) with 128.
        change (to_Z 904%uint63) with 904. change (to_Z 8%uint63) with 8.
        split.
        - (* [comment removed for export] *)
          split; [apply (RWC (of_Z A_master_once_ret)); vm_compute; reflexivity|].
          split; [exact Rtsd3|].
          split; [apply (AGR A_stopped 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hstat))))))))]|].
          split; [apply (AGR A_base_once 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hstat))))))))))]|].
          split; [apply (RWC (of_Z A_load_strings_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_optsdone)); vm_compute; reflexivity|].
          split.
          { apply (proj2 (rw_cells_app rsegs m1 A_err_string_once [C4 (wz 2); C4 (wz 1)] [C8 (wz (g_addr g10)); C8 (wz (g_addr g11))])).
            split; [apply (RWC (of_Z A_err_string_once)); vm_compute; reflexivity|].
            apply (proj2 (rw_cells_app rsegs m1 _ [C8 (wz (g_addr g10))] [C8 (wz (g_addr g11))])). split; [exact Resl | exact Resh]. }
          split.
          { apply (proj2 (rw_cells_app rsegs m1 A_tevent_once [C4 (wz 2); C4 (wz 1)] [C8 (wz (g_addr g5))])).
            split; [apply (RWC (of_Z A_tevent_once)); vm_compute; reflexivity | exact Rtev]. }
          split; [apply (RWC (of_Z (A_keys + 24))); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_next_key)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_key_lock)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_td_cancelbuf)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_td_tsd_used)); vm_compute; reflexivity|].
          exact Rtsd1.
        - (* [comment removed for export] *)
          split; [apply in_app_iff; left; exact In0|]. split; [reflexivity|].
          split; [exact Rmkey|].
          split; [apply in_app_iff; left; exact In1|]. split; [reflexivity|].
          split.
          { unfold sa_cells. apply (proj2 (rw_cells_app rsegs m1 (g_addr g1) [C4 (wz 1); C4 (wz 0); C8 (wz 0); C8 (wz 1)] [C8 (wz (g_addr g2))])).
            split; [| exact Rsa]. rewrite <- (Z.add_0_r (g_addr g1)). change 0 with (to_Z 0%uint63) at 2.
            apply (RWB 1%uint63 g1 0%uint63 _ Hg1). vm_compute. reflexivity. }
          split; [apply in_app_iff; left; exact In2|]. split; [reflexivity|].
          split; [exact Rnodes|].
          split; [apply in_app_iff; left; exact In3|]. split; [reflexivity|].
          split; [apply in_app_iff; left; exact In4|]. split; [reflexivity|].
          cbn [chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands].
          apply Forall_cons; [exact (post_block_range H IMX GenO3s0_plain.K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 (g_id g0, g_addr g0, 72) ltac:(apply in_app_iff; left; exact In0))|].
          apply Forall_cons; [exact (post_block_range H IMX GenO3s0_plain.K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 (g_id g1, g_addr g1, 32) ltac:(apply in_app_iff; left; exact In1))|].
          apply Forall_cons; [exact (post_block_range H IMX GenO3s0_plain.K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 (g_id g2, g_addr g2, 128) ltac:(apply in_app_iff; left; exact In2))|].
          apply Forall_cons; [exact (post_block_range H IMX GenO3s0_plain.K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 (g_id g3, g_addr g3, 904) ltac:(apply in_app_iff; left; exact In3))|].
          apply Forall_cons; [exact (post_block_range H IMX GenO3s0_plain.K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 (g_id g4, g_addr g4, 8) ltac:(apply in_app_iff; left; exact In4))|].
          apply Forall_nil. }
      split.
      { (* [comment removed for export] *)
        cbn [CTXPH]. destruct Hstat as (Cs1 & Cs2 & Cs3 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10 & Cs11 & Cs12). split.
        - unfold CTX_statics.
          split; [apply (AGR A_defctx_inited 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs1]|].
          split; [apply (AGR A_defctx_exlock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs2]|].
          split; [apply (AGR A_defctx_exmeth_bio 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs3]|].
          split; [apply (AGR A_td_tsd 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs4]|].
          split; [apply (AGR A_tsd_main 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs5]|].
          split; [apply (AGR A_destructor_key 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs6]|].
          split; [apply (AGR A_base_inited 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs7]|].
          split; [apply (AGR A_stopped 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs8]|].
          split; [apply (AGR A_in_init_config_key 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs9]|].
          split; [apply (AGR A_base_once 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs10]|].
          split; [apply (AGR A_optsdone_lock 16 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs11]|].
          apply (AGR A_keys 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs12].
        - destruct Hblk as [(Ein & Esz & Erng & Emut) (po & pi & Hpo & Hpi)]. split.
          + split; [apply in_app_iff; right; exact Ein|]. split; [exact Esz|]. split; [exact Erng|].
            unfold MUTEX in *. apply (rw_cells_agree (in_range (blk_addr (cx_exlock cx)) (blk_size (cx_exlock cx))) m m1 _ _ (MAGB _ Ein ltac:(rewrite Esz; exact Erng)) Emut).
            intros a Ha. unfold in_range in *. rewrite Esz. unfold MUTEX_SIZE. cbn [cells_size csize length Nat.add] in Ha. slia.
          + exists po, pi. split; apply in_app_iff; right; assumption. }
      split.
      { (* [comment removed for export] *)
        unfold gblock. cbn [blk_addr blk_size fst snd].
        unfold ERRST. cbn [es_slots es_top es_bottom errst_zero].
        split; [reflexivity|]. split; [slia|]. split; [slia|].
        cbn [map repeat sl_flags sl_buffer sl_file sl_line sl_func slot_clear]. unfold zero16. cbn [repeat].
        unfold u32arr, u64arr, O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP.
        split. { destruct (RWA 3%uint63 g3 0%uint63 (u32s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1].
                 change (to_Z 0%uint63) with 0 in B1, W1. rewrite Z.add_0_r in B1, W1. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 64%uint63 (u32s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 128%uint63 (u64s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 256%uint63 (u64s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 384%uint63 (u64s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 512%uint63 (u32s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 576%uint63 (u64s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 704%uint63 (u32s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 768%uint63 (u64s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { change 896 with (to_Z 896%uint63). apply (RWB 3%uint63 g3 896%uint63 _ Hg3). vm_compute. reflexivity. }
        repeat (apply Forall_cons; [cbn; repeat split; (slia || reflexivity)|]). apply Forall_nil. }
      (* [comment removed for export] *)
      exact (post_xpres H IMX GenO3s0_plain.K chk0_K Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 ERR_X chk0_xw
               (fun b Hb => HH_RHEAP_block_range H HH _ _ _ b Hheap Hb)).
    + (* [comment removed for export] *)
      assert (Ea0 : x 10 = Z_to_bv 64 1) by exact Ha0.
      assert (Cc : to_Z (c_cost GenO3s1_plain.K) <= 2 ^ 16) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cn : to_Z (c_cnt GenO3s1_plain.K) <= 1600) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cb : to_Z (c_big GenO3s1_plain.K) <= 2) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cs : to_Z (c_stack GenO3s1_plain.K) = 48 + (1024 + (64 + 8192))) by (vm_compute; reflexivity).
      assert (Hby' : lb_bytes LB + to_Z (c_cost GenO3s1_plain.K) <= hs_LIVE_MAX H) by (clear - Hby Cc; slia).
      assert (Hcnt' : Z.of_nat (length LB) + to_Z (c_cnt GenO3s1_plain.K) <= hs_LIVE_CNT_MAX H) by (clear - Hcnt Cn; slia).
      assert (Hbig' : lb_big LB + to_Z (c_big GenO3s1_plain.K) <= hs_LIVE_BIG_MAX H) by (clear - Hbig Cb; slia).
      assert (Hlo'' : lo <= bv_unsigned (x 2) - to_Z (c_stack GenO3s1_plain.K)) by (clear - Hlo' Cs; slia).
      pose proof (start_Rn GenO3s1_plain.K GenO3s1_plain.d0 (S_O3 1) x W F fc m lo chk1_K
                    (S_O3_holds x m s LB errv cx 1 Hheap Etp Ea0 Himpl Hmf Hinv Hrelro Hfresh Hkeys Hstat Herr)
                    Hstk (conj Hhl Hlo'') Hsp63 Hsp16 IMX GenO3s1_plain.facts0 GenO3s1_plain.n0 IMX_ok IMX_wr_ok chk1_ho chk1_tags chk1_facts) as HRn.
      pose proof (i2_certificate H IMX GenO3s1_plain.K GenO3s1_plain.code chk1_K HHx IMX_ok IMX_wr_ok chk1_code (ro_const_intro H GenO3s1_plain.K HHx chk1_roc)
                    GenO3s1_plain.fuel GenO3s1_plain.st0 GenO3s1_plain.X [] (rho_of GenO3s1_plain.K GenO3s1_plain.d0 x W) x F fc m mo s LB lo B chk1_run chk1_shape eq_refl (List.NoDup_nil _) (Forall_nil _)
                    HRn eq_refl eq_refl Hheap Hkrel Hby' Hcnt' Hbig'
                    Haux HB HB64 Hstk Hhl Hlo'' Hsp16 Herr Hinv) as HC.
      clear HRn.
      match goal with |- hs_SR _ _ ?c => match type of HC with hs_SR _ _ ?c' => replace c with c' by reflexivity end end.
      apply (sr_mono H HH _ _ _ HC). clear HC.
      (* [comment removed for export] *)
      intros k (rho' & st' & ms1 & s' & LB' & G' & Ek & X1 & Hfin & HXR & HXC & HXB & Hsz & Hes).
      set (Q := I2E _ _ _ _ _ _ _ _ _ _ _) in X1.
      assert (HG0 : q_G0 Q = []) by reflexivity.
      assert (HQ : q_rho0 Q = rho_of GenO3s1_plain.K GenO3s1_plain.d0 x W) by reflexivity.
      pose proof (post_magree H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0) as MAG. cbn [q_m0 Q] in MAG.
      pose proof (post_magree_block H IMX GenO3s1_plain.K chk1_K Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0) as MAGB. cbn [q_m0 q_LB0 Q] in MAGB.
      pose proof (post_rw_cells rho' ms1 G' GenO3s1_plain.X HXC) as RWC.
      pose proof (post_blk_rw_cells H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s1_plain.X X1 Hsz HXB) as RWB.
      pose proof (post_blk_arr H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s1_plain.X X1 Hsz HXB) as RWA.
      set (m1 := ms_mem ms1) in *.
      (* [comment removed for export] *)
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_plain.X HXC (of_Z (A_tsd_main + 24)) 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g0 & Hg0 & Rtsd3).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_plain.X HXC (of_Z (A_tsd_main + 8)) 4%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g4 & Hg4 & Rtsd1).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_plain.X HXC (of_Z (A_tevent_once + 8)) 5%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g5 & Hg5 & Rtev).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_plain.X HXC (of_Z (A_err_string_once + 8)) 10%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g10 & Hg10 & Resl).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_plain.X HXC (of_Z (A_err_string_once + 16)) 11%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g11 & Hg11 & Resh).
      destruct (post_blk_ptr0 H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s1_plain.X X1 Hsz HXB 0%uint63 g0 24%uint63 1%uint63 Hg0 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s1_plain.X Hsz _ _ Hg0))); vm_compute; discriminate)) as (g1 & Hg1 & Rmkey).
      destruct (post_blk_ptr0 H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s1_plain.X X1 Hsz HXB 1%uint63 g1 24%uint63 2%uint63 Hg1 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s1_plain.X Hsz _ _ Hg1))); vm_compute; discriminate)) as (g2 & Hg2 & Rsa).
      destruct (post_blk_ptr0 H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s1_plain.X X1 Hsz HXB 2%uint63 g2 0%uint63 3%uint63 Hg2 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s1_plain.X Hsz _ _ Hg2))); vm_compute; discriminate)) as (g3 & Hg3 & Rnodes).
      change (to_Z 0%uint63) with 0 in Rnodes. rewrite Z.add_0_r in Rnodes.
      destruct (blk_of_LBN G' GenO3s1_plain.X Hsz _ _ Hg0) as (In0 & _ & Sz0). destruct (blk_of_LBN G' GenO3s1_plain.X Hsz _ _ Hg1) as (In1 & _ & Sz1).
      destruct (blk_of_LBN G' GenO3s1_plain.X Hsz _ _ Hg2) as (In2 & _ & Sz2). destruct (blk_of_LBN G' GenO3s1_plain.X Hsz _ _ Hg3) as (In3 & _ & Sz3).
      destruct (blk_of_LBN G' GenO3s1_plain.X Hsz _ _ Hg4) as (In4 & _ & Sz4).
      change (nth (Z.to_nat (to_Z 0%uint63)) (x_sizes GenO3s1_plain.X) 0%uint63) with 72%uint63 in Sz0.
      change (nth (Z.to_nat (to_Z 1%uint63)) (x_sizes GenO3s1_plain.X) 0%uint63) with 32%uint63 in Sz1.
      change (nth (Z.to_nat (to_Z 2%uint63)) (x_sizes GenO3s1_plain.X) 0%uint63) with 128%uint63 in Sz2.
      change (nth (Z.to_nat (to_Z 3%uint63)) (x_sizes GenO3s1_plain.X) 0%uint63) with 904%uint63 in Sz3.
      change (nth (Z.to_nat (to_Z 4%uint63)) (x_sizes GenO3s1_plain.X) 0%uint63) with 8%uint63 in Sz4.
      destruct (post_errno H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1) as [errv0 Herr0].
      (* [comment removed for export] *)
      assert (AGR : forall A n, unw_range GenO3s1_plain.K A n = true -> forall cs, Z.of_nat (cells_size cs) = n -> rw_cells rsegs m A cs -> rw_cells rsegs m1 A cs).
      { intros A n Hu cs Hn Hrw. apply (rw_cells_agree (in_range A n) m m1 A cs (MAG A n Hu) Hrw). rewrite Hn. exact (fun a h => h). }
      (* [comment removed for export] *)
      exists (rv rho' (i_F st') 5), (rv rho' (i_F st') 6), (rv rho' (i_F st') 7),
             (rv rho' (i_F st') 11), (rv rho' (i_F st') 12), (rv rho' (i_F st') 13), (rv rho' (i_F st') 14),
             (rv rho' (i_F st') 15), (rv rho' (i_F st') 16), (rv rho' (i_F st') 17),
             (rv rho' (i_F st') 28), (rv rho' (i_F st') 29), (rv rho' (i_F st') 30), (rv rho' (i_F st') 31),
             m1, errv, s', (LBN G'),
             (mkEC (gblock g0) (gblock g1) (gblock g2) (gblock g3) (gblock g4) (g_addr g10) (g_addr g11) (g_addr g5)).
      assert (Hn0 : forall t : int, (t <? GenO3s1_plain.n0)%uint63 = true -> to_Z t < to_Z (q_n0 Q)) by (intros t Ht; exact (i_ltb_lt _ _ Ht)).
      pose proof (fun kk t r => xreg_entry H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s1_plain.X X1 HXR GenO3s1_plain.d0 x W kk t r HQ) as XE.
      cbn [ec_mkey ec_sa ec_nodes ec_es ec_hands ec_eslock ec_eshash ec_tevreg].
      split.
      { rewrite Ek, (post_regs H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1).
        change (q_F Q) with F. change (q_fc Q) with fc. replace (q_rho0 Q (c_tra GenO3s1_plain.K)) with ra by reflexivity. fold m1.
        rewrite <- (XE 1%uint63 2%uint63 1%uint63 eq_refl eq_refl (Hn0 2%uint63 eq_refl) eq_refl : rv rho' (i_F st') 1 = ra).
        rewrite <- (xreg_sp H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' GenO3s1_plain.X X1 HXR GenO3s1_plain.d0 x W HQ eq_refl eq_refl : rv rho' (i_F st') 2 = sp).
        rewrite <- (XE 3%uint63 3%uint63 3%uint63 eq_refl eq_refl (Hn0 3%uint63 eq_refl) eq_refl : rv rho' (i_F st') 3 = gp).
        assert (E4 : rv rho' (i_F st') 4 = tp).
        { rewrite (xreg_W st' rho' G' GenO3s1_plain.X HXR 4%uint63 _ eq_refl : rv rho' (i_F st') 4 = _), Htp. apply bv_eq. vm_compute. reflexivity. }
        rewrite <- E4.
        rewrite <- (XE 8%uint63 7%uint63 8%uint63 eq_refl eq_refl (Hn0 7%uint63 eq_refl) eq_refl : rv rho' (i_F st') 8 = s0).
        rewrite <- (XE 9%uint63 8%uint63 9%uint63 eq_refl eq_refl (Hn0 8%uint63 eq_refl) eq_refl : rv rho' (i_F st') 9 = s1).
        assert (E10 : rv rho' (i_F st') 10 = Z_to_bv 64 (blk_addr (gblock g3))).
        { destruct (xreg_New st' rho' G' GenO3s1_plain.X HXR 10%uint63 3%uint63 0%uint63 eq_refl) as (g3' & Hg3' & E).
          rewrite Hg3 in Hg3'. injection Hg3' as <-. change (to_Z 10%uint63) with 10 in E. rewrite E, Z.add_0_r. reflexivity. }
        rewrite <- E10.
        rewrite <- (XE 18%uint63 16%uint63 18%uint63 eq_refl eq_refl (Hn0 16%uint63 eq_refl) eq_refl : rv rho' (i_F st') 18 = s2).
        rewrite <- (XE 19%uint63 17%uint63 19%uint63 eq_refl eq_refl (Hn0 17%uint63 eq_refl) eq_refl : rv rho' (i_F st') 19 = s3).
        rewrite <- (XE 20%uint63 18%uint63 20%uint63 eq_refl eq_refl (Hn0 18%uint63 eq_refl) eq_refl : rv rho' (i_F st') 20 = s4).
        rewrite <- (XE 21%uint63 19%uint63 21%uint63 eq_refl eq_refl (Hn0 19%uint63 eq_refl) eq_refl : rv rho' (i_F st') 21 = s5).
        rewrite <- (XE 22%uint63 20%uint63 22%uint63 eq_refl eq_refl (Hn0 20%uint63 eq_refl) eq_refl : rv rho' (i_F st') 22 = s6).
        rewrite <- (XE 23%uint63 21%uint63 23%uint63 eq_refl eq_refl (Hn0 21%uint63 eq_refl) eq_refl : rv rho' (i_F st') 23 = s7).
        rewrite <- (XE 24%uint63 22%uint63 24%uint63 eq_refl eq_refl (Hn0 22%uint63 eq_refl) eq_refl : rv rho' (i_F st') 24 = s8).
        rewrite <- (XE 25%uint63 23%uint63 25%uint63 eq_refl eq_refl (Hn0 23%uint63 eq_refl) eq_refl : rv rho' (i_F st') 25 = s9).
        rewrite <- (XE 26%uint63 24%uint63 26%uint63 eq_refl eq_refl (Hn0 24%uint63 eq_refl) eq_refl : rv rho' (i_F st') 26 = s10).
        rewrite <- (XE 27%uint63 25%uint63 27%uint63 eq_refl eq_refl (Hn0 25%uint63 eq_refl) eq_refl : rv rho' (i_F st') 27 = s11).
        reflexivity. }
      split; [exact (post_mpres H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
      split.
      { (* [comment removed for export] *)
        split; [exact (post_krel H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
        split; [exact (post_inv H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
        split; [exact (post_stk H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
        split; [exact (post_auxv H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
        split; [cbn [app]; exact (post_heap H IMX GenO3s1_plain.K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0)|].
        split.
        { destruct Hmf as (fb & Hrw & Hfb & H01). exists fb. split; [|split; [exact Hfb | exact H01]].
          apply (AGR A_mem_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Hrw]. }
        split; [apply (AGR A_malloc_impl 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Himpl]|].
        split; [apply (AGR A_got_CRYPTO_malloc 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Hgot]|].
        intros a Ha Hg. unfold relro_lib in Hrelro.
        destruct (Z_lt_ge_dec a RGOT_SSP) as [Hlt|Hge].
        - rewrite (proj1 (MAG RELRO_LO (RGOT_SSP - RELRO_LO) ltac:(vm_compute; reflexivity) a ltac:(unfold RELRO_LO, RELRO_HI, RGOT_SSP in *; slia)
                            ltac:(unfold in_range, RELRO_LO, RELRO_HI, RGOT_SSP in *; slia))). exact (Hrelro a Ha Hg).
        - rewrite (proj1 (MAG (RGOT_SSP + 8) (RELRO_HI - RGOT_SSP - 8) ltac:(vm_compute; reflexivity) a ltac:(unfold RELRO_LO, RELRO_HI, RGOT_SSP in *; slia)
                            ltac:(unfold in_range, RELRO_LO, RELRO_HI, RGOT_SSP in *; slia))). exact (Hrelro a Ha Hg). }
      split; [rewrite Eerr; cbn [x_errno GenO3s1_plain.X] in Hes; exact (post_errno_kept H IMX GenO3s1_plain.K Q st' rho' ms1 (cfg_model k) s' LB' G' X1 30%uint63 GenO3s1_plain.d0 x W HQ eq_refl (Hn0 30%uint63 eq_refl) eq_refl Hes)|].
      split; [intros _; reflexivity|].
      split.
      { (* [comment removed for export] *)
        cbn [errph_delta chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands].
        split; [rewrite (LBN_length G' GenO3s1_plain.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        split; [rewrite (LBN_bytes G' GenO3s1_plain.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        split; [rewrite (LBN_big G' GenO3s1_plain.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        repeat constructor; assumption. }
      pose proof In0 as In0g. pose proof In1 as In1g. pose proof In2 as In2g. pose proof In3 as In3g. pose proof In4 as In4g.
      unfold gblock in In0, In1, In2, In3, In4.
      rewrite Sz0 in In0. rewrite Sz1 in In1. rewrite Sz2 in In2. rewrite Sz3 in In3. rewrite Sz4 in In4.
      split.
      { (* [comment removed for export] *)
        cbn [ERRPH]. unfold ERR_statics, ERR_chain. cbn [ec_mkey ec_sa ec_nodes ec_es ec_hands ec_eslock ec_eshash ec_tevreg chain_blocks].
        unfold gblock. cbn [blk_addr blk_size fst snd]. rewrite Sz0, Sz1, Sz2, Sz3, Sz4.
        change (to_Z 72%uint63) with 72. change (to_Z 32%uint63) with 32. change (to_Z 128%uint63) with 128.
        change (to_Z 904%uint63) with 904. change (to_Z 8%uint63) with 8.
        split.
        - (* [comment removed for export] *)
          split; [apply (RWC (of_Z A_master_once_ret)); vm_compute; reflexivity|].
          split; [exact Rtsd3|].
          split; [apply (AGR A_stopped 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hstat))))))))]|].
          split; [apply (AGR A_base_once 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hstat))))))))))]|].
          split; [apply (RWC (of_Z A_load_strings_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_optsdone)); vm_compute; reflexivity|].
          split.
          { apply (proj2 (rw_cells_app rsegs m1 A_err_string_once [C4 (wz 2); C4 (wz 1)] [C8 (wz (g_addr g10)); C8 (wz (g_addr g11))])).
            split; [apply (RWC (of_Z A_err_string_once)); vm_compute; reflexivity|].
            apply (proj2 (rw_cells_app rsegs m1 _ [C8 (wz (g_addr g10))] [C8 (wz (g_addr g11))])). split; [exact Resl | exact Resh]. }
          split.
          { apply (proj2 (rw_cells_app rsegs m1 A_tevent_once [C4 (wz 2); C4 (wz 1)] [C8 (wz (g_addr g5))])).
            split; [apply (RWC (of_Z A_tevent_once)); vm_compute; reflexivity | exact Rtev]. }
          split; [apply (RWC (of_Z (A_keys + 24))); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_next_key)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_key_lock)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_td_cancelbuf)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_td_tsd_used)); vm_compute; reflexivity|].
          exact Rtsd1.
        - (* [comment removed for export] *)
          split; [apply in_app_iff; left; exact In0|]. split; [reflexivity|].
          split; [exact Rmkey|].
          split; [apply in_app_iff; left; exact In1|]. split; [reflexivity|].
          split.
          { unfold sa_cells. apply (proj2 (rw_cells_app rsegs m1 (g_addr g1) [C4 (wz 1); C4 (wz 0); C8 (wz 0); C8 (wz 1)] [C8 (wz (g_addr g2))])).
            split; [| exact Rsa]. rewrite <- (Z.add_0_r (g_addr g1)). change 0 with (to_Z 0%uint63) at 2.
            apply (RWB 1%uint63 g1 0%uint63 _ Hg1). vm_compute. reflexivity. }
          split; [apply in_app_iff; left; exact In2|]. split; [reflexivity|].
          split; [exact Rnodes|].
          split; [apply in_app_iff; left; exact In3|]. split; [reflexivity|].
          split; [apply in_app_iff; left; exact In4|]. split; [reflexivity|].
          cbn [chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands].
          apply Forall_cons; [exact (post_block_range H IMX GenO3s1_plain.K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 (g_id g0, g_addr g0, 72) ltac:(apply in_app_iff; left; exact In0))|].
          apply Forall_cons; [exact (post_block_range H IMX GenO3s1_plain.K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 (g_id g1, g_addr g1, 32) ltac:(apply in_app_iff; left; exact In1))|].
          apply Forall_cons; [exact (post_block_range H IMX GenO3s1_plain.K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 (g_id g2, g_addr g2, 128) ltac:(apply in_app_iff; left; exact In2))|].
          apply Forall_cons; [exact (post_block_range H IMX GenO3s1_plain.K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 (g_id g3, g_addr g3, 904) ltac:(apply in_app_iff; left; exact In3))|].
          apply Forall_cons; [exact (post_block_range H IMX GenO3s1_plain.K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 (g_id g4, g_addr g4, 8) ltac:(apply in_app_iff; left; exact In4))|].
          apply Forall_nil. }
      split.
      { (* [comment removed for export] *)
        cbn [CTXPH]. destruct Hstat as (Cs1 & Cs2 & Cs3 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10 & Cs11 & Cs12). split.
        - unfold CTX_statics.
          split; [apply (AGR A_defctx_inited 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs1]|].
          split; [apply (AGR A_defctx_exlock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs2]|].
          split; [apply (AGR A_defctx_exmeth_bio 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs3]|].
          split; [apply (AGR A_td_tsd 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs4]|].
          split; [apply (AGR A_tsd_main 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs5]|].
          split; [apply (AGR A_destructor_key 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs6]|].
          split; [apply (AGR A_base_inited 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs7]|].
          split; [apply (AGR A_stopped 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs8]|].
          split; [apply (AGR A_in_init_config_key 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs9]|].
          split; [apply (AGR A_base_once 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs10]|].
          split; [apply (AGR A_optsdone_lock 16 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs11]|].
          apply (AGR A_keys 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs12].
        - destruct Hblk as [(Ein & Esz & Erng & Emut) (po & pi & Hpo & Hpi)]. split.
          + split; [apply in_app_iff; right; exact Ein|]. split; [exact Esz|]. split; [exact Erng|].
            unfold MUTEX in *. apply (rw_cells_agree (in_range (blk_addr (cx_exlock cx)) (blk_size (cx_exlock cx))) m m1 _ _ (MAGB _ Ein ltac:(rewrite Esz; exact Erng)) Emut).
            intros a Ha. unfold in_range in *. rewrite Esz. unfold MUTEX_SIZE. cbn [cells_size csize length Nat.add] in Ha. slia.
          + exists po, pi. split; apply in_app_iff; right; assumption. }
      split.
      { (* [comment removed for export] *)
        unfold gblock. cbn [blk_addr blk_size fst snd].
        unfold ERRST. cbn [es_slots es_top es_bottom errst_zero].
        split; [reflexivity|]. split; [slia|]. split; [slia|].
        cbn [map repeat sl_flags sl_buffer sl_file sl_line sl_func slot_clear]. unfold zero16. cbn [repeat].
        unfold u32arr, u64arr, O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP.
        split. { destruct (RWA 3%uint63 g3 0%uint63 (u32s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1].
                 change (to_Z 0%uint63) with 0 in B1, W1. rewrite Z.add_0_r in B1, W1. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 64%uint63 (u32s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 128%uint63 (u64s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 256%uint63 (u64s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 384%uint63 (u64s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 512%uint63 (u32s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 576%uint63 (u64s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 704%uint63 (u32s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { destruct (RWA 3%uint63 g3 768%uint63 (u64s (repeat (wz 0) 16)) Hg3 ltac:(vm_compute; reflexivity)) as [B1 W1]. split; [exact B1 | exact W1]. }
        split. { change 896 with (to_Z 896%uint63). apply (RWB 3%uint63 g3 896%uint63 _ Hg3). vm_compute. reflexivity. }
        repeat (apply Forall_cons; [cbn; repeat split; (slia || reflexivity)|]). apply Forall_nil. }
      (* [comment removed for export] *)
      exact (post_xpres H IMX GenO3s1_plain.K chk1_K Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 ERR_X chk1_xw
               (fun b Hb => HH_RHEAP_block_range H HH _ _ _ b Hheap Hb)).
  Qed.
End C.
