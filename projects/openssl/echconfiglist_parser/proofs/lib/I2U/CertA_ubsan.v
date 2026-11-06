(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX CellsX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import InitMem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_SR ECH_Img ECH_Xpres ECH_Rep ECH_LibState ECH_C1_stmt ECH_C3_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom I2Canon I2Mach I2Image I2Run I2ImgUbsan GenA_ubsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2U Require Import
  I2Inv I2NodeLib I2NodeM I2Start I2Top I2Cert I2CertE.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma chkA_K : K_ok K = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chkA_roc : K_roc_ok K = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chkA_code_some : match build_code usegs pcs with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chkA_code : code_ok usegs code.
Proof.
  unfold code_. pose proof chkA_code_some as Hs.
  destruct (build_code usegs pcs) as [C|] eqn:E; [|discriminate Hs]. exact (build_code_ok usegs pcs C E).
Qed.
Lemma chkA_run : i2_check IM code K fuel st0 X = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chkA_shape : start_shape_ok K IMX st0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chkA_ho : ho_check2 IMX facts0 d0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chkA_tags : forallb (fact_tags_lt n0) facts0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition S_A : ssrc :=
  SSrc [(4, RATP)]
       [(A_malloc_impl, le8Z P_CRYPTO_malloc ++ le8Z P_CRYPTO_realloc ++ le8Z P_CRYPTO_free);
        (A_mem_inited, [1]);
        (RGOT_SSP, le8Z RSSP_GUARD)]
       [(RO_LO, RO_HI); (RELRO_LO, RGOT_SSP); (RGOT_SSP + 8, RELRO_HI);
        (A_destructor_key, A_destructor_key + 8); (A_defctx_inited, A_tevent_once); (A_base_inited, A_load_strings_once);
        (A_optsdone_lock, A_optsdone + 8); (A_td_cancelbuf, A_td_cancelbuf + 16); (A_keys, A_key_lock + 16); (A_tsd_main, A_tsd_main + 8)]
       [(RERRNO, 4, 31%uint63); (RSSP_GUARD, 8, 32%uint63)].
Lemma chkA_facts : forallb (fact_ok K d0 S_A) facts0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma chkA_xw : xw_in K CTX_X = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section C.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HHx : heap_sr_hyps_x H.
  Let HH : heap_sr_hyps H := proj1 HHx.

  (* [comment removed for export] *)
  Lemma S_A_holds : forall (x : Z -> word) m s LB (errv : word),
    hs_RHEAP H s LB m -> x 4 = Z_to_bv 64 RATP -> IMPL_mem m -> MEMFLAG m 1 -> mem_inv usegs m -> relro_lib m ->
    CTX_fresh m -> rw_cells usegs m RERRNO [C4 errv] ->
    ssrc_holds S_A x [(31%uint63, errv); (32%uint63, wz (hs_canary H))] m.
  Proof.
    intros x m s LB errv Hheap Htp Himpl Hmf Hinv Hrelro Hfresh Herr.
    pose proof HHx as (_ & _ & _ & _ & Hst & _). destruct (Hst _ _ _ Hheap) as (_ & Hgot & _ & Hcan).
    destruct Hfresh as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    unfold ssrc_holds, S_A. cbn [s_cregs s_vals s_clear s_words fst snd].
    split; [|split; [|split]].
    - constructor; [exact Htp | constructor].
    - constructor. { eapply schunk_of_rw_cells; [exact Himpl|]. vm_compute. reflexivity. }
      constructor.
      { destruct Hmf as (fb & Hrw & Hfb & _). intros i Hi. destruct i as [|i]; [|cbn in Hi; slia]. cbn [nth].
        destruct Hrw as [[_ (_ & _ & HB)] _]. cbn [cells_bytes cbytes app length] in HB. rewrite (HB 0%nat ltac:(slia)). cbn [nth_error].
        f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hfb. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Hgot|]. vm_compute. reflexivity. }
      constructor.
    - unfold relro_lib in Hrelro.
      unfold RO_LO, RO_HI, RELRO_LO, RELRO_HI, RGOT_SSP, A_destructor_key, A_defctx_inited, A_tevent_once, A_base_inited, A_load_strings_once,
        A_optsdone_lock, A_optsdone, A_td_cancelbuf, A_keys, A_key_lock, A_tsd_main in *.
      unfold none_on in *.
      constructor. { intros a Ha. cbn in Ha. apply mem_inv_ro_none; [exact Hinv | slia | slia]. }
      constructor. { intros a Ha. cbn in Ha. apply Hrelro; slia. }
      constructor. { intros a Ha. cbn in Ha. apply Hrelro; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F1; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F2; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F3; slia. }
      constructor. { intros a Ha. cbn in Ha. destruct (Z_lt_ge_dec a (A_optsdone_lock + 16)); unfold A_optsdone_lock in *; [apply F4 | apply F5]; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F6; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F7; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F8; slia. }
      constructor.
    - constructor; [exact (sword_of_C4 m RERRNO errv Herr)|]. constructor; [exact (sword_of_C8 m RSSP_GUARD _ Hcan) | constructor].
  Qed.

  (* [comment removed for export] *)
  Definition xregs_of (errv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (i : Z) : word :=
    nth (Z.to_nat i) [errv; ra; sp; gp; tp; t0; t1; t2; s0; s1; a0; a1; a2; a3; a4; a5; a6; a7; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] w0.

  Theorem getdefctx_fresh_cert : getdefctx_fresh_stmt H.
  Proof.
    unfold getdefctx_fresh_stmt, getdefctx_stmt_for.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB lo B errv
           Ha0 Hheap Hkrel Hby Hcnt Hbig Haux HB Hsp16 Hstk Hhl Hlo Herr Hinv Htp Hmf Himpl Hgot Hrelro Hfresh Hra.
    set (x := xregs_of errv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
    set (W := [(31%uint63, errv); (32%uint63, wz (hs_canary H))]).
    (* [comment removed for export] *)
    pose proof HHx as (_ & _ & _ & Hrx & _ & _).
    destruct (Hrx _ _ Haux) as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & sec & _ & _ & _ & _ & HBav & Hav & _).
    assert (HB64 : B < 2 ^ 64) by (clear - HBav Hav; slia).
    assert (Hsp63 : bv_unsigned (x 2) < 2 ^ 63) by (clear - HBav Hav HB; change (x 2) with sp; slia).
    clear HBav Hav av x3 x4 x5 x16 x6 x11 x12 x23 rnd sec Hrx.
    change (bv_unsigned sp) with (bv_unsigned (x 2)) in HB, Hsp16, Hstk, Hlo.
    assert (Etp : x 4 = Z_to_bv 64 RATP) by exact Htp.
    assert (Eerr : bv_unsigned tp + -164 = errA K).
    { rewrite Htp, Z_to_bv_unsigned. vm_compute. reflexivity. }
    rewrite Eerr in Herr.
    cbn [ctxph_bytes ctxph_cnt ctxph_big ctxph_stack CTXPH] in Hby, Hcnt, Hbig, Hlo, Hfresh.
    unfold CTXINIT_BYTES, CTXINIT_CNT, CTXINIT_BIG, CTXINIT_STACK, FR_get_default_context, RREALLOC_STACK, RMALLOC_STACK in Hby, Hcnt, Hbig, Hlo.
    assert (Cc : to_Z (c_cost K) <= 2 ^ 16) by (apply Z.leb_le; vm_compute; reflexivity).
    assert (Cn : to_Z (c_cnt K) <= 160) by (apply Z.leb_le; vm_compute; reflexivity).
    assert (Cb : to_Z (c_big K) <= 2) by (apply Z.leb_le; vm_compute; reflexivity).
    assert (Cs : to_Z (c_stack K) = 32 + (1024 + (64 + 8192))) by (vm_compute; reflexivity).
    assert (Hby' : lb_bytes LB + to_Z (c_cost K) <= hs_LIVE_MAX H) by (clear - Hby Cc; slia).
    assert (Hcnt' : Z.of_nat (length LB) + to_Z (c_cnt K) <= hs_LIVE_CNT_MAX H) by (clear - Hcnt Cn; slia).
    assert (Hbig' : lb_big LB + to_Z (c_big K) <= hs_LIVE_BIG_MAX H) by (clear - Hbig Cb; slia).
    assert (Hlo' : lo <= bv_unsigned (x 2) - to_Z (c_stack K)) by (clear - Hlo Cs; slia).
    (* [comment removed for export] *)
    pose proof (start_Rn K d0 S_A x W F fc m lo chkA_K (S_A_holds x m s LB errv Hheap Etp Himpl Hmf Hinv Hrelro Hfresh Herr)
                  Hstk (conj Hhl Hlo') Hsp63 Hsp16 IMX facts0 n0 IMX_ok IMX_wr_ok chkA_ho chkA_tags chkA_facts) as HRn.
    pose proof (i2_certificate H IMX K code chkA_K HHx IMX_ok IMX_wr_ok chkA_code (ro_const_intro H K HHx chkA_roc)
                  fuel st0 X [] (rho_of K d0 x W) x F fc m mo s LB lo B chkA_run chkA_shape eq_refl (List.NoDup_nil _) (Forall_nil _)
                  HRn eq_refl eq_refl Hheap Hkrel Hby' Hcnt' Hbig' Haux HB HB64 Hstk Hhl Hlo' Hsp16 Herr Hinv) as HC.
    clear HRn.
    match goal with |- hs_SR _ _ ?c => match type of HC with hs_SR _ _ ?c' => replace c with c' by reflexivity end end.
    apply (sr_mono H HH _ _ _ HC). clear HC.
    (* [comment removed for export] *)
    intros k (rho' & st' & ms1 & s' & LB' & G' & Ek & X1 & Hfin & HXR & HXC & HXB & Hsz & _).
    set (Q := I2E _ _ _ _ _ _ _ _ _ _ _) in X1.
    assert (HG0 : q_G0 Q = []) by reflexivity.
    assert (HQ : q_rho0 Q = rho_of K d0 x W) by reflexivity.
    (* [comment removed for export] *)
    destruct (post_ptr_rw rho' ms1 G' X HXC (of_Z A_defctx_exlock) 1%uint63 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g1 & Hg1 & Rexl).
    destruct (post_ptr_rw rho' ms1 G' X HXC (of_Z A_optsdone_lock) 20%uint63 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g20 & Hg20 & Rol).
    destruct (post_ptr_rw rho' ms1 G' X HXC (of_Z (A_optsdone_lock + 8)) 21%uint63 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g21 & Hg21 & Ril).
    rewrite Z.add_0_r in Rexl, Rol, Ril.
    destruct (blk_of_LBN G' X Hsz _ _ Hg1) as (In1 & _ & Sz1).
    destruct (blk_of_LBN G' X Hsz _ _ Hg20) as (In20 & _ & Sz20).
    destruct (blk_of_LBN G' X Hsz _ _ Hg21) as (In21 & _ & Sz21).
    change (nth (Z.to_nat (to_Z 1%uint63)) (x_sizes X) 0%uint63) with 40%uint63 in Sz1.
    change (nth (Z.to_nat (to_Z 20%uint63)) (x_sizes X) 0%uint63) with 40%uint63 in Sz20.
    change (nth (Z.to_nat (to_Z 21%uint63)) (x_sizes X) 0%uint63) with 40%uint63 in Sz21.
    pose proof In1 as In1g. unfold gblock in In1, In20, In21. rewrite Sz1 in In1. rewrite Sz20 in In20. rewrite Sz21 in In21.
    change (to_Z 40%uint63) with 40 in In1, In20, In21.
    (* [comment removed for export] *)
    pose proof (post_magree H IMX K Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0) as MAG. cbn [q_m0 Q] in MAG.
    pose proof (post_rw_cells rho' ms1 G' X HXC) as RWC.
    pose proof (post_blk_rw_cells H IMX K Q st' rho' ms1 (cfg_model k) s' LB' G' X X1 Hsz HXB) as RWB.
    destruct (post_errno H IMX K Q st' rho' ms1 (cfg_model k) s' LB' G' X1) as [errv' Herr'].
    set (m1 := ms_mem ms1) in *.
    destruct Hfresh as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    (* [comment removed for export] *)
    assert (AGR : forall A n, unw_range K A n = true -> forall cs, Z.of_nat (cells_size cs) = n -> rw_cells usegs m A cs -> rw_cells usegs m1 A cs).
    { intros A n Hu cs Hn Hrw. apply (rw_cells_agree (in_range A n) m m1 A cs (MAG A n Hu) Hrw). rewrite Hn. exact (fun a h => h). }
    assert (AGN : forall A n, unw_range K A n = true -> 0 <= A -> A + n <= 2 ^ 64 -> none_on m A n -> none_on m1 A n).
    { intros A n Hu HA HAn Hn. exact (none_on_agree (in_range A n) m m1 A n (MAG A n Hu) Hn (fun a h => h) HA HAn). }
    assert (Nbio : none_on m1 A_defctx_exmeth_bio 8).
    { apply (AGN A_defctx_exmeth_bio 8 ltac:(vm_compute; reflexivity)); unfold A_defctx_exmeth_bio; [slia | slia |].
      intros a Ha. apply F2. unfold A_defctx_inited, A_tevent_once. slia. }
    assert (Ntsd : none_on m1 A_tsd_main 8).
    { apply (AGN A_tsd_main 8 ltac:(vm_compute; reflexivity)); unfold A_tsd_main; [slia | slia | exact F8]. }
    assert (Nstop : none_on m1 A_stopped 4).
    { apply (AGN A_stopped 4 ltac:(vm_compute; reflexivity)); unfold A_stopped; [slia | slia |].
      intros a Ha. apply F3. unfold A_base_inited, A_load_strings_once. slia. }
    (* [comment removed for export] *)
    exists (rv rho' (i_F st') 5), (rv rho' (i_F st') 6), (rv rho' (i_F st') 7),
           (rv rho' (i_F st') 11), (rv rho' (i_F st') 12), (rv rho' (i_F st') 13), (rv rho' (i_F st') 14),
           (rv rho' (i_F st') 15), (rv rho' (i_F st') 16), (rv rho' (i_F st') 17),
           (rv rho' (i_F st') 28), (rv rho' (i_F st') 29), (rv rho' (i_F st') 30), (rv rho' (i_F st') 31),
           m1, errv', s', (LBN G'), (mkCX (gblock g1) (g_addr g20) (g_addr g21)).
    assert (Hn0 : forall t : int, (t <? n0)%uint63 = true -> to_Z t < to_Z (q_n0 Q)) by (intros t Ht; exact (i_ltb_lt _ _ Ht)).
    pose proof (fun kk t r => xreg_entry H IMX K Q st' rho' ms1 (cfg_model k) s' LB' G' X X1 HXR d0 x W kk t r HQ) as XE.
    split.
    { rewrite Ek, (post_regs H IMX K Q st' rho' ms1 (cfg_model k) s' LB' G' X1).
      change (q_F Q) with F. change (q_fc Q) with fc. replace (q_rho0 Q (c_tra K)) with ra by reflexivity. fold m1.
      rewrite <- (XE 1%uint63 2%uint63 1%uint63 eq_refl eq_refl (Hn0 2%uint63 eq_refl) eq_refl : rv rho' (i_F st') 1 = ra).
      rewrite <- (xreg_sp H IMX K Q st' rho' ms1 (cfg_model k) s' LB' G' X X1 HXR d0 x W HQ eq_refl eq_refl : rv rho' (i_F st') 2 = sp).
      rewrite <- (XE 3%uint63 3%uint63 3%uint63 eq_refl eq_refl (Hn0 3%uint63 eq_refl) eq_refl : rv rho' (i_F st') 3 = gp).
      assert (E4 : rv rho' (i_F st') 4 = tp).
      { rewrite (xreg_W st' rho' G' X HXR 4%uint63 _ eq_refl : rv rho' (i_F st') 4 = _), Htp. apply bv_eq. vm_compute. reflexivity. }
      rewrite <- E4.
      rewrite <- (XE 8%uint63 7%uint63 8%uint63 eq_refl eq_refl (Hn0 7%uint63 eq_refl) eq_refl : rv rho' (i_F st') 8 = s0).
      rewrite <- (XE 9%uint63 8%uint63 9%uint63 eq_refl eq_refl (Hn0 8%uint63 eq_refl) eq_refl : rv rho' (i_F st') 9 = s1).
      assert (E10 : rv rho' (i_F st') 10 = Z_to_bv 64 A_defctx).
      { rewrite (xreg_W st' rho' G' X HXR 10%uint63 _ eq_refl : rv rho' (i_F st') 10 = _). apply bv_eq. vm_compute. reflexivity. }
      rewrite <- E10.
      rewrite <- (XE 18%uint63 17%uint63 18%uint63 eq_refl eq_refl (Hn0 17%uint63 eq_refl) eq_refl : rv rho' (i_F st') 18 = s2).
      rewrite <- (XE 19%uint63 18%uint63 19%uint63 eq_refl eq_refl (Hn0 18%uint63 eq_refl) eq_refl : rv rho' (i_F st') 19 = s3).
      rewrite <- (XE 20%uint63 19%uint63 20%uint63 eq_refl eq_refl (Hn0 19%uint63 eq_refl) eq_refl : rv rho' (i_F st') 20 = s4).
      rewrite <- (XE 21%uint63 20%uint63 21%uint63 eq_refl eq_refl (Hn0 20%uint63 eq_refl) eq_refl : rv rho' (i_F st') 21 = s5).
      rewrite <- (XE 22%uint63 21%uint63 22%uint63 eq_refl eq_refl (Hn0 21%uint63 eq_refl) eq_refl : rv rho' (i_F st') 22 = s6).
      rewrite <- (XE 23%uint63 22%uint63 23%uint63 eq_refl eq_refl (Hn0 22%uint63 eq_refl) eq_refl : rv rho' (i_F st') 23 = s7).
      rewrite <- (XE 24%uint63 23%uint63 24%uint63 eq_refl eq_refl (Hn0 23%uint63 eq_refl) eq_refl : rv rho' (i_F st') 24 = s8).
      rewrite <- (XE 25%uint63 24%uint63 25%uint63 eq_refl eq_refl (Hn0 24%uint63 eq_refl) eq_refl : rv rho' (i_F st') 25 = s9).
      rewrite <- (XE 26%uint63 25%uint63 26%uint63 eq_refl eq_refl (Hn0 25%uint63 eq_refl) eq_refl : rv rho' (i_F st') 26 = s10).
      rewrite <- (XE 27%uint63 26%uint63 27%uint63 eq_refl eq_refl (Hn0 26%uint63 eq_refl) eq_refl : rv rho' (i_F st') 27 = s11).
      reflexivity. }
    split; [exact (post_krel H IMX K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
    split; [exact (post_mpres H IMX K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
    split; [exact (post_inv H IMX K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
    split; [exact (post_stk H IMX K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
    split; [rewrite Eerr; exact Herr'|].
    split; [exact (post_auxv H IMX K Q st' rho' ms1 (cfg_model k) s' LB' G' X1)|].
    split; [exact (post_heap H IMX K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0)|].
    split.
    { (* [comment removed for export] *)
      cbn [ctxph_delta cx_exlock cx_olock cx_ilock].
      split; [rewrite (LBN_length G' X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
      split; [rewrite (LBN_bytes G' X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
      split; [rewrite (LBN_big G' X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
      split; [exact In1g|].
      exists (g_id g20), (g_id g21). split; [exact In20 | exact In21]. }
    split.
    { (* [comment removed for export] *)
      cbn [CTXPH]. split.
      - unfold CTX_statics. cbn [cx_exlock cx_olock cx_ilock]. unfold gblock. cbn [blk_addr fst snd].
        split; [apply (RWC (of_Z A_defctx_inited)); vm_compute; reflexivity|].
        split; [exact Rexl|].
        split.
        { apply (rw_cells_recast usegs m1 A_defctx_exmeth_bio [Cells.CB 8%nat (repeat (Z_to_bv 8 0) 8)]);
            [ apply (none_on_rw_cells m1 A_defctx_exmeth_bio); [exact Nbio | vm_compute; reflexivity | unfold A_defctx_exmeth_bio; slia | rewrite repeat_length; unfold A_defctx_exmeth_bio; slia]
            | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]. }
        split; [apply (RWC (of_Z A_td_tsd)); vm_compute; reflexivity|].
        split.
        { apply (rw_cells_recast usegs m1 A_tsd_main [Cells.CB 8%nat (repeat (Z_to_bv 8 0) 8)]);
            [ apply (none_on_rw_cells m1 A_tsd_main); [exact Ntsd | vm_compute; reflexivity | unfold A_tsd_main; slia | rewrite repeat_length; unfold A_tsd_main; slia]
            | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]. }
        split; [apply (RWC (of_Z A_destructor_key)); vm_compute; reflexivity|].
        split; [apply (RWC (of_Z A_base_inited)); vm_compute; reflexivity|].
        split.
        { apply (rw_cells_recast usegs m1 A_stopped [Cells.CB 4%nat (repeat (Z_to_bv 8 0) 4)]);
            [ apply (none_on_rw_cells m1 A_stopped); [exact Nstop | vm_compute; reflexivity | unfold A_stopped; slia | rewrite repeat_length; unfold A_stopped; slia]
            | cbn; repeat split; reflexivity || exact I | vm_compute; reflexivity | reflexivity ]. }
        split; [apply (RWC (of_Z A_in_init_config_key)); vm_compute; reflexivity|].
        split; [apply (RWC (of_Z A_base_once)); vm_compute; reflexivity|].
        split; [|apply (RWC (of_Z A_keys)); vm_compute; reflexivity].
        apply (proj2 (rw_cells_app usegs m1 A_optsdone_lock [C8 (wz (g_addr g20))] [C8 (wz (g_addr g21))])).
        split; [exact Rol | exact Ril].
      - unfold CTX_blocks, EXLOCK. cbn [cx_exlock cx_olock cx_ilock]. unfold gblock. cbn [blk_addr blk_size fst snd]. rewrite Sz1.
        change (to_Z 40%uint63) with 40.
        split.
        + split; [apply in_app_iff; left; exact In1|]. split; [reflexivity|].
          split; [exact (post_block_range H IMX K HHx Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 (g_id g1, g_addr g1, 40) ltac:(apply in_app_iff; left; exact In1))|].
          unfold MUTEX. rewrite <- (Z.add_0_r (g_addr g1)). change 0 with (to_Z 0%uint63) at 2. apply (RWB 1%uint63 g1 0%uint63 _ Hg1). vm_compute. reflexivity.
        + exists (g_id g20), (g_id g21). split; apply in_app_iff; left; [exact In20 | exact In21]. }
    split.
    { (* [comment removed for export] *) intros _. unfold CTX_keys.
      split; [apply (RWC (of_Z A_next_key)); vm_compute; reflexivity|].
      split; [apply (RWC (of_Z A_key_lock)); vm_compute; reflexivity|].
      apply (RWC (of_Z A_td_cancelbuf)); vm_compute; reflexivity. }
    split.
    { (* [comment removed for export] *) destruct Hmf as (fb & Hrw & Hfb & H01). exists fb. split; [|split; [exact Hfb | exact H01]].
      apply (AGR A_mem_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Hrw]. }
    split; [apply (AGR A_malloc_impl 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Himpl]|].
    split; [apply (AGR A_got_CRYPTO_malloc 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Hgot]|].
    split.
    { (* [comment removed for export] *) intros a Ha Hg. unfold relro_lib in Hrelro.
      destruct (Z_lt_ge_dec a RGOT_SSP) as [Hlt|Hge].
      - rewrite (proj1 (MAG RELRO_LO (RGOT_SSP - RELRO_LO) ltac:(vm_compute; reflexivity) a ltac:(unfold RELRO_LO, RELRO_HI, RGOT_SSP in *; slia)
                          ltac:(unfold in_range, RELRO_LO, RELRO_HI, RGOT_SSP in *; slia))). exact (Hrelro a Ha Hg).
      - rewrite (proj1 (MAG (RGOT_SSP + 8) (RELRO_HI - RGOT_SSP - 8) ltac:(vm_compute; reflexivity) a ltac:(unfold RELRO_LO, RELRO_HI, RGOT_SSP in *; slia)
                          ltac:(unfold in_range, RELRO_LO, RELRO_HI, RGOT_SSP in *; slia))). exact (Hrelro a Ha Hg). }
    (* [comment removed for export] *)
    exact (post_xpres H IMX K chkA_K Q st' rho' ms1 (cfg_model k) s' LB' G' X1 HG0 CTX_X chkA_xw
             (fun b Hb => HH_RHEAP_block_range H HH _ _ _ b Hheap Hb)).
  Qed.
End C.
