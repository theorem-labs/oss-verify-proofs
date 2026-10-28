(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX CellsX Arr InNth.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import InitMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0
     ECH_AImg ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1 ECH_AStmt_C3.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2 Require Import I2ImgAsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeKit
  I2ANodeSig I2ANodeS I2ANodeX I2ANodeA I2ASound I2ACert I2AStart I2ASh0 I2ATop I2ACertE.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2 Require GenA0_asan GenA16_asan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import CertA_asanK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Section C.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  (* [comment removed for export] *)
  Hypothesis MAL : memalign_stmt H 0x1bf180 0x1bfb98.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma S_A_holds : forall (x : Z -> word) m (errv : word) (can : Z),
    x 4 = Z_to_bv 64 ATP -> IMPL_mem m -> MEMFLAG m 1 -> mem_inv asegs m -> arelro_lib m -> CTX_fresh m -> ACONST m ->
    rw_cells asegs m AERRNO [C4 errv] -> rw_cells asegs m ACANARYX [C8 (Z_to_bv 64 can)] ->
    ssrc_holds H S_A x [(33%uint63, errv); (34%uint63, Z_to_bv 64 can)] m.
  Proof.
    intros x m errv can Htp Himpl Hmf Hinv Hrelro Hfresh Hac Herr Hcan.
    destruct Himpl as (I1 & I2 & I3).
    destruct Hfresh as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & (M1 & M2 & M3 & M4)).
    pose proof (ACONST_cell m AMUSL_TSD _ Hac ltac:(in_nth)) as C1.
    pose proof (proj2 (ACONST_shbase m Hac)) as C2. pose proof (proj2 (ACONST_uar m Hac)) as C3.
    unfold ssrc_holds, S_A. cbn [s_cregs s_vals s_clear s_words s_blks fst snd].
    split; [|split; [|split; [|split]]].
    - constructor; [exact Htp | constructor].
    - constructor. { eapply schunk_of_rw_cells; [exact I1|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact I2|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact I3|]. vm_compute. reflexivity. }
      constructor.
      { destruct Hmf as (fb & Hrw & Hfb & _). intros i Hi. destruct i as [|i]; [|cbn in Hi; slia]. cbn [nth].
        destruct Hrw as [[_ (_ & _ & HB)] _]. cbn [cells_bytes cbytes app length] in HB. rewrite (HB 0%nat ltac:(slia)). cbn [nth_error].
        f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hfb. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact C1|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact M1|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact M2|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact M3|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact M4|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact C2|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact C3|]. vm_compute. reflexivity. }
      constructor.
    - unfold arelro_lib in Hrelro. unfold none_on in *.
      unfold A_destructor_key, A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
        A_base_inited, A_stopped, A_in_init_config_key, A_base_once, A_base_ret, A_load_strings_once, A_load_strings_ret, A_optsdone_lock, A_init_lock,
        A_optsdone, A_td_cancelbuf, A_keys, A_tsd_main in *.
      constructor. { intros a Ha. cbn in Ha. apply asan_mem_inv_ro_none; [exact Hinv | slia | slia]. }
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
      constructor. { intros a Ha. cbn in Ha. apply F10; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F11; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F12; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F13; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F14; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F15; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F16; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F17; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F18; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F19; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F20; slia. }
      constructor. { intros a Ha. cbn in Ha. apply F21; slia. }
      constructor.
    - constructor; [exact (sword_of_C4 m AERRNO errv Herr)|]. constructor; [exact (sword_of_C8 m ACANARYX _ Hcan) | constructor].
    - constructor.
  Qed.


  Theorem getdefctx_fresh_cert : getdefctx_fresh_stmt H.
  Proof.
    unfold getdefctx_fresh_stmt, getdefctx_stmt_for.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF lo B errv CH
           Hvis Ha0 Hheap Hkrel Hby Hcnt Haux HB Hsp16 Hstk Hhl Hlo Hsh0 Herr Hinv Htp Hac Hmf Himpl Hgot Hrelro Hfresh
           Hrfs Hlf Hchain HCH Hpf Hclosed HAL Hra.
    cbn [ctxph_bytes ctxph_cnt ctxph_stack ctxph_sh0 ctxph_frames gdf_frames ctxph_cost ctxph_closed_ok PF_ctx CTXPH] in Hby, Hcnt, Hlo, Hsh0, Hfresh, Hlf, Hpf, Hclosed, HAL.
    unfold CTXINIT_BYTES, CTXINIT_CNT, CTXINIT_STACK, FR_get_default_context, AREALLOC_STACK in Hby, Hcnt, Hlo.
    set (x := xregs_ofA errv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
    destruct (HHx_canary H HHx _ _ _ Hheap) as (can & _ & Hcan & Hcan64).
    set (W := [(33%uint63, errv); (34%uint63, Z_to_bv 64 can)]).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof Hsh0 as (g0 & _ & HhiA & _ & _). unfold AAPP_HI in HhiA.
    assert (Hsp63 : bv_unsigned (x 2) < 2 ^ 63) by (clear - HhiA; change (x 2) with sp; slia).
    assert (HB64 : bv_unsigned (x 2) < 2 ^ 64) by (clear - Hsp63; slia).
    clear g0 HhiA.
        change (bv_unsigned sp) with (bv_unsigned (x 2)) in HB, Hsp16, Hstk, Hlo, Hsh0, HCH.
    assert (Etp : x 4 = Z_to_bv 64 ATP) by exact Htp.
    assert (Eerr : bv_unsigned tp + -164 = errA GenA0_asan.KA).
    { rewrite Htp, Z_to_bv_unsigned. vm_compute. reflexivity. }
    rewrite Eerr in Herr.
    assert (Es0 : bv_unsigned s0 = bv_unsigned (x 8)) by reflexivity. rewrite Es0 in Hchain.
    assert (Era : bv_unsigned ra = bv_unsigned (x 1)) by reflexivity. rewrite Era in Hpf.
    pose proof (cost_le_AL := HAL).
    (* [comment removed for export] *)
    assert (Hsp32 : (bv_unsigned (x 2) - 9024) mod 32 = 0 \/ (bv_unsigned (x 2) - 9040) mod 32 = 0) by (clear - Hsp16; slia).
    destruct Hsp32 as [Hsp32 | Hsp32].
    { (* [comment removed for export] *)
      assert (Cc : to_Z (c_cost GenA0_asan.K) <= 2 ^ 16) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cn : to_Z (c_cnt GenA0_asan.K) <= 160) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cs : to_Z (c_stack GenA0_asan.K) = 9024) by (vm_compute; reflexivity).
      assert (Cf : Z.to_nat (to_Z (ka_fsmax GenA0_asan.KA)) = 3%nat) by (vm_compute; reflexivity).
      assert (Hby' : lb_bytes LB + to_Z (c_cost GenA0_asan.K) <= as_LIVE_MAX H) by (clear - Hby Cc; slia).
      assert (Hcnt' : Z.of_nat (length LB) + to_Z (c_cnt GenA0_asan.K) <= as_LIVE_CNT_MAX H) by (clear - Hcnt Cn; slia).
      assert (Hlo' : lo <= bv_unsigned (x 2) - to_Z (c_stack GenA0_asan.K)) by (clear - Hlo Cs; slia).
      assert (Hsp32' : (bv_unsigned (x 2) - to_Z (c_stack GenA0_asan.K)) mod 32 = 0) by (rewrite Cs; exact Hsp32).
      assert (Hlf' : (length LF + Z.to_nat (to_Z (ka_fsmax GenA0_asan.KA)) <= AFS_MAXLIVE)%nat) by (rewrite Cf; clear - Hlf; slia).
      assert (HALc : csum H (ka_costs GenA0_asan.KA) <= as_AL H s).
      { eapply Z.le_trans; [| exact HAL]. unfold CTXINIT_COST.
        apply (csum_le H HH); apply Z.leb_le; [exact chk0_msum | exact chk0_fsum]. }
      pose proof (rows_closed (as_TR H) PFC_CTXINIT (ka_pfc GenA0_asan.KA) chk0_pfc Hclosed) as Hpfc.
      pose proof (rows_open (as_TR H) PF_ctxinit (ka_pfo GenA0_asan.KA) (bv_unsigned (x 1)) CH chk0_pfo Hpf) as Hpfo.
      pose proof (start_RnA H GenA0_asan.KA GenA0_asan.d0 S_A x W F fc m lo chk0_K
                    (S_A_holds x m errv can Etp Himpl Hmf Hinv Hrelro Hfresh Hac Herr Hcan)
                    Hstk (conj Hhl Hlo') Hsp63 Hsp16 Hsp32' IMX GenA0_asan.facts0 GenA0_asan.n0 IMX_ok IMX_wr_ok chk0_ho chk0_tags chk0_facts) as HRn.
      pose proof (i2a_certificate H IMX GenA0_asan.KA GenA0_asan.code chk0_K HHx IMX_ok IMX_wr_ok chk0_code (ro_const_introA GenA0_asan.KA chk0_roc)
                    (sh0_of_aconst GenA0_asan.KA chk0_sh0) Hpfc (anode_fsmalloc_sound H IMX GenA0_asan.KA chk0_K HHx (sh0_of_aconst GenA0_asan.KA chk0_sh0)) (anode_fsfree_sound H IMX GenA0_asan.KA chk0_K HHx (sh0_of_aconst GenA0_asan.KA chk0_sh0) GenA0_asan.code chk0_code) (anode_memset_sound H IMX GenA0_asan.KA chk0_K HHx (sh0_of_aconst GenA0_asan.KA chk0_sh0)) (anode_memcpy_sound H IMX GenA0_asan.KA chk0_K HHx IMX_ok (sh0_of_aconst GenA0_asan.KA chk0_sh0)) (anode_strlen_sound H IMX GenA0_asan.KA chk0_K HHx IMX_ok (sh0_of_aconst GenA0_asan.KA chk0_sh0)) (anode_memalign_sound H IMX GenA0_asan.KA chk0_K HHx IMX_ok IMX_wr_ok (sh0_of_aconst GenA0_asan.KA chk0_sh0) Hpfc (ro_const_introA GenA0_asan.KA chk0_roc) MAL)
                    GenA0_asan.fuel (I2AS (state_of GenA0_asan.d0) GenA0_asan.n0 GenA0_asan.blk0 [] 0%uint63 0%uint63 0%uint63 []) GenA0_asan.X [] (rho_ofA GenA0_asan.K GenA0_asan.d0 x W) x F fc msF m mo s LB LF lo B CH
                    chk0_run chk0_shape eq_refl eq_refl (List.NoDup_nil _) (Forall_nil _)
                    HRn eq_refl eq_refl eq_refl eq_refl Hvis Hkrel Hheap Hrfs Hac Hsh0 Hchain HCH Hpfo HALc Hby' Hcnt' Hlf'
                    Haux HB HB64 Hstk Hhl Hlo' Hsp16 Hsp32' Herr Hinv) as HC.
      clear HRn.
      match goal with |- as_SR _ _ ?c => match type of HC with as_SR _ _ ?c' => replace c with c' by reflexivity end end.
      apply (ah_mono H HH _ _ _ HC). clear HC.
      (* [comment removed for export] *)
      intros k (rho' & st' & s' & LB' & G' & XS' & ms1 & Ek & Hak & Hmp & (msF1 & mo1 & X1) & Hfin & Hcs & HXR & HXC & HXB & Hsz & _ & HSH).
      set (Q := I2AE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in X1.
      assert (HG0 : q_G0 Q = []) by reflexivity.
      assert (HQ : q_rho0 Q = rho_ofA GenA0_asan.K GenA0_asan.d0 x W) by reflexivity.
      (* [comment removed for export] *)
      destruct (post_ptr_rw rho' ms1 G' GenA0_asan.X HXC (of_Z A_defctx_exlock) 1%uint63 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g1 & Hg1 & Rexl).
      destruct (post_ptr_rw rho' ms1 G' GenA0_asan.X HXC (of_Z A_optsdone_lock) 20%uint63 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g20 & Hg20 & Rol).
      destruct (post_ptr_rw rho' ms1 G' GenA0_asan.X HXC (of_Z A_init_lock) 21%uint63 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g21 & Hg21 & Ril).
      change (to_Z 0%uint63) with 0 in Rexl, Rol, Ril. rewrite Z.add_0_r in Rexl, Rol, Ril.
      destruct (blk_of_LBN G' GenA0_asan.X Hsz _ _ Hg1) as (In1 & InG1 & Sz1).
      destruct (blk_of_LBN G' GenA0_asan.X Hsz _ _ Hg20) as (In20 & _ & Sz20).
      destruct (blk_of_LBN G' GenA0_asan.X Hsz _ _ Hg21) as (In21 & _ & Sz21).
      change (nth (Z.to_nat (to_Z 1%uint63)) (x_sizes GenA0_asan.X) 0%uint63) with 40%uint63 in Sz1.
      change (nth (Z.to_nat (to_Z 20%uint63)) (x_sizes GenA0_asan.X) 0%uint63) with 40%uint63 in Sz20.
      change (nth (Z.to_nat (to_Z 21%uint63)) (x_sizes GenA0_asan.X) 0%uint63) with 40%uint63 in Sz21.
      pose proof In1 as In1g. unfold gblock in In1, In20, In21. rewrite Sz1 in In1. rewrite Sz20 in In20. rewrite Sz21 in In21.
      change (to_Z 40%uint63) with 40 in In1, In20, In21.
      (* [comment removed for export] *)
      pose proof (post_magree H IMX GenA0_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0) as MAG. cbn [q_m0 Q] in MAG.
      pose proof (post_rw_cells rho' ms1 G' GenA0_asan.X HXC) as RWC.
      pose proof (post_blk_rw_cells H IMX GenA0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenA0_asan.X X1 Hsz HXB) as RWB.
      destruct (post_errno H IMX GenA0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1) as [errv' Herr'].
      set (m1 := ms_mem ms1) in *.
      destruct Hfresh as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & (M1 & M2 & M3 & M4)).
      (* [comment removed for export] *)
      assert (AGR : forall A n, unw_range GenA0_asan.K A n = true -> forall cs, Z.of_nat (cells_size cs) = n -> rw_cells asegs m A cs -> rw_cells asegs m1 A cs).
      { intros A n Hu cs Hn Hrw. apply (rw_cells_agree (in_range A n) m m1 A cs (MAG A n Hu) Hrw). rewrite Hn. exact (fun a h => h). }
      assert (AGN : forall A n, unw_range GenA0_asan.K A n = true -> 0 <= A -> A + n <= 2 ^ 64 -> none_on m A n -> none_on m1 A n).
      { intros A n Hu HA HAn Hn. exact (none_on_agree (in_range A n) m m1 A n (MAG A n Hu) Hn (fun a h => h) HA HAn). }
      assert (Nbio : none_on m1 A_defctx_exmeth_bio 8).
      { apply (AGN A_defctx_exmeth_bio 8 ltac:(vm_compute; reflexivity)); unfold A_defctx_exmeth_bio; [slia | slia |].
        intros a Ha. apply F3. unfold A_defctx. slia. }
      assert (Ntsd : none_on m1 (A_tsd_main + 8) 8).
      { apply (AGN (A_tsd_main + 8) 8 ltac:(vm_compute; reflexivity)); unfold A_tsd_main; [slia | slia | exact F21]. }
      assert (Nstop : none_on m1 A_stopped 1).
      { apply (AGN A_stopped 1 ltac:(vm_compute; reflexivity)); unfold A_stopped; [slia | slia | exact F10]. }
      (* [comment removed for export] *)
      exists (rv rho' (a_F st') 5), (rv rho' (a_F st') 6), (rv rho' (a_F st') 7),
             (rv rho' (a_F st') 11), (rv rho' (a_F st') 12), (rv rho' (a_F st') 13), (rv rho' (a_F st') 14),
             (rv rho' (a_F st') 15), (rv rho' (a_F st') 16), (rv rho' (a_F st') 17),
             (rv rho' (a_F st') 28), (rv rho' (a_F st') 29), (rv rho' (a_F st') 30), (rv rho' (a_F st') 31),
             m1, errv', s', (LBN G'), (mkCX (gblock g1) (g_addr g20) (g_addr g21)), XS'.
      assert (Hn0 : forall t : int, (t <? GenA0_asan.n0)%uint63 = true -> to_Z t < to_Z (q_n0 Q)) by (intros t Ht; exact (i_ltb_lt _ _ Ht)).
      pose proof (fun kk t r => xreg_entry H IMX GenA0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenA0_asan.X X1 HXR GenA0_asan.d0 x W kk t r HQ) as XE.
      split.
      { rewrite Ek, (post_regs H IMX GenA0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1).
        change (q_F Q) with F. change (q_fc Q) with fc. replace (q_rho0 Q (c_tra GenA0_asan.K)) with ra by reflexivity. fold m1.
        rewrite <- (XE 1%uint63 4%uint63 1%uint63 eq_refl eq_refl (Hn0 4%uint63 eq_refl) eq_refl : rv rho' (a_F st') 1 = ra).
        rewrite <- (xreg_sp H IMX GenA0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenA0_asan.X X1 HXR GenA0_asan.d0 x W HQ eq_refl eq_refl : rv rho' (a_F st') 2 = sp).
        rewrite <- (XE 3%uint63 5%uint63 3%uint63 eq_refl eq_refl (Hn0 5%uint63 eq_refl) eq_refl : rv rho' (a_F st') 3 = gp).
        assert (E4 : rv rho' (a_F st') 4 = tp).
        { rewrite (xreg_W st' rho' G' GenA0_asan.X HXR 4%uint63 _ eq_refl : rv rho' (a_F st') 4 = _), Htp. apply bv_eq. vm_compute. reflexivity. }
        rewrite <- E4.
        rewrite <- (XE 8%uint63 9%uint63 8%uint63 eq_refl eq_refl (Hn0 9%uint63 eq_refl) eq_refl : rv rho' (a_F st') 8 = s0).
        rewrite <- (XE 9%uint63 10%uint63 9%uint63 eq_refl eq_refl (Hn0 10%uint63 eq_refl) eq_refl : rv rho' (a_F st') 9 = s1).
        assert (E10 : rv rho' (a_F st') 10 = Z_to_bv 64 A_defctx).
        { rewrite (xreg_W st' rho' G' GenA0_asan.X HXR 10%uint63 _ eq_refl : rv rho' (a_F st') 10 = _). apply bv_eq. vm_compute. reflexivity. }
        rewrite <- E10.
        rewrite <- (XE 18%uint63 19%uint63 18%uint63 eq_refl eq_refl (Hn0 19%uint63 eq_refl) eq_refl : rv rho' (a_F st') 18 = s2).
        rewrite <- (XE 19%uint63 20%uint63 19%uint63 eq_refl eq_refl (Hn0 20%uint63 eq_refl) eq_refl : rv rho' (a_F st') 19 = s3).
        rewrite <- (XE 20%uint63 21%uint63 20%uint63 eq_refl eq_refl (Hn0 21%uint63 eq_refl) eq_refl : rv rho' (a_F st') 20 = s4).
        rewrite <- (XE 21%uint63 22%uint63 21%uint63 eq_refl eq_refl (Hn0 22%uint63 eq_refl) eq_refl : rv rho' (a_F st') 21 = s5).
        rewrite <- (XE 22%uint63 23%uint63 22%uint63 eq_refl eq_refl (Hn0 23%uint63 eq_refl) eq_refl : rv rho' (a_F st') 22 = s6).
        rewrite <- (XE 23%uint63 24%uint63 23%uint63 eq_refl eq_refl (Hn0 24%uint63 eq_refl) eq_refl : rv rho' (a_F st') 23 = s7).
        rewrite <- (XE 24%uint63 25%uint63 24%uint63 eq_refl eq_refl (Hn0 25%uint63 eq_refl) eq_refl : rv rho' (a_F st') 24 = s8).
        rewrite <- (XE 25%uint63 26%uint63 25%uint63 eq_refl eq_refl (Hn0 26%uint63 eq_refl) eq_refl : rv rho' (a_F st') 25 = s9).
        rewrite <- (XE 26%uint63 27%uint63 26%uint63 eq_refl eq_refl (Hn0 27%uint63 eq_refl) eq_refl : rv rho' (a_F st') 26 = s10).
        rewrite <- (XE 27%uint63 28%uint63 27%uint63 eq_refl eq_refl (Hn0 28%uint63 eq_refl) eq_refl : rv rho' (a_F st') 27 = s11).
        reflexivity. }
      split; [exact Hmp|].
      split.
      { (* [comment removed for export] *)
        split; [exact Hak|].
        split; [exact (post_inv H IMX GenA0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_aconst H IMX GenA0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_stk H IMX GenA0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [rewrite Eerr; exact Herr'|].
        split; [exact (post_auxv H IMX GenA0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_heap H IMX GenA0_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0)|].
        split.
        { destruct Hmf as (fb & Hrw & Hfb & H01). exists fb. split; [|split; [exact Hfb | exact H01]].
          apply (AGR A_mem_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Hrw]. }
        destruct Himpl as (I1 & I2 & I3).
        split.
        { split; [apply (AGR A_malloc_impl 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact I1]|].
          split; [apply (AGR A_realloc_impl 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact I2]|].
          apply (AGR A_free_impl 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact I3]. }
        split; [apply (AGR A_got_CRYPTO_malloc 32 ltac:(vm_compute; reflexivity)); [reflexivity | exact Hgot]|].
        intros a Ha. unfold arelro_lib in Hrelro.
        rewrite (proj1 (MAG 0x571000 (0x5ea000 - 0x571000) ltac:(vm_compute; reflexivity) a ltac:(slia) ltac:(unfold in_range; slia))). exact (Hrelro a Ha). }
      split.
      { (* [comment removed for export] *)
        cbn [ctxph_delta cx_exlock cx_olock cx_ilock].
        split; [rewrite (LBN_length G' GenA0_asan.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        split; [rewrite (LBN_bytes G' GenA0_asan.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        split; [exact In1g|].
        exists (g_id g20), (g_id g21). split; [exact In20 | exact In21]. }
      split.
      { (* [comment removed for export] *)
        unfold LBN. apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (g & <- & Hg). apply (proj2 (in_rev _ _)) in Hg.
        cbn [gblock blk_addr blk_size fst snd]. exact (proj1 (Forall_forall _ _) HSH g Hg). }
      split.
      { (* [comment removed for export] *)
        cbn [CTXPH]. split.
        - unfold CTX_statics. cbn [cx_exlock cx_olock cx_ilock]. unfold gblock. cbn [blk_addr fst snd].
          split; [apply (RWC (of_Z A_defctx_inited)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_defctx_tlkey)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_defctx_tlkey_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_defctx_tlkey_ret)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_defctx_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_defctx_once_ret)); vm_compute; reflexivity|].
          split; [exact Rexl|].
          split.
          { apply (rw_cells_recast asegs m1 A_defctx_exmeth_bio [Cells.CB 8%nat (repeat (Z_to_bv 8 0) 8)]);
              [ apply (none_on_rw_cells m1 A_defctx_exmeth_bio); [exact Nbio | vm_compute; reflexivity | unfold A_defctx_exmeth_bio; slia | rewrite repeat_length; unfold A_defctx_exmeth_bio; slia]
              | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]. }
          split.
          { unfold LIBKEY0. apply (rw_cells_recast asegs m1 (A_tsd_main + 8 * 1) [Cells.CB 8%nat (repeat (Z_to_bv 8 0) 8)]);
              [ replace (A_tsd_main + 8 * 1) with (A_tsd_main + 8) by slia;
                apply (none_on_rw_cells m1 (A_tsd_main + 8)); [exact Ntsd | vm_compute; reflexivity | unfold A_tsd_main; slia | rewrite repeat_length; unfold A_tsd_main; slia]
              | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]. }
          split; [apply (RWC (of_Z A_destructor_key)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_base_inited)); vm_compute; reflexivity|].
          split.
          { apply (rw_cells_recast asegs m1 A_stopped [Cells.CB 1%nat [Z_to_bv 8 0]]);
              [ apply (none_on_rw_cells m1 A_stopped); [exact Nstop | vm_compute; reflexivity | unfold A_stopped; slia | unfold A_stopped; cbn; slia]
              | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]. }
          split; [apply (RWC (of_Z A_in_init_config_key)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_base_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_base_ret)); vm_compute; reflexivity|].
          split; [exact Rol|].
          split; [exact Ril|].
          split; [unfold LIBKEY0; apply (RWC (of_Z (A_keys + 8 * 1))); vm_compute; reflexivity|].
          apply (AGR A_keys 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact M1].
        - split.
          + split; [apply in_app_iff; left; exact In1g|]. split; [unfold gblock; cbn [blk_size snd]; rewrite Sz1; reflexivity|].
            split.
            { pose proof (post_block_range H IMX GenA0_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0 _ ltac:(apply in_app_iff; left; exact In1)) as (R0 & R16 & Rn & Rtop & Rce & _).
              cbn [blk_addr blk_size fst snd] in R0, R16, Rn, Rtop, Rce. pose proof aceil_facts as ACF. unfold arange, MUTEX_SIZE. cbn [cx_exlock blk_addr blk_size gblock fst snd]. unfold AIMG_TOP in *.
              split; [exact R0|]. split; [exact R16|]. split; [clear; slia|]. split; [clear -Rtop; slia|]. clear -Rce ACF; slia. }
            unfold MUTEX. cbn [cx_exlock blk_addr blk_size gblock fst snd]. rewrite <- (Z.add_0_r (g_addr g1)). change 0 with (to_Z 0%uint63) at 1.
            apply (RWB 1%uint63 g1 0%uint63 _ Hg1). vm_compute. reflexivity.
          + exists (g_id g20), (g_id g21). split; apply in_app_iff; left; assumption. }
      split.
      { (* [comment removed for export] *)
        intros _. unfold CTX_keys.
        split; [unfold LIBKEY0; apply (RWC (of_Z A_next_key)); vm_compute; reflexivity|].
        split.
        { apply (proj2 (rw_cells_app asegs m1 A_key_lock [C8 (wz 0)] [C8 (wz 0)])). split.
          - apply (RWC (of_Z A_key_lock)); vm_compute; reflexivity.
          - cbn [cells_size csize Z.of_nat].
            apply (AGR (A_key_lock + 8) 8 ltac:(vm_compute; reflexivity)); [reflexivity |].
            exact (proj2 (proj1 (rw_cells_app asegs m A_key_lock [C8 (wz 0)] [C8 (wz 0)]) M3)). }
        split; [apply (RWC (of_Z A_td_cancelbuf)); vm_compute; reflexivity|].
        apply (AGR A_td_tsd_used 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact M4]. }
      split; [exact (post_xs H IMX GenA0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
      split; [exact (post_rfs H IMX GenA0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
      split.
      { (* [comment removed for export] *)
        cbn [ctxph_foot].
        eapply xpres_weaken; [exact (post_xpres H IMX GenA0_asan.KA chk0_K Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0 _ chk0_xw) | apply Z.eq_le_incl; reflexivity | intros b Hb; exact Hb |].
        intros a Ha. apply rin_ivs_app. apply rin_ivs_app in Ha. tauto. }
      pose proof (post_AL H IMX GenA0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 Hcs) as HAL'. unfold Q in HAL'. cbn [q_AL0 q_cs] in HAL'.
      pose proof (csum_le H HH (ka_costs GenA0_asan.KA) CTXINIT_BYTES CTXINIT_BYTES ltac:(apply Z.leb_le; exact chk0_msum) ltac:(apply Z.leb_le; exact chk0_fsum)) as Hcsum.
      cbn [ctxph_cost]. unfold CTXINIT_COST. clear - HAL' Hcsum. slia. }
    { (* [comment removed for export] *)
      assert (Cc : to_Z (c_cost GenA16_asan.K) <= 2 ^ 16) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cn : to_Z (c_cnt GenA16_asan.K) <= 160) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cs : to_Z (c_stack GenA16_asan.K) = 9040) by (vm_compute; reflexivity).
      assert (Cf : Z.to_nat (to_Z (ka_fsmax GenA16_asan.KA)) = 3%nat) by (vm_compute; reflexivity).
      assert (Hby' : lb_bytes LB + to_Z (c_cost GenA16_asan.K) <= as_LIVE_MAX H) by (clear - Hby Cc; slia).
      assert (Hcnt' : Z.of_nat (length LB) + to_Z (c_cnt GenA16_asan.K) <= as_LIVE_CNT_MAX H) by (clear - Hcnt Cn; slia).
      assert (Hlo' : lo <= bv_unsigned (x 2) - to_Z (c_stack GenA16_asan.K)) by (clear - Hlo Cs; slia).
      assert (Hsp32' : (bv_unsigned (x 2) - to_Z (c_stack GenA16_asan.K)) mod 32 = 0) by (rewrite Cs; exact Hsp32).
      assert (Hlf' : (length LF + Z.to_nat (to_Z (ka_fsmax GenA16_asan.KA)) <= AFS_MAXLIVE)%nat) by (rewrite Cf; clear - Hlf; slia).
      assert (HALc : csum H (ka_costs GenA16_asan.KA) <= as_AL H s).
      { eapply Z.le_trans; [| exact HAL]. unfold CTXINIT_COST.
        apply (csum_le H HH); apply Z.leb_le; [exact chk16_msum | exact chk16_fsum]. }
      pose proof (rows_closed (as_TR H) PFC_CTXINIT (ka_pfc GenA16_asan.KA) chk16_pfc Hclosed) as Hpfc.
      pose proof (rows_open (as_TR H) PF_ctxinit (ka_pfo GenA16_asan.KA) (bv_unsigned (x 1)) CH chk16_pfo Hpf) as Hpfo.
      pose proof (start_RnA H GenA16_asan.KA GenA16_asan.d0 S_A x W F fc m lo chk16_K
                    (S_A_holds x m errv can Etp Himpl Hmf Hinv Hrelro Hfresh Hac Herr Hcan)
                    Hstk (conj Hhl Hlo') Hsp63 Hsp16 Hsp32' IMX GenA16_asan.facts0 GenA16_asan.n0 IMX_ok IMX_wr_ok chk16_ho chk16_tags chk16_facts) as HRn.
      pose proof (i2a_certificate H IMX GenA16_asan.KA GenA16_asan.code chk16_K HHx IMX_ok IMX_wr_ok chk16_code (ro_const_introA GenA16_asan.KA chk16_roc)
                    (sh0_of_aconst GenA16_asan.KA chk16_sh0) Hpfc (anode_fsmalloc_sound H IMX GenA16_asan.KA chk16_K HHx (sh0_of_aconst GenA16_asan.KA chk16_sh0)) (anode_fsfree_sound H IMX GenA16_asan.KA chk16_K HHx (sh0_of_aconst GenA16_asan.KA chk16_sh0) GenA16_asan.code chk16_code) (anode_memset_sound H IMX GenA16_asan.KA chk16_K HHx (sh0_of_aconst GenA16_asan.KA chk16_sh0)) (anode_memcpy_sound H IMX GenA16_asan.KA chk16_K HHx IMX_ok (sh0_of_aconst GenA16_asan.KA chk16_sh0)) (anode_strlen_sound H IMX GenA16_asan.KA chk16_K HHx IMX_ok (sh0_of_aconst GenA16_asan.KA chk16_sh0)) (anode_memalign_sound H IMX GenA16_asan.KA chk16_K HHx IMX_ok IMX_wr_ok (sh0_of_aconst GenA16_asan.KA chk16_sh0) Hpfc (ro_const_introA GenA16_asan.KA chk16_roc) MAL)
                    GenA16_asan.fuel (I2AS (state_of GenA16_asan.d0) GenA16_asan.n0 GenA16_asan.blk0 [] 0%uint63 0%uint63 0%uint63 []) GenA16_asan.X [] (rho_ofA GenA16_asan.K GenA16_asan.d0 x W) x F fc msF m mo s LB LF lo B CH
                    chk16_run chk16_shape eq_refl eq_refl (List.NoDup_nil _) (Forall_nil _)
                    HRn eq_refl eq_refl eq_refl eq_refl Hvis Hkrel Hheap Hrfs Hac Hsh0 Hchain HCH Hpfo HALc Hby' Hcnt' Hlf'
                    Haux HB HB64 Hstk Hhl Hlo' Hsp16 Hsp32' Herr Hinv) as HC.
      clear HRn.
      match goal with |- as_SR _ _ ?c => match type of HC with as_SR _ _ ?c' => replace c with c' by reflexivity end end.
      apply (ah_mono H HH _ _ _ HC). clear HC.
      (* [comment removed for export] *)
      intros k (rho' & st' & s' & LB' & G' & XS' & ms1 & Ek & Hak & Hmp & (msF1 & mo1 & X1) & Hfin & Hcs & HXR & HXC & HXB & Hsz & _ & HSH).
      set (Q := I2AE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in X1.
      assert (HG0 : q_G0 Q = []) by reflexivity.
      assert (HQ : q_rho0 Q = rho_ofA GenA16_asan.K GenA16_asan.d0 x W) by reflexivity.
      (* [comment removed for export] *)
      destruct (post_ptr_rw rho' ms1 G' GenA16_asan.X HXC (of_Z A_defctx_exlock) 1%uint63 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g1 & Hg1 & Rexl).
      destruct (post_ptr_rw rho' ms1 G' GenA16_asan.X HXC (of_Z A_optsdone_lock) 20%uint63 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g20 & Hg20 & Rol).
      destruct (post_ptr_rw rho' ms1 G' GenA16_asan.X HXC (of_Z A_init_lock) 21%uint63 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g21 & Hg21 & Ril).
      change (to_Z 0%uint63) with 0 in Rexl, Rol, Ril. rewrite Z.add_0_r in Rexl, Rol, Ril.
      destruct (blk_of_LBN G' GenA16_asan.X Hsz _ _ Hg1) as (In1 & InG1 & Sz1).
      destruct (blk_of_LBN G' GenA16_asan.X Hsz _ _ Hg20) as (In20 & _ & Sz20).
      destruct (blk_of_LBN G' GenA16_asan.X Hsz _ _ Hg21) as (In21 & _ & Sz21).
      change (nth (Z.to_nat (to_Z 1%uint63)) (x_sizes GenA16_asan.X) 0%uint63) with 40%uint63 in Sz1.
      change (nth (Z.to_nat (to_Z 20%uint63)) (x_sizes GenA16_asan.X) 0%uint63) with 40%uint63 in Sz20.
      change (nth (Z.to_nat (to_Z 21%uint63)) (x_sizes GenA16_asan.X) 0%uint63) with 40%uint63 in Sz21.
      pose proof In1 as In1g. unfold gblock in In1, In20, In21. rewrite Sz1 in In1. rewrite Sz20 in In20. rewrite Sz21 in In21.
      change (to_Z 40%uint63) with 40 in In1, In20, In21.
      (* [comment removed for export] *)
      pose proof (post_magree H IMX GenA16_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0) as MAG. cbn [q_m0 Q] in MAG.
      pose proof (post_rw_cells rho' ms1 G' GenA16_asan.X HXC) as RWC.
      pose proof (post_blk_rw_cells H IMX GenA16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenA16_asan.X X1 Hsz HXB) as RWB.
      destruct (post_errno H IMX GenA16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1) as [errv' Herr'].
      set (m1 := ms_mem ms1) in *.
      destruct Hfresh as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & (M1 & M2 & M3 & M4)).
      (* [comment removed for export] *)
      assert (AGR : forall A n, unw_range GenA16_asan.K A n = true -> forall cs, Z.of_nat (cells_size cs) = n -> rw_cells asegs m A cs -> rw_cells asegs m1 A cs).
      { intros A n Hu cs Hn Hrw. apply (rw_cells_agree (in_range A n) m m1 A cs (MAG A n Hu) Hrw). rewrite Hn. exact (fun a h => h). }
      assert (AGN : forall A n, unw_range GenA16_asan.K A n = true -> 0 <= A -> A + n <= 2 ^ 64 -> none_on m A n -> none_on m1 A n).
      { intros A n Hu HA HAn Hn. exact (none_on_agree (in_range A n) m m1 A n (MAG A n Hu) Hn (fun a h => h) HA HAn). }
      assert (Nbio : none_on m1 A_defctx_exmeth_bio 8).
      { apply (AGN A_defctx_exmeth_bio 8 ltac:(vm_compute; reflexivity)); unfold A_defctx_exmeth_bio; [slia | slia |].
        intros a Ha. apply F3. unfold A_defctx. slia. }
      assert (Ntsd : none_on m1 (A_tsd_main + 8) 8).
      { apply (AGN (A_tsd_main + 8) 8 ltac:(vm_compute; reflexivity)); unfold A_tsd_main; [slia | slia | exact F21]. }
      assert (Nstop : none_on m1 A_stopped 1).
      { apply (AGN A_stopped 1 ltac:(vm_compute; reflexivity)); unfold A_stopped; [slia | slia | exact F10]. }
      (* [comment removed for export] *)
      exists (rv rho' (a_F st') 5), (rv rho' (a_F st') 6), (rv rho' (a_F st') 7),
             (rv rho' (a_F st') 11), (rv rho' (a_F st') 12), (rv rho' (a_F st') 13), (rv rho' (a_F st') 14),
             (rv rho' (a_F st') 15), (rv rho' (a_F st') 16), (rv rho' (a_F st') 17),
             (rv rho' (a_F st') 28), (rv rho' (a_F st') 29), (rv rho' (a_F st') 30), (rv rho' (a_F st') 31),
             m1, errv', s', (LBN G'), (mkCX (gblock g1) (g_addr g20) (g_addr g21)), XS'.
      assert (Hn0 : forall t : int, (t <? GenA16_asan.n0)%uint63 = true -> to_Z t < to_Z (q_n0 Q)) by (intros t Ht; exact (i_ltb_lt _ _ Ht)).
      pose proof (fun kk t r => xreg_entry H IMX GenA16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenA16_asan.X X1 HXR GenA16_asan.d0 x W kk t r HQ) as XE.
      split.
      { rewrite Ek, (post_regs H IMX GenA16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1).
        change (q_F Q) with F. change (q_fc Q) with fc. replace (q_rho0 Q (c_tra GenA16_asan.K)) with ra by reflexivity. fold m1.
        rewrite <- (XE 1%uint63 4%uint63 1%uint63 eq_refl eq_refl (Hn0 4%uint63 eq_refl) eq_refl : rv rho' (a_F st') 1 = ra).
        rewrite <- (xreg_sp H IMX GenA16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenA16_asan.X X1 HXR GenA16_asan.d0 x W HQ eq_refl eq_refl : rv rho' (a_F st') 2 = sp).
        rewrite <- (XE 3%uint63 5%uint63 3%uint63 eq_refl eq_refl (Hn0 5%uint63 eq_refl) eq_refl : rv rho' (a_F st') 3 = gp).
        assert (E4 : rv rho' (a_F st') 4 = tp).
        { rewrite (xreg_W st' rho' G' GenA16_asan.X HXR 4%uint63 _ eq_refl : rv rho' (a_F st') 4 = _), Htp. apply bv_eq. vm_compute. reflexivity. }
        rewrite <- E4.
        rewrite <- (XE 8%uint63 9%uint63 8%uint63 eq_refl eq_refl (Hn0 9%uint63 eq_refl) eq_refl : rv rho' (a_F st') 8 = s0).
        rewrite <- (XE 9%uint63 10%uint63 9%uint63 eq_refl eq_refl (Hn0 10%uint63 eq_refl) eq_refl : rv rho' (a_F st') 9 = s1).
        assert (E10 : rv rho' (a_F st') 10 = Z_to_bv 64 A_defctx).
        { rewrite (xreg_W st' rho' G' GenA16_asan.X HXR 10%uint63 _ eq_refl : rv rho' (a_F st') 10 = _). apply bv_eq. vm_compute. reflexivity. }
        rewrite <- E10.
        rewrite <- (XE 18%uint63 19%uint63 18%uint63 eq_refl eq_refl (Hn0 19%uint63 eq_refl) eq_refl : rv rho' (a_F st') 18 = s2).
        rewrite <- (XE 19%uint63 20%uint63 19%uint63 eq_refl eq_refl (Hn0 20%uint63 eq_refl) eq_refl : rv rho' (a_F st') 19 = s3).
        rewrite <- (XE 20%uint63 21%uint63 20%uint63 eq_refl eq_refl (Hn0 21%uint63 eq_refl) eq_refl : rv rho' (a_F st') 20 = s4).
        rewrite <- (XE 21%uint63 22%uint63 21%uint63 eq_refl eq_refl (Hn0 22%uint63 eq_refl) eq_refl : rv rho' (a_F st') 21 = s5).
        rewrite <- (XE 22%uint63 23%uint63 22%uint63 eq_refl eq_refl (Hn0 23%uint63 eq_refl) eq_refl : rv rho' (a_F st') 22 = s6).
        rewrite <- (XE 23%uint63 24%uint63 23%uint63 eq_refl eq_refl (Hn0 24%uint63 eq_refl) eq_refl : rv rho' (a_F st') 23 = s7).
        rewrite <- (XE 24%uint63 25%uint63 24%uint63 eq_refl eq_refl (Hn0 25%uint63 eq_refl) eq_refl : rv rho' (a_F st') 24 = s8).
        rewrite <- (XE 25%uint63 26%uint63 25%uint63 eq_refl eq_refl (Hn0 26%uint63 eq_refl) eq_refl : rv rho' (a_F st') 25 = s9).
        rewrite <- (XE 26%uint63 27%uint63 26%uint63 eq_refl eq_refl (Hn0 27%uint63 eq_refl) eq_refl : rv rho' (a_F st') 26 = s10).
        rewrite <- (XE 27%uint63 28%uint63 27%uint63 eq_refl eq_refl (Hn0 28%uint63 eq_refl) eq_refl : rv rho' (a_F st') 27 = s11).
        reflexivity. }
      split; [exact Hmp|].
      split.
      { (* [comment removed for export] *)
        split; [exact Hak|].
        split; [exact (post_inv H IMX GenA16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_aconst H IMX GenA16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_stk H IMX GenA16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [rewrite Eerr; exact Herr'|].
        split; [exact (post_auxv H IMX GenA16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_heap H IMX GenA16_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0)|].
        split.
        { destruct Hmf as (fb & Hrw & Hfb & H01). exists fb. split; [|split; [exact Hfb | exact H01]].
          apply (AGR A_mem_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Hrw]. }
        destruct Himpl as (I1 & I2 & I3).
        split.
        { split; [apply (AGR A_malloc_impl 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact I1]|].
          split; [apply (AGR A_realloc_impl 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact I2]|].
          apply (AGR A_free_impl 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact I3]. }
        split; [apply (AGR A_got_CRYPTO_malloc 32 ltac:(vm_compute; reflexivity)); [reflexivity | exact Hgot]|].
        intros a Ha. unfold arelro_lib in Hrelro.
        rewrite (proj1 (MAG 0x571000 (0x5ea000 - 0x571000) ltac:(vm_compute; reflexivity) a ltac:(slia) ltac:(unfold in_range; slia))). exact (Hrelro a Ha). }
      split.
      { (* [comment removed for export] *)
        cbn [ctxph_delta cx_exlock cx_olock cx_ilock].
        split; [rewrite (LBN_length G' GenA16_asan.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        split; [rewrite (LBN_bytes G' GenA16_asan.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        split; [exact In1g|].
        exists (g_id g20), (g_id g21). split; [exact In20 | exact In21]. }
      split.
      { (* [comment removed for export] *)
        unfold LBN. apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (g & <- & Hg). apply (proj2 (in_rev _ _)) in Hg.
        cbn [gblock blk_addr blk_size fst snd]. exact (proj1 (Forall_forall _ _) HSH g Hg). }
      split.
      { (* [comment removed for export] *)
        cbn [CTXPH]. split.
        - unfold CTX_statics. cbn [cx_exlock cx_olock cx_ilock]. unfold gblock. cbn [blk_addr fst snd].
          split; [apply (RWC (of_Z A_defctx_inited)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_defctx_tlkey)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_defctx_tlkey_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_defctx_tlkey_ret)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_defctx_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_defctx_once_ret)); vm_compute; reflexivity|].
          split; [exact Rexl|].
          split.
          { apply (rw_cells_recast asegs m1 A_defctx_exmeth_bio [Cells.CB 8%nat (repeat (Z_to_bv 8 0) 8)]);
              [ apply (none_on_rw_cells m1 A_defctx_exmeth_bio); [exact Nbio | vm_compute; reflexivity | unfold A_defctx_exmeth_bio; slia | rewrite repeat_length; unfold A_defctx_exmeth_bio; slia]
              | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]. }
          split.
          { unfold LIBKEY0. apply (rw_cells_recast asegs m1 (A_tsd_main + 8 * 1) [Cells.CB 8%nat (repeat (Z_to_bv 8 0) 8)]);
              [ replace (A_tsd_main + 8 * 1) with (A_tsd_main + 8) by slia;
                apply (none_on_rw_cells m1 (A_tsd_main + 8)); [exact Ntsd | vm_compute; reflexivity | unfold A_tsd_main; slia | rewrite repeat_length; unfold A_tsd_main; slia]
              | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]. }
          split; [apply (RWC (of_Z A_destructor_key)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_base_inited)); vm_compute; reflexivity|].
          split.
          { apply (rw_cells_recast asegs m1 A_stopped [Cells.CB 1%nat [Z_to_bv 8 0]]);
              [ apply (none_on_rw_cells m1 A_stopped); [exact Nstop | vm_compute; reflexivity | unfold A_stopped; slia | unfold A_stopped; cbn; slia]
              | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]. }
          split; [apply (RWC (of_Z A_in_init_config_key)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_base_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_base_ret)); vm_compute; reflexivity|].
          split; [exact Rol|].
          split; [exact Ril|].
          split; [unfold LIBKEY0; apply (RWC (of_Z (A_keys + 8 * 1))); vm_compute; reflexivity|].
          apply (AGR A_keys 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact M1].
        - split.
          + split; [apply in_app_iff; left; exact In1g|]. split; [unfold gblock; cbn [blk_size snd]; rewrite Sz1; reflexivity|].
            split.
            { pose proof (post_block_range H IMX GenA16_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0 _ ltac:(apply in_app_iff; left; exact In1)) as (R0 & R16 & Rn & Rtop & Rce & _).
              cbn [blk_addr blk_size fst snd] in R0, R16, Rn, Rtop, Rce. pose proof aceil_facts as ACF. unfold arange, MUTEX_SIZE. cbn [cx_exlock blk_addr blk_size gblock fst snd]. unfold AIMG_TOP in *.
              split; [exact R0|]. split; [exact R16|]. split; [clear; slia|]. split; [clear -Rtop; slia|]. clear -Rce ACF; slia. }
            unfold MUTEX. cbn [cx_exlock blk_addr blk_size gblock fst snd]. rewrite <- (Z.add_0_r (g_addr g1)). change 0 with (to_Z 0%uint63) at 1.
            apply (RWB 1%uint63 g1 0%uint63 _ Hg1). vm_compute. reflexivity.
          + exists (g_id g20), (g_id g21). split; apply in_app_iff; left; assumption. }
      split.
      { (* [comment removed for export] *)
        intros _. unfold CTX_keys.
        split; [unfold LIBKEY0; apply (RWC (of_Z A_next_key)); vm_compute; reflexivity|].
        split.
        { apply (proj2 (rw_cells_app asegs m1 A_key_lock [C8 (wz 0)] [C8 (wz 0)])). split.
          - apply (RWC (of_Z A_key_lock)); vm_compute; reflexivity.
          - cbn [cells_size csize Z.of_nat].
            apply (AGR (A_key_lock + 8) 8 ltac:(vm_compute; reflexivity)); [reflexivity |].
            exact (proj2 (proj1 (rw_cells_app asegs m A_key_lock [C8 (wz 0)] [C8 (wz 0)]) M3)). }
        split; [apply (RWC (of_Z A_td_cancelbuf)); vm_compute; reflexivity|].
        apply (AGR A_td_tsd_used 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact M4]. }
      split; [exact (post_xs H IMX GenA16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
      split; [exact (post_rfs H IMX GenA16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
      split.
      { (* [comment removed for export] *)
        cbn [ctxph_foot].
        eapply xpres_weaken; [exact (post_xpres H IMX GenA16_asan.KA chk16_K Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0 _ chk16_xw) | apply Z.eq_le_incl; reflexivity | intros b Hb; exact Hb |].
        intros a Ha. apply rin_ivs_app. apply rin_ivs_app in Ha. tauto. }
      pose proof (post_AL H IMX GenA16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 Hcs) as HAL'. unfold Q in HAL'. cbn [q_AL0 q_cs] in HAL'.
      pose proof (csum_le H HH (ka_costs GenA16_asan.KA) CTXINIT_BYTES CTXINIT_BYTES ltac:(apply Z.leb_le; exact chk16_msum) ltac:(apply Z.leb_le; exact chk16_fsum)) as Hcsum.
      cbn [ctxph_cost]. unfold CTXINIT_COST. clear - HAL' Hcsum. slia. }
  Qed.
End C.
