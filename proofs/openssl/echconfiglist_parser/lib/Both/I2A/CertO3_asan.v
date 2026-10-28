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
     ECH_AImg ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1 ECH_AStmt_C3 ECH_APF_C4 ECH_AStmt_C4.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2 Require Import I2ImgAsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeKit
  I2ANodeSig I2ANodeM I2ASound I2ACert I2AStart I2ASh0 I2ATop I2ACertE CertA_asanK.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2 Require GenO3s0_0_asan GenO3s0_16_asan GenO3s1_0_asan GenO3s1_16_asan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2ANodeS I2ANodeX I2ANodeA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import CertO3_asanK.
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
  Lemma S_O3_holds : forall (x : Z -> word) m (errv : word) (cx : ctxinfo) (save can : Z),
    x 4 = Z_to_bv 64 ATP -> x 10 = Z_to_bv 64 save -> IMPL_mem m -> MEMFLAG m 1 -> mem_inv asegs m -> arelro_lib m ->
    ERR_fresh_core m -> CTX_keys m -> CTX_statics m cx -> ACONST m ->
    rw_cells asegs m AERRNO [C4 errv] -> rw_cells asegs m ACANARYX [C8 (Z_to_bv 64 can)] ->
    ssrc_holds H (S_O3 save) x [(32%uint63, errv); (33%uint63, wz (cx_olock cx)); (34%uint63, Z_to_bv 64 can)] m.
  Proof.
    intros x m errv cx save can Htp Ha0 Himpl Hmf Hinv Hrelro Hfresh Hkeys Hctx Hac Herr Hcan.
    destruct Himpl as (I1 & I2 & I3).
    destruct Hfresh as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    destruct Hkeys as (K1 & K2 & K3 & K4).
    destruct Hctx as (Cs1 & Cs2 & Cs3 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10 & Cs11 & Cs12 & Cs13 & Cs14 & Cs15 & Cs16 & Cs17 & Cs18 & Cs19).
    pose proof (ACONST_cell m AMUSL_TSD _ Hac ltac:(in_nth)) as C1.
    pose proof (proj2 (ACONST_shbase m Hac)) as C2. pose proof (proj2 (ACONST_uar m Hac)) as C3.
    unfold ssrc_holds, S_O3. cbn [s_cregs s_vals s_clear s_words s_blks fst snd].
    split; [|split; [|split; [|split]]].
    - constructor; [exact Htp | constructor; [exact Ha0 | constructor]].
    - constructor. { eapply schunk_of_rw_cells; [exact I1|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact I2|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact I3|]. vm_compute. reflexivity. }
      constructor.
      { destruct Hmf as (fb & Hrw & Hfb & _). intros i Hi. destruct i as [|i]; [|cbn in Hi; slia]. cbn [nth].
        destruct Hrw as [[_ (_ & _ & HB)] _]. cbn [cells_bytes cbytes app length] in HB. rewrite (HB 0%nat ltac:(slia)). cbn [nth_error].
        f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hfb. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact C1|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact C2|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact C3|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Cs12|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Cs14|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Cs15|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Cs10|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Cs18|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact Cs19|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact K1|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact K2|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact K3|]. vm_compute. reflexivity. }
      constructor. { eapply schunk_of_rw_cells; [exact K4|]. vm_compute. reflexivity. }
      constructor.
    - unfold arelro_lib in Hrelro. unfold none_on in *.
      unfold A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret,
        A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_keys, A_tsd_main, LIBKEY0 in *.
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
      constructor.
    - constructor; [exact (sword_of_C4 m AERRNO errv Herr)|].
      constructor; [exact (sword_of_C8 m A_optsdone_lock _ Cs16)|].
      constructor; [exact (sword_of_C8 m ACANARYX _ Hcan) | constructor].
    - constructor.
  Qed.

  Theorem egs_fresh_cert : egs_fresh_stmt H.
  Proof.
    unfold egs_fresh_stmt, egs_stmt_for.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF cx save lo B errv CH
           Hvis Ha0 Hsave Hs01 Hheap Hkrel Hby Hcnt Haux HB Hsp16 Hstk Hhl Hlo Hsh0 Herr Hinv Htp Hac Hmf Himpl Hgot Hrelro
           Herrph Herrx Hbelow Hershad Hctx Hrfs Hlf Hchain HCH Hpf Hclosed HAL Hra.
    change (blocks_ERRST errst_zero) with (@nil block) in *. cbn [app] in Hheap, Hby, Hcnt.
    cbn [errph_bytes errph_cnt errph_stack errph_sh0 ERRPH_LF errph_cost errph_closed_ok PF_egs ERRPH CTXPH] in Hby, Hcnt, Hlo, Hsh0, Herrph, Hctx, Hlf, Hpf, Hclosed, HAL.
    unfold ERRINIT_BYTES, ERRINIT_CNT, ERRINIT_STACK, FR_ossl_err_get_state_int, AREALLOC_STACK in Hby, Hcnt, Hlo.
    destruct Herrph as [Hfresh Hkeys]. destruct Hctx as [Hstat Hblk].
    set (x := xregs_of3 errv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
    destruct (HHx_canary H HHx _ _ _ Hheap) as (can & _ & Hcan & Hcan64).
    set (W := [(32%uint63, errv); (33%uint63, wz (cx_olock cx)); (34%uint63, Z_to_bv 64 can)]).
    (* [comment removed for export] *)
    pose proof Hsh0 as (g0_ & _ & HhiA & _ & _). unfold AAPP_HI in HhiA.
    assert (Hsp63 : bv_unsigned (x 2) < 2 ^ 63) by (clear - HhiA; change (x 2) with sp; slia).
    assert (HB64 : bv_unsigned (x 2) < 2 ^ 64) by (clear - Hsp63; slia).
    clear g0_ HhiA.
    change (bv_unsigned sp) with (bv_unsigned (x 2)) in HB, Hsp16, Hstk, Hlo, Hsh0, HCH.
    assert (Etp : x 4 = Z_to_bv 64 ATP) by exact Htp.
    assert (Es0 : bv_unsigned s0 = bv_unsigned (x 8)) by reflexivity. rewrite Es0 in Hchain.
    assert (Era : bv_unsigned ra = bv_unsigned (x 1)) by reflexivity. rewrite Era in Hpf.
    change (x 10 = Z_to_bv 64 save) in Ha0.
    assert (Hsp32 : (bv_unsigned (x 2) - 9056) mod 32 = 0 \/ (bv_unsigned (x 2) - 9072) mod 32 = 0) by (clear - Hsp16; slia).
    destruct (Hs01 eq_refl) as [Es | Es]; rewrite Es in Ha0 |- *; clear Es Hsave Hs01; destruct Hsp32 as [Hsp32 | Hsp32].
    { (* [comment removed for export] *)
      assert (Ea0 : x 10 = Z_to_bv 64 0) by exact Ha0.
      assert (Eerr : bv_unsigned tp + -164 = errA GenO3s0_0_asan.KA).
      { rewrite Htp, Z_to_bv_unsigned. vm_compute. reflexivity. }
      pose proof Herr as HerrE. rewrite Eerr in HerrE.
      assert (Cc : to_Z (c_cost GenO3s0_0_asan.K) <= 2 ^ 16) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cn : to_Z (c_cnt GenO3s0_0_asan.K) <= 1600) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cs : to_Z (c_stack GenO3s0_0_asan.K) = 9056) by (vm_compute; reflexivity).
      assert (Cf : Z.to_nat (to_Z (ka_fsmax GenO3s0_0_asan.KA)) = 4%nat) by (vm_compute; reflexivity).
      assert (Hby' : lb_bytes LB + to_Z (c_cost GenO3s0_0_asan.K) <= as_LIVE_MAX H) by (clear - Hby Cc; slia).
      assert (Hcnt' : Z.of_nat (length LB) + to_Z (c_cnt GenO3s0_0_asan.K) <= as_LIVE_CNT_MAX H) by (clear - Hcnt Cn; slia).
      assert (Hlo' : lo <= bv_unsigned (x 2) - to_Z (c_stack GenO3s0_0_asan.K)) by (clear - Hlo Cs; slia).
      assert (Hsp32' : (bv_unsigned (x 2) - to_Z (c_stack GenO3s0_0_asan.K)) mod 32 = 0) by (rewrite Cs; exact Hsp32).
      assert (Hlf' : (length LF + Z.to_nat (to_Z (ka_fsmax GenO3s0_0_asan.KA)) <= AFS_MAXLIVE)%nat) by (rewrite Cf; clear - Hlf; slia).
      assert (HALc : csum H (ka_costs GenO3s0_0_asan.KA) <= as_AL H s).
      { eapply Z.le_trans; [| exact HAL]. unfold ERRINIT_COST.
        apply (csum_le H HH); apply Z.leb_le; [exact chks0_0_msum | exact chks0_0_fsum]. }
      pose proof (rows_closed (as_TR H) PFC_ERRINIT (ka_pfc GenO3s0_0_asan.KA) chks0_0_pfc Hclosed) as Hpfc.
      pose proof (rows_open (as_TR H) PF_EGS_FRESH (ka_pfo GenO3s0_0_asan.KA) (bv_unsigned (x 1)) CH chks0_0_pfo Hpf) as Hpfo.
      pose proof (start_RnA H GenO3s0_0_asan.KA GenO3s0_0_asan.d0 (S_O3 0) x W F fc m lo chks0_0_K
                    (S_O3_holds x m errv cx 0 can Etp Ea0 Himpl Hmf Hinv Hrelro Hfresh Hkeys Hstat Hac HerrE Hcan)
                    Hstk (conj Hhl Hlo') Hsp63 Hsp16 Hsp32' IMX GenO3s0_0_asan.facts0 GenO3s0_0_asan.n0 IMX_ok IMX_wr_ok chks0_0_ho chks0_0_tags chks0_0_facts) as HRn.
      pose proof (i2a_certificate H IMX GenO3s0_0_asan.KA GenO3s0_0_asan.code chks0_0_K HHx IMX_ok IMX_wr_ok chks0_0_code (ro_const_introA GenO3s0_0_asan.KA chks0_0_roc)
                    (sh0_of_aconst GenO3s0_0_asan.KA chks0_0_sh0) Hpfc
                    (anode_fsmalloc_sound H IMX GenO3s0_0_asan.KA chks0_0_K HHx (sh0_of_aconst GenO3s0_0_asan.KA chks0_0_sh0))
                    (anode_fsfree_sound H IMX GenO3s0_0_asan.KA chks0_0_K HHx (sh0_of_aconst GenO3s0_0_asan.KA chks0_0_sh0) GenO3s0_0_asan.code chks0_0_code)
                    (anode_memset_sound H IMX GenO3s0_0_asan.KA chks0_0_K HHx (sh0_of_aconst GenO3s0_0_asan.KA chks0_0_sh0))
                    (anode_memcpy_sound H IMX GenO3s0_0_asan.KA chks0_0_K HHx IMX_ok (sh0_of_aconst GenO3s0_0_asan.KA chks0_0_sh0))
                    (anode_strlen_sound H IMX GenO3s0_0_asan.KA chks0_0_K HHx IMX_ok (sh0_of_aconst GenO3s0_0_asan.KA chks0_0_sh0)) (anode_memalign_sound H IMX GenO3s0_0_asan.KA chks0_0_K HHx IMX_ok IMX_wr_ok (sh0_of_aconst GenO3s0_0_asan.KA chks0_0_sh0) Hpfc (ro_const_introA GenO3s0_0_asan.KA chks0_0_roc) MAL)
                    GenO3s0_0_asan.fuel (I2AS (state_of GenO3s0_0_asan.d0) GenO3s0_0_asan.n0 GenO3s0_0_asan.blk0 [] 0%uint63 0%uint63 0%uint63 []) GenO3s0_0_asan.X [] (rho_ofA GenO3s0_0_asan.K GenO3s0_0_asan.d0 x W) x F fc msF m mo s LB LF lo B CH
                    chks0_0_run chks0_0_shape eq_refl eq_refl (List.NoDup_nil _) (Forall_nil _)
                    HRn eq_refl eq_refl eq_refl eq_refl Hvis Hkrel Hheap Hrfs Hac Hsh0 Hchain HCH Hpfo HALc Hby' Hcnt' Hlf'
                    Haux HB HB64 Hstk Hhl Hlo' Hsp16 Hsp32' HerrE Hinv) as HC.
      clear HRn.
      match goal with |- as_SR _ _ ?c => match type of HC with as_SR _ _ ?c' => replace c with c' by reflexivity end end.
      apply (ah_mono H HH _ _ _ HC). clear HC.
      (* [comment removed for export] *)
      intros k (rho' & st' & s' & LB' & G' & XS' & ms1 & Ek & Hak & Hmp & (msF1 & mo1 & X1) & Hfin & Hcs & HXR & HXC & HXB & Hsz & Hes & HSH).
      set (Q := I2AE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in X1.
      assert (HG0 : q_G0 Q = []) by reflexivity.
      assert (HQ : q_rho0 Q = rho_ofA GenO3s0_0_asan.K GenO3s0_0_asan.d0 x W) by reflexivity.
      pose proof (post_magree H IMX GenO3s0_0_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0) as MAG. cbn [q_m0 Q] in MAG.
      pose proof (post_magree_block H IMX GenO3s0_0_asan.KA chks0_0_K HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0) as MAGB. cbn [q_m0 q_LB0 Q] in MAGB.
      pose proof (post_rw_cells rho' ms1 G' GenO3s0_0_asan.X HXC) as RWC.
      pose proof (post_blk_rw_cells H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_0_asan.X X1 Hsz HXB) as RWB.
      pose proof (post_blk_arr H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_0_asan.X X1 Hsz HXB) as RWA.
      set (m1 := ms_mem ms1) in *.
      (* [comment removed for export] *)
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_0_asan.X HXC (of_Z (A_tsd_main + 8 * (LIBKEY0 + 3))) 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g0 & Hg0 & Rtsd3).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_0_asan.X HXC (of_Z (A_tsd_main + 8 * (LIBKEY0 + 1))) 4%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g4 & Hg4 & Rtsd1).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_0_asan.X HXC (of_Z A_glob_tevent_reg) 5%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g5 & Hg5 & Rtev).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_0_asan.X HXC (of_Z A_err_string_lock) 10%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g10 & Hg10 & Resl).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_0_asan.X HXC (of_Z A_int_error_hash) 11%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g11 & Hg11 & Resh).
      destruct (post_blk_ptr0 H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_0_asan.X X1 Hsz HXB 0%uint63 g0 24%uint63 1%uint63 Hg0 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s0_0_asan.X Hsz _ _ Hg0))); vm_compute; discriminate)) as (g1 & Hg1 & Rmkey).
      destruct (post_blk_ptr0 H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_0_asan.X X1 Hsz HXB 1%uint63 g1 24%uint63 2%uint63 Hg1 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s0_0_asan.X Hsz _ _ Hg1))); vm_compute; discriminate)) as (g2 & Hg2 & Rsa).
      destruct (post_blk_ptr0 H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_0_asan.X X1 Hsz HXB 2%uint63 g2 0%uint63 3%uint63 Hg2 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s0_0_asan.X Hsz _ _ Hg2))); vm_compute; discriminate)) as (g3 & Hg3 & Rnodes).
      change (to_Z 0%uint63) with 0 in Rnodes. rewrite Z.add_0_r in Rnodes.
      destruct (blk_of_LBN G' GenO3s0_0_asan.X Hsz _ _ Hg0) as (In0 & InG0 & Sz0). destruct (blk_of_LBN G' GenO3s0_0_asan.X Hsz _ _ Hg1) as (In1 & InG1 & Sz1).
      destruct (blk_of_LBN G' GenO3s0_0_asan.X Hsz _ _ Hg2) as (In2 & InG2 & Sz2). destruct (blk_of_LBN G' GenO3s0_0_asan.X Hsz _ _ Hg3) as (In3 & InG3 & Sz3).
      destruct (blk_of_LBN G' GenO3s0_0_asan.X Hsz _ _ Hg4) as (In4 & InG4 & Sz4).
      change (nth (Z.to_nat (to_Z 0%uint63)) (x_sizes GenO3s0_0_asan.X) 0%uint63) with 72%uint63 in Sz0.
      change (nth (Z.to_nat (to_Z 1%uint63)) (x_sizes GenO3s0_0_asan.X) 0%uint63) with 32%uint63 in Sz1.
      change (nth (Z.to_nat (to_Z 2%uint63)) (x_sizes GenO3s0_0_asan.X) 0%uint63) with 128%uint63 in Sz2.
      change (nth (Z.to_nat (to_Z 3%uint63)) (x_sizes GenO3s0_0_asan.X) 0%uint63) with 904%uint63 in Sz3.
      change (nth (Z.to_nat (to_Z 4%uint63)) (x_sizes GenO3s0_0_asan.X) 0%uint63) with 8%uint63 in Sz4.
      destruct (post_errno H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1) as [errv0 Herr0].
      (* [comment removed for export] *)
      assert (AGR : forall A n, unw_range GenO3s0_0_asan.K A n = true -> forall cs, Z.of_nat (cells_size cs) = n -> rw_cells asegs m A cs -> rw_cells asegs m1 A cs).
      { intros A n Hu cs Hn Hrw. apply (rw_cells_agree (in_range A n) m m1 A cs (MAG A n Hu) Hrw). rewrite Hn. exact (fun a h => h). }
      (* [comment removed for export] *)
      exists (rv rho' (a_F st') 5), (rv rho' (a_F st') 6), (rv rho' (a_F st') 7),
             (rv rho' (a_F st') 11), (rv rho' (a_F st') 12), (rv rho' (a_F st') 13), (rv rho' (a_F st') 14),
             (rv rho' (a_F st') 15), (rv rho' (a_F st') 16), (rv rho' (a_F st') 17),
             (rv rho' (a_F st') 28), (rv rho' (a_F st') 29), (rv rho' (a_F st') 30), (rv rho' (a_F st') 31),
             m1, errv0, s', (LBN G'),
             (mkEC (gblock g0) (gblock g1) (gblock g2) (gblock g3) (gblock g4) (g_addr g10) (g_addr g11) (g_addr g5)), XS'.
      assert (Hn0 : forall t : int, (t <? GenO3s0_0_asan.n0)%uint63 = true -> to_Z t < to_Z (q_n0 Q)) by (intros t Ht; exact (i_ltb_lt _ _ Ht)).
      pose proof (fun kk t r => xreg_entry H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_0_asan.X X1 HXR GenO3s0_0_asan.d0 x W kk t r HQ) as XE.
      cbn [ec_mkey ec_sa ec_nodes ec_es ec_hands ec_eslock ec_eshash ec_tevreg].
      split.
      { rewrite Ek, (post_regs H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1).
        change (q_F Q) with F. change (q_fc Q) with fc. replace (q_rho0 Q (c_tra GenO3s0_0_asan.K)) with ra by reflexivity. fold m1.
        rewrite <- (XE 1%uint63 4%uint63 1%uint63 eq_refl eq_refl (Hn0 4%uint63 eq_refl) eq_refl : rv rho' (a_F st') 1 = ra).
        rewrite <- (xreg_sp H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_0_asan.X X1 HXR GenO3s0_0_asan.d0 x W HQ eq_refl eq_refl : rv rho' (a_F st') 2 = sp).
        rewrite <- (XE 3%uint63 5%uint63 3%uint63 eq_refl eq_refl (Hn0 5%uint63 eq_refl) eq_refl : rv rho' (a_F st') 3 = gp).
        assert (E4 : rv rho' (a_F st') 4 = tp).
        { rewrite (xreg_W st' rho' G' GenO3s0_0_asan.X HXR 4%uint63 _ eq_refl : rv rho' (a_F st') 4 = _), Htp. apply bv_eq. vm_compute. reflexivity. }
        rewrite <- E4.
        rewrite <- (XE 8%uint63 9%uint63 8%uint63 eq_refl eq_refl (Hn0 9%uint63 eq_refl) eq_refl : rv rho' (a_F st') 8 = s0).
        rewrite <- (XE 9%uint63 10%uint63 9%uint63 eq_refl eq_refl (Hn0 10%uint63 eq_refl) eq_refl : rv rho' (a_F st') 9 = s1).
        assert (E10 : rv rho' (a_F st') 10 = Z_to_bv 64 (blk_addr (gblock g3))).
        { destruct (xreg_New st' rho' G' GenO3s0_0_asan.X HXR 10%uint63 3%uint63 0%uint63 eq_refl) as (g3' & Hg3' & E).
          rewrite Hg3 in Hg3'. injection Hg3' as <-. change (to_Z 10%uint63) with 10 in E. rewrite E, Z.add_0_r. reflexivity. }
        rewrite <- E10.
        rewrite <- (XE 18%uint63 18%uint63 18%uint63 eq_refl eq_refl (Hn0 18%uint63 eq_refl) eq_refl : rv rho' (a_F st') 18 = s2).
        rewrite <- (XE 19%uint63 19%uint63 19%uint63 eq_refl eq_refl (Hn0 19%uint63 eq_refl) eq_refl : rv rho' (a_F st') 19 = s3).
        rewrite <- (XE 20%uint63 20%uint63 20%uint63 eq_refl eq_refl (Hn0 20%uint63 eq_refl) eq_refl : rv rho' (a_F st') 20 = s4).
        rewrite <- (XE 21%uint63 21%uint63 21%uint63 eq_refl eq_refl (Hn0 21%uint63 eq_refl) eq_refl : rv rho' (a_F st') 21 = s5).
        rewrite <- (XE 22%uint63 22%uint63 22%uint63 eq_refl eq_refl (Hn0 22%uint63 eq_refl) eq_refl : rv rho' (a_F st') 22 = s6).
        rewrite <- (XE 23%uint63 23%uint63 23%uint63 eq_refl eq_refl (Hn0 23%uint63 eq_refl) eq_refl : rv rho' (a_F st') 23 = s7).
        rewrite <- (XE 24%uint63 24%uint63 24%uint63 eq_refl eq_refl (Hn0 24%uint63 eq_refl) eq_refl : rv rho' (a_F st') 24 = s8).
        rewrite <- (XE 25%uint63 25%uint63 25%uint63 eq_refl eq_refl (Hn0 25%uint63 eq_refl) eq_refl : rv rho' (a_F st') 25 = s9).
        rewrite <- (XE 26%uint63 26%uint63 26%uint63 eq_refl eq_refl (Hn0 26%uint63 eq_refl) eq_refl : rv rho' (a_F st') 26 = s10).
        rewrite <- (XE 27%uint63 27%uint63 27%uint63 eq_refl eq_refl (Hn0 27%uint63 eq_refl) eq_refl : rv rho' (a_F st') 27 = s11).
        reflexivity. }
      split; [exact Hmp|].
      split.
      { (* [comment removed for export] *)
        split; [exact Hak|].
        split; [exact (post_inv H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_aconst H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_stk H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_auxv H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [cbn [app]; exact (post_heap H IMX GenO3s0_0_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0)|].
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
      split; [rewrite Eerr; exact Herr0|].
      split; [intros Hne; exfalso; exact (Hne eq_refl)|].
      pose proof In0 as In0g. pose proof In1 as In1g. pose proof In2 as In2g. pose proof In3 as In3g. pose proof In4 as In4g.
      unfold gblock in In0, In1, In2, In3, In4.
      rewrite Sz0 in In0. rewrite Sz1 in In1. rewrite Sz2 in In2. rewrite Sz3 in In3. rewrite Sz4 in In4.
      change (to_Z 72%uint63) with 72 in In0. change (to_Z 32%uint63) with 32 in In1. change (to_Z 128%uint63) with 128 in In2.
      change (to_Z 904%uint63) with 904 in In3. change (to_Z 8%uint63) with 8 in In4.
      split.
      { (* [comment removed for export] *)
        cbn [errph_delta chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands].
        split; [rewrite (LBN_length G' GenO3s0_0_asan.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        split; [rewrite (LBN_bytes G' GenO3s0_0_asan.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        apply Forall_cons; [exact In0g|]. apply Forall_cons; [exact In1g|]. apply Forall_cons; [exact In2g|].
        apply Forall_cons; [exact In3g|]. apply Forall_cons; [exact In4g|]. apply Forall_nil. }
      split.
      { (* [comment removed for export] *)
        cbn [ERRPH]. unfold ERR_statics, ERR_chain. cbn [ec_mkey ec_sa ec_nodes ec_es ec_hands ec_eslock ec_eshash ec_tevreg chain_blocks].
        unfold gblock. cbn [blk_addr blk_size fst snd]. rewrite Sz0, Sz1, Sz2, Sz3, Sz4.
        change (to_Z 72%uint63) with 72. change (to_Z 32%uint63) with 32. change (to_Z 128%uint63) with 128.
        change (to_Z 904%uint63) with 904. change (to_Z 8%uint63) with 8.
        destruct Hstat as (Cs1 & Cs2 & Cs3 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10 & Cs11 & Cs12 & Cs13 & Cs14 & Cs15 & Cs16 & Cs17 & Cs18 & Cs19).
        split.
        - (* [comment removed for export] *)
          split; [apply (RWC (of_Z A_master_once_ret)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_master_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_master_key)); vm_compute; reflexivity|].
          split; [unfold LIBKEY0; exact Rtsd3|].
          split; [apply (AGR A_stopped 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs12]|].
          split; [apply (AGR A_base_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs14]|].
          split; [apply (AGR A_base_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs15]|].
          split; [apply (RWC (of_Z A_load_strings_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_load_strings_ret)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_optsdone)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_err_string_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_err_string_ret)); vm_compute; reflexivity|].
          split; [exact Resl|].
          split; [exact Resh|].
          split; [apply (RWC (of_Z A_tevent_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_tevent_ret)); vm_compute; reflexivity|].
          split; [exact Rtev|].
          split; [unfold LIBKEY0; apply (RWC (of_Z (A_keys + 8 * (1 + 3)))); vm_compute; reflexivity|].
          split; [unfold LIBKEY0; apply (RWC (of_Z A_next_key)); vm_compute; reflexivity|].
          split.
          { apply (proj2 (rw_cells_app asegs m1 A_key_lock [C8 (wz 0)] [C8 (wz 0)])). split.
            - apply (RWC (of_Z A_key_lock)); vm_compute; reflexivity.
            - cbn [cells_size csize Z.of_nat]. destruct Hkeys as (K1 & K2 & K3 & K4).
              apply (AGR (A_key_lock + 8) 8 ltac:(vm_compute; reflexivity)); [reflexivity |].
              exact (proj2 (proj1 (rw_cells_app asegs m A_key_lock [C8 (wz 0)] [C8 (wz 0)]) K2)). }
          split; [apply (RWC (of_Z A_td_cancelbuf)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_td_tsd_used)); vm_compute; reflexivity|].
          split; [apply (AGR A_keys 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs19]|].
          unfold LIBKEY0. exact Rtsd1.
        - (* [comment removed for export] *)
          split; [apply in_app_iff; left; exact In0|]. split; [reflexivity|].
          split; [exact Rmkey|].
          split; [apply in_app_iff; left; exact In1|]. split; [reflexivity|].
          split.
          { unfold sa_cells. apply (proj2 (rw_cells_app asegs m1 (g_addr g1) [C4 (wz 1); C4 (wz 0); C8 (wz 0); C8 (wz 1)] [C8 (wz (g_addr g2))])).
            split; [| exact Rsa]. rewrite <- (Z.add_0_r (g_addr g1)). change 0 with (to_Z 0%uint63) at 2.
            apply (RWB 1%uint63 g1 0%uint63 _ Hg1). vm_compute. reflexivity. }
          split; [apply in_app_iff; left; exact In2|]. split; [reflexivity|].
          split; [exact Rnodes|].
          split; [apply in_app_iff; left; exact In3|]. split; [reflexivity|].
          split; [apply in_app_iff; left; exact In4|]. split; [reflexivity|].
          cbn [chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands].
          pose proof aceil_facts as ACF.
          assert (ARG : forall b, In b (LBN G' ++ q_LB0 Q) -> arange (blk_addr b) (blk_size b)).
          { intros b Hb. pose proof (post_block_range H IMX GenO3s0_0_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0 b Hb) as (R0 & R16 & Rn & Rtop & Rce & _).
            unfold arange. split; [exact R0|]. split; [exact R16|]. split; [exact Rn|]. split; [exact Rtop|]. clear - Rce Rn ACF. slia. }
          apply Forall_cons; [exact (ARG (g_id g0, g_addr g0, 72) ltac:(apply in_app_iff; left; exact In0))|].
          apply Forall_cons; [exact (ARG (g_id g1, g_addr g1, 32) ltac:(apply in_app_iff; left; exact In1))|].
          apply Forall_cons; [exact (ARG (g_id g2, g_addr g2, 128) ltac:(apply in_app_iff; left; exact In2))|].
          apply Forall_cons; [exact (ARG (g_id g3, g_addr g3, 904) ltac:(apply in_app_iff; left; exact In3))|].
          apply Forall_cons; [exact (ARG (g_id g4, g_addr g4, 8) ltac:(apply in_app_iff; left; exact In4))|].
          apply Forall_nil. }
      split.
      { (* [comment removed for export] *)
        cbn [CTXPH]. destruct Hstat as (Cs1 & Cs2 & Cs3 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10 & Cs11 & Cs12 & Cs13 & Cs14 & Cs15 & Cs16 & Cs17 & Cs18 & Cs19). split.
        - unfold CTX_statics.
          split; [apply (AGR A_defctx_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs1]|].
          split; [apply (AGR A_defctx_tlkey 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs2]|].
          split; [apply (AGR A_defctx_tlkey_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs3]|].
          split; [apply (AGR A_defctx_tlkey_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs4]|].
          split; [apply (AGR A_defctx_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs5]|].
          split; [apply (AGR A_defctx_once_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs6]|].
          split; [apply (AGR A_defctx_exlock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs7]|].
          split; [apply (AGR A_defctx_exmeth_bio 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs8]|].
          split; [apply (AGR (A_tsd_main + 8 * LIBKEY0) 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs9]|].
          split; [apply (AGR A_destructor_key 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs10]|].
          split; [apply (AGR A_base_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs11]|].
          split; [apply (AGR A_stopped 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs12]|].
          split; [apply (AGR A_in_init_config_key 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs13]|].
          split; [apply (AGR A_base_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs14]|].
          split; [apply (AGR A_base_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs15]|].
          split; [apply (AGR A_optsdone_lock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs16]|].
          split; [apply (AGR A_init_lock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs17]|].
          split; [apply (AGR (A_keys + 8 * LIBKEY0) 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs18]|].
          apply (AGR A_keys 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs19].
        - destruct Hblk as [(Ein & Esz & Erng & Emut) (po & pi & Hpo & Hpi)]. split.
          + split; [apply in_app_iff; right; exact Ein|]. split; [exact Esz|]. split; [exact Erng|].
            unfold MUTEX in *. apply (rw_cells_agree (in_range (blk_addr (cx_exlock cx)) (blk_size (cx_exlock cx))) m m1 _ _ (MAGB _ Ein) Emut).
            intros a Ha. unfold in_range in *. rewrite Esz. unfold MUTEX_SIZE. cbn [cells_size csize length Nat.add] in Ha. slia.
          + exists po, pi. split; apply in_app_iff; right; assumption. }
      split.
      { (* [comment removed for export] *)
        split; [| split; [apply Forall_forall; intros sl Hsl; cbn [errst_zero es_slots] in Hsl; apply repeat_spec in Hsl; subst sl; cbn; slia
                      | split; [apply Forall_nil | apply Forall_nil]]].
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
      split.
      { (* [comment removed for export] *)
        unfold lib_shad. cbn [chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands]. unfold gblock. cbn [blk_addr blk_size fst snd].
        pose proof (proj1 (Forall_forall _ _) HSH) as SH.
        apply Forall_cons; [exact (SH g0 InG0)|]. apply Forall_cons; [exact (SH g1 InG1)|]. apply Forall_cons; [exact (SH g2 InG2)|].
        apply Forall_cons; [exact (SH g3 InG3)|]. apply Forall_cons; [exact (SH g4 InG4)|]. apply Forall_nil. }
      split; [exact (post_xs H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
      split.
      { (* [comment removed for export] *)
        exact (post_xpres H IMX GenO3s0_0_asan.KA chks0_0_K Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0 _ chks0_0_xw). }
      split; [exact (post_rfs H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
      pose proof (post_AL H IMX GenO3s0_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 Hcs) as HAL'. unfold Q in HAL'. cbn [q_AL0 q_cs] in HAL'.
      pose proof (csum_le H HH (ka_costs GenO3s0_0_asan.KA) ERRINIT_BYTES ERRINIT_BYTES ltac:(apply Z.leb_le; exact chks0_0_msum) ltac:(apply Z.leb_le; exact chks0_0_fsum)) as Hcsum.
      cbn [errph_cost]. unfold ERRINIT_COST. clear - HAL' Hcsum. slia. }
    { (* [comment removed for export] *)
      assert (Ea0 : x 10 = Z_to_bv 64 0) by exact Ha0.
      assert (Eerr : bv_unsigned tp + -164 = errA GenO3s0_16_asan.KA).
      { rewrite Htp, Z_to_bv_unsigned. vm_compute. reflexivity. }
      pose proof Herr as HerrE. rewrite Eerr in HerrE.
      assert (Cc : to_Z (c_cost GenO3s0_16_asan.K) <= 2 ^ 16) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cn : to_Z (c_cnt GenO3s0_16_asan.K) <= 1600) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cs : to_Z (c_stack GenO3s0_16_asan.K) = 9072) by (vm_compute; reflexivity).
      assert (Cf : Z.to_nat (to_Z (ka_fsmax GenO3s0_16_asan.KA)) = 4%nat) by (vm_compute; reflexivity).
      assert (Hby' : lb_bytes LB + to_Z (c_cost GenO3s0_16_asan.K) <= as_LIVE_MAX H) by (clear - Hby Cc; slia).
      assert (Hcnt' : Z.of_nat (length LB) + to_Z (c_cnt GenO3s0_16_asan.K) <= as_LIVE_CNT_MAX H) by (clear - Hcnt Cn; slia).
      assert (Hlo' : lo <= bv_unsigned (x 2) - to_Z (c_stack GenO3s0_16_asan.K)) by (clear - Hlo Cs; slia).
      assert (Hsp32' : (bv_unsigned (x 2) - to_Z (c_stack GenO3s0_16_asan.K)) mod 32 = 0) by (rewrite Cs; exact Hsp32).
      assert (Hlf' : (length LF + Z.to_nat (to_Z (ka_fsmax GenO3s0_16_asan.KA)) <= AFS_MAXLIVE)%nat) by (rewrite Cf; clear - Hlf; slia).
      assert (HALc : csum H (ka_costs GenO3s0_16_asan.KA) <= as_AL H s).
      { eapply Z.le_trans; [| exact HAL]. unfold ERRINIT_COST.
        apply (csum_le H HH); apply Z.leb_le; [exact chks0_16_msum | exact chks0_16_fsum]. }
      pose proof (rows_closed (as_TR H) PFC_ERRINIT (ka_pfc GenO3s0_16_asan.KA) chks0_16_pfc Hclosed) as Hpfc.
      pose proof (rows_open (as_TR H) PF_EGS_FRESH (ka_pfo GenO3s0_16_asan.KA) (bv_unsigned (x 1)) CH chks0_16_pfo Hpf) as Hpfo.
      pose proof (start_RnA H GenO3s0_16_asan.KA GenO3s0_16_asan.d0 (S_O3 0) x W F fc m lo chks0_16_K
                    (S_O3_holds x m errv cx 0 can Etp Ea0 Himpl Hmf Hinv Hrelro Hfresh Hkeys Hstat Hac HerrE Hcan)
                    Hstk (conj Hhl Hlo') Hsp63 Hsp16 Hsp32' IMX GenO3s0_16_asan.facts0 GenO3s0_16_asan.n0 IMX_ok IMX_wr_ok chks0_16_ho chks0_16_tags chks0_16_facts) as HRn.
      pose proof (i2a_certificate H IMX GenO3s0_16_asan.KA GenO3s0_16_asan.code chks0_16_K HHx IMX_ok IMX_wr_ok chks0_16_code (ro_const_introA GenO3s0_16_asan.KA chks0_16_roc)
                    (sh0_of_aconst GenO3s0_16_asan.KA chks0_16_sh0) Hpfc
                    (anode_fsmalloc_sound H IMX GenO3s0_16_asan.KA chks0_16_K HHx (sh0_of_aconst GenO3s0_16_asan.KA chks0_16_sh0))
                    (anode_fsfree_sound H IMX GenO3s0_16_asan.KA chks0_16_K HHx (sh0_of_aconst GenO3s0_16_asan.KA chks0_16_sh0) GenO3s0_16_asan.code chks0_16_code)
                    (anode_memset_sound H IMX GenO3s0_16_asan.KA chks0_16_K HHx (sh0_of_aconst GenO3s0_16_asan.KA chks0_16_sh0))
                    (anode_memcpy_sound H IMX GenO3s0_16_asan.KA chks0_16_K HHx IMX_ok (sh0_of_aconst GenO3s0_16_asan.KA chks0_16_sh0))
                    (anode_strlen_sound H IMX GenO3s0_16_asan.KA chks0_16_K HHx IMX_ok (sh0_of_aconst GenO3s0_16_asan.KA chks0_16_sh0)) (anode_memalign_sound H IMX GenO3s0_16_asan.KA chks0_16_K HHx IMX_ok IMX_wr_ok (sh0_of_aconst GenO3s0_16_asan.KA chks0_16_sh0) Hpfc (ro_const_introA GenO3s0_16_asan.KA chks0_16_roc) MAL)
                    GenO3s0_16_asan.fuel (I2AS (state_of GenO3s0_16_asan.d0) GenO3s0_16_asan.n0 GenO3s0_16_asan.blk0 [] 0%uint63 0%uint63 0%uint63 []) GenO3s0_16_asan.X [] (rho_ofA GenO3s0_16_asan.K GenO3s0_16_asan.d0 x W) x F fc msF m mo s LB LF lo B CH
                    chks0_16_run chks0_16_shape eq_refl eq_refl (List.NoDup_nil _) (Forall_nil _)
                    HRn eq_refl eq_refl eq_refl eq_refl Hvis Hkrel Hheap Hrfs Hac Hsh0 Hchain HCH Hpfo HALc Hby' Hcnt' Hlf'
                    Haux HB HB64 Hstk Hhl Hlo' Hsp16 Hsp32' HerrE Hinv) as HC.
      clear HRn.
      match goal with |- as_SR _ _ ?c => match type of HC with as_SR _ _ ?c' => replace c with c' by reflexivity end end.
      apply (ah_mono H HH _ _ _ HC). clear HC.
      (* [comment removed for export] *)
      intros k (rho' & st' & s' & LB' & G' & XS' & ms1 & Ek & Hak & Hmp & (msF1 & mo1 & X1) & Hfin & Hcs & HXR & HXC & HXB & Hsz & Hes & HSH).
      set (Q := I2AE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in X1.
      assert (HG0 : q_G0 Q = []) by reflexivity.
      assert (HQ : q_rho0 Q = rho_ofA GenO3s0_16_asan.K GenO3s0_16_asan.d0 x W) by reflexivity.
      pose proof (post_magree H IMX GenO3s0_16_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0) as MAG. cbn [q_m0 Q] in MAG.
      pose proof (post_magree_block H IMX GenO3s0_16_asan.KA chks0_16_K HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0) as MAGB. cbn [q_m0 q_LB0 Q] in MAGB.
      pose proof (post_rw_cells rho' ms1 G' GenO3s0_16_asan.X HXC) as RWC.
      pose proof (post_blk_rw_cells H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_16_asan.X X1 Hsz HXB) as RWB.
      pose proof (post_blk_arr H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_16_asan.X X1 Hsz HXB) as RWA.
      set (m1 := ms_mem ms1) in *.
      (* [comment removed for export] *)
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_16_asan.X HXC (of_Z (A_tsd_main + 8 * (LIBKEY0 + 3))) 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g0 & Hg0 & Rtsd3).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_16_asan.X HXC (of_Z (A_tsd_main + 8 * (LIBKEY0 + 1))) 4%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g4 & Hg4 & Rtsd1).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_16_asan.X HXC (of_Z A_glob_tevent_reg) 5%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g5 & Hg5 & Rtev).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_16_asan.X HXC (of_Z A_err_string_lock) 10%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g10 & Hg10 & Resl).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s0_16_asan.X HXC (of_Z A_int_error_hash) 11%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g11 & Hg11 & Resh).
      destruct (post_blk_ptr0 H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_16_asan.X X1 Hsz HXB 0%uint63 g0 24%uint63 1%uint63 Hg0 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s0_16_asan.X Hsz _ _ Hg0))); vm_compute; discriminate)) as (g1 & Hg1 & Rmkey).
      destruct (post_blk_ptr0 H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_16_asan.X X1 Hsz HXB 1%uint63 g1 24%uint63 2%uint63 Hg1 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s0_16_asan.X Hsz _ _ Hg1))); vm_compute; discriminate)) as (g2 & Hg2 & Rsa).
      destruct (post_blk_ptr0 H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_16_asan.X X1 Hsz HXB 2%uint63 g2 0%uint63 3%uint63 Hg2 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s0_16_asan.X Hsz _ _ Hg2))); vm_compute; discriminate)) as (g3 & Hg3 & Rnodes).
      change (to_Z 0%uint63) with 0 in Rnodes. rewrite Z.add_0_r in Rnodes.
      destruct (blk_of_LBN G' GenO3s0_16_asan.X Hsz _ _ Hg0) as (In0 & InG0 & Sz0). destruct (blk_of_LBN G' GenO3s0_16_asan.X Hsz _ _ Hg1) as (In1 & InG1 & Sz1).
      destruct (blk_of_LBN G' GenO3s0_16_asan.X Hsz _ _ Hg2) as (In2 & InG2 & Sz2). destruct (blk_of_LBN G' GenO3s0_16_asan.X Hsz _ _ Hg3) as (In3 & InG3 & Sz3).
      destruct (blk_of_LBN G' GenO3s0_16_asan.X Hsz _ _ Hg4) as (In4 & InG4 & Sz4).
      change (nth (Z.to_nat (to_Z 0%uint63)) (x_sizes GenO3s0_16_asan.X) 0%uint63) with 72%uint63 in Sz0.
      change (nth (Z.to_nat (to_Z 1%uint63)) (x_sizes GenO3s0_16_asan.X) 0%uint63) with 32%uint63 in Sz1.
      change (nth (Z.to_nat (to_Z 2%uint63)) (x_sizes GenO3s0_16_asan.X) 0%uint63) with 128%uint63 in Sz2.
      change (nth (Z.to_nat (to_Z 3%uint63)) (x_sizes GenO3s0_16_asan.X) 0%uint63) with 904%uint63 in Sz3.
      change (nth (Z.to_nat (to_Z 4%uint63)) (x_sizes GenO3s0_16_asan.X) 0%uint63) with 8%uint63 in Sz4.
      destruct (post_errno H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1) as [errv0 Herr0].
      (* [comment removed for export] *)
      assert (AGR : forall A n, unw_range GenO3s0_16_asan.K A n = true -> forall cs, Z.of_nat (cells_size cs) = n -> rw_cells asegs m A cs -> rw_cells asegs m1 A cs).
      { intros A n Hu cs Hn Hrw. apply (rw_cells_agree (in_range A n) m m1 A cs (MAG A n Hu) Hrw). rewrite Hn. exact (fun a h => h). }
      (* [comment removed for export] *)
      exists (rv rho' (a_F st') 5), (rv rho' (a_F st') 6), (rv rho' (a_F st') 7),
             (rv rho' (a_F st') 11), (rv rho' (a_F st') 12), (rv rho' (a_F st') 13), (rv rho' (a_F st') 14),
             (rv rho' (a_F st') 15), (rv rho' (a_F st') 16), (rv rho' (a_F st') 17),
             (rv rho' (a_F st') 28), (rv rho' (a_F st') 29), (rv rho' (a_F st') 30), (rv rho' (a_F st') 31),
             m1, errv0, s', (LBN G'),
             (mkEC (gblock g0) (gblock g1) (gblock g2) (gblock g3) (gblock g4) (g_addr g10) (g_addr g11) (g_addr g5)), XS'.
      assert (Hn0 : forall t : int, (t <? GenO3s0_16_asan.n0)%uint63 = true -> to_Z t < to_Z (q_n0 Q)) by (intros t Ht; exact (i_ltb_lt _ _ Ht)).
      pose proof (fun kk t r => xreg_entry H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_16_asan.X X1 HXR GenO3s0_16_asan.d0 x W kk t r HQ) as XE.
      cbn [ec_mkey ec_sa ec_nodes ec_es ec_hands ec_eslock ec_eshash ec_tevreg].
      split.
      { rewrite Ek, (post_regs H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1).
        change (q_F Q) with F. change (q_fc Q) with fc. replace (q_rho0 Q (c_tra GenO3s0_16_asan.K)) with ra by reflexivity. fold m1.
        rewrite <- (XE 1%uint63 4%uint63 1%uint63 eq_refl eq_refl (Hn0 4%uint63 eq_refl) eq_refl : rv rho' (a_F st') 1 = ra).
        rewrite <- (xreg_sp H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s0_16_asan.X X1 HXR GenO3s0_16_asan.d0 x W HQ eq_refl eq_refl : rv rho' (a_F st') 2 = sp).
        rewrite <- (XE 3%uint63 5%uint63 3%uint63 eq_refl eq_refl (Hn0 5%uint63 eq_refl) eq_refl : rv rho' (a_F st') 3 = gp).
        assert (E4 : rv rho' (a_F st') 4 = tp).
        { rewrite (xreg_W st' rho' G' GenO3s0_16_asan.X HXR 4%uint63 _ eq_refl : rv rho' (a_F st') 4 = _), Htp. apply bv_eq. vm_compute. reflexivity. }
        rewrite <- E4.
        rewrite <- (XE 8%uint63 9%uint63 8%uint63 eq_refl eq_refl (Hn0 9%uint63 eq_refl) eq_refl : rv rho' (a_F st') 8 = s0).
        rewrite <- (XE 9%uint63 10%uint63 9%uint63 eq_refl eq_refl (Hn0 10%uint63 eq_refl) eq_refl : rv rho' (a_F st') 9 = s1).
        assert (E10 : rv rho' (a_F st') 10 = Z_to_bv 64 (blk_addr (gblock g3))).
        { destruct (xreg_New st' rho' G' GenO3s0_16_asan.X HXR 10%uint63 3%uint63 0%uint63 eq_refl) as (g3' & Hg3' & E).
          rewrite Hg3 in Hg3'. injection Hg3' as <-. change (to_Z 10%uint63) with 10 in E. rewrite E, Z.add_0_r. reflexivity. }
        rewrite <- E10.
        rewrite <- (XE 18%uint63 18%uint63 18%uint63 eq_refl eq_refl (Hn0 18%uint63 eq_refl) eq_refl : rv rho' (a_F st') 18 = s2).
        rewrite <- (XE 19%uint63 19%uint63 19%uint63 eq_refl eq_refl (Hn0 19%uint63 eq_refl) eq_refl : rv rho' (a_F st') 19 = s3).
        rewrite <- (XE 20%uint63 20%uint63 20%uint63 eq_refl eq_refl (Hn0 20%uint63 eq_refl) eq_refl : rv rho' (a_F st') 20 = s4).
        rewrite <- (XE 21%uint63 21%uint63 21%uint63 eq_refl eq_refl (Hn0 21%uint63 eq_refl) eq_refl : rv rho' (a_F st') 21 = s5).
        rewrite <- (XE 22%uint63 22%uint63 22%uint63 eq_refl eq_refl (Hn0 22%uint63 eq_refl) eq_refl : rv rho' (a_F st') 22 = s6).
        rewrite <- (XE 23%uint63 23%uint63 23%uint63 eq_refl eq_refl (Hn0 23%uint63 eq_refl) eq_refl : rv rho' (a_F st') 23 = s7).
        rewrite <- (XE 24%uint63 24%uint63 24%uint63 eq_refl eq_refl (Hn0 24%uint63 eq_refl) eq_refl : rv rho' (a_F st') 24 = s8).
        rewrite <- (XE 25%uint63 25%uint63 25%uint63 eq_refl eq_refl (Hn0 25%uint63 eq_refl) eq_refl : rv rho' (a_F st') 25 = s9).
        rewrite <- (XE 26%uint63 26%uint63 26%uint63 eq_refl eq_refl (Hn0 26%uint63 eq_refl) eq_refl : rv rho' (a_F st') 26 = s10).
        rewrite <- (XE 27%uint63 27%uint63 27%uint63 eq_refl eq_refl (Hn0 27%uint63 eq_refl) eq_refl : rv rho' (a_F st') 27 = s11).
        reflexivity. }
      split; [exact Hmp|].
      split.
      { (* [comment removed for export] *)
        split; [exact Hak|].
        split; [exact (post_inv H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_aconst H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_stk H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_auxv H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [cbn [app]; exact (post_heap H IMX GenO3s0_16_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0)|].
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
      split; [rewrite Eerr; exact Herr0|].
      split; [intros Hne; exfalso; exact (Hne eq_refl)|].
      pose proof In0 as In0g. pose proof In1 as In1g. pose proof In2 as In2g. pose proof In3 as In3g. pose proof In4 as In4g.
      unfold gblock in In0, In1, In2, In3, In4.
      rewrite Sz0 in In0. rewrite Sz1 in In1. rewrite Sz2 in In2. rewrite Sz3 in In3. rewrite Sz4 in In4.
      change (to_Z 72%uint63) with 72 in In0. change (to_Z 32%uint63) with 32 in In1. change (to_Z 128%uint63) with 128 in In2.
      change (to_Z 904%uint63) with 904 in In3. change (to_Z 8%uint63) with 8 in In4.
      split.
      { (* [comment removed for export] *)
        cbn [errph_delta chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands].
        split; [rewrite (LBN_length G' GenO3s0_16_asan.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        split; [rewrite (LBN_bytes G' GenO3s0_16_asan.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        apply Forall_cons; [exact In0g|]. apply Forall_cons; [exact In1g|]. apply Forall_cons; [exact In2g|].
        apply Forall_cons; [exact In3g|]. apply Forall_cons; [exact In4g|]. apply Forall_nil. }
      split.
      { (* [comment removed for export] *)
        cbn [ERRPH]. unfold ERR_statics, ERR_chain. cbn [ec_mkey ec_sa ec_nodes ec_es ec_hands ec_eslock ec_eshash ec_tevreg chain_blocks].
        unfold gblock. cbn [blk_addr blk_size fst snd]. rewrite Sz0, Sz1, Sz2, Sz3, Sz4.
        change (to_Z 72%uint63) with 72. change (to_Z 32%uint63) with 32. change (to_Z 128%uint63) with 128.
        change (to_Z 904%uint63) with 904. change (to_Z 8%uint63) with 8.
        destruct Hstat as (Cs1 & Cs2 & Cs3 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10 & Cs11 & Cs12 & Cs13 & Cs14 & Cs15 & Cs16 & Cs17 & Cs18 & Cs19).
        split.
        - (* [comment removed for export] *)
          split; [apply (RWC (of_Z A_master_once_ret)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_master_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_master_key)); vm_compute; reflexivity|].
          split; [unfold LIBKEY0; exact Rtsd3|].
          split; [apply (AGR A_stopped 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs12]|].
          split; [apply (AGR A_base_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs14]|].
          split; [apply (AGR A_base_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs15]|].
          split; [apply (RWC (of_Z A_load_strings_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_load_strings_ret)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_optsdone)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_err_string_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_err_string_ret)); vm_compute; reflexivity|].
          split; [exact Resl|].
          split; [exact Resh|].
          split; [apply (RWC (of_Z A_tevent_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_tevent_ret)); vm_compute; reflexivity|].
          split; [exact Rtev|].
          split; [unfold LIBKEY0; apply (RWC (of_Z (A_keys + 8 * (1 + 3)))); vm_compute; reflexivity|].
          split; [unfold LIBKEY0; apply (RWC (of_Z A_next_key)); vm_compute; reflexivity|].
          split.
          { apply (proj2 (rw_cells_app asegs m1 A_key_lock [C8 (wz 0)] [C8 (wz 0)])). split.
            - apply (RWC (of_Z A_key_lock)); vm_compute; reflexivity.
            - cbn [cells_size csize Z.of_nat]. destruct Hkeys as (K1 & K2 & K3 & K4).
              apply (AGR (A_key_lock + 8) 8 ltac:(vm_compute; reflexivity)); [reflexivity |].
              exact (proj2 (proj1 (rw_cells_app asegs m A_key_lock [C8 (wz 0)] [C8 (wz 0)]) K2)). }
          split; [apply (RWC (of_Z A_td_cancelbuf)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_td_tsd_used)); vm_compute; reflexivity|].
          split; [apply (AGR A_keys 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs19]|].
          unfold LIBKEY0. exact Rtsd1.
        - (* [comment removed for export] *)
          split; [apply in_app_iff; left; exact In0|]. split; [reflexivity|].
          split; [exact Rmkey|].
          split; [apply in_app_iff; left; exact In1|]. split; [reflexivity|].
          split.
          { unfold sa_cells. apply (proj2 (rw_cells_app asegs m1 (g_addr g1) [C4 (wz 1); C4 (wz 0); C8 (wz 0); C8 (wz 1)] [C8 (wz (g_addr g2))])).
            split; [| exact Rsa]. rewrite <- (Z.add_0_r (g_addr g1)). change 0 with (to_Z 0%uint63) at 2.
            apply (RWB 1%uint63 g1 0%uint63 _ Hg1). vm_compute. reflexivity. }
          split; [apply in_app_iff; left; exact In2|]. split; [reflexivity|].
          split; [exact Rnodes|].
          split; [apply in_app_iff; left; exact In3|]. split; [reflexivity|].
          split; [apply in_app_iff; left; exact In4|]. split; [reflexivity|].
          cbn [chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands].
          pose proof aceil_facts as ACF.
          assert (ARG : forall b, In b (LBN G' ++ q_LB0 Q) -> arange (blk_addr b) (blk_size b)).
          { intros b Hb. pose proof (post_block_range H IMX GenO3s0_16_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0 b Hb) as (R0 & R16 & Rn & Rtop & Rce & _).
            unfold arange. split; [exact R0|]. split; [exact R16|]. split; [exact Rn|]. split; [exact Rtop|]. clear - Rce Rn ACF. slia. }
          apply Forall_cons; [exact (ARG (g_id g0, g_addr g0, 72) ltac:(apply in_app_iff; left; exact In0))|].
          apply Forall_cons; [exact (ARG (g_id g1, g_addr g1, 32) ltac:(apply in_app_iff; left; exact In1))|].
          apply Forall_cons; [exact (ARG (g_id g2, g_addr g2, 128) ltac:(apply in_app_iff; left; exact In2))|].
          apply Forall_cons; [exact (ARG (g_id g3, g_addr g3, 904) ltac:(apply in_app_iff; left; exact In3))|].
          apply Forall_cons; [exact (ARG (g_id g4, g_addr g4, 8) ltac:(apply in_app_iff; left; exact In4))|].
          apply Forall_nil. }
      split.
      { (* [comment removed for export] *)
        cbn [CTXPH]. destruct Hstat as (Cs1 & Cs2 & Cs3 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10 & Cs11 & Cs12 & Cs13 & Cs14 & Cs15 & Cs16 & Cs17 & Cs18 & Cs19). split.
        - unfold CTX_statics.
          split; [apply (AGR A_defctx_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs1]|].
          split; [apply (AGR A_defctx_tlkey 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs2]|].
          split; [apply (AGR A_defctx_tlkey_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs3]|].
          split; [apply (AGR A_defctx_tlkey_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs4]|].
          split; [apply (AGR A_defctx_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs5]|].
          split; [apply (AGR A_defctx_once_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs6]|].
          split; [apply (AGR A_defctx_exlock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs7]|].
          split; [apply (AGR A_defctx_exmeth_bio 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs8]|].
          split; [apply (AGR (A_tsd_main + 8 * LIBKEY0) 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs9]|].
          split; [apply (AGR A_destructor_key 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs10]|].
          split; [apply (AGR A_base_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs11]|].
          split; [apply (AGR A_stopped 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs12]|].
          split; [apply (AGR A_in_init_config_key 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs13]|].
          split; [apply (AGR A_base_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs14]|].
          split; [apply (AGR A_base_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs15]|].
          split; [apply (AGR A_optsdone_lock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs16]|].
          split; [apply (AGR A_init_lock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs17]|].
          split; [apply (AGR (A_keys + 8 * LIBKEY0) 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs18]|].
          apply (AGR A_keys 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs19].
        - destruct Hblk as [(Ein & Esz & Erng & Emut) (po & pi & Hpo & Hpi)]. split.
          + split; [apply in_app_iff; right; exact Ein|]. split; [exact Esz|]. split; [exact Erng|].
            unfold MUTEX in *. apply (rw_cells_agree (in_range (blk_addr (cx_exlock cx)) (blk_size (cx_exlock cx))) m m1 _ _ (MAGB _ Ein) Emut).
            intros a Ha. unfold in_range in *. rewrite Esz. unfold MUTEX_SIZE. cbn [cells_size csize length Nat.add] in Ha. slia.
          + exists po, pi. split; apply in_app_iff; right; assumption. }
      split.
      { (* [comment removed for export] *)
        split; [| split; [apply Forall_forall; intros sl Hsl; cbn [errst_zero es_slots] in Hsl; apply repeat_spec in Hsl; subst sl; cbn; slia
                      | split; [apply Forall_nil | apply Forall_nil]]].
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
      split.
      { (* [comment removed for export] *)
        unfold lib_shad. cbn [chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands]. unfold gblock. cbn [blk_addr blk_size fst snd].
        pose proof (proj1 (Forall_forall _ _) HSH) as SH.
        apply Forall_cons; [exact (SH g0 InG0)|]. apply Forall_cons; [exact (SH g1 InG1)|]. apply Forall_cons; [exact (SH g2 InG2)|].
        apply Forall_cons; [exact (SH g3 InG3)|]. apply Forall_cons; [exact (SH g4 InG4)|]. apply Forall_nil. }
      split; [exact (post_xs H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
      split.
      { (* [comment removed for export] *)
        exact (post_xpres H IMX GenO3s0_16_asan.KA chks0_16_K Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0 _ chks0_16_xw). }
      split; [exact (post_rfs H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
      pose proof (post_AL H IMX GenO3s0_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 Hcs) as HAL'. unfold Q in HAL'. cbn [q_AL0 q_cs] in HAL'.
      pose proof (csum_le H HH (ka_costs GenO3s0_16_asan.KA) ERRINIT_BYTES ERRINIT_BYTES ltac:(apply Z.leb_le; exact chks0_16_msum) ltac:(apply Z.leb_le; exact chks0_16_fsum)) as Hcsum.
      cbn [errph_cost]. unfold ERRINIT_COST. clear - HAL' Hcsum. slia. }
    { (* [comment removed for export] *)
      assert (Ea0 : x 10 = Z_to_bv 64 1) by exact Ha0.
      assert (Eerr : bv_unsigned tp + -164 = errA GenO3s1_0_asan.KA).
      { rewrite Htp, Z_to_bv_unsigned. vm_compute. reflexivity. }
      pose proof Herr as HerrE. rewrite Eerr in HerrE.
      assert (Cc : to_Z (c_cost GenO3s1_0_asan.K) <= 2 ^ 16) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cn : to_Z (c_cnt GenO3s1_0_asan.K) <= 1600) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cs : to_Z (c_stack GenO3s1_0_asan.K) = 9056) by (vm_compute; reflexivity).
      assert (Cf : Z.to_nat (to_Z (ka_fsmax GenO3s1_0_asan.KA)) = 4%nat) by (vm_compute; reflexivity).
      assert (Hby' : lb_bytes LB + to_Z (c_cost GenO3s1_0_asan.K) <= as_LIVE_MAX H) by (clear - Hby Cc; slia).
      assert (Hcnt' : Z.of_nat (length LB) + to_Z (c_cnt GenO3s1_0_asan.K) <= as_LIVE_CNT_MAX H) by (clear - Hcnt Cn; slia).
      assert (Hlo' : lo <= bv_unsigned (x 2) - to_Z (c_stack GenO3s1_0_asan.K)) by (clear - Hlo Cs; slia).
      assert (Hsp32' : (bv_unsigned (x 2) - to_Z (c_stack GenO3s1_0_asan.K)) mod 32 = 0) by (rewrite Cs; exact Hsp32).
      assert (Hlf' : (length LF + Z.to_nat (to_Z (ka_fsmax GenO3s1_0_asan.KA)) <= AFS_MAXLIVE)%nat) by (rewrite Cf; clear - Hlf; slia).
      assert (HALc : csum H (ka_costs GenO3s1_0_asan.KA) <= as_AL H s).
      { eapply Z.le_trans; [| exact HAL]. unfold ERRINIT_COST.
        apply (csum_le H HH); apply Z.leb_le; [exact chks1_0_msum | exact chks1_0_fsum]. }
      pose proof (rows_closed (as_TR H) PFC_ERRINIT (ka_pfc GenO3s1_0_asan.KA) chks1_0_pfc Hclosed) as Hpfc.
      pose proof (rows_open (as_TR H) PF_EGS_FRESH (ka_pfo GenO3s1_0_asan.KA) (bv_unsigned (x 1)) CH chks1_0_pfo Hpf) as Hpfo.
      pose proof (start_RnA H GenO3s1_0_asan.KA GenO3s1_0_asan.d0 (S_O3 1) x W F fc m lo chks1_0_K
                    (S_O3_holds x m errv cx 1 can Etp Ea0 Himpl Hmf Hinv Hrelro Hfresh Hkeys Hstat Hac HerrE Hcan)
                    Hstk (conj Hhl Hlo') Hsp63 Hsp16 Hsp32' IMX GenO3s1_0_asan.facts0 GenO3s1_0_asan.n0 IMX_ok IMX_wr_ok chks1_0_ho chks1_0_tags chks1_0_facts) as HRn.
      pose proof (i2a_certificate H IMX GenO3s1_0_asan.KA GenO3s1_0_asan.code chks1_0_K HHx IMX_ok IMX_wr_ok chks1_0_code (ro_const_introA GenO3s1_0_asan.KA chks1_0_roc)
                    (sh0_of_aconst GenO3s1_0_asan.KA chks1_0_sh0) Hpfc
                    (anode_fsmalloc_sound H IMX GenO3s1_0_asan.KA chks1_0_K HHx (sh0_of_aconst GenO3s1_0_asan.KA chks1_0_sh0))
                    (anode_fsfree_sound H IMX GenO3s1_0_asan.KA chks1_0_K HHx (sh0_of_aconst GenO3s1_0_asan.KA chks1_0_sh0) GenO3s1_0_asan.code chks1_0_code)
                    (anode_memset_sound H IMX GenO3s1_0_asan.KA chks1_0_K HHx (sh0_of_aconst GenO3s1_0_asan.KA chks1_0_sh0))
                    (anode_memcpy_sound H IMX GenO3s1_0_asan.KA chks1_0_K HHx IMX_ok (sh0_of_aconst GenO3s1_0_asan.KA chks1_0_sh0))
                    (anode_strlen_sound H IMX GenO3s1_0_asan.KA chks1_0_K HHx IMX_ok (sh0_of_aconst GenO3s1_0_asan.KA chks1_0_sh0)) (anode_memalign_sound H IMX GenO3s1_0_asan.KA chks1_0_K HHx IMX_ok IMX_wr_ok (sh0_of_aconst GenO3s1_0_asan.KA chks1_0_sh0) Hpfc (ro_const_introA GenO3s1_0_asan.KA chks1_0_roc) MAL)
                    GenO3s1_0_asan.fuel (I2AS (state_of GenO3s1_0_asan.d0) GenO3s1_0_asan.n0 GenO3s1_0_asan.blk0 [] 0%uint63 0%uint63 0%uint63 []) GenO3s1_0_asan.X [] (rho_ofA GenO3s1_0_asan.K GenO3s1_0_asan.d0 x W) x F fc msF m mo s LB LF lo B CH
                    chks1_0_run chks1_0_shape eq_refl eq_refl (List.NoDup_nil _) (Forall_nil _)
                    HRn eq_refl eq_refl eq_refl eq_refl Hvis Hkrel Hheap Hrfs Hac Hsh0 Hchain HCH Hpfo HALc Hby' Hcnt' Hlf'
                    Haux HB HB64 Hstk Hhl Hlo' Hsp16 Hsp32' HerrE Hinv) as HC.
      clear HRn.
      match goal with |- as_SR _ _ ?c => match type of HC with as_SR _ _ ?c' => replace c with c' by reflexivity end end.
      apply (ah_mono H HH _ _ _ HC). clear HC.
      (* [comment removed for export] *)
      intros k (rho' & st' & s' & LB' & G' & XS' & ms1 & Ek & Hak & Hmp & (msF1 & mo1 & X1) & Hfin & Hcs & HXR & HXC & HXB & Hsz & Hes & HSH).
      set (Q := I2AE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in X1.
      assert (HG0 : q_G0 Q = []) by reflexivity.
      assert (HQ : q_rho0 Q = rho_ofA GenO3s1_0_asan.K GenO3s1_0_asan.d0 x W) by reflexivity.
      pose proof (post_magree H IMX GenO3s1_0_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0) as MAG. cbn [q_m0 Q] in MAG.
      pose proof (post_magree_block H IMX GenO3s1_0_asan.KA chks1_0_K HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0) as MAGB. cbn [q_m0 q_LB0 Q] in MAGB.
      pose proof (post_rw_cells rho' ms1 G' GenO3s1_0_asan.X HXC) as RWC.
      pose proof (post_blk_rw_cells H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_0_asan.X X1 Hsz HXB) as RWB.
      pose proof (post_blk_arr H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_0_asan.X X1 Hsz HXB) as RWA.
      set (m1 := ms_mem ms1) in *.
      (* [comment removed for export] *)
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_0_asan.X HXC (of_Z (A_tsd_main + 8 * (LIBKEY0 + 3))) 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g0 & Hg0 & Rtsd3).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_0_asan.X HXC (of_Z (A_tsd_main + 8 * (LIBKEY0 + 1))) 4%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g4 & Hg4 & Rtsd1).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_0_asan.X HXC (of_Z A_glob_tevent_reg) 5%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g5 & Hg5 & Rtev).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_0_asan.X HXC (of_Z A_err_string_lock) 10%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g10 & Hg10 & Resl).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_0_asan.X HXC (of_Z A_int_error_hash) 11%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g11 & Hg11 & Resh).
      destruct (post_blk_ptr0 H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_0_asan.X X1 Hsz HXB 0%uint63 g0 24%uint63 1%uint63 Hg0 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s1_0_asan.X Hsz _ _ Hg0))); vm_compute; discriminate)) as (g1 & Hg1 & Rmkey).
      destruct (post_blk_ptr0 H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_0_asan.X X1 Hsz HXB 1%uint63 g1 24%uint63 2%uint63 Hg1 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s1_0_asan.X Hsz _ _ Hg1))); vm_compute; discriminate)) as (g2 & Hg2 & Rsa).
      destruct (post_blk_ptr0 H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_0_asan.X X1 Hsz HXB 2%uint63 g2 0%uint63 3%uint63 Hg2 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s1_0_asan.X Hsz _ _ Hg2))); vm_compute; discriminate)) as (g3 & Hg3 & Rnodes).
      change (to_Z 0%uint63) with 0 in Rnodes. rewrite Z.add_0_r in Rnodes.
      destruct (blk_of_LBN G' GenO3s1_0_asan.X Hsz _ _ Hg0) as (In0 & InG0 & Sz0). destruct (blk_of_LBN G' GenO3s1_0_asan.X Hsz _ _ Hg1) as (In1 & InG1 & Sz1).
      destruct (blk_of_LBN G' GenO3s1_0_asan.X Hsz _ _ Hg2) as (In2 & InG2 & Sz2). destruct (blk_of_LBN G' GenO3s1_0_asan.X Hsz _ _ Hg3) as (In3 & InG3 & Sz3).
      destruct (blk_of_LBN G' GenO3s1_0_asan.X Hsz _ _ Hg4) as (In4 & InG4 & Sz4).
      change (nth (Z.to_nat (to_Z 0%uint63)) (x_sizes GenO3s1_0_asan.X) 0%uint63) with 72%uint63 in Sz0.
      change (nth (Z.to_nat (to_Z 1%uint63)) (x_sizes GenO3s1_0_asan.X) 0%uint63) with 32%uint63 in Sz1.
      change (nth (Z.to_nat (to_Z 2%uint63)) (x_sizes GenO3s1_0_asan.X) 0%uint63) with 128%uint63 in Sz2.
      change (nth (Z.to_nat (to_Z 3%uint63)) (x_sizes GenO3s1_0_asan.X) 0%uint63) with 904%uint63 in Sz3.
      change (nth (Z.to_nat (to_Z 4%uint63)) (x_sizes GenO3s1_0_asan.X) 0%uint63) with 8%uint63 in Sz4.
      destruct (post_errno H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1) as [errv0 Herr0].
      (* [comment removed for export] *)
      assert (AGR : forall A n, unw_range GenO3s1_0_asan.K A n = true -> forall cs, Z.of_nat (cells_size cs) = n -> rw_cells asegs m A cs -> rw_cells asegs m1 A cs).
      { intros A n Hu cs Hn Hrw. apply (rw_cells_agree (in_range A n) m m1 A cs (MAG A n Hu) Hrw). rewrite Hn. exact (fun a h => h). }
      (* [comment removed for export] *)
      exists (rv rho' (a_F st') 5), (rv rho' (a_F st') 6), (rv rho' (a_F st') 7),
             (rv rho' (a_F st') 11), (rv rho' (a_F st') 12), (rv rho' (a_F st') 13), (rv rho' (a_F st') 14),
             (rv rho' (a_F st') 15), (rv rho' (a_F st') 16), (rv rho' (a_F st') 17),
             (rv rho' (a_F st') 28), (rv rho' (a_F st') 29), (rv rho' (a_F st') 30), (rv rho' (a_F st') 31),
             m1, errv, s', (LBN G'),
             (mkEC (gblock g0) (gblock g1) (gblock g2) (gblock g3) (gblock g4) (g_addr g10) (g_addr g11) (g_addr g5)), XS'.
      assert (Hn0 : forall t : int, (t <? GenO3s1_0_asan.n0)%uint63 = true -> to_Z t < to_Z (q_n0 Q)) by (intros t Ht; exact (i_ltb_lt _ _ Ht)).
      pose proof (fun kk t r => xreg_entry H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_0_asan.X X1 HXR GenO3s1_0_asan.d0 x W kk t r HQ) as XE.
      cbn [ec_mkey ec_sa ec_nodes ec_es ec_hands ec_eslock ec_eshash ec_tevreg].
      split.
      { rewrite Ek, (post_regs H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1).
        change (q_F Q) with F. change (q_fc Q) with fc. replace (q_rho0 Q (c_tra GenO3s1_0_asan.K)) with ra by reflexivity. fold m1.
        rewrite <- (XE 1%uint63 4%uint63 1%uint63 eq_refl eq_refl (Hn0 4%uint63 eq_refl) eq_refl : rv rho' (a_F st') 1 = ra).
        rewrite <- (xreg_sp H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_0_asan.X X1 HXR GenO3s1_0_asan.d0 x W HQ eq_refl eq_refl : rv rho' (a_F st') 2 = sp).
        rewrite <- (XE 3%uint63 5%uint63 3%uint63 eq_refl eq_refl (Hn0 5%uint63 eq_refl) eq_refl : rv rho' (a_F st') 3 = gp).
        assert (E4 : rv rho' (a_F st') 4 = tp).
        { rewrite (xreg_W st' rho' G' GenO3s1_0_asan.X HXR 4%uint63 _ eq_refl : rv rho' (a_F st') 4 = _), Htp. apply bv_eq. vm_compute. reflexivity. }
        rewrite <- E4.
        rewrite <- (XE 8%uint63 9%uint63 8%uint63 eq_refl eq_refl (Hn0 9%uint63 eq_refl) eq_refl : rv rho' (a_F st') 8 = s0).
        rewrite <- (XE 9%uint63 10%uint63 9%uint63 eq_refl eq_refl (Hn0 10%uint63 eq_refl) eq_refl : rv rho' (a_F st') 9 = s1).
        assert (E10 : rv rho' (a_F st') 10 = Z_to_bv 64 (blk_addr (gblock g3))).
        { destruct (xreg_New st' rho' G' GenO3s1_0_asan.X HXR 10%uint63 3%uint63 0%uint63 eq_refl) as (g3' & Hg3' & E).
          rewrite Hg3 in Hg3'. injection Hg3' as <-. change (to_Z 10%uint63) with 10 in E. rewrite E, Z.add_0_r. reflexivity. }
        rewrite <- E10.
        rewrite <- (XE 18%uint63 18%uint63 18%uint63 eq_refl eq_refl (Hn0 18%uint63 eq_refl) eq_refl : rv rho' (a_F st') 18 = s2).
        rewrite <- (XE 19%uint63 19%uint63 19%uint63 eq_refl eq_refl (Hn0 19%uint63 eq_refl) eq_refl : rv rho' (a_F st') 19 = s3).
        rewrite <- (XE 20%uint63 20%uint63 20%uint63 eq_refl eq_refl (Hn0 20%uint63 eq_refl) eq_refl : rv rho' (a_F st') 20 = s4).
        rewrite <- (XE 21%uint63 21%uint63 21%uint63 eq_refl eq_refl (Hn0 21%uint63 eq_refl) eq_refl : rv rho' (a_F st') 21 = s5).
        rewrite <- (XE 22%uint63 22%uint63 22%uint63 eq_refl eq_refl (Hn0 22%uint63 eq_refl) eq_refl : rv rho' (a_F st') 22 = s6).
        rewrite <- (XE 23%uint63 23%uint63 23%uint63 eq_refl eq_refl (Hn0 23%uint63 eq_refl) eq_refl : rv rho' (a_F st') 23 = s7).
        rewrite <- (XE 24%uint63 24%uint63 24%uint63 eq_refl eq_refl (Hn0 24%uint63 eq_refl) eq_refl : rv rho' (a_F st') 24 = s8).
        rewrite <- (XE 25%uint63 25%uint63 25%uint63 eq_refl eq_refl (Hn0 25%uint63 eq_refl) eq_refl : rv rho' (a_F st') 25 = s9).
        rewrite <- (XE 26%uint63 26%uint63 26%uint63 eq_refl eq_refl (Hn0 26%uint63 eq_refl) eq_refl : rv rho' (a_F st') 26 = s10).
        rewrite <- (XE 27%uint63 27%uint63 27%uint63 eq_refl eq_refl (Hn0 27%uint63 eq_refl) eq_refl : rv rho' (a_F st') 27 = s11).
        reflexivity. }
      split; [exact Hmp|].
      split.
      { (* [comment removed for export] *)
        split; [exact Hak|].
        split; [exact (post_inv H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_aconst H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_stk H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_auxv H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [cbn [app]; exact (post_heap H IMX GenO3s1_0_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0)|].
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
      split; [rewrite Eerr; cbn [x_errno GenO3s1_0_asan.X] in Hes; exact (post_errno_kept H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 32%uint63 GenO3s1_0_asan.d0 x W HQ eq_refl (Hn0 32%uint63 eq_refl) eq_refl Hes)|].
      split; [intros _; reflexivity|].
      pose proof In0 as In0g. pose proof In1 as In1g. pose proof In2 as In2g. pose proof In3 as In3g. pose proof In4 as In4g.
      unfold gblock in In0, In1, In2, In3, In4.
      rewrite Sz0 in In0. rewrite Sz1 in In1. rewrite Sz2 in In2. rewrite Sz3 in In3. rewrite Sz4 in In4.
      change (to_Z 72%uint63) with 72 in In0. change (to_Z 32%uint63) with 32 in In1. change (to_Z 128%uint63) with 128 in In2.
      change (to_Z 904%uint63) with 904 in In3. change (to_Z 8%uint63) with 8 in In4.
      split.
      { (* [comment removed for export] *)
        cbn [errph_delta chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands].
        split; [rewrite (LBN_length G' GenO3s1_0_asan.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        split; [rewrite (LBN_bytes G' GenO3s1_0_asan.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        apply Forall_cons; [exact In0g|]. apply Forall_cons; [exact In1g|]. apply Forall_cons; [exact In2g|].
        apply Forall_cons; [exact In3g|]. apply Forall_cons; [exact In4g|]. apply Forall_nil. }
      split.
      { (* [comment removed for export] *)
        cbn [ERRPH]. unfold ERR_statics, ERR_chain. cbn [ec_mkey ec_sa ec_nodes ec_es ec_hands ec_eslock ec_eshash ec_tevreg chain_blocks].
        unfold gblock. cbn [blk_addr blk_size fst snd]. rewrite Sz0, Sz1, Sz2, Sz3, Sz4.
        change (to_Z 72%uint63) with 72. change (to_Z 32%uint63) with 32. change (to_Z 128%uint63) with 128.
        change (to_Z 904%uint63) with 904. change (to_Z 8%uint63) with 8.
        destruct Hstat as (Cs1 & Cs2 & Cs3 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10 & Cs11 & Cs12 & Cs13 & Cs14 & Cs15 & Cs16 & Cs17 & Cs18 & Cs19).
        split.
        - (* [comment removed for export] *)
          split; [apply (RWC (of_Z A_master_once_ret)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_master_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_master_key)); vm_compute; reflexivity|].
          split; [unfold LIBKEY0; exact Rtsd3|].
          split; [apply (AGR A_stopped 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs12]|].
          split; [apply (AGR A_base_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs14]|].
          split; [apply (AGR A_base_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs15]|].
          split; [apply (RWC (of_Z A_load_strings_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_load_strings_ret)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_optsdone)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_err_string_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_err_string_ret)); vm_compute; reflexivity|].
          split; [exact Resl|].
          split; [exact Resh|].
          split; [apply (RWC (of_Z A_tevent_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_tevent_ret)); vm_compute; reflexivity|].
          split; [exact Rtev|].
          split; [unfold LIBKEY0; apply (RWC (of_Z (A_keys + 8 * (1 + 3)))); vm_compute; reflexivity|].
          split; [unfold LIBKEY0; apply (RWC (of_Z A_next_key)); vm_compute; reflexivity|].
          split.
          { apply (proj2 (rw_cells_app asegs m1 A_key_lock [C8 (wz 0)] [C8 (wz 0)])). split.
            - apply (RWC (of_Z A_key_lock)); vm_compute; reflexivity.
            - cbn [cells_size csize Z.of_nat]. destruct Hkeys as (K1 & K2 & K3 & K4).
              apply (AGR (A_key_lock + 8) 8 ltac:(vm_compute; reflexivity)); [reflexivity |].
              exact (proj2 (proj1 (rw_cells_app asegs m A_key_lock [C8 (wz 0)] [C8 (wz 0)]) K2)). }
          split; [apply (RWC (of_Z A_td_cancelbuf)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_td_tsd_used)); vm_compute; reflexivity|].
          split; [apply (AGR A_keys 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs19]|].
          unfold LIBKEY0. exact Rtsd1.
        - (* [comment removed for export] *)
          split; [apply in_app_iff; left; exact In0|]. split; [reflexivity|].
          split; [exact Rmkey|].
          split; [apply in_app_iff; left; exact In1|]. split; [reflexivity|].
          split.
          { unfold sa_cells. apply (proj2 (rw_cells_app asegs m1 (g_addr g1) [C4 (wz 1); C4 (wz 0); C8 (wz 0); C8 (wz 1)] [C8 (wz (g_addr g2))])).
            split; [| exact Rsa]. rewrite <- (Z.add_0_r (g_addr g1)). change 0 with (to_Z 0%uint63) at 2.
            apply (RWB 1%uint63 g1 0%uint63 _ Hg1). vm_compute. reflexivity. }
          split; [apply in_app_iff; left; exact In2|]. split; [reflexivity|].
          split; [exact Rnodes|].
          split; [apply in_app_iff; left; exact In3|]. split; [reflexivity|].
          split; [apply in_app_iff; left; exact In4|]. split; [reflexivity|].
          cbn [chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands].
          pose proof aceil_facts as ACF.
          assert (ARG : forall b, In b (LBN G' ++ q_LB0 Q) -> arange (blk_addr b) (blk_size b)).
          { intros b Hb. pose proof (post_block_range H IMX GenO3s1_0_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0 b Hb) as (R0 & R16 & Rn & Rtop & Rce & _).
            unfold arange. split; [exact R0|]. split; [exact R16|]. split; [exact Rn|]. split; [exact Rtop|]. clear - Rce Rn ACF. slia. }
          apply Forall_cons; [exact (ARG (g_id g0, g_addr g0, 72) ltac:(apply in_app_iff; left; exact In0))|].
          apply Forall_cons; [exact (ARG (g_id g1, g_addr g1, 32) ltac:(apply in_app_iff; left; exact In1))|].
          apply Forall_cons; [exact (ARG (g_id g2, g_addr g2, 128) ltac:(apply in_app_iff; left; exact In2))|].
          apply Forall_cons; [exact (ARG (g_id g3, g_addr g3, 904) ltac:(apply in_app_iff; left; exact In3))|].
          apply Forall_cons; [exact (ARG (g_id g4, g_addr g4, 8) ltac:(apply in_app_iff; left; exact In4))|].
          apply Forall_nil. }
      split.
      { (* [comment removed for export] *)
        cbn [CTXPH]. destruct Hstat as (Cs1 & Cs2 & Cs3 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10 & Cs11 & Cs12 & Cs13 & Cs14 & Cs15 & Cs16 & Cs17 & Cs18 & Cs19). split.
        - unfold CTX_statics.
          split; [apply (AGR A_defctx_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs1]|].
          split; [apply (AGR A_defctx_tlkey 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs2]|].
          split; [apply (AGR A_defctx_tlkey_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs3]|].
          split; [apply (AGR A_defctx_tlkey_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs4]|].
          split; [apply (AGR A_defctx_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs5]|].
          split; [apply (AGR A_defctx_once_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs6]|].
          split; [apply (AGR A_defctx_exlock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs7]|].
          split; [apply (AGR A_defctx_exmeth_bio 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs8]|].
          split; [apply (AGR (A_tsd_main + 8 * LIBKEY0) 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs9]|].
          split; [apply (AGR A_destructor_key 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs10]|].
          split; [apply (AGR A_base_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs11]|].
          split; [apply (AGR A_stopped 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs12]|].
          split; [apply (AGR A_in_init_config_key 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs13]|].
          split; [apply (AGR A_base_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs14]|].
          split; [apply (AGR A_base_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs15]|].
          split; [apply (AGR A_optsdone_lock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs16]|].
          split; [apply (AGR A_init_lock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs17]|].
          split; [apply (AGR (A_keys + 8 * LIBKEY0) 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs18]|].
          apply (AGR A_keys 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs19].
        - destruct Hblk as [(Ein & Esz & Erng & Emut) (po & pi & Hpo & Hpi)]. split.
          + split; [apply in_app_iff; right; exact Ein|]. split; [exact Esz|]. split; [exact Erng|].
            unfold MUTEX in *. apply (rw_cells_agree (in_range (blk_addr (cx_exlock cx)) (blk_size (cx_exlock cx))) m m1 _ _ (MAGB _ Ein) Emut).
            intros a Ha. unfold in_range in *. rewrite Esz. unfold MUTEX_SIZE. cbn [cells_size csize length Nat.add] in Ha. slia.
          + exists po, pi. split; apply in_app_iff; right; assumption. }
      split.
      { (* [comment removed for export] *)
        split; [| split; [apply Forall_forall; intros sl Hsl; cbn [errst_zero es_slots] in Hsl; apply repeat_spec in Hsl; subst sl; cbn; slia
                      | split; [apply Forall_nil | apply Forall_nil]]].
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
      split.
      { (* [comment removed for export] *)
        unfold lib_shad. cbn [chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands]. unfold gblock. cbn [blk_addr blk_size fst snd].
        pose proof (proj1 (Forall_forall _ _) HSH) as SH.
        apply Forall_cons; [exact (SH g0 InG0)|]. apply Forall_cons; [exact (SH g1 InG1)|]. apply Forall_cons; [exact (SH g2 InG2)|].
        apply Forall_cons; [exact (SH g3 InG3)|]. apply Forall_cons; [exact (SH g4 InG4)|]. apply Forall_nil. }
      split; [exact (post_xs H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
      split.
      { (* [comment removed for export] *)
        exact (post_xpres H IMX GenO3s1_0_asan.KA chks1_0_K Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0 _ chks1_0_xw). }
      split; [exact (post_rfs H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
      pose proof (post_AL H IMX GenO3s1_0_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 Hcs) as HAL'. unfold Q in HAL'. cbn [q_AL0 q_cs] in HAL'.
      pose proof (csum_le H HH (ka_costs GenO3s1_0_asan.KA) ERRINIT_BYTES ERRINIT_BYTES ltac:(apply Z.leb_le; exact chks1_0_msum) ltac:(apply Z.leb_le; exact chks1_0_fsum)) as Hcsum.
      cbn [errph_cost]. unfold ERRINIT_COST. clear - HAL' Hcsum. slia. }
    { (* [comment removed for export] *)
      assert (Ea0 : x 10 = Z_to_bv 64 1) by exact Ha0.
      assert (Eerr : bv_unsigned tp + -164 = errA GenO3s1_16_asan.KA).
      { rewrite Htp, Z_to_bv_unsigned. vm_compute. reflexivity. }
      pose proof Herr as HerrE. rewrite Eerr in HerrE.
      assert (Cc : to_Z (c_cost GenO3s1_16_asan.K) <= 2 ^ 16) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cn : to_Z (c_cnt GenO3s1_16_asan.K) <= 1600) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (Cs : to_Z (c_stack GenO3s1_16_asan.K) = 9072) by (vm_compute; reflexivity).
      assert (Cf : Z.to_nat (to_Z (ka_fsmax GenO3s1_16_asan.KA)) = 4%nat) by (vm_compute; reflexivity).
      assert (Hby' : lb_bytes LB + to_Z (c_cost GenO3s1_16_asan.K) <= as_LIVE_MAX H) by (clear - Hby Cc; slia).
      assert (Hcnt' : Z.of_nat (length LB) + to_Z (c_cnt GenO3s1_16_asan.K) <= as_LIVE_CNT_MAX H) by (clear - Hcnt Cn; slia).
      assert (Hlo' : lo <= bv_unsigned (x 2) - to_Z (c_stack GenO3s1_16_asan.K)) by (clear - Hlo Cs; slia).
      assert (Hsp32' : (bv_unsigned (x 2) - to_Z (c_stack GenO3s1_16_asan.K)) mod 32 = 0) by (rewrite Cs; exact Hsp32).
      assert (Hlf' : (length LF + Z.to_nat (to_Z (ka_fsmax GenO3s1_16_asan.KA)) <= AFS_MAXLIVE)%nat) by (rewrite Cf; clear - Hlf; slia).
      assert (HALc : csum H (ka_costs GenO3s1_16_asan.KA) <= as_AL H s).
      { eapply Z.le_trans; [| exact HAL]. unfold ERRINIT_COST.
        apply (csum_le H HH); apply Z.leb_le; [exact chks1_16_msum | exact chks1_16_fsum]. }
      pose proof (rows_closed (as_TR H) PFC_ERRINIT (ka_pfc GenO3s1_16_asan.KA) chks1_16_pfc Hclosed) as Hpfc.
      pose proof (rows_open (as_TR H) PF_EGS_FRESH (ka_pfo GenO3s1_16_asan.KA) (bv_unsigned (x 1)) CH chks1_16_pfo Hpf) as Hpfo.
      pose proof (start_RnA H GenO3s1_16_asan.KA GenO3s1_16_asan.d0 (S_O3 1) x W F fc m lo chks1_16_K
                    (S_O3_holds x m errv cx 1 can Etp Ea0 Himpl Hmf Hinv Hrelro Hfresh Hkeys Hstat Hac HerrE Hcan)
                    Hstk (conj Hhl Hlo') Hsp63 Hsp16 Hsp32' IMX GenO3s1_16_asan.facts0 GenO3s1_16_asan.n0 IMX_ok IMX_wr_ok chks1_16_ho chks1_16_tags chks1_16_facts) as HRn.
      pose proof (i2a_certificate H IMX GenO3s1_16_asan.KA GenO3s1_16_asan.code chks1_16_K HHx IMX_ok IMX_wr_ok chks1_16_code (ro_const_introA GenO3s1_16_asan.KA chks1_16_roc)
                    (sh0_of_aconst GenO3s1_16_asan.KA chks1_16_sh0) Hpfc
                    (anode_fsmalloc_sound H IMX GenO3s1_16_asan.KA chks1_16_K HHx (sh0_of_aconst GenO3s1_16_asan.KA chks1_16_sh0))
                    (anode_fsfree_sound H IMX GenO3s1_16_asan.KA chks1_16_K HHx (sh0_of_aconst GenO3s1_16_asan.KA chks1_16_sh0) GenO3s1_16_asan.code chks1_16_code)
                    (anode_memset_sound H IMX GenO3s1_16_asan.KA chks1_16_K HHx (sh0_of_aconst GenO3s1_16_asan.KA chks1_16_sh0))
                    (anode_memcpy_sound H IMX GenO3s1_16_asan.KA chks1_16_K HHx IMX_ok (sh0_of_aconst GenO3s1_16_asan.KA chks1_16_sh0))
                    (anode_strlen_sound H IMX GenO3s1_16_asan.KA chks1_16_K HHx IMX_ok (sh0_of_aconst GenO3s1_16_asan.KA chks1_16_sh0)) (anode_memalign_sound H IMX GenO3s1_16_asan.KA chks1_16_K HHx IMX_ok IMX_wr_ok (sh0_of_aconst GenO3s1_16_asan.KA chks1_16_sh0) Hpfc (ro_const_introA GenO3s1_16_asan.KA chks1_16_roc) MAL)
                    GenO3s1_16_asan.fuel (I2AS (state_of GenO3s1_16_asan.d0) GenO3s1_16_asan.n0 GenO3s1_16_asan.blk0 [] 0%uint63 0%uint63 0%uint63 []) GenO3s1_16_asan.X [] (rho_ofA GenO3s1_16_asan.K GenO3s1_16_asan.d0 x W) x F fc msF m mo s LB LF lo B CH
                    chks1_16_run chks1_16_shape eq_refl eq_refl (List.NoDup_nil _) (Forall_nil _)
                    HRn eq_refl eq_refl eq_refl eq_refl Hvis Hkrel Hheap Hrfs Hac Hsh0 Hchain HCH Hpfo HALc Hby' Hcnt' Hlf'
                    Haux HB HB64 Hstk Hhl Hlo' Hsp16 Hsp32' HerrE Hinv) as HC.
      clear HRn.
      match goal with |- as_SR _ _ ?c => match type of HC with as_SR _ _ ?c' => replace c with c' by reflexivity end end.
      apply (ah_mono H HH _ _ _ HC). clear HC.
      (* [comment removed for export] *)
      intros k (rho' & st' & s' & LB' & G' & XS' & ms1 & Ek & Hak & Hmp & (msF1 & mo1 & X1) & Hfin & Hcs & HXR & HXC & HXB & Hsz & Hes & HSH).
      set (Q := I2AE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in X1.
      assert (HG0 : q_G0 Q = []) by reflexivity.
      assert (HQ : q_rho0 Q = rho_ofA GenO3s1_16_asan.K GenO3s1_16_asan.d0 x W) by reflexivity.
      pose proof (post_magree H IMX GenO3s1_16_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0) as MAG. cbn [q_m0 Q] in MAG.
      pose proof (post_magree_block H IMX GenO3s1_16_asan.KA chks1_16_K HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0) as MAGB. cbn [q_m0 q_LB0 Q] in MAGB.
      pose proof (post_rw_cells rho' ms1 G' GenO3s1_16_asan.X HXC) as RWC.
      pose proof (post_blk_rw_cells H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_16_asan.X X1 Hsz HXB) as RWB.
      pose proof (post_blk_arr H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_16_asan.X X1 Hsz HXB) as RWA.
      set (m1 := ms_mem ms1) in *.
      (* [comment removed for export] *)
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_16_asan.X HXC (of_Z (A_tsd_main + 8 * (LIBKEY0 + 3))) 0%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g0 & Hg0 & Rtsd3).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_16_asan.X HXC (of_Z (A_tsd_main + 8 * (LIBKEY0 + 1))) 4%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g4 & Hg4 & Rtsd1).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_16_asan.X HXC (of_Z A_glob_tevent_reg) 5%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g5 & Hg5 & Rtev).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_16_asan.X HXC (of_Z A_err_string_lock) 10%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g10 & Hg10 & Resl).
      destruct (post_ptr_rw0 rho' ms1 G' GenO3s1_16_asan.X HXC (of_Z A_int_error_hash) 11%uint63 eq_refl ltac:(vm_compute; reflexivity)) as (g11 & Hg11 & Resh).
      destruct (post_blk_ptr0 H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_16_asan.X X1 Hsz HXB 0%uint63 g0 24%uint63 1%uint63 Hg0 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s1_16_asan.X Hsz _ _ Hg0))); vm_compute; discriminate)) as (g1 & Hg1 & Rmkey).
      destruct (post_blk_ptr0 H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_16_asan.X X1 Hsz HXB 1%uint63 g1 24%uint63 2%uint63 Hg1 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s1_16_asan.X Hsz _ _ Hg1))); vm_compute; discriminate)) as (g2 & Hg2 & Rsa).
      destruct (post_blk_ptr0 H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_16_asan.X X1 Hsz HXB 2%uint63 g2 0%uint63 3%uint63 Hg2 eq_refl
                  ltac:(rewrite (proj2 (proj2 (blk_of_LBN G' GenO3s1_16_asan.X Hsz _ _ Hg2))); vm_compute; discriminate)) as (g3 & Hg3 & Rnodes).
      change (to_Z 0%uint63) with 0 in Rnodes. rewrite Z.add_0_r in Rnodes.
      destruct (blk_of_LBN G' GenO3s1_16_asan.X Hsz _ _ Hg0) as (In0 & InG0 & Sz0). destruct (blk_of_LBN G' GenO3s1_16_asan.X Hsz _ _ Hg1) as (In1 & InG1 & Sz1).
      destruct (blk_of_LBN G' GenO3s1_16_asan.X Hsz _ _ Hg2) as (In2 & InG2 & Sz2). destruct (blk_of_LBN G' GenO3s1_16_asan.X Hsz _ _ Hg3) as (In3 & InG3 & Sz3).
      destruct (blk_of_LBN G' GenO3s1_16_asan.X Hsz _ _ Hg4) as (In4 & InG4 & Sz4).
      change (nth (Z.to_nat (to_Z 0%uint63)) (x_sizes GenO3s1_16_asan.X) 0%uint63) with 72%uint63 in Sz0.
      change (nth (Z.to_nat (to_Z 1%uint63)) (x_sizes GenO3s1_16_asan.X) 0%uint63) with 32%uint63 in Sz1.
      change (nth (Z.to_nat (to_Z 2%uint63)) (x_sizes GenO3s1_16_asan.X) 0%uint63) with 128%uint63 in Sz2.
      change (nth (Z.to_nat (to_Z 3%uint63)) (x_sizes GenO3s1_16_asan.X) 0%uint63) with 904%uint63 in Sz3.
      change (nth (Z.to_nat (to_Z 4%uint63)) (x_sizes GenO3s1_16_asan.X) 0%uint63) with 8%uint63 in Sz4.
      destruct (post_errno H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1) as [errv0 Herr0].
      (* [comment removed for export] *)
      assert (AGR : forall A n, unw_range GenO3s1_16_asan.K A n = true -> forall cs, Z.of_nat (cells_size cs) = n -> rw_cells asegs m A cs -> rw_cells asegs m1 A cs).
      { intros A n Hu cs Hn Hrw. apply (rw_cells_agree (in_range A n) m m1 A cs (MAG A n Hu) Hrw). rewrite Hn. exact (fun a h => h). }
      (* [comment removed for export] *)
      exists (rv rho' (a_F st') 5), (rv rho' (a_F st') 6), (rv rho' (a_F st') 7),
             (rv rho' (a_F st') 11), (rv rho' (a_F st') 12), (rv rho' (a_F st') 13), (rv rho' (a_F st') 14),
             (rv rho' (a_F st') 15), (rv rho' (a_F st') 16), (rv rho' (a_F st') 17),
             (rv rho' (a_F st') 28), (rv rho' (a_F st') 29), (rv rho' (a_F st') 30), (rv rho' (a_F st') 31),
             m1, errv, s', (LBN G'),
             (mkEC (gblock g0) (gblock g1) (gblock g2) (gblock g3) (gblock g4) (g_addr g10) (g_addr g11) (g_addr g5)), XS'.
      assert (Hn0 : forall t : int, (t <? GenO3s1_16_asan.n0)%uint63 = true -> to_Z t < to_Z (q_n0 Q)) by (intros t Ht; exact (i_ltb_lt _ _ Ht)).
      pose proof (fun kk t r => xreg_entry H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_16_asan.X X1 HXR GenO3s1_16_asan.d0 x W kk t r HQ) as XE.
      cbn [ec_mkey ec_sa ec_nodes ec_es ec_hands ec_eslock ec_eshash ec_tevreg].
      split.
      { rewrite Ek, (post_regs H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1).
        change (q_F Q) with F. change (q_fc Q) with fc. replace (q_rho0 Q (c_tra GenO3s1_16_asan.K)) with ra by reflexivity. fold m1.
        rewrite <- (XE 1%uint63 4%uint63 1%uint63 eq_refl eq_refl (Hn0 4%uint63 eq_refl) eq_refl : rv rho' (a_F st') 1 = ra).
        rewrite <- (xreg_sp H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' GenO3s1_16_asan.X X1 HXR GenO3s1_16_asan.d0 x W HQ eq_refl eq_refl : rv rho' (a_F st') 2 = sp).
        rewrite <- (XE 3%uint63 5%uint63 3%uint63 eq_refl eq_refl (Hn0 5%uint63 eq_refl) eq_refl : rv rho' (a_F st') 3 = gp).
        assert (E4 : rv rho' (a_F st') 4 = tp).
        { rewrite (xreg_W st' rho' G' GenO3s1_16_asan.X HXR 4%uint63 _ eq_refl : rv rho' (a_F st') 4 = _), Htp. apply bv_eq. vm_compute. reflexivity. }
        rewrite <- E4.
        rewrite <- (XE 8%uint63 9%uint63 8%uint63 eq_refl eq_refl (Hn0 9%uint63 eq_refl) eq_refl : rv rho' (a_F st') 8 = s0).
        rewrite <- (XE 9%uint63 10%uint63 9%uint63 eq_refl eq_refl (Hn0 10%uint63 eq_refl) eq_refl : rv rho' (a_F st') 9 = s1).
        assert (E10 : rv rho' (a_F st') 10 = Z_to_bv 64 (blk_addr (gblock g3))).
        { destruct (xreg_New st' rho' G' GenO3s1_16_asan.X HXR 10%uint63 3%uint63 0%uint63 eq_refl) as (g3' & Hg3' & E).
          rewrite Hg3 in Hg3'. injection Hg3' as <-. change (to_Z 10%uint63) with 10 in E. rewrite E, Z.add_0_r. reflexivity. }
        rewrite <- E10.
        rewrite <- (XE 18%uint63 18%uint63 18%uint63 eq_refl eq_refl (Hn0 18%uint63 eq_refl) eq_refl : rv rho' (a_F st') 18 = s2).
        rewrite <- (XE 19%uint63 19%uint63 19%uint63 eq_refl eq_refl (Hn0 19%uint63 eq_refl) eq_refl : rv rho' (a_F st') 19 = s3).
        rewrite <- (XE 20%uint63 20%uint63 20%uint63 eq_refl eq_refl (Hn0 20%uint63 eq_refl) eq_refl : rv rho' (a_F st') 20 = s4).
        rewrite <- (XE 21%uint63 21%uint63 21%uint63 eq_refl eq_refl (Hn0 21%uint63 eq_refl) eq_refl : rv rho' (a_F st') 21 = s5).
        rewrite <- (XE 22%uint63 22%uint63 22%uint63 eq_refl eq_refl (Hn0 22%uint63 eq_refl) eq_refl : rv rho' (a_F st') 22 = s6).
        rewrite <- (XE 23%uint63 23%uint63 23%uint63 eq_refl eq_refl (Hn0 23%uint63 eq_refl) eq_refl : rv rho' (a_F st') 23 = s7).
        rewrite <- (XE 24%uint63 24%uint63 24%uint63 eq_refl eq_refl (Hn0 24%uint63 eq_refl) eq_refl : rv rho' (a_F st') 24 = s8).
        rewrite <- (XE 25%uint63 25%uint63 25%uint63 eq_refl eq_refl (Hn0 25%uint63 eq_refl) eq_refl : rv rho' (a_F st') 25 = s9).
        rewrite <- (XE 26%uint63 26%uint63 26%uint63 eq_refl eq_refl (Hn0 26%uint63 eq_refl) eq_refl : rv rho' (a_F st') 26 = s10).
        rewrite <- (XE 27%uint63 27%uint63 27%uint63 eq_refl eq_refl (Hn0 27%uint63 eq_refl) eq_refl : rv rho' (a_F st') 27 = s11).
        reflexivity. }
      split; [exact Hmp|].
      split.
      { (* [comment removed for export] *)
        split; [exact Hak|].
        split; [exact (post_inv H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_aconst H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_stk H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [exact (post_auxv H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
        split; [cbn [app]; exact (post_heap H IMX GenO3s1_16_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0)|].
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
      split; [rewrite Eerr; cbn [x_errno GenO3s1_16_asan.X] in Hes; exact (post_errno_kept H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 32%uint63 GenO3s1_16_asan.d0 x W HQ eq_refl (Hn0 32%uint63 eq_refl) eq_refl Hes)|].
      split; [intros _; reflexivity|].
      pose proof In0 as In0g. pose proof In1 as In1g. pose proof In2 as In2g. pose proof In3 as In3g. pose proof In4 as In4g.
      unfold gblock in In0, In1, In2, In3, In4.
      rewrite Sz0 in In0. rewrite Sz1 in In1. rewrite Sz2 in In2. rewrite Sz3 in In3. rewrite Sz4 in In4.
      change (to_Z 72%uint63) with 72 in In0. change (to_Z 32%uint63) with 32 in In1. change (to_Z 128%uint63) with 128 in In2.
      change (to_Z 904%uint63) with 904 in In3. change (to_Z 8%uint63) with 8 in In4.
      split.
      { (* [comment removed for export] *)
        cbn [errph_delta chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands].
        split; [rewrite (LBN_length G' GenO3s1_16_asan.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        split; [rewrite (LBN_bytes G' GenO3s1_16_asan.X Hsz); apply Z.leb_le; vm_compute; reflexivity|].
        apply Forall_cons; [exact In0g|]. apply Forall_cons; [exact In1g|]. apply Forall_cons; [exact In2g|].
        apply Forall_cons; [exact In3g|]. apply Forall_cons; [exact In4g|]. apply Forall_nil. }
      split.
      { (* [comment removed for export] *)
        cbn [ERRPH]. unfold ERR_statics, ERR_chain. cbn [ec_mkey ec_sa ec_nodes ec_es ec_hands ec_eslock ec_eshash ec_tevreg chain_blocks].
        unfold gblock. cbn [blk_addr blk_size fst snd]. rewrite Sz0, Sz1, Sz2, Sz3, Sz4.
        change (to_Z 72%uint63) with 72. change (to_Z 32%uint63) with 32. change (to_Z 128%uint63) with 128.
        change (to_Z 904%uint63) with 904. change (to_Z 8%uint63) with 8.
        destruct Hstat as (Cs1 & Cs2 & Cs3 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10 & Cs11 & Cs12 & Cs13 & Cs14 & Cs15 & Cs16 & Cs17 & Cs18 & Cs19).
        split.
        - (* [comment removed for export] *)
          split; [apply (RWC (of_Z A_master_once_ret)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_master_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_master_key)); vm_compute; reflexivity|].
          split; [unfold LIBKEY0; exact Rtsd3|].
          split; [apply (AGR A_stopped 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs12]|].
          split; [apply (AGR A_base_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs14]|].
          split; [apply (AGR A_base_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs15]|].
          split; [apply (RWC (of_Z A_load_strings_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_load_strings_ret)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_optsdone)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_err_string_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_err_string_ret)); vm_compute; reflexivity|].
          split; [exact Resl|].
          split; [exact Resh|].
          split; [apply (RWC (of_Z A_tevent_once)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_tevent_ret)); vm_compute; reflexivity|].
          split; [exact Rtev|].
          split; [unfold LIBKEY0; apply (RWC (of_Z (A_keys + 8 * (1 + 3)))); vm_compute; reflexivity|].
          split; [unfold LIBKEY0; apply (RWC (of_Z A_next_key)); vm_compute; reflexivity|].
          split.
          { apply (proj2 (rw_cells_app asegs m1 A_key_lock [C8 (wz 0)] [C8 (wz 0)])). split.
            - apply (RWC (of_Z A_key_lock)); vm_compute; reflexivity.
            - cbn [cells_size csize Z.of_nat]. destruct Hkeys as (K1 & K2 & K3 & K4).
              apply (AGR (A_key_lock + 8) 8 ltac:(vm_compute; reflexivity)); [reflexivity |].
              exact (proj2 (proj1 (rw_cells_app asegs m A_key_lock [C8 (wz 0)] [C8 (wz 0)]) K2)). }
          split; [apply (RWC (of_Z A_td_cancelbuf)); vm_compute; reflexivity|].
          split; [apply (RWC (of_Z A_td_tsd_used)); vm_compute; reflexivity|].
          split; [apply (AGR A_keys 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs19]|].
          unfold LIBKEY0. exact Rtsd1.
        - (* [comment removed for export] *)
          split; [apply in_app_iff; left; exact In0|]. split; [reflexivity|].
          split; [exact Rmkey|].
          split; [apply in_app_iff; left; exact In1|]. split; [reflexivity|].
          split.
          { unfold sa_cells. apply (proj2 (rw_cells_app asegs m1 (g_addr g1) [C4 (wz 1); C4 (wz 0); C8 (wz 0); C8 (wz 1)] [C8 (wz (g_addr g2))])).
            split; [| exact Rsa]. rewrite <- (Z.add_0_r (g_addr g1)). change 0 with (to_Z 0%uint63) at 2.
            apply (RWB 1%uint63 g1 0%uint63 _ Hg1). vm_compute. reflexivity. }
          split; [apply in_app_iff; left; exact In2|]. split; [reflexivity|].
          split; [exact Rnodes|].
          split; [apply in_app_iff; left; exact In3|]. split; [reflexivity|].
          split; [apply in_app_iff; left; exact In4|]. split; [reflexivity|].
          cbn [chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands].
          pose proof aceil_facts as ACF.
          assert (ARG : forall b, In b (LBN G' ++ q_LB0 Q) -> arange (blk_addr b) (blk_size b)).
          { intros b Hb. pose proof (post_block_range H IMX GenO3s1_16_asan.KA HHx Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0 b Hb) as (R0 & R16 & Rn & Rtop & Rce & _).
            unfold arange. split; [exact R0|]. split; [exact R16|]. split; [exact Rn|]. split; [exact Rtop|]. clear - Rce Rn ACF. slia. }
          apply Forall_cons; [exact (ARG (g_id g0, g_addr g0, 72) ltac:(apply in_app_iff; left; exact In0))|].
          apply Forall_cons; [exact (ARG (g_id g1, g_addr g1, 32) ltac:(apply in_app_iff; left; exact In1))|].
          apply Forall_cons; [exact (ARG (g_id g2, g_addr g2, 128) ltac:(apply in_app_iff; left; exact In2))|].
          apply Forall_cons; [exact (ARG (g_id g3, g_addr g3, 904) ltac:(apply in_app_iff; left; exact In3))|].
          apply Forall_cons; [exact (ARG (g_id g4, g_addr g4, 8) ltac:(apply in_app_iff; left; exact In4))|].
          apply Forall_nil. }
      split.
      { (* [comment removed for export] *)
        cbn [CTXPH]. destruct Hstat as (Cs1 & Cs2 & Cs3 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10 & Cs11 & Cs12 & Cs13 & Cs14 & Cs15 & Cs16 & Cs17 & Cs18 & Cs19). split.
        - unfold CTX_statics.
          split; [apply (AGR A_defctx_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs1]|].
          split; [apply (AGR A_defctx_tlkey 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs2]|].
          split; [apply (AGR A_defctx_tlkey_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs3]|].
          split; [apply (AGR A_defctx_tlkey_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs4]|].
          split; [apply (AGR A_defctx_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs5]|].
          split; [apply (AGR A_defctx_once_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs6]|].
          split; [apply (AGR A_defctx_exlock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs7]|].
          split; [apply (AGR A_defctx_exmeth_bio 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs8]|].
          split; [apply (AGR (A_tsd_main + 8 * LIBKEY0) 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs9]|].
          split; [apply (AGR A_destructor_key 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs10]|].
          split; [apply (AGR A_base_inited 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs11]|].
          split; [apply (AGR A_stopped 1 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs12]|].
          split; [apply (AGR A_in_init_config_key 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs13]|].
          split; [apply (AGR A_base_once 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs14]|].
          split; [apply (AGR A_base_ret 4 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs15]|].
          split; [apply (AGR A_optsdone_lock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs16]|].
          split; [apply (AGR A_init_lock 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs17]|].
          split; [apply (AGR (A_keys + 8 * LIBKEY0) 24 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs18]|].
          apply (AGR A_keys 8 ltac:(vm_compute; reflexivity)); [reflexivity | exact Cs19].
        - destruct Hblk as [(Ein & Esz & Erng & Emut) (po & pi & Hpo & Hpi)]. split.
          + split; [apply in_app_iff; right; exact Ein|]. split; [exact Esz|]. split; [exact Erng|].
            unfold MUTEX in *. apply (rw_cells_agree (in_range (blk_addr (cx_exlock cx)) (blk_size (cx_exlock cx))) m m1 _ _ (MAGB _ Ein) Emut).
            intros a Ha. unfold in_range in *. rewrite Esz. unfold MUTEX_SIZE. cbn [cells_size csize length Nat.add] in Ha. slia.
          + exists po, pi. split; apply in_app_iff; right; assumption. }
      split.
      { (* [comment removed for export] *)
        split; [| split; [apply Forall_forall; intros sl Hsl; cbn [errst_zero es_slots] in Hsl; apply repeat_spec in Hsl; subst sl; cbn; slia
                      | split; [apply Forall_nil | apply Forall_nil]]].
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
      split.
      { (* [comment removed for export] *)
        unfold lib_shad. cbn [chain_blocks ec_mkey ec_sa ec_nodes ec_es ec_hands]. unfold gblock. cbn [blk_addr blk_size fst snd].
        pose proof (proj1 (Forall_forall _ _) HSH) as SH.
        apply Forall_cons; [exact (SH g0 InG0)|]. apply Forall_cons; [exact (SH g1 InG1)|]. apply Forall_cons; [exact (SH g2 InG2)|].
        apply Forall_cons; [exact (SH g3 InG3)|]. apply Forall_cons; [exact (SH g4 InG4)|]. apply Forall_nil. }
      split; [exact (post_xs H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
      split.
      { (* [comment removed for export] *)
        exact (post_xpres H IMX GenO3s1_16_asan.KA chks1_16_K Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 HG0 _ chks1_16_xw). }
      split; [exact (post_rfs H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1)|].
      pose proof (post_AL H IMX GenO3s1_16_asan.KA Q st' rho' msF1 mo1 ms1 s' LB' G' XS' X1 Hcs) as HAL'. unfold Q in HAL'. cbn [q_AL0 q_cs] in HAL'.
      pose proof (csum_le H HH (ka_costs GenO3s1_16_asan.KA) ERRINIT_BYTES ERRINIT_BYTES ltac:(apply Z.leb_le; exact chks1_16_msum) ltac:(apply Z.leb_le; exact chks1_16_fsum)) as Hcsum.
      cbn [errph_cost]. unfold ERRINIT_COST. clear - HAL' Hcsum. slia. }
  Qed.
End C.
