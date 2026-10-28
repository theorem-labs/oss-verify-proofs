(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsWalk AsAtomics ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AKit ECH_AsKit ECH_AKitS ECH_AStmt_C0 ECH_AC0_locks ECH_AStmt_C1 ECH_AStmt_C2 ECH_AC2_ex ECH_AC2_init ECH_APF_C4 ECH_AStmt_C4.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition EGS_RA1 : Z := 0x1f26cc.   (* [comment removed for export] *)
Definition EGS_BODY : Z := 0x1f26f4.  (* [comment removed for export] *)
Definition EGS_RA2 : Z := 0x1f2700.   (* [comment removed for export] *)
Definition EGS_RA3 : Z := 0x1f2710.   (* [comment removed for export] *)
Definition EGS_JOIN : Z := 0x1f277c.  (* [comment removed for export] *)
Definition EGS_RA4 : Z := 0x1f2788.   (* [comment removed for export] *)
Definition EGS_EXIT : Z := 0x1f27c8.  (* [comment removed for export] *)
Definition EGS_ERRG : Z := 0xbe1be8.  (* [comment removed for export] *)

Ltac ret_lit RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac ret_lit_any := match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => ret_lit r end.
Ltac show_goal := match goal with |- evt _ _ (MS ?R _ ?pc _ _ ?mx _) => idtac "PC" pc; idtac R end.
Ltac ubal_any :=
  repeat match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] => rewrite (al8u x) by (first [assumption | lia])
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (al4u x) by (first [assumption | lia])
  | |- context [Z.land ?x 7] => rewrite (al8 x) by (first [assumption | lia])
  | |- context [Z.land ?x 3] => rewrite (al4 x) by (first [assumption | lia])
  end.

(* [comment removed for export] *)
Lemma egs_le4_sx32 : forall w : word, le4 (sx32 w) = le4 w.
Proof.
  intros w. transitivity (le4 (Z_to_bv 64 (bv_unsigned w))); [| f_equal; apply Z_to_bv_bv_unsigned].
  unfold sx32. apply le4_congr. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite Zminus_mod_idemp_l. replace (bv_unsigned w + 2^31 - 2^31) with (bv_unsigned w) by lia. reflexivity.
Qed.
Lemma egs_rw_C4_sx32 : forall m A w, rw_cells asegs m A [C4 (sx32 w)] -> rw_cells asegs m A [C4 w].
Proof.
  intros mq A w C. destruct C as [[Hwf Hb] Hw]. split; [split|]; [exact Hwf| |exact Hw].
  revert Hb. cbn [cells_bytes cbytes app]. rewrite egs_le4_sx32. exact (fun x => x).
Qed.

(* [comment removed for export] *)
Lemma aconst_ok_errno {HCEIL : HeapCeil} : aconst_ok (ARERRNO, ARERRNO + 4).
Proof.
  unfold ARERRNO, ATP. apply aconst_ok_intro;
    unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL, AF_DCO_CELL, AVERBOSITY_CELL,
      AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP in *; rewrite ?ASHADOW_BASE_val; lia.
Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma egs_lib_at : forall LF LB m m' c exl lo hi XS,
    as_RFS H LF m -> chain_apl H c -> Forall (fs_scratch H LF) XS ->
    munch ((lo, hi) :: XS ++ ERRNO_X) m m' -> wmono asegs m m' -> aceil <= lo ->
    CTX_statics m exl -> ERR_statics m c -> ERR_chain LB m c -> lib_shad (chain_blocks c) m ->
    CTX_statics m' exl /\ ERR_statics m' c /\ ERR_chain LB m' c /\ lib_shad (chain_blocks c) m'.
  Proof.
    intros LF LB m m' c exl lo hi XS RFS CA FXS MU WM CE CS ES EC LS.
    assert (AG : magree (lib_addr (chain_blocks c)) m m').
    { eapply (lib_magree_scratch H HH); [exact RFS| exact CA| exact MU| exact WM| exact CE|].
      apply Forall_app. split; [apply scr_ok_of_scratch; exact FXS| apply scr_ok_errno]. }
    split; [eapply CTX_statics_frame; [exact CS| eapply magree_statics_of; exact AG]|].
    split; [eapply ERR_statics_frame; [exact ES| eapply magree_statics_of; exact AG]|].
    split; [eapply ERR_chain_frame_chain; [exact EC| exact AG]|].
    eapply lib_shad_frame; [exact LS| exact AG].
  Qed.

  Lemma aegs_ready_spec : egs_ready_stmt H.
  Proof.
    unfold egs_ready_stmt. intros until errv. intros A0 SV TP ERR CS ES EC CB CA LS AC RL RFS LFN THR SPA ST CEIL LO MI RAE. subst a0.
    unfold P_ossl_err_get_state_int, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, AFS_STACK in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. unfold ATP in *. rewrite (unsigned_lit 12459152) in ERR by lia. change (12459152 + -164) with 12458988 in ERR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    (* [comment removed for export] *)
    pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CA)))) as R5. cbv beta in R5. rewrite Z5 in R5.
    destruct R5 as (E1 & E2 & E3 & E4 & E5 & E6 & E7). unfold ERRST_SIZE in *.
    set (es := blk_addr (ec_es c)) in *.
    pose proof (rw_cells_bound _ _ _ _ ERR) as ERRB. cbn [cells_size csize Nat.add length] in ERRB.
    carve_frame 48%nat ST.
    do 7 st1. step.
    (* [comment removed for export] *)
    step. st1. st1. step.
    assert (TOPW : Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) [(lo, bv_unsigned sp)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AIMG_TOP in *; lia| apply Forall_nil]).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ ?P (MS (mkR ?ra_ ?sp_ ?gp_ ?tp_ ?t0_ ?t1_ ?t2_ ?s0_ ?s1_ _ _ ?a2_ ?a3_ ?a4_ ?a5_ ?a6_ ?a7_ ?s2_ ?s3_ _ ?s5_ ?s6_ ?s7_ ?s8_ ?s9_ ?s10_ ?s11_ ?t3_ ?t4_ ?t5_ ?t6_) ?F_ _ ?fc_ _ ?mx ?rom) =>
    assert (BODY : forall (rax a0x a1x s4x : word), (save <> 0 -> s4x = sx32 errv) ->
      evt asegs P (MS (mkR rax sp_ gp_ tp_ t0_ t1_ t2_ s0_ s1_ a0x a1x a2_ a3_ a4_ a5_ a6_ a7_ s2_ s3_ s4x s5_ s6_ s7_ s8_ s9_ s10_ s11_ t3_ t4_ t5_ t6_)
                       F_ (Z_to_bv 64 EGS_BODY) fc_ None mx rom)) end.
    { intros rax a0x a1x s4x S4X. unfold EGS_BODY.
      (* [comment removed for export] *)
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        assert (ES1 : ERR_statics m1 c) by (eapply ERR_statics_across; [exact ES| exact MU| exact WM| exact TOPW]);
        assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]);
        assert (RL1 : arelro_lib m1) by (eapply arelro_across; [exact RL| exact MU| apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]]);
        assert (RFS1 : as_RFS H LF m1) by (eapply (RFS_stack H HH); [exact RFS| exact MU| exact WM| exact CEIL]);
        assert (THR1 : athr_cells m1) by (eapply athr_cells_frame; [exact THR| exact MU| exact WM| apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]]) end.
      eapply evt_cut.
      { eapply (cinitcrypto_spec H HHx) with (lo := lo) (c := c) (LF := LF);
          [ reflexivity| reflexivity| exact ES1| exact AC1| exact RL1| exact RFS1| exact LFN| exact THR1| reflexivity
          | rewrite unsigned_lit by lia; clear - SPA SPR; Z.div_mod_to_equations; lia
          | rewrite unsigned_lit by lia; exact ST| exact CEIL
          | rewrite unsigned_lit by lia; unfold CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, AFS_STACK in *; lia| exact MI
          | rewrite unsigned_lit by lia; reflexivity ]. }
      clear ES1 AC1 RL1 RFS1 THR1 THR.
      intros ms' PO. unfold cinit_post in PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & XS & -> & FXS & MU' & WM' & MI2 & ST2 & ES2 & RFS2 & AC2 & RL2).
      ret_lit_any. rewrite (unsigned_lit (bv_unsigned sp + -48)) in MU' by lia. rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2 by lia.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        lazymatch type of FR with rw_cells _ ?m1 ?A ?cs =>
          assert (FR2 : rw_cells asegs mq A cs)
            by (eapply (rw_cells_scratch_hi H HH); [exact FR| exact MU'| exact WM'| exact CEIL| lia| lia| exact RFS| apply scr_ok_of_scratch; exact FXS]) end end.
      lazymatch type of MU' with munch _ ?m1 ?mq =>
        assert (MU2 : munch ((lo, bv_unsigned sp) :: XS ++ ERRNO_X) m mq)
          by (eapply (munch_cons_compose _ _ _ _ _ _ MU MU');
              [ intros a K; cbn in K |- *; split; [| exact I]; destruct K as [K _]; exact K
              | intros a K; cbn in K |- *; destruct K as [K1 K2]; apply (proj1 (outside_app _ _ _)) in K2; destruct K2 as [K2 _];
                split; [clear - K1 SPR; lia| exact K2] ]);
        pose proof (wmono_trans _ _ _ _ WM WM') as WM2 end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        assert (ERR2 : rw_cells asegs mq 12458988 [C4 errv])
          by (eapply (rw_cells_scratch_img H HH) with (W := XS); [exact ERR| exact MU'| exact WM'| exact CEIL| cbn; unfold AIMG_TOP; lia| exact RFS
              | apply scr_ok_of_scratch; exact FXS
              | eapply Forall_impl; [| exact FXS]; intros iv SC _; pose proof (fs_scratch_range H HH _ _ _ RFS SC) as K; cbn in K |- *; unfold AIMG_TOP in K; lia ]) end.
      clear FR ERR MU WM MU' WM' MI ST. rename MI2 into MI. rename ST2 into ST.
      pose proof (egs_lib_at _ _ _ _ _ _ _ _ _ RFS CA FXS MU2 WM2 CEIL CS ES EC LS) as (CS2 & _ & EC2 & LS2).
      (* [comment removed for export] *)
      step. try if_lit. step. step. step.
      eapply evt_cut.
      { eapply cgetlocalex_spec with (lo := lo) (c := c) (exl := exl) (LIB := chain_blocks c);
          [ reflexivity| reflexivity| reflexivity| exact CS2| exact ES2| apply (ERR_chain_restrict LB); exact EC2| exact CB| exact LS2| exact AC2
          | rewrite unsigned_lit by lia; exact ST| exact CEIL
          | rewrite unsigned_lit by lia; unfold CGETLOCALEX_STACK, FR_get_local_ex, FR_CRYPTO_THREAD_get_local_ex, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *; lia| exact MI
          | rewrite unsigned_lit by lia; reflexivity ]. }
      intros ms' PO. unfold c2_post in PO.
      destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m3 & -> & MU' & WM' & MI3 & ST3 & CS3 & ES3 & EC3).
      ret_lit_any. rewrite (unsigned_lit (bv_unsigned sp + -48)) in MU' by lia. rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST3 by lia.
      carry MU' WM'.
      lazymatch type of MU' with munch _ ?m1 ?mq =>
        assert (MU3 : munch ((lo, bv_unsigned sp) :: XS ++ ERRNO_X) m mq)
          by (eapply (munch_cons_compose _ _ _ _ _ _ MU2 MU');
              [ intros a K; exact K
              | intros a K; cbn in K |- *; destruct K as [K1 _]; split; [clear - K1 SPR; lia| exact I] ]);
        pose proof (wmono_trans _ _ _ _ WM2 WM') as WM3;
        assert (RFS3 : as_RFS H LF mq) by (eapply (RFS_stack H HH); [exact RFS2| exact MU'| exact WM'| exact CEIL]);
        assert (AC3 : ACONST mq) by (eapply ACONST_stack_frame; [exact AC2| exact MU'| exact WM'| exact CEIL]);
        assert (RL3 : arelro_lib mq) by (eapply arelro_across; [exact RL2| exact MU'| apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]]) end.
      clear MU2 WM2 MU' WM' MI ST CS2 EC2 LS2 ES2 RFS2 AC2 RL2. rename MI3 into MI. rename ST3 into ST.
      pose proof (egs_lib_at _ _ _ _ _ _ _ _ _ RFS CA FXS MU3 WM3 CEIL CS ES EC LS) as (_ & _ & EC3' & LS3). clear EC3.
      (* [comment removed for export] *)
      step. step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
      step. step. if_cases K1; zify_cond K1; [|kill K1]; clear K1.
      (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2.
      - (* [comment removed for export] *)
        step. do 6 st1. step. step.
        release_frame FR2 ST (bv_unsigned sp).
        finish; [exact FXS| exact MU3].
      - (* [comment removed for export] *)
        step. step.
        eapply evt_cut. { eapply errnoloc_spec; [reflexivity| exact MI]. }
        intros ms' ->. ret_lit_any.
        pose proof (ACONST_errno_accessible _ AC3) as ACCE. unfold ATP.
        step. ub_dead. step. ubal_any. step. if_lit. zstep. zstep. ck8_check_lit ACCE 0xbe1be8. clear ACCE.
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
          assert (MU4 : munch ((ARERRNO, ARERRNO + 4) :: (lo, bv_unsigned sp) :: XS) m mq)
            by (intros x Hx; apply MU3; cbn in Hx |- *; destruct Hx as (Kx1 & Kx2 & Kx3); split; [exact Kx2|];
                apply (proj2 (outside_app _ _ _)); split; [exact Kx3| cbn; split; [exact Kx1| exact I]]);
          pose proof (munch_refl [(ARERRNO, ARERRNO + 4)] mq) as MUE; pose proof (wmono_refl asegs mq) as WME end.
        clear MU3. unfold ARERRNO, ATP in MU4, MUE. rewrite (S4X ltac:(lia)).
        st1. apply egs_rw_C4_sx32 in ERR2.
        (* [comment removed for export] *)
        step. step. do 6 st1. step. step.
        release_frame FR2 ST (bv_unsigned sp).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
          assert (MUf : munch ((lo, bv_unsigned sp) :: XS ++ ERRNO_X) m mq)
            by (intros x Hx; apply MU4; cbn in Hx |- *; destruct Hx as [Kx1 Kx2]; apply (proj1 (outside_app _ _ _)) in Kx2;
                destruct Kx2 as [Kx2 Kx3]; cbn in Kx3; unfold ARERRNO, ATP in Kx3; destruct Kx3 as [Kx3 _];
                split; [exact Kx3| split; [exact Kx1| exact Kx2]]);
          assert (RFSf : as_RFS H LF mq)
            by (eapply (ah_RFS_frame H HH); [exact RFS3| exact MUE| exact WME|]; apply Forall_cons; [| apply Forall_nil]; left; cbn [fst snd];
                pose proof (RFS_fsb H HH _ _ RFS3) as (F1 & F2 & F3 & F4); unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AIMG_TOP in *; lia);
          assert (ACf : ACONST mq)
            by (eapply ACONST_frame; [exact AC3| exact MUE| exact WME|]; apply Forall_cons; [exact aconst_ok_errno| apply Forall_nil]);
          assert (RLf : arelro_lib mq)
            by (eapply arelro_across; [exact RL3| exact MUE| apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]]) end.
        pose proof (egs_lib_at _ _ _ _ _ _ _ _ _ RFS CA FXS MUf WM3 CEIL CS ES EC LS) as (CSf & ESf & ECf & LSf).
        finish; [exact FXS| exact MUf]. }
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      step. apply BODY. intros K. exfalso. exact (K K0).
    - (* [comment removed for export] *)
      step. step.
      eapply evt_cut. { eapply errnoloc_spec; [reflexivity| exact MI]. }
      intros ms' ->. ret_lit_any. unfold ATP.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        assert (ACCE : accessible mq 0xbe1bc8 64) by (apply ACONST_errno_accessible; eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]) end.
      step. ub_dead. step. ubal_any. step. if_lit. zstep. zstep. ck8_check_lit ACCE 0xbe1be8. clear ACCE.
      st1. step. apply BODY. intros _. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Hypothesis O3 : egs_fresh_stmt H.

  Lemma aegs_spec : egs_stmt H.
  Proof.
    intros ph E. destruct ph as [|c].
    { unfold egs_stmt_for. intros until errv. intros CH VIS A0 SV SVF HP KREL BY CN AUX SPB SPA ST CEIL LO SH0 ERR MI TP AC MF IM GM RL EP EX EB ESH CP RFS LFN CHN CHS PF ECL AL RAE.
      cbn [ERRX] in EX. subst E. eapply O3; try eassumption. cbn [ERRX]. reflexivity. }
    unfold egs_stmt_for. intros until errv. intros CH VIS A0 SV SVF HP KREL BY CN AUX SPB SPA ST CEIL LO SH0 ERR MI TP AC MF IM GM RL EP EX EB ESH CP RFS LFN CHN CHS PF ECL AL RAE.
    cbn [ERRPH ERRX errph_below errph_shad errph_stack CTXPH errph_cnt errph_bytes errph_cost ERRPH_LF PF_egs] in *.
    destruct EP as [ES EC]. destruct CP as [CS CBK].
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (SUB : forall b, In b LB -> In b (blocks_ERRST E ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    pose proof (chain_apl_of_RHEAP H HH _ _ _ _ _ HP EC SUB) as CA.
    pose proof (ah_thr H HH _ _ _ HP) as THR.
    assert (PL : Forall (fun b => ablock_range H (blk_addr b) (blk_size b)) (blocks_ERRST E ++ LB)).
    { apply Forall_forall. intros b Hb. eapply (ah_blocks H HH); [exact HP| exact Hb]. }
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS
      | eapply (aegs_ready_spec H HHx) with (lo := lo) (c := c) (exl := x) (LB := LB) (save := save) (errv := errv) (LF := LF);
        try eassumption; unfold EGS_STACK in *; lia|].
    intros msF2 mo2 KREL2 MP2 PO. unfold egsr_post in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & XS & VIS2 & FXS & MU1 & WM1 & MI1 & ST1 & ERR1 & CS1 & ES1 & EC1 & LS1 & RFS1 & AC1 & RL1).
    pose proof (write_ok_scratch H LF (blocks_ERRST E ++ LB) lo (bv_unsigned sp) XS FXS CEIL) as CW.
    assert (HP1 : as_RHEAP H s (blocks_ERRST E ++ LB) m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (FW : Forall (scr_ok H LF) (XS ++ ERRNO_X)) by (apply Forall_app; split; [apply scr_ok_of_scratch; exact FXS| apply scr_ok_errno]).
    assert (AG : magree (lib_addr (blocks_ERRST E ++ LB)) m m1) by (eapply (lib_magree_scratch H HH); [exact RFS| exact PL| exact MU1| exact WM1| exact CEIL| exact FW]).
    assert (AGL : magree (lib_addr LB) m m1) by (eapply magree_mono; [exact AG|]; intros a Ha; eapply lib_addr_mono; [exact SUB| exact Ha]).
    assert (DJ : forall A n, A + n <= AIMG_TOP -> (A + n <= ARERRNO \/ ARERRNO + 4 <= A) -> disjoint_from ((lo, bv_unsigned sp) :: XS ++ ERRNO_X) A n).
    { intros A n HA HE. eapply (disjoint_scratch_img H HH); [exact RFS| exact FW| exact CEIL| exact HA|].
      apply Forall_app. split; [eapply (low_img_scratch H HH); [exact RFS| exact FXS| exact HA]| apply low_img_errno; exact HE]. }
    eapply (ah_done H HH). unfold egs_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m1, errv, s, (@nil block), c, XS.
    split; [exact VIS2|]. split; [exact MP2|].
    split.
    { unfold c4_frame. cbn [app]. split; [exact KREL2|]. split; [exact MI1|]. split; [exact AC1|]. split; [exact ST1|].
      split; [exact AUX1|]. split; [exact HP1|].
      split; [eapply MEMFLAG_across; [exact MU1| exact WM1| apply DJ; unfold A_mem_inited, AIMG_TOP, ARERRNO, ATP; lia| exact MF]|].
      split; [eapply IMPL_across; [exact MU1| exact WM1| apply DJ; unfold A_malloc_impl, AIMG_TOP, ARERRNO, ATP; lia| exact IM]|].
      split; [eapply GOT_across; [exact MU1| exact WM1| apply DJ; unfold A_got_CRYPTO_malloc, AIMG_TOP, ARERRNO, ATP; lia| exact GM]|].
      exact RL1. }
    split; [exact ERR1|]. split; [intros _; reflexivity|].
    split; [cbn [errph_delta]; split; reflexivity|].
    cbn [app ERRPH CTXPH]. split; [split; [exact ES1| exact EC1]|].
    split; [eapply (CTXPH_frame LB m m1 (CtxReady x)); [cbn [CTXPH]; split; assumption| exact AGL]|].
    split.
    { destruct EX as (EST & ESZ & ESH2 & ESC). split; [| split; [exact ESZ| split]].
      - eapply ERRST_agree; [exact AG| exact EST|]. intros a Ha. right; left. exists (ec_es c).
        pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _). split; [apply SUB; exact I5|]. unfold in_range, ERRST_SIZE in *. rewrite Z5. lia.
      - eapply lib_shad_frame; [exact ESH2|]. eapply magree_mono; [exact AG|]. intros a Ha. eapply lib_addr_mono; [| exact Ha]. intros b Hb. apply in_or_app. left. exact Hb.
      - unfold estrs_cells in *. apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) ESC _ Hb) as [bs BC]. exists bs.
        eapply rw_cells_agree; [exact AG| exact BC|]. intros a Ha. right; left. exists b. split; [apply in_or_app; left; exact Hb|].
        unfold in_range in Ha. pose proof (proj1 (Forall_forall _ _) PL _ (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & B3 & _).
        pose proof (rw_cells_bound _ _ _ _ BC) as BB. revert Ha BB. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. intros Ha BB. lia. }
    split; [exact LS1|]. split; [exact FXS|].
    split.
    { eapply (xpres_weaken H (blocks_ERRST E ++ LB) LB); [| apply Z.le_refl| exact SUB| intros ax K; exact K].
      eapply (xpres_of_munch H s (blocks_ERRST E ++ LB)); [exact HH| exact HP| exact MU1| exact WM1|].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_app. split.
      - apply Forall_forall. intros iv Hiv. right. intros a Ha. apply (proj2 (rin_ivs_app _ _ _)). left.
        clear - Hiv Ha. induction XS as [|y XS IH]; [destruct Hiv|]. destruct Hiv as [<-|Hiv]; [left; exact Ha| right; exact (IH Hiv)].
      - apply Forall_cons; [| apply Forall_nil]. right. intros a Ha. apply (proj2 (rin_ivs_app _ _ _)). right. cbn. left. exact Ha. }
    split; [exact RFS1| cbn [errph_cost]; lia].
  Qed.
End W.
