(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_ALibMF ECH_ALibOK ECH_Iface ECH_AKit
     ECH_AStmt_C1 ECH_AStmt_C2 ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C11 ECH_AStmt_C14 ECH_ALibMid.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Local Ltac unfold_addrs_in Ha :=
  unfold in_range in Ha; cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in Ha;
  unfold LIBKEY0, A_malloc_impl, A_realloc_impl, A_free_impl, A_destructor_key, A_vdso_func, A_mem_inited, A_err_string_once, A_err_string_ret,
    A_err_string_lock, A_int_error_hash, A_master_once_ret, A_master_once, A_master_key,
    A_defctx_inited, A_defctx, A_defctx_exlock, A_defctx_exmeth_bio, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
    A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_stopped, A_base_inited, A_global_cleanup, A_base_once, A_base_ret, A_optsdone,
    A_optsdone_lock, A_init_lock, A_in_init_config_key, A_load_strings_once, A_load_strings_ret, A_td_tsd, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key,
    A_key_lock, A_tsd_main in Ha;
  cbn in Ha.
Local Ltac solve_in_LIBX_mv :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold_addrs_in Ha;
  split; [| unfold A_mem_inited, A_vdso_func; split; lia];
  left;
  lazymatch type of Ha with
  | ?lo <= a < ?hi => apply (sub_iv_b_sound lo hi LIBX a); [vm_compute; reflexivity | exact Ha]
  end.
Local Ltac frame_conj AG :=
  first [ eapply rw_cells_agree; [exact AG | eassumption | solve_in_LIBX_mv]
        | eapply none_on_agree_mv; [exact AG | eassumption | solve_in_LIBX_mv | | ];
          unfold A_destructor_key, A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
            A_defctx_exmeth_bio, A_tevent_once, A_base_inited, A_stopped, A_in_init_config_key, A_base_once, A_base_ret, A_load_strings_once, A_load_strings_ret,
            A_optsdone_lock, A_init_lock, A_optsdone, A_td_cancelbuf, A_keys, A_key_lock, A_tsd_main, A_err_string_lock, A_int_error_hash, A_err_string_once,
            A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_ret, A_glob_tevent_reg, LIBKEY0; lia
        | assumption ].
Local Ltac frame_group AG :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with |- _ /\ _ => split end; frame_conj AG.

Lemma ERRPH_mid_frame_mv : forall LIB m m' cph eph, ERRPH_mid LIB m cph eph -> magree (lib_addr_mv LIB) m m' -> ERRPH_mid LIB m' cph eph.
Proof.
  intros LIB m m' [|x] [|c] P AG; cbn [ERRPH_mid] in *; [| destruct P| |].
  - eapply ERR_fresh_core_frame_mv; eauto.
  - eapply ERRPH_frame_mv; eauto.
  - eapply ERRPH_frame_mv; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
  Variable H : asr.

  Lemma LIBMID_xagree_any : forall LIB LBx SP X m m' M f' (v' : bool),
    LIBMID LIB m M ->
    xpres H LBx SP X m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) ->
    (forall a, rin_ivs X a -> rin_ivs LIBX a -> (A_mem_inited <= a < A_mem_inited + 1) \/ (A_vdso_func <= a < A_vdso_func + 8)) ->
    (forall a, rin_ivs X a -> ~ (0x571000 <= a < 0x5ea000)) ->
    (forall a, rin_ivs X a -> ~ in_block LIB a) -> (forall a, rin_ivs X a -> ~ in_block_sh LIB a) ->
    (forall a, rin_ivs X a -> ~ in_block_sh (mid_errblocks M) a) ->
    MEMFLAG m' f' -> rw_cells asegs m' A_vdso_func [C8 (wz (if v' then 0 else P_cgt_init))] ->
    (forall a, rin_ivs X a -> ~ in_block (mid_errblocks M) a) ->          (* [comment removed for export] *)
    LIBMID LIB m' (mkMID f' (mid_ctx M) (mid_err M) (mid_E M) v').
  Proof.
    intros until v'. intros LM XP SUBL SUBE XS XR XB XBS XES MF' VD' XEB.
    destruct LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & SH & BL).
    pose proof (magree_of_xpres H _ _ _ _ _ XP) as AG.
    assert (AGmv : magree (lib_addr_mv LIB) m m').
    { eapply magree_mono; [exact AG|]. intros a (HL & NF & NV). split.
      - destruct HL as [HX|[HB|HBS]].
        + right; left. pose proof (alo_libx_proof a HX) as W. unfold alibx_ok, aimg_client in *. lia.
        + right; right; left. destruct HB as (b & Hb & R). exists b. split; [apply SUBL; exact Hb| exact R].
        + right; right; right; left. destruct HBS as (b & Hb & R). exists b. split; [apply SUBL; exact Hb| exact R].
      - intros K. destruct HL as [HX|[HB|HBS]]; [destruct (XS a K HX); tauto| exact (XB a K HB)| exact (XBS a K HBS)]. }
    assert (AGrel : forall A cs (P : Prop), rw_cells asegs m A cs -> 0x571000 <= A -> A + Z.of_nat (cells_size cs) <= 0x5ea000 -> rw_cells asegs m' A cs).
    { intros A cs _ RC B1 B2. eapply rw_cells_agree; [exact AG| exact RC|]. intros a Ha. unfold in_range in Ha.
      split; [right; left; unfold aimg_client; lia| intros K; exact (XR a K ltac:(lia))]. }
    unfold mid_errblocks in *. remember (mid_err M) as eph eqn:EE. remember (mid_ctx M) as cph eqn:EC.
    unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso].
    split. { unfold IMPL_mem in *. frame_group AGmv. }
    split; [exact MF'|].
    split. { eapply CTXPH_frame_mv; [exact CP| exact AGmv]. }
    split. { eapply ERRPH_mid_frame_mv; [exact EPm| exact AGmv]. }
    split. { destruct eph as [|c]; cbn [ERRX] in *; [exact EX|].
             pose proof (ERRPH_mid_chain _ _ _ _ EPm) as CH. pose proof CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
             eapply ERRXR_agreeR; [exact AG| | | | exact EX].
             - intros a Ha. unfold in_range in Ha. assert (HB : in_block LIB a) by (exists (ec_es c); split; [exact I5| rewrite Z5; lia]).
               split; [right; right; left; destruct HB as (b & Hb & R); exists b; split; [apply SUBL; exact Hb| exact R]| intros K; exact (XB a K HB)].
             - intros a Ha. split; [| intros K; exact (XES a K Ha)].
               right; right; right; left. destruct Ha as (b & Hb & R). exists b. split; [apply SUBE; exact Hb| exact R].
             - intros a Ha. split; [| intros K; exact (XEB a K Ha)].
               right; right; left. destruct Ha as (b & Hb & R). exists b. split; [apply SUBE; exact Hb| exact R]. }
    split; [exact VD'|].
    split. { eapply none_agree; [exact AGmv| unfold A_global_cleanup; lia| | exact CL].
             split; [| unfold A_global_cleanup, A_mem_inited, A_vdso_func; split; lia].
             left. apply (sub_iv_b_sound A_global_cleanup (A_global_cleanup + 1) LIBX A_global_cleanup); [vm_compute; reflexivity| lia]. }
    split; [exact FIT|].
    split. { unfold GOT_mem in *. eapply (AGrel _ _ True); [exact G1| unfold A_got_CRYPTO_malloc; lia| unfold A_got_CRYPTO_malloc; cbn; lia]. }
    split. { unfold GOT_echfree in *. eapply (AGrel _ _ True); [exact G2| unfold A_got_ossl_echext_free; lia| unfold A_got_ossl_echext_free; cbn; lia]. }
    split. { unfold GOT_x509vpm in *. eapply (AGrel _ _ True); [exact G3| unfold A_got_ASN1_OBJECT_free; lia| unfold A_got_ASN1_OBJECT_free; cbn; lia]. }
    split. { unfold METH_mem in *. eapply (AGrel _ _ True); [exact M1| unfold A_mem_buf_method, O_METH_BREAD; lia| unfold A_mem_buf_method, O_METH_BREAD; cbn; lia]. }
    split. { unfold METH_b64 in *. eapply (AGrel _ _ True); [exact M2| unfold A_b64_method, O_METH_BREAD; lia| unfold A_b64_method, O_METH_BREAD; cbn; lia]. }
    split. { unfold HPKE_tabs, id_rows, HPKE_KEM_IDS, HPKE_KDF_IDS, HPKE_AEAD_IDS, HPKE_KEM_ROW, HPKE_KDF_ROW, HPKE_AEAD_ROW in *.
             repeat match goal with K : _ /\ _ |- _ => destruct K end.
             repeat match goal with |- _ /\ _ => split end; try exact I;
               (eapply (AGrel _ _ True); [eassumption| unfold A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab; lia| unfold A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab; cbn; lia]). }
    split. { unfold relro_lib, arelro_lib in *. intros i Hi.
             destruct (AG i ltac:(lia) ltac:(split; [right; left; unfold aimg_client; lia| intros K; exact (XR i K ltac:(lia))])) as [E _].
             rewrite E. apply RL. exact Hi. }
    split. { destruct eph as [|c]; cbn [errph_shad] in *; [exact I|].
             pose proof (ERRPH_mid_chain _ _ _ _ EPm) as CH.
             eapply lib_shad_agreeR; [exact AG| | exact SH]. intros a (b & Hb & R).
             assert (HBS : in_block_sh LIB a) by (exists b; split; [eapply chain_blocks_in; [exact CH| exact Hb]| exact R]).
             split; [| intros K; exact (XBS a K HBS)].
             right; right; right; left. destruct HBS as (b' & Hb' & R'). exists b'. split; [apply SUBL; exact Hb'| exact R']. }
    exact BL.
  Qed.

  (* [comment removed for export] *)
  Lemma LIBMID_xpres0_any : forall LIB LBx SP m m' M,
    LIBMID LIB m M -> xpres H LBx SP [] m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) -> LIBMID LIB m' M.
  Proof.
    intros LIB LBx SP m m' M LM XP SUBL SUBE. pose proof LM as (_ & MF & _ & _ & _ & VD & _).
    pose proof (magree_of_xpres H _ _ _ _ _ XP) as AG.
    assert (R1 : forall a, rin_ivs LIBX a -> xR H LBx SP [] a).
    { intros a HX. split; [| intros K; exact K]. right; left. pose proof (alo_libx_proof a HX) as W. unfold alibx_ok, aimg_client in *. lia. }
    pose proof (LIBMID_xagree_any LIB LBx SP [] m m' M (mid_flag M) (mid_vdso M) LM XP SUBL SUBE
                  ltac:(intros a K; destruct K) ltac:(intros a K; destruct K) ltac:(intros a K; destruct K) ltac:(intros a K; destruct K) ltac:(intros a K; destruct K)) as K.
    destruct M as [f c e E v]; cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. apply K.
    - destruct MF as (fb & MF1 & MF2). exists fb. split; [| exact MF2].
      eapply rw_cells_agree; [exact AG| exact MF1|]. intros a Ha. apply R1. unfold_addrs_in Ha.
      apply (sub_iv_b_sound A_mem_inited (A_mem_inited + 1) LIBX a); [vm_compute; reflexivity| unfold A_mem_inited; lia].
    - eapply rw_cells_agree; [exact AG| exact VD|]. intros a Ha. apply R1. unfold_addrs_in Ha.
      apply (sub_iv_b_sound A_vdso_func (A_vdso_func + 8) LIBX a); [vm_compute; reflexivity| unfold A_vdso_func; lia].
    - intros a K0; destruct K0.
  Qed.

  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Lemma LIBMID_mfX_any : forall s m0 LIB LBx SP X m m' M,
    as_RHEAP H s LBx m0 ->
    LIBMID LIB m M -> xpres H LBx SP (memflag_foot ++ X) m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) ->
    (forall a, rin_ivs X a -> ~ rin_ivs LIBX a) -> (forall a, rin_ivs X a -> ~ (0x571000 <= a < 0x5ea000)) ->
    (forall a, rin_ivs X a -> ~ in_block LIB a) -> (forall a, rin_ivs X a -> ~ in_block_sh LIB a) ->
    (forall a, rin_ivs X a -> ~ in_block_sh (mid_errblocks M) a) ->
    MEMFLAG m' 1 ->
    (forall a, rin_ivs X a -> ~ in_block (mid_errblocks M) a) ->          (* [comment removed for export] *)
    LIBMID LIB m' (mkMID 1 (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M)).
  Proof.
    intros s m0 LIB LBx SP X m m' M HP LM XP SUBL SUBE X1 X2 X3 X4 X5 MF' X6. pose proof LM as (_ & _ & _ & _ & _ & VD & _).
    pose proof (magree_of_xpres H _ _ _ _ _ XP) as AG. acb.
    assert (MFL : forall a, rin_ivs memflag_foot a -> A_mem_inited <= a < A_mem_inited + 1) by (intros a Ha; unfold memflag_foot in Ha; cbn in Ha; lia).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    eapply LIBMID_xagree_any; [exact LM| exact XP| exact SUBL| exact SUBE| | | | | | exact MF'| |].
    - intros a K HX. apply rin_ivs_app in K. destruct K as [K|K]; [left; exact (MFL a K)| destruct (X1 a K HX)].
    - intros a K R. apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (MFL a K); unfold A_mem_inited in *; lia| exact (X2 a K R)].
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X3 a K HB)].
      pose proof (in_block_where H HH _ _ _ _ _ HP SUBL HB). pose proof (MFL a K). unfold A_mem_inited, AIMG_TOP in *. lia.
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X4 a K HB)].
      pose proof (in_block_sh_where H HH _ _ _ _ _ HP SUBL HB). pose proof (MFL a K). unfold A_mem_inited, AIMG_TOP in *. lia.
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X5 a K HB)].
      pose proof (in_block_sh_where H HH _ _ _ _ _ HP SUBE HB). pose proof (MFL a K). unfold A_mem_inited, AIMG_TOP in *. lia.
    - eapply rw_cells_agree; [exact AG| exact VD|]. intros a Ha. unfold_addrs_in Ha. split.
      + right; left. unfold aimg_client. lia.
      + intros K. apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (MFL a K); unfold A_mem_inited in *; lia|].
        apply (X1 a K). apply (sub_iv_b_sound A_vdso_func (A_vdso_func + 8) LIBX a); [vm_compute; reflexivity| unfold A_vdso_func; lia].
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X6 a K HB)].
      pose proof (in_block_where H HH _ _ _ _ _ HP SUBE HB). pose proof (MFL a K). unfold A_mem_inited, AIMG_TOP in *. lia.
  Qed.
  Lemma LIBMID_mf_any : forall s m0 LIB LBx SP m m' M,
    as_RHEAP H s LBx m0 ->
    LIBMID LIB m M -> xpres H LBx SP memflag_foot m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) -> MEMFLAG m' 1 ->
    LIBMID LIB m' (mkMID 1 (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M)).
  Proof.
    intros s m0 LIB LBx SP m m' M HP LM XP SUBL SUBE MF'.
    apply (LIBMID_mfX_any s m0 LIB LBx SP [] m m' M HP LM).
    - eapply xpres_X_mono; [exact XP|]. intros a K. apply rin_ivs_app. left. exact K.
    - exact SUBL.
    - exact SUBE.
    - intros a K; destruct K.
    - intros a K; destruct K.
    - intros a K; destruct K.
    - intros a K; destruct K.
    - intros a K; destruct K.
    - exact MF'.
    - intros a K; destruct K.
  Qed.
  (* [comment removed for export] *)
  Lemma LIBMID_mf_xs_any : forall s m0 LIB LBx SP XS LF m m' M,
    as_RHEAP H s LBx m0 -> as_RFS H LF m -> Forall (fs_scratch H LF) XS ->
    LIBMID LIB m M -> xpres H LBx SP (memflag_foot ++ XS) m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) -> MEMFLAG m' 1 ->
    LIBMID LIB m' (mkMID 1 (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M)).
  Proof.
    intros s m0 LIB LBx SP XS LF m m' M HP RF SCR LM XP SUBL SUBE MF'. acb.
    assert (XSlo : forall a, rin_ivs XS a -> AIMG_TOP <= a).
    { intros a K. destruct (rin_ivs_In _ _ K) as (iv & I & R). pose proof (fs_scratch_lo H HH LF m iv RF (proj1 (Forall_forall _ _) SCR iv I)). lia. }
    assert (XSoff : forall L a, (forall b, In b L -> In b LBx) -> rin_ivs XS a -> ~ in_block L a /\ ~ in_block_sh L a).
    { intros L a SUB K. destruct (rin_ivs_In _ _ K) as (iv & I & R).
      eapply fs_scratch_off_block; [exact HH| exact HP| exact SUB| exact RF| exact (proj1 (Forall_forall _ _) SCR iv I)| exact R]. }
    eapply (LIBMID_mfX_any s m0 LIB LBx SP XS); [exact HP| exact LM| exact XP| exact SUBL| exact SUBE| | | | | | exact MF'|].
    - intros a K HX. pose proof (XSlo a K). pose proof (LIBX_below a HX). lia.
    - intros a K R. pose proof (XSlo a K). unfold AIMG_TOP in *. lia.
    - intros a K HB. exact (proj1 (XSoff LIB a SUBL K) HB).
    - intros a K HB. exact (proj2 (XSoff LIB a SUBL K) HB).
    - intros a K HB. exact (proj2 (XSoff _ a SUBE K) HB).
    - intros a K HB. exact (proj1 (XSoff _ a SUBE K) HB).
  Qed.

  (* [comment removed for export] *)
  Lemma LIBMID_stageA : forall s m0 LIB LBx Lnew LA SP XS LF m m' f E v x,
    as_RHEAP H s LBx m0 -> as_RFS H LF m -> Forall (fs_scratch H LF) XS ->
    LIBMID LIB m (mkMID f CtxFresh ErrFresh E v) ->
    xpres H LBx SP (memflag_foot ++ (CTX_X ++ AERRNO_X) ++ XS) m m' ->
    CTXPH Lnew m' (CtxReady x) -> ctxph_delta CtxFresh LA x -> CTX_keys m' -> MEMFLAG m' 1 ->
    LIBMID (LA ++ LIB) m' (mkMID 1 (CtxReady x) ErrFresh E v).
  Proof.
    intros until x. intros HP RF SCR LM XP CP D KE MF'. acb.
    destruct LM as (IM & MF & _ & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & SH & BL).
    cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid ERRX errph_shad errph_below] in *.
    pose proof (magree_of_xpres H _ _ _ _ _ XP) as AG.
    assert (XSlo : forall a, rin_ivs XS a -> AIMG_TOP <= a).
    { intros a K. destruct (rin_ivs_In _ _ K) as (iv & I & R). pose proof (fs_scratch_lo H HH LF m iv RF (proj1 (Forall_forall _ _) SCR iv I)). lia. }
    (* [comment removed for export] *)
    assert (STAT : forall a, 0x571000 <= a < 0x5ea848 \/ 0x5ed1a0 <= a < 0x6a7220 \/ 0xbccf50 <= a < 0xc03570 ->
                   ~ (A_mem_inited <= a < A_mem_inited + 1) -> ~ rin_ivs (CTX_X ++ AERRNO_X) a -> xR H LBx SP (memflag_foot ++ (CTX_X ++ AERRNO_X) ++ XS) a).
    { intros a Ha Hf Hc. split; [right; left; unfold aimg_client; lia|].
      intros K. apply rin_ivs_app in K. destruct K as [K|K]; [unfold memflag_foot in K; cbn [rin_ivs fst snd] in K; lia|].
      apply rin_ivs_app in K. destruct K as [K|K]; [exact (Hc K)|]. pose proof (XSlo a K). unfold AIMG_TOP in *. lia. }
    (* [comment removed for export] *)
    assert (CTXd : forall a, rin_ivs (CTX_X ++ AERRNO_X) a ->
                A_destructor_key <= a < A_destructor_key + 8 \/ A_defctx_inited <= a < A_defctx_inited + 1 \/ A_defctx <= a < A_defctx + 328
             \/ A_defctx_tlkey <= a < A_defctx_tlkey + 4 \/ A_defctx_tlkey_once <= a < A_defctx_tlkey_once + 4 \/ A_defctx_tlkey_ret <= a < A_defctx_tlkey_ret + 4
             \/ A_defctx_once <= a < A_defctx_once + 4 \/ A_defctx_once_ret <= a < A_defctx_once_ret + 4
             \/ A_base_inited <= a < A_base_inited + 1 \/ A_in_init_config_key <= a < A_in_init_config_key + 4
             \/ A_base_once <= a < A_base_once + 4 \/ A_base_ret <= a < A_base_ret + 4
             \/ A_optsdone_lock <= a < A_optsdone_lock + 8 \/ A_init_lock <= a < A_init_lock + 8
             \/ A_td_cancelbuf <= a < A_td_cancelbuf + 8 \/ A_keys + 8 <= a < A_keys + 32 \/ A_next_key <= a < A_key_lock + 8
             \/ ATP - 164 <= a < ATP - 164 + 4).
    { intros a K. unfold CTX_X, AERRNO_X in K. cbn [rin_ivs fst snd app] in K. tauto. }
    Local Ltac statR STAT CTXd :=
      let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold_addrs_in Ha; apply STAT;
      [ unfold A_mem_inited; lia
      | unfold A_mem_inited; lia
      | let K := fresh "K" in intros K; apply CTXd in K; revert K;
        unfold A_destructor_key, A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
          A_base_inited, A_in_init_config_key, A_base_once, A_base_ret, A_optsdone_lock, A_init_lock, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, ATP; lia ].
    cbn [ctxph_delta] in D. destruct D as (_ & _ & XIN & (po & pi & OIN & IIN)).
    cbn [CTXPH] in CP. destruct CP as [CS EXL]. destruct EXL as [(_ & Z1 & R1 & MU1) _].
    unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid ERRPH CTXPH ERRX errph_shad errph_below].
    split. { unfold IMPL_mem in *. repeat match goal with K : _ /\ _ |- _ => destruct K end. repeat match goal with |- _ /\ _ => split end;
             (eapply rw_cells_agree; [exact AG| eassumption| statR STAT CTXd]). }
    split; [exact MF'|].
    split. { split; [exact CS|]. split; [| exists po, pi; split; apply in_or_app; left; assumption].
             split; [apply in_or_app; left; exact XIN|]. split; [exact Z1|]. split; [exact R1| exact MU1]. }
    split. { split; [| exact KE]. unfold ERR_fresh_core in *. repeat match goal with K : _ /\ _ |- _ => destruct K end.
             repeat match goal with |- _ /\ _ => split end;
             (eapply none_on_agree_mv; [exact AG| eassumption| statR STAT CTXd| |];
              unfold A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
                A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_keys, A_tsd_main, LIBKEY0; lia). }
    split; [exact EX|].
    split. { eapply rw_cells_agree; [exact AG| exact VD| statR STAT CTXd]. }
    split. { eapply none_agree; [exact AG| unfold A_global_cleanup; lia| | exact CL].
             apply STAT; [unfold A_global_cleanup; lia| unfold A_global_cleanup, A_mem_inited; lia|].
             intros K. apply CTXd in K. revert K.
             unfold A_global_cleanup, A_destructor_key, A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
               A_base_inited, A_in_init_config_key, A_base_once, A_base_ret, A_optsdone_lock, A_init_lock, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, ATP; lia. }
    split; [exact FIT|].
    assert (AGrel : forall A cs (P : Prop), rw_cells asegs m A cs -> 0x571000 <= A -> A + Z.of_nat (cells_size cs) <= 0x5ea000 -> rw_cells asegs m' A cs).
    { intros A cs _ RC B1 B2. eapply rw_cells_agree; [exact AG| exact RC|]. intros a Ha. unfold in_range in Ha.
      apply STAT; [lia| unfold A_mem_inited; lia|]. intros K. apply CTXd in K. revert K.
      unfold A_destructor_key, A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
        A_base_inited, A_in_init_config_key, A_base_once, A_base_ret, A_optsdone_lock, A_init_lock, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, ATP; lia. }
    split. { unfold GOT_mem in *. eapply (AGrel _ _ True); [exact G1| unfold A_got_CRYPTO_malloc; lia| unfold A_got_CRYPTO_malloc; cbn; lia]. }
    split. { unfold GOT_echfree in *. eapply (AGrel _ _ True); [exact G2| unfold A_got_ossl_echext_free; lia| unfold A_got_ossl_echext_free; cbn; lia]. }
    split. { unfold GOT_x509vpm in *. eapply (AGrel _ _ True); [exact G3| unfold A_got_ASN1_OBJECT_free; lia| unfold A_got_ASN1_OBJECT_free; cbn; lia]. }
    split. { unfold METH_mem in *. eapply (AGrel _ _ True); [exact M1| unfold A_mem_buf_method, O_METH_BREAD; lia| unfold A_mem_buf_method, O_METH_BREAD; cbn; lia]. }
    split. { unfold METH_b64 in *. eapply (AGrel _ _ True); [exact M2| unfold A_b64_method, O_METH_BREAD; lia| unfold A_b64_method, O_METH_BREAD; cbn; lia]. }
    split. { unfold HPKE_tabs, id_rows, HPKE_KEM_IDS, HPKE_KDF_IDS, HPKE_AEAD_IDS, HPKE_KEM_ROW, HPKE_KDF_ROW, HPKE_AEAD_ROW in *.
             repeat match goal with K : _ /\ _ |- _ => destruct K end.
             repeat match goal with |- _ /\ _ => split end; try exact I;
               (eapply (AGrel _ _ True); [eassumption| unfold A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab; lia| unfold A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab; cbn; lia]). }
    split. { unfold relro_lib, arelro_lib in *. intros i Hi.
             assert (Xi : xR H LBx SP (memflag_foot ++ (CTX_X ++ AERRNO_X) ++ XS) i).
             { apply STAT; [lia| unfold A_mem_inited; lia|]. intros K. apply CTXd in K. revert K.
               unfold A_destructor_key, A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
                 A_base_inited, A_in_init_config_key, A_base_once, A_base_ret, A_optsdone_lock, A_init_lock, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, ATP; lia. }
             destruct (AG i ltac:(lia) Xi) as [E' _]. rewrite E'. apply RL. exact Hi. }
    split; [exact I| exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma LIBMID_newmembuf : forall s m0 LIB LBx Lnew LA SP XS LF m m' M x,
    as_RHEAP H s LBx m0 -> as_RFS H LF m -> Forall (fs_scratch H LF) XS ->
    LIBMID LIB m M ->
    xpres H LBx SP (memflag_foot ++ ctxph_foot (mid_ctx M) ++ XS) m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) ->
    CTXPH Lnew m' (CtxReady x) -> ctxph_delta (mid_ctx M) LA x -> (mid_ctx M = CtxFresh -> CTX_keys m') -> MEMFLAG m' 1 ->
    LIBMID (LA ++ LIB) m' (mkMID 1 (CtxReady x) (mid_err M) (mid_E M) (mid_vdso M)).
  Proof.
    intros until x. intros HP RF SCR LM XP SUBL SUBE CP D KE MF'.
    destruct M as [f [|b] eph E v]; cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ctxph_foot ctxph_delta mid_errblocks] in *.
    - assert (EF : eph = ErrFresh) by (destruct eph as [|c]; [reflexivity| destruct LM as (_ & _ & _ & F & _); destruct F]).
      subst eph. eapply LIBMID_stageA; [exact HP| exact RF| exact SCR| exact LM| exact XP| exact CP| exact D| exact (KE eq_refl)| exact MF'].
    - destruct D as [-> ->]. cbn [app].
      pose proof (LIBMID_mf_xs_any s m0 LIB LBx SP XS LF m m' (mkMID f (CtxReady b) eph E v) HP RF SCR LM XP SUBL SUBE MF') as K.
      cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in K.
      exact K.
  Qed.
End W.
End HCW.
