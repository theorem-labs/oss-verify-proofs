(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio Malloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanDepot AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_base A_alloc_iface A_iface A_iface5x AI_shadow AI_iface AI_lowshadow AI_gtrans AI_globals2 AYajlRep AYajl_iface
  AF_fakestack_rep AF_unwind AF_statics AX_file AX_Exit
  AI_adapt AI_adapt2 AX_adapt AI_adapt_fwrite AI_adapt_oc AI_adapt_printf
  A_live A_policy5 A_budget5 A_slack5 A_bundle A_benv5 A_bframe A_bframe2 A_bframe3 A_bframe4 A_init5 A_instD5 A_instY5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Section Inst5.
Variables (E0 : aenv) (FSB0 : Z) (PL0 : fs_plumb) (HR0 : list (Z * Z)) (L0 RES0 : list (word * word)) (EB0 : Z).
(* [comment removed for export] *)
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis HS_tot : gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat.

(* [comment removed for export] *)
Definition SR : stdout_st -> mem -> Prop := stdio_rep.
Definition RT : aenv -> mem -> Prop := rt_misc5 FSB0 PL0.
Definition AHKc : aps -> list ablock -> list fblock -> mem -> Model -> Prop := AHK SR RT E0 FSB0 HR0 L0 RES0 EB0.
Definition aSc : aps -> word -> Prop := A_bundle.aS E0 FSB0 HR0.
Definition aNc : aps -> nat := A_bundle.aN E0 FSB0 HR0.
Definition aEBc : aps -> Z := A_bundle.aEB EB0.

Lemma aalloc_same_refl : forall s, aalloc_same s s.
Proof. intros s. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Ltac provide :=
  first [ eassumption
        | exact ENV0 | exact PL0OK | exact HR0_ok | exact EB0_ok | exact ENV_depot | exact HS_tot
        | exact (rt_misc5_agree E0 FSB0 PL0) | exact (rt_fpc_where E0 FSB0 PL0) | exact (rt_fpc_where2 E0 FSB0 PL0)
        | exact (rt_misc5_fsenv E0 FSB0 PL0) | exact (rt_misc5_ams E0 FSB0 PL0)
        | exact stdio_rep_agree | exact so_fpc_where | exact so_fpc_where2 | exact stdio_rep_buf
        | exact aalloc_same_refl
        | match goal with |- ?g => idtac "PROVIDE-FAIL" g; fail end ].
Ltac inst lem := hnf; intros; eapply lem; provide.

(* [comment removed for export] *)
Lemma D_kip : AHK_kip_stmt ACONSTS aps AHKc aSc aNc aEBc.
Proof. inst (AHK_kip SR RT E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma D_mem_inv : AHK_mem_inv_stmt asegs aps AHKc.
Proof. inst (AHK_mem_inv SR RT E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma D_perm : AHK_perm_stmt aps AHKc.
Proof. hnf. intros s LB LB' LF m mo H P. eapply (AHK_perm SR RT E0 FSB0 HR0 L0 RES0 EB0); [exact H| exact P| reflexivity]. Qed.
Lemma D_frame : AHK_frame_stmt asegs ACONSTS aps AHKc.
Proof. inst (AHK_frame_drv SR RT E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma D_vmsame : AHK_vmsame_stmt aps AHKc.
Proof. inst (AHK_vmsame_fs SR RT E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma D_blocks : AHK_blocks_stmt ACONSTS aps AHKc.
Proof. inst (AHK_blocks SR RT E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma D_so : AHK_so_stmt aps AHKc aps_so.
Proof. hnf. intros. unfold STDOUT_BUFSIZ, zlength. eapply (AHK_so SR RT E0 FSB0 HR0 L0 RES0 EB0); provide. Qed.
Lemma D_charge : acharge_bound_stmt acharge arefund.
Proof.
  hnf. intros n. split; [apply arefund_nonneg|]. unfold acharge, arefund, kCmPrim.
  destruct (from_primary n); [lia|]. destruct (map_size n <? kBigMapSize); lia.
Qed.
Lemma D_asame_refl : aalloc_same_refl_stmt aps aalloc_same.
Proof. exact aalloc_same_refl. Qed.

(* [comment removed for export] *)
Lemma D_icp_globals : AHK_icp_globals_stmt asegs aps AHKc.
Proof. inst (AHK_icp_globals SR RT E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma D_icp_block_shadow : AHK_icp_block_shadow_stmt asegs aps AHKc.
Proof. inst (AHK_icp_block_shadow SR RT E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma D_icp_regions : AHK_icp_regions_stmt aps AHKc aSc.
Proof. inst (AHK_icp_regions SR RT E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma D_icp_stack_shadow : AHK_icp_stack_shadow_stmt asegs aps AHKc aSc.
Proof. inst (AHK_icp_stack_shadow SR RT E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma D_icp_stack_shadow0 : AI_adapt_printf.AHK_icp_stack_shadow0_stmt aps AHKc aSc.
Proof. inst (AHK_icp_stack_shadow0 SR RT E0 FSB0 HR0 L0 RES0 EB0). Qed.
Lemma D_icp_musl_statics_shadow : AHK_icp_musl_statics_shadow_stmt asegs aps AHKc aSc.
Proof. inst (AHK_icp_musl_statics_shadow SR RT E0 FSB0 HR0 L0 RES0 EB0). Qed.

Lemma AHKc_env : forall s LB LF m mo, AHKc s LB LF m mo -> aps_env s = E0 /\ aps_fsbase s = FSB0.
Proof. intros s LB LF m mo H. exact (AHK_env SR RT E0 FSB0 HR0 L0 RES0 EB0 s LB LF m mo H). Qed.
Lemma AHKc_rt : forall s LB LF m mo, AHKc s LB LF m mo -> rt_misc5 FSB0 PL0 E0 m.
Proof.
  intros s LB LF m mo H. pose proof (AHKc_env _ _ _ _ _ H) as [E1 _].
  unfold AHKc in H. ahk_open H. unfold RT in Hrt. rewrite E1 in Hrt. exact Hrt.
Qed.
Lemma AHKc_low : forall s LB LF m mo, AHKc s LB LF m mo -> low_shadow_ok m.
Proof. intros s LB LF m mo H. unfold AHKc in H. ahk_open H. exact Hlow. Qed.
Lemma AHKc_so : forall s LB LF m mo, AHKc s LB LF m mo -> stdio_rep (aps_so s) m.
Proof. intros s LB LF m mo H. unfold AHKc in H. ahk_open H. exact Hso. Qed.

Lemma D_icp_globals2 : AHK_icp_globals2_stmt aps AHKc.
Proof. hnf. intros s LB LF m mo H. exact (rt_misc5_icp2 E0 FSB0 PL0 m (AHKc_rt _ _ _ _ _ H)). Qed.
Lemma D_icp_errno : AHK_icp_errno_stmt aps AHKc.
Proof.
  hnf. intros s LB LF m mo H. split.
  - exact (errno_cell m).
  - intros m' W MU WM MI FW. eapply (AHK_frame_drv_errno SR RT E0 FSB0 HR0 L0 RES0 EB0); provide.
Qed.
Lemma D_icp_exit : AHK_icp_exit_stmt aps AHKc aps_so aSc.
Proof.
  hnf. intros s LB LF m mo H. pose proof (rt_misc5_exit E0 FSB0 PL0 m (AHKc_rt _ _ _ _ _ H)) as EX.
  split; [exact EX|]. split; [exact (AHKc_so _ _ _ _ _ H)|]. split; [exact (AHKc_low _ _ _ _ _ H)|].
  pose proof (AHK_icp_regions SR RT E0 FSB0 HR0 L0 RES0 EB0 ENV0 s LB LF m mo H) as (R1 & R2 & _).
  split; [| split; [| split; [exact R1| exact R2]]];
    (eapply (AHK_low_pages_budgeted SR RT E0 FSB0 HR0 L0 RES0 EB0); [exact H| lia| lia]).
Qed.
Lemma D_icp_lowpages : AHK_icp_lowpages_stmt aps AHKc aSc.
Proof. hnf. intros s LB LF m mo lo hi H H1 H2. eapply (AHK_low_pages_budgeted SR RT E0 FSB0 HR0 L0 RES0 EB0); [exact H| lia| lia]. Qed.
Lemma D_icp_stdio_upd : AHK_icp_stdio_upd_stmt aps AHKc aps_so aSc aNc aEBc aalloc_same.
Proof.
  hnf. intros s LB LF m mo m' W so' guard cdt thr sec tm1 H MU WM MI FW ST BUF.
  exists (aps_set_so so' s). split; [| split; [reflexivity| split; [repeat split; reflexivity| repeat split; reflexivity]]].
  eapply (AHK_stdio_write SR RT E0 FSB0 HR0 L0 RES0 EB0); try provide.
  - apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as [X|X]; [left| right].
    + unfold aclient_write_ok in X. cbn [c_initialized ACONSTS] in X. unfold cl_write_ok.
      destruct X as [X|[X|[X|X]]]; [left; exact X| right; left; exact X| do 4 right; left; cbn [c_initialized ACONSTS]; lia
                                   | do 7 right; cbn [c_initialized ACONSTS]; exact X].
    + unfold stdio_ivs in X. unfold stdio_w_ivs. cbn [c_stderr_F c_stdout_F c_stdout_buf ACONSTS]. cbn in X. exact X.
  - unfold SR, stdio_rep. exists guard, cdt, thr, sec, tm1. exact ST.
Qed.

(* [comment removed for export] *)
Lemma D_memcpy : amemcpy_icp_stmt asegs ACONSTS aps AHKc aps_so aalloc_same.
Proof.
  exact (amemcpy_icp_ok aps AHKc aps_so aSc aNc aEBc aalloc_same
           D_kip D_mem_inv D_blocks D_frame D_icp_globals D_icp_block_shadow D_icp_regions aalloc_same_refl).
Qed.
Lemma D_memcpy_s : amemcpy_static_rz_stmt asegs ACONSTS aps AHKc aps_so aalloc_same.
Proof.
  exact (amemcpy_static_ok aps AHKc aps_so aSc aNc aEBc aalloc_same
           D_kip D_mem_inv D_blocks D_frame D_icp_globals D_icp_block_shadow D_icp_regions aalloc_same_refl D_icp_musl_statics_shadow).
Qed.
Lemma D_read : aread_rz_stmt asegs ACONSTS aps AHKc aps_so aalloc_same.
Proof.
  exact (aread_ok aps AHKc aps_so aSc aNc aEBc aalloc_same
           D_kip D_mem_inv D_blocks D_vmsame D_icp_globals D_icp_globals2 D_icp_errno D_icp_block_shadow D_icp_regions aalloc_same_refl).
Qed.
(* [comment removed for export] *)
Lemma D_frame_rstage : AHK_frame_rstage_stmt asegs ACONSTS aps AHKc.
Proof. inst (AHK_frame_rstage SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0). Qed.
Lemma D_read_s : aread_static_rz_stmt asegs ACONSTS aps AHKc aps_so aalloc_same.
Proof.
  exact (aread_static_ok aps AHKc aps_so aSc aNc aEBc aalloc_same
           D_kip D_mem_inv D_blocks D_vmsame D_icp_globals D_icp_globals2 D_icp_errno aalloc_same_refl
           D_icp_musl_statics_shadow D_frame_rstage).
Qed.
Lemma D_exit : aexit_atx_stmt asegs ACONSTS aps AHKc aps_so.
Proof. exact (aexit_ok aps AHKc aps_so aSc aNc aEBc D_kip D_mem_inv D_icp_exit). Qed.
Lemma D_libc_head : AHK_libc_head_stmt asegs aps AHKc.
Proof. exact (alibc_head_ok aps AHKc aps_so aSc D_icp_exit). Qed.
Lemma D_fwrite : afwrite_diag_stmt asegs ACONSTS aps AHKc aps_so aalloc_same.
Proof.
  exact (afwrite_diag_rz aps AHKc aps_so aSc aNc aEBc aalloc_same
           D_kip D_mem_inv D_so D_icp_globals D_icp_globals2 D_icp_exit D_icp_stdio_upd D_icp_lowpages).
Qed.
Lemma D_open : aopen_stmt asegs ACONSTS aps AHKc aps_so aalloc_same.
Proof.
  hnf. intros. eapply (aopen_rz aps AHKc aps_so aSc aNc aEBc aalloc_same);
    first [ exact D_kip | exact D_mem_inv | exact D_vmsame | exact D_icp_errno | exact D_icp_exit | exact aalloc_same_refl | eassumption ].
Qed.
Lemma D_close : aclose_stmt asegs ACONSTS aps AHKc aps_so aalloc_same.
Proof.
  hnf. intros. eapply (aclose_rz aps AHKc aps_so aSc aNc aEBc aalloc_same);
    first [ exact D_kip | exact D_mem_inv | exact D_vmsame | exact D_icp_errno | exact D_icp_exit | exact aalloc_same_refl | eassumption ].
Qed.

(* [comment removed for export] *)
Lemma D_uanchor : uanchor_triv_stmt (AF_unwind.uanchor asegs) AF_unwind.URA.
Proof. exact (AF_unwind.uanchor_triv asegs). Qed.
Lemma D_uanchor_step : uanchor_step_stmt asegs (AF_unwind.uanchor asegs) AF_unwind.URA.
Proof. exact (AF_unwind.uanchor_step asegs). Qed.
Lemma D_uanchor_frame : uanchor_frame_stmt (AF_unwind.uanchor asegs).
Proof. exact (AF_unwind.uanchor_frame asegs). Qed.

(* [comment removed for export] *)
Lemma D_hd_malloc : ahead_malloc_stmt aps (amalloc_rel E0) AHEAD.
Proof. exact (ahead_malloc E0). Qed.
Lemma D_hd_free : ahead_free_stmt aps (afree_rel E0) AHEAD.
Proof. exact (ahead_free E0). Qed.
Lemma D_hd_free0 : ahead_free0_stmt aps (afree_rel E0) AHEAD.
Proof. exact (ahead_free0 E0). Qed.
Lemma D_hd_perm : ahead_perm_stmt aps AHEAD.
Proof. exact ahead_perm. Qed.
Lemma D_hd_weaken : ahead_weaken_stmt aps AHEAD.
Proof. exact ahead_weaken. Qed.
Lemma D_hd_yfuzz : ahead_yfuzz_stmt aps ayfuzz_rel AHEAD.
Proof. exact ahead_yfuzz. Qed.
Lemma D_hd_magree : ahead_magree_stmt aps AHEAD.
Proof. exact ahead_magree. Qed.
Lemma D_hd_vmsame : ahead_vmsame_stmt aps AHEAD.
Proof. exact ahead_vmsame. Qed.
Lemma D_hd_aps : ahead_aps_stmt aps aalloc_same AHEAD.
Proof. exact ahead_aps. Qed.
Lemma D_hd_cmalloc : ahead_credit_malloc_stmt aps aps_credit acharge AHEAD.
Proof. exact ahead_credit_malloc. Qed.
Lemma D_hd_cfree : ahead_credit_free_stmt aps aps_credit AHEAD.
Proof. exact ahead_credit_free. Qed.
Lemma D_hd_reserve : ahead_reserve_stmt aps aps_credit AHEAD.
Proof. exact ahead_reserve. Qed.
Lemma D_hd_cyfuzz : ahead_credit_yfuzz_stmt aps aps_credit AHEAD.
Proof. exact ahead_credit_yfuzz. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section DIsec.
#[local] Notation uanchorc := (AF_unwind.uanchor asegs).
Hypothesis W_malloc : amalloc_rz_stmt asegs ACONSTS aps AHKc aps_so (amalloc_rel E0) aps_credit acharge uanchorc.
Hypothesis W_free : afree_rz_stmt asegs ACONSTS aps AHKc aps_so (afree_rel E0) aps_credit arefund uanchorc.
Hypothesis W_realloc : arealloc_rz_stmt asegs ACONSTS aps AHKc aps_so (arealloc_rel E0) aps_credit acharge arefund uanchorc.
Hypothesis W_realloc0 : arealloc_null_rz_stmt asegs ACONSTS aps AHKc aps_so (arealloc_rel E0) aps_credit acharge uanchorc.
(* [comment removed for export] *)
Lemma W_fprintf : afprintf_diag_stmt asegs ACONSTS AFMTS aps AHKc aps_so aalloc_same.
Proof.
  exact (afprintf_diag_proof aps AHKc aps_so aSc aNc aEBc aalloc_same
           D_kip D_mem_inv D_so D_icp_globals D_icp_globals2 D_icp_exit D_icp_stdio_upd D_icp_lowpages D_icp_stack_shadow0).
Qed.
Lemma W_printf : aprintf_rz_stmt asegs ACONSTS AFMTS aps AHKc aps_so aalloc_same.
Proof.
  first [ exact (aprintf_proof aps AHKc aps_so aSc aNc aEBc aalloc_same
                  D_kip D_mem_inv D_icp_globals D_icp_globals2 D_icp_exit D_icp_stdio_upd D_icp_lowpages D_icp_stack_shadow0)
        | exact (aprintf_proof aps AHKc aps_so aSc aNc aEBc aalloc_same
                  D_kip D_mem_inv D_so D_icp_globals D_icp_globals2 D_icp_exit D_icp_stdio_upd D_icp_lowpages D_icp_stack_shadow0) ].
Qed.

(* [comment removed for export] *)
Definition URA5 : list Z := c_uras ACONSTS.
Lemma D_uras5 : forall z, In z (c_uras ACONSTS) -> In z URA5.
Proof. intros z H. exact H. Qed.
Lemma D_uanchor5 : uanchor_triv_stmt uanchorc URA5.
Proof. intros m SP ra s0 H _. apply AF_unwind.ua_stop. left. exact H. Qed.
Lemma D_uanchor_step5 : uanchor_step_stmt asegs uanchorc URA5.
Proof. intros m SP ra s0 ra' s0' _ [H1 H2] RC U. eapply AF_unwind.ua_step; eauto. Qed.

Definition DREC : adrv_params :=
  mkADrvParams aps AHKc aps_so aSc aNc aEBc (amalloc_rel E0) (afree_rel E0) ayfuzz_rel aalloc_same
               (arealloc_rel E0) aps_credit acharge arefund uanchorc URA5 AHEAD.

Lemma D_yfuzz : A_iface.ayfuzz_stmt asegs ACONSTS aps AHKc aps_so ayfuzz_rel aps_credit uanchorc.
Proof.
  exact (W_yfuzz SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK
           (rt_fpc E0 FSB0 PL0) (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where E0 FSB0 PL0) (rt_misc5_fsenv E0 FSB0 PL0) (rt_misc5_icp2 E0 FSB0 PL0)
           so_fpc stdio_rep_agree so_fpc_where
           (amalloc_rel E0) (afree_rel E0) (arealloc_rel E0) W_malloc W_free W_realloc W_realloc0).
Qed.

Theorem DI : a_drv_iface asegs ACONSTS AFMTS DREC.
Proof.
  constructor; cbn [DREC p_APS p_AHK p_SO p_aS p_aN p_aEB p_amalloc_rel p_afree_rel p_ayfuzz_rel p_aalloc_same p_arealloc_rel
                    p_acredit p_acharge p_arefund p_uanchor p_URA p_AHEAD].
  all: first [ exact D_kip | exact D_mem_inv | exact D_perm | exact D_frame | exact D_vmsame | exact D_blocks | exact D_so
             | exact D_charge | exact D_asame_refl | exact D_uras5 | exact D_uanchor5 | exact D_uanchor_step5 | exact D_uanchor_frame
             | exact W_free | exact W_malloc | exact W_realloc | exact W_realloc0
             | exact D_memcpy | exact D_read | exact D_open | exact D_close | exact D_fwrite | exact W_fprintf | exact W_printf
             | exact D_exit | exact D_yfuzz
             | exact D_hd_malloc | exact D_hd_free | exact D_hd_free0 | exact D_hd_perm | exact D_hd_weaken | exact D_hd_yfuzz
             | exact D_hd_magree | exact D_hd_vmsame | exact D_hd_aps | exact D_hd_cmalloc | exact D_hd_cfree | exact D_hd_reserve | exact D_hd_cyfuzz
             | match goal with |- ?g => idtac "DI-FIELD-MISSING" g; fail end ].
Qed.

Theorem DIx5 : a_drv_iface5x asegs ACONSTS DREC.
Proof. constructor; cbn. - exact D_frame_rstage. - exact D_read_s. - exact D_memcpy_s. - exact D_exit. - exact D_libc_head. Qed.
End DIsec.

End Inst5.
End RC__1.
