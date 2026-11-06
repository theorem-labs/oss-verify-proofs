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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA AImages AImageFacts LazyModel NodesA Shadow BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanFakeStack AsanPS AsanKern AsanClient AsanDepot AsanBudget AsanBudget2 AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_alloc_iface B_iface B_live B_policy5 B_budget5 B_slack5 BI_shadow BI_lowshadow BI_gtrans BYajlRep BYajl_iface BF_place BF_fakestack_rep B_bundle B_benv5 B_bframe B_bframe2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanRepFrame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Ltac lia ::= LiaA.liaA.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Lemma img_cells_not_stdio : forall x,
  in_cells icp_globals_cellsL x \/ in_cells ay_statics_cellsL x \/ in_cells ay_cells_cellsL x -> ~ stdio_w x.
Proof.
  intros x H SW.
  assert (R : forall l y, in_cells l y -> Exists (fun c => fst c <= y < fst c + snd c) l).
  { intros l y (c & Hc & Hr). apply Exists_exists. exists c. auto. }
  unfold stdio_w in SW. cbn [c_stderr_F c_stdout_F c_stdout_buf ACONSTS] in SW.
  unfold icp_globals_cellsL, ay_statics_cellsL, ay_cells_cellsL in *.
  unfold A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND,
         A_GOT_HIGHEND, A_HIGHEND, A_INITED, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, AY_CALLBACKS, AY_BUF_ALLOC_ERROR, AY_NOOP_ALLOCS in *.
  destruct H as [H|[H|H]]; apply R in H; repeat (apply Exists_cons in H; destruct H as [H|H]; [cbn in H; lia|]); apply Exists_nil in H; destruct H.
Qed.

Lemma stdio_w_range : forall x, stdio_w x -> 0xa9c68 <= x < 0x602060.
Proof. intros x SW. unfold stdio_w in SW. cbn [c_stderr_F c_stdout_F c_stdout_buf ACONSTS] in SW. lia. Qed.

Lemma stdio_w_ivs_range : forall iv, In iv stdio_w_ivs -> 0xa9c68 <= fst iv /\ snd iv <= 0x602060 /\ (forall x, fst iv <= x < snd iv -> stdio_w x).
Proof.
  intros iv Hiv. split; [| split]; [ | | intros x Hx; exact (stdio_w_In iv x Hiv Hx)];
  unfold stdio_w_ivs in Hiv; cbn [c_stderr_F c_stdout_F c_stdout_buf ACONSTS] in Hiv; destruct Hiv as [<-|[<-|[<-|[]]]]; cbn; lia.
Qed.

Section Bundle.
(* [comment removed for export] *)
Variable StdioRep : stdout_st -> mem -> Prop.
Variable RTMisc : aenv -> mem -> Prop.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
#[local] Notation AHKc := (AHK StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (aS E0 FSB0 HR0).
#[local] Notation aNc := (aN E0 FSB0 HR0).
#[local] Notation aEBc := (aEB EB0).
Variable PL0 : fs_plumb.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Variable rt_fp : Z -> Prop.
Hypothesis RTMisc_agree : forall m m', RTMisc E0 m -> (forall a, rt_fp a -> m' (wa a) = m (wa a)) -> RTMisc E0 m'.
Hypothesis rt_fp_where : forall a, rt_fp a -> (0x10000 <= a < 0x603000 /\ ~ cl_cells a /\ ~ stdio_w a /\ ~ in_cells img_mut a) \/ rt_high2 E0 PL0 a.
Variable so_fp : Z -> Prop.
Hypothesis StdioRep_agree : forall so m m', StdioRep so m -> (forall a, so_fp a -> m' (wa a) = m (wa a)) -> StdioRep so m'.
Hypothesis so_fp_where : forall a, so_fp a -> 0x10000 <= a < 0x603000 /\ ~ cl_cells a /\ ~ in_cells img_mut a.
Ltac clear_frame_kit := clear so_fp_where StdioRep_agree so_fp rt_fp_where RTMisc_agree rt_fp.
Ltac clear_all_hyps := clear_frame_kit; clear PL0OK ENV0.

(* [comment removed for export] *)
#[local] Notation cl_byte_not_fp := (B_bframe2.cl_byte_not_fp StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 ENV0).
#[local] Notation cl_byte_where := (B_bframe2.cl_byte_where StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 PL0 PL0OK).
#[local] Notation rt_high_range := (B_bframe2.rt_high_range E0 PL0 PL0OK).
#[local] Notation RTMisc_frame := (B_bframe2.RTMisc_frame RTMisc E0 PL0 PL0OK rt_fp RTMisc_agree rt_fp_where).
#[local] Notation StdioRep_frame := (B_bframe2.StdioRep_frame StdioRep so_fp StdioRep_agree so_fp_where).
#[local] Notation cl_write_ok_high := (B_bframe2.cl_write_ok_high StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation cl_write_ok_split := (B_bframe2.cl_write_ok_split StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation AK_blocks_sep := (B_bframe2.AK_blocks_sep E0 FSB0 ENV0).
#[local] Notation IMG_IN_of := (B_bframe2.IMG_IN_of E0 FSB0 ENV0).
#[local] Notation lazy_disjoint_high := (B_bframe.lazy_disjoint_high E0 FSB0).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AHK_stdio_write : forall s LB LF m m' mo W so',
  AHKc s LB LF m mo -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => cl_write_ok LB LF iv \/ In iv stdio_w_ivs) W ->
  StdioRep so' m' -> AHKc (aps_set_so so' s) LB LF m' mo.
Proof.
  intros s LB LF m m' mo W so' H MU WM FW SR. pose proof H as H0. ahk_open H. pose proof B_bframe.ceil_range as CR.
  pose proof (fun x CB => cl_byte_where _ _ _ _ _ x H0 CB) as WH.
  pose proof (fun x CB => cl_byte_not_fp _ _ _ _ _ x H0 CB) as NFP.
  pose proof Henv as Henv0. destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & EI1 & EI2).
  (* [comment removed for export] *)
  assert (AG : forall x, 0 <= x < 2^64 -> ~ cl_byte s LB LF x -> ~ stdio_w x -> m' (wa x) = m (wa x)).
  { intros x Hx NCB NSW. destruct (decide (m' (wa x) = m (wa x))) as [E|NE]; [exact E|]. exfalso.
    destruct (munch_changed W m m' x MU Hx NE) as (iv & Hiv & R).
    destruct (proj1 (Forall_forall _ _) FW iv Hiv) as [CW|SW].
    - apply NCB. eapply cl_write_byte; [exact Hfs| exact CW| exact R].
    - apply NSW. eapply stdio_w_In; [exact SW| exact R]. }
  (* [comment removed for export] *)
  assert (AGI : forall a, a < 0x140c80 -> 0x10000 <= a -> ~ stdio_w a -> m' (wa a) = m (wa a)).
  { intros a H1 H2 H3. apply AG; [clear -H1 H2; lia| | exact H3]. intros CB. destruct (WH a CB) as (W1 & _). unfold cl_cells in W1. cbn [c_initialized c_errno ACONSTS] in W1. lia. }
  assert (AGL : forall a, LSLO <= a < LSHI -> m' (wa a) = m (wa a)).
  { intros a Ha. unfold LSLO, LSHI in Ha. apply MU. rewrite wa_unsigned by lia. eapply outside_of_Forall; [exact FW|]. intros iv [CW|SW].
    - pose proof (cl_write_ok_split _ _ _ _ _ iv H0 CW) as X. unfold LSLO, LSHI in X. clear -X Ha. lia.
    - pose proof (stdio_w_ivs_range iv SW) as (X1 & X2 & _). clear -X1 X2 Ha. lia. }
  assert (OUT : forall x, ~ cl_byte s LB LF x -> ~ stdio_w x -> outside W x).
  { intros x NCB NSW. eapply outside_of_Forall; [exact FW|]. intros iv [CW|SW] R.
    - apply NCB. eapply cl_write_byte; [exact Hfs| exact CW| exact R].
    - apply NSW. eapply stdio_w_In; [exact SW| exact R]. }
  unfold AHK. cbn [aps_env aps_alloc aps_fsbase aps_fs aps_so aps_credit aps_set_so].
  split. { (* [comment removed for export] *) eapply (ARep_frame_client bsegs _ _ (DepotFP (aps_env s))); [| exact Hrep| exact WM|].
           - intros a0 mm mm' D W' A'. eapply DepotR_frame; [exact D| exact W'| exact A'].
           - intros x FPx. pose proof Hwf as WF'.
             pose proof (AK_blocks_sep s mo Hwf Hkern Henv0) as BS. pose proof (IMG_IN_of s Henv0) as IMG_IN.
             assert (Hx : 0 <= x < 2^64).
             { pose proof (fp_below_ceiling _ _ [] [] IMG_IN (DepotFP_where (aps_env s)) _ _ WF' BS FPx) as UB.
               destruct (fp_locate _ _ [] [] IMG_IN (DepotFP_where (aps_env s)) _ _ WF' BS FPx) as [(r & Hr & R)|[[R _]|[R _]]].
               - pose proof (IMG_IN r Hr). pose proof (B_bframe.wf_env_img _ (proj1 WF')) as (_ & I2 & _). lia.
               - unfold sh_band, kLowShadowBeg, kShadowBase in R. rewrite kHighShadowBeg_val in R. clear -UB CR R. lia.
               - unfold app_addr in R. rewrite kHighMemBeg_val in R. clear -UB CR R. lia. }
             apply AG; [exact Hx| intros CB; exact (NFP x CB FPx)|].
             intros SW. pose proof (stdio_w_range x SW) as SR'. revert FPx.
             apply (fp_img_free _ _ [] [] IMG_IN (DepotFP_where (aps_env s)) _ _ Hwf BS).
             + unfold in_img. rewrite EI1. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; clear -SR' EI2; lia.
             + intros (r & Hr & R). destruct ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG_CL & _).
               rewrite EE in Hr. exact (proj2 (IMG_CL r x Hr R) SW). }
  split; [exact Hwf|]. split; [exact Hkern|]. split; [exact Hkvm|]. split; [exact Hres|]. split; [exact Hqb|]. split; [exact Hdi|]. split; [exact Hbinv|].
  split; [exact Hbm|].
  split. { (* [comment removed for export] *) eapply FSRep_frame_w; [| exact WM| exact Hfs].
           intros a Ha. pose proof Hfs as (_ & P2 & P3 & _). apply AG.
           - unfold kFsBytes in P3. clear -Ha P2 P3 CR. lia.
           - intros CB. destruct (WH a CB) as (_ & _ & NF & _). exact (NF Ha).
           - intros SW. pose proof (stdio_w_range a SW). clear -Ha P2 H. lia. }
  split. { (* [comment removed for export] *) eapply icp_globals_agree; [exact Hicp|]. intros a Ha.
           pose proof (img_cells_not_cl a (or_introl Ha)). pose proof (img_cells_not_mut a (or_introl Ha)) as [? _].
           apply AGI; [lia| lia| exact (img_cells_not_stdio a (or_introl Ha))]. }
  split. { (* [comment removed for export] *) eapply ay_statics_agree; [exact Hyst|]. intros a Ha.
           pose proof (img_cells_not_cl a (or_intror (or_introl Ha))). pose proof (img_cells_not_mut a (or_intror (or_introl Ha))) as [? _].
           apply AGI; [lia| lia| exact (img_cells_not_stdio a (or_intror (or_introl Ha)))]. }
  split. { (* [comment removed for export] *) eapply low_shadow_agree; [exact Hlow| exact AGL]. }
  rewrite EE in Hrt.
  split. { (* [comment removed for export] *) rewrite EE. eapply RTMisc_frame; [exact Hrt| exact MU| exact WM|]. intros a Ra.
           destruct (rt_fp_where a Ra) as [(R1 & R2 & R3 & R4)|R].
           - apply OUT; [| exact R3]. intros CB. destruct (WH a CB) as (W1 & _). exact (R2 (W1 ltac:(lia))).
           - pose proof (rt_high_range a (rt_high2_high _ _ _ R)) as RR.
             apply OUT; [| intros SW; pose proof (stdio_w_range a SW); clear -RR H; lia].
             intros CB. destruct (WH a CB) as (_ & _ & _ & W4). exact (W4 (rt_high2_high _ _ _ R)). }
  split; [exact SR|].
  split; [exact Hkm|]. split; [exact Hli|]. split; [exact Hbud|].
  split.
  { (* [comment removed for export] *)
    intros w b Hb. pose proof (bvu64 w) as Hw.
    destruct (decide (m' w = m w)) as [E|NE].
    - apply (Hmi w b). rewrite <- E. exact Hb.
    - assert (NO : ~ outside W (bv_unsigned w)) by (intros O; apply NE; apply MU; exact O).
      destruct (not_outside_In W _ NO) as (iv & Hiv & R).
      apply asan_ro_addr_false_data.
      destruct (proj1 (Forall_forall _ _) FW iv Hiv) as [CW|SW].
      + pose proof (cl_write_ok_high _ _ _ _ _ iv H0 CW). lia.
      + pose proof (stdio_w_ivs_range iv SW) as (X1 & _). lia. }
  split; [exact Henv0|].
  (* [comment removed for export] *)
  split; [| split; [exact Hss| exact Hcs]].                    (* [comment removed for export] *)
  eapply ay_cells_agree; [exact Hycl|]. intros a Ha.
  pose proof (img_cells_not_cl a (or_intror (or_intror Ha))). pose proof (img_cells_not_mut a (or_intror (or_intror Ha))) as [? _].
  apply AGI; [lia| lia| exact (img_cells_not_stdio a (or_intror (or_intror Ha)))].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fs_w (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (FSB0 <= fst iv /\ snd iv <= FSB0 + kFsBytes)
  \/ (0x7fff8000 + FSB0 / 8 <= fst iv /\ snd iv <= 0x7fff8000 + (FSB0 + kFsBytes) / 8).

(* [comment removed for export] *)
Lemma lazy_disjoint_resv_range : forall {P D} s mo r0 rl,
  AKern (aps_env s) (aps_alloc s) mo -> AWf (aps_env s) P D (aps_alloc s) -> ENVOK E0 FSB0 s ->
  resv_range_ok E0 r0 rl -> 0 <= rl -> lazy_disjoint mo r0 (r0 + rl).
Proof.
  clear_all_hyps.
  intros P D s mo r0 rl K WF Henv RR Hl.
  pose proof Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  pose proof (resv_range_num _ r0 rl RR Hl) as (N1 & N2 & N3 & N4).
  destruct RR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  apply (B_bframe.lazy_disjoint_gen E0 FSB0 s mo _ _ K WF Henv); rewrite ?EE.
  - exact N4.
  - exact R6.
  - intros b Hb. pose proof (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & B5).
    rewrite EE in B5. destruct (B5 _ R1) as [X|X]; cbn [fst snd] in X; [right| left]; exact X.
  - exact R7.
  - exact R4.
Qed.

Lemma AHK_fs_call : forall s LB LF LF' fs' m m' mo mo' W,
  AHKc s LB LF m mo -> munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> Forall fs_w W ->
  FSRep bsegs E0 FSB0 fs' LF' m' -> magree mo mo' -> LI (aSc s) (aNc s) (aEBc s) mo' ->
  AHKc (aps_set_fs fs' s) LB LF' m' mo'.
Proof.
  intros s LB LF LF' fs' m m' mo mo' W H MU WM MI' FW FS' Hag HLI'.
  pose proof (AHK_magree _ _ _ _ _ _ _ _ _ _ _ _ _ _ H Hag HLI') as H1. clear H Hag HLI'.
  pose proof H1 as H0. ahk_open H1. pose proof B_bframe.ceil_range as CR.
  pose proof Henv as Henv0. destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & EI1 & EI2).
  unfold app_mem in V3. rewrite kLowAppEnd_val, kHighMemBeg_val in V3 || (unfold kLowAppEnd, kLowShadowMapBeg, kShadowBase, kPageSize in V3; rewrite kHighMemBeg_val in V3).
  rewrite kFsBytes_val in *.
  (* [comment removed for export] *)
  set (fsb (x : Z) := alloc_ceiling <= x \/ (FSB0 <= x < FSB0 + 11571200) \/ (0x7fff8000 + FSB0 / 8 <= x < 0x7fff8000 + (FSB0 + 11571200) / 8)).
  assert (AG : forall x, 0 <= x < 2^64 -> ~ fsb x -> m' (wa x) = m (wa x)).
  { intros x Hx NW. destruct (decide (m' (wa x) = m (wa x))) as [E|NE]; [exact E|]. exfalso.
    destruct (munch_changed W m m' x MU Hx NE) as (iv & Hiv & R). apply NW. subst fsb.
    pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as X. unfold fs_w in X. rewrite kFsBytes_val in X.
    destruct X as [X|[[X1 X2]|[X1 X2]]]; lia. }
  assert (OUT : forall x, ~ fsb x -> outside W x).
  { intros x NW. eapply outside_of_Forall; [exact FW|]. intros iv Piv R. apply NW. subst fsb.
    unfold fs_w in Piv. rewrite kFsBytes_val in Piv. destruct Piv as [X|[[X1 X2]|[X1 X2]]]; lia. }
  (* [comment removed for export] *)
  pose proof Hfs as (FP1 & FP2 & FP3 & FP4 & _). rewrite ?kFsBytes_val in FP3. unfold FS_SB in FP4. rewrite ?kFsBytes_val in FP4.
  rewrite EFS in FP1, FP2, FP3, FP4, V3, V4.
  assert (AGI : forall a, 0x10000 <= a < 0x603000 -> m' (wa a) = m (wa a)).
  { intros a Ha. apply AG; [clear -Ha; lia|]. subst fsb. clear -Ha FP2 CR. intros [X|[X|X]]; [lia| lia| Z.div_mod_to_equations; lia]. }
  assert (AGL : forall a, LSLO <= a < LSHI -> m' (wa a) = m (wa a)).
  { intros a Ha. unfold LSLO, LSHI in Ha. apply AG; [clear -Ha; lia|]. subst fsb. clear -Ha FP2 FP4 CR. intros [X|[X|X]]; [lia| lia|].
    Z.div_mod_to_equations. lia. }
  unfold AHK. cbn [aps_env aps_alloc aps_fsbase aps_fs aps_so aps_credit aps_set_fs].
  split. { (* [comment removed for export] *) eapply (ARep_frame_client bsegs _ _ (DepotFP (aps_env s))); [| exact Hrep| exact WM|].
           - intros a0 mm mm' D W' A'. eapply DepotR_frame; [exact D| exact W'| exact A'].
           - intros x FPx. pose proof Hwf as WF'.
             pose proof (AK_blocks_sep s mo' Hwf Hkern Henv0) as BS. pose proof (IMG_IN_of s Henv0) as IMG_IN.
             pose proof (DepotFP_where (aps_env s)) as DW.
             assert (Hx : 0 <= x < 2^64).
             { pose proof (fp_below_ceiling _ _ [] [] IMG_IN DW _ _ WF' BS FPx) as UB.
               destruct (fp_locate _ _ [] [] IMG_IN DW _ _ WF' BS FPx) as [(r & Hr & R)|[[R _]|[R _]]].
               - pose proof (IMG_IN r Hr). pose proof (B_bframe.wf_env_img _ (proj1 WF')) as (_ & I2 & _). lia.
               - unfold sh_band, kLowShadowBeg, kShadowBase in R. rewrite kHighShadowBeg_val in R. clear -UB CR R. lia.
               - unfold app_addr in R. rewrite kHighMemBeg_val in R. clear -UB CR R. lia. }
             apply AG; [exact Hx|]. subst fsb. intros [X|[X|X]].
             + exact (fp_stack_free _ _ [] [] IMG_IN DW _ _ WF' BS X FPx).
             + revert FPx. apply (fp_fs_free _ _ [] [] IMG_IN DW _ _ WF' BS).
               unfold in_fakestack. rewrite EF1, EF2, EFS. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; rewrite ?kFsBytes_val; lia.
             + revert FPx. pose proof (fp_fs_shadow_free _ _ [] [] IMG_IN DW _ (x - kShadowBase) WF' BS) as C.
               unfold kShadowBase in C. replace (2147450880 + (x - 2147450880)) with x in C by lia. apply C.
               unfold in_fakestack. rewrite EF1, EF2, EFS. apply andb_true_iff.
               destruct Hfs as (P1 & _). rewrite EFS in P1.
               split; [apply Z.leb_le| apply Z.ltb_lt]; rewrite ?kFsBytes_val; clear -X P1; Z.div_mod_to_equations; lia. }
  split; [exact Hwf|]. split; [exact Hkern|]. split; [exact Hkvm|]. split; [exact Hres|]. split; [exact Hqb|]. split; [exact Hdi|]. split; [exact Hbinv|].
  split; [exact Hbm|].
  split. { rewrite EE, EFS. exact FS'. }
  split. { (* [comment removed for export] *) eapply icp_globals_agree; [exact Hicp|]. intros a Ha. pose proof (img_cells_not_mut a (or_introl Ha)) as [? _]. apply AGI; lia. }
  split. { (* [comment removed for export] *) eapply ay_statics_agree; [exact Hyst|]. intros a Ha. pose proof (img_cells_not_mut a (or_intror (or_introl Ha))) as [? _]. apply AGI; lia. }
  split. { (* [comment removed for export] *) eapply low_shadow_agree; [exact Hlow| exact AGL]. }
  rewrite EE in Hrt.
  split. { (* [comment removed for export] *)
           rewrite EE. eapply RTMisc_frame; [exact Hrt| exact MU| exact WM|]. intros a Ra.
           destruct (rt_fp_where a Ra) as [(R1 & R2 & R3 & R4)|R].
           - apply OUT. subst fsb. clear -R1 FP2 CR. intros [X|[X|X]]; [lia| lia| Z.div_mod_to_equations; lia].
           - pose proof (rt_high_range a (rt_high2_high _ _ _ R)) as RR.
             destruct PL0OK as ((c0 & cl & CRR & CC1 & CC2) & (d0 & dl & DRR & DD1 & DD2) & TRR & _).
             pose proof (resv_range_num _ _ _ CRR ltac:(clear -CC1 CC2; lia)) as (CN1 & CN2 & CN3 & CN4).
             pose proof (resv_range_num _ _ _ DRR ltac:(clear -DD1 DD2; lia)) as (DN1 & DN2 & DN3 & DN4).
             pose proof (resv_range_num _ _ _ TRR ltac:(clear; lia)) as (TN1 & TN2 & TN3 & TN4).
             destruct CRR as (_ & _ & _ & _ & CR5 & _). destruct DRR as (_ & _ & _ & _ & DR5 & _). destruct TRR as (_ & _ & _ & _ & TR5 & _).
             rewrite <- EE, EF1, EF2, EFS in CR5, DR5, TR5. rewrite ?kFsBytes_val in CR5, DR5, TR5. rewrite ?EE in CR5. rewrite ?EE in DR5. rewrite ?EE in TR5.
             unfold rt_high2 in R.
             apply OUT. subst fsb. clear -R CR5 DR5 TR5 CC1 CC2 DD1 DD2 CN2 DN2 TN2 CN4 DN4 TN4 FP2 FP3 CR.
             intros [X|[X|X]]; [lia| lia|]. Z.div_mod_to_equations. lia. }
  split. { eapply StdioRep_frame; [exact Hso| exact MU| exact WM|]. intros a Sa. destruct (so_fp_where a Sa) as [R1 _].
           apply OUT. subst fsb. clear -R1 FP2 CR. intros [X|[X|X]]; [lia| lia| Z.div_mod_to_equations; lia]. }
  split; [exact Hkm|]. split; [exact Hli|]. split; [exact Hbud|].
  split; [exact MI'|]. split; [exact Henv0|].
  (* [comment removed for export] *)
  split; [| split; [exact Hss| exact Hcs]].                    (* [comment removed for export] *)
  eapply ay_cells_agree; [exact Hycl|]. intros a Ha. pose proof (img_cells_not_mut a (or_intror (or_intror Ha))) as [? _]. apply AGI; lia.
Qed.

End Bundle.
End RC__1.
