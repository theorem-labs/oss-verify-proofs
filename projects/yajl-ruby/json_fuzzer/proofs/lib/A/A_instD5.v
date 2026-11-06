(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanFakeStack AsanPS.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_base AI_shadow AI_lowshadow AI_globals2 AI_gtrans AYajlRep AF_fakestack_rep AM_syscalls AM_stdio_lib AX_file AX_fini2 AX_unreg AX_Exit AF_statics
  A_bundle A_benv5 A_init5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Ltac not_in_lit_cells R :=
  let c := fresh "c" in let Hc := fresh "Hc" in let R' := fresh "R" in
  intros (c & Hc & R');
  unfold img_mut in Hc;
  cbn [aic_instance aic_internal_alloc_initialized aic_internal_allocator_instance aic_theDepot aic_stackStore asan_ic c_errno ACONSTS] in Hc;
  repeat (destruct Hc as [<-|Hc]; [cbn in R'; lia|]); destruct Hc.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma errno_cell : forall m : mem, exists errv, rw_cells asegs m 0x5e0a6c [C4 errv].
Proof.
  intros m.
  assert (BY : forall a, 0x5e0a6c <= a < 0x5e0a70 -> wview asegs m (wa a) <> None /\ exists b, mrd asegs m (wa a) = Some b).
  { intros a Ha. unfold mrd, wview.
    assert (H4 : a = 0x5e0a6c \/ a = 0x5e0a6d \/ a = 0x5e0a6e \/ a = 0x5e0a6f) by lia.
    destruct (m (wa a)) as [b|] eqn:Hm.
    - split; [discriminate| exists b; reflexivity].
    - destruct H4 as [-> |[-> |[-> | ->]]]; (split; [vm_compute; discriminate| eexists; vm_compute; reflexivity]). }
  assert (STK : stk asegs m 0x5e0a6c 0x5e0a70).
  { split; [lia|]. split; [lia|]. intros a Ha. exact (BY a Ha). }
  destruct (stk_carve asegs m 0x5e0a6c 0x5e0a70 4 STK ltac:(lia)) as [_ (junk & R)].
  exists (le_bytes_to_word junk).
  destruct R as [[Hwf HB] HW]. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  assert (HL : length junk = 4%nat) by (cbn in Hwf; destruct Hwf as [Hwf _]; exact Hwf).
  split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite AM_stdio_lib.le4_of_bytes by exact HL. exact HB.
  - cbn [cells_size csize] in *. exact HW.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition so_fpc : Z -> Prop := in_cells stdio_regions.

Lemma stdio_rep_agree : forall so m m',
  stdio_rep so m -> (forall a, so_fpc a -> m' (wa a) = m (wa a)) -> stdio_rep so m'.
Proof.
  intros so m m' (guard & cdt & thr & sec & tm1 & ST) AG. exists guard, cdt, thr, sec, tm1.
  unfold stdio_state, stdio_statics, stdin_file, stdout_file, stderr_wfile0, ssp_cells in *.
  unfold so_fpc, stdio_regions in AG.
  Ltac fp1 a Ha := unfold got_ssp, ssp_guard, stdin_cells, file_cells in Ha; solve_in_cells.
  agree_xfer AG ST fp1.
Qed.

Lemma so_fpc_where : forall a, so_fpc a -> 0x10000 <= a < 0x603000 /\ ~ cl_cells a /\ ~ in_cells img_mut a.
Proof.
  intros a (c & Hc & R). unfold stdio_regions in Hc. unfold cl_cells. cbn [c_initialized c_errno ACONSTS].
  destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn in R; (split; [lia| split; [lia| not_in_lit_cells R]]).
Qed.

Lemma stdio_rep_buf : forall so m, stdio_rep so m -> Z.of_nat (length (so_buf so)) <= 1024.
Proof.
  intros so m (guard & cdt & thr & sec & tm1 & (_ & _ & SOF & _)).
  destruct SOF as (flags & mode & tail & bufb & _ & _ & _ & _ & B & _). exact B.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rt_img_cells : list (Z * Z) := icp_globals2_cells ++ exit_regions ++ amalloc_statics_cells.

Section InstD.
Variables (E0 : aenv) (FSB0 : Z) (PL0 : fs_plumb).

(* [comment removed for export] *)
Definition athr_fp (a : Z) : Prop := (ae_thread E0 <= a < ae_thread E0 + 8) \/ (fp_ctx PL0 + 8 <= a < fp_ctx PL0 + 12).
Definition rt_fpc (a : Z) : Prop := in_cells rt_img_cells a \/ fsenv_fp E0 FSB0 PL0 a \/ athr_fp a.

Lemma fsenv_fp_cases : forall x, fsenv_fp E0 FSB0 PL0 x ->
  (0x10000 <= x < 0x603000 /\ ~ cl_cells x /\ ~ stdio_w x /\ ~ in_cells img_mut x) \/ rt_high2 E0 PL0 x.
Proof.
  intros x H. unfold fsenv_fp, fsenv_ranges in H. unfold FS_TP, FS_CF, FS_VB, FS_DTO in H.
  unfold cl_cells, stdio_w, rt_high2. cbn [c_initialized c_errno c_stderr_F c_stdout_F c_stdout_buf ACONSTS].
  repeat match type of H with
  | Exists _ (_ :: _) =>
      apply Exists_cons in H; destruct H as [H|H];
      [cbn in H; first [right; lia | left; split; [lia| split; [lia| split; [lia| not_in_lit_cells H]]]] |]
  end.
  apply Exists_nil in H; destruct H.
Qed.

Lemma rt_img_cells_where : forall x, in_cells rt_img_cells x ->
  0x10000 <= x < 0x603000 /\ ~ cl_cells x /\ ~ stdio_w x /\ ~ in_cells img_mut x.
Proof.
  intros x (c & Hc & R). unfold rt_img_cells, icp_globals2_cells, exit_regions, fini_statics_cells, unreg_statics_cells, amalloc_statics_cells in Hc.
  unfold A_REAL_STRLEN, A_REAL_READ, A_REAL_FWRITE, A_REAL_VPRINTF, A_REAL_VFPRINTF, A_REAL_STRNLEN, A_REAL_MEMCHR,
         A_GOT_CFLAGS, A_CF_INTERCEPT_STRLEN, A_CF_CHECK_PRINTF, A_CFLAGS in Hc.
  rewrite ?in_app_iff in Hc. cbn [List.app In] in Hc.
  unfold cl_cells, stdio_w. cbn [c_initialized c_errno c_stderr_F c_stdout_F c_stdout_buf ACONSTS].
  repeat match type of Hc with
  | _ \/ _ => destruct Hc as [Hc|Hc]
  end;
  first [ subst c; cbn in R; split; [lia| split; [lia| split; [lia| not_in_lit_cells R]]] | destruct Hc ].
Qed.

Lemma rt_fpc_where : forall a, rt_fpc a ->
  (0x10000 <= a < 0x603000 /\ ~ cl_cells a /\ ~ stdio_w a /\ ~ in_cells img_mut a) \/ rt_high2 E0 PL0 a.
Proof.
  intros a [IC|[FE|AT]]; [left; exact (rt_img_cells_where a IC)| exact (fsenv_fp_cases a FE)|].
  right. unfold athr_fp in AT. unfold rt_high2. lia.
Qed.

Lemma rt_fpc_where_high : forall a, rt_fpc a ->
  (0x10000 <= a < 0x603000 /\ ~ cl_cells a /\ ~ stdio_w a /\ ~ in_cells img_mut a) \/ rt_high E0 PL0 a.
Proof. intros a H. destruct (rt_fpc_where a H) as [L|R]; [left; exact L| right; exact (rt_high2_high E0 PL0 a R)]. Qed.

(* [comment removed for export] *)
Lemma rt_fpc_where2 : forall a, rt_fpc a -> (0x10000 <= a < 0x603000 /\ ~ in_cells img_mut a) \/ rt_high2 E0 PL0 a.
Proof. intros a H. destruct (rt_fpc_where a H) as [(A & _ & _ & B)|R]; [left; split; [exact A| exact B]| right; exact R]. Qed.
Lemma so_fpc_where2 : forall a, so_fpc a -> 0x10000 <= a < 0x603000 /\ ~ in_cells img_mut a.
Proof. intros a H. destruct (so_fpc_where a H) as (A & _ & B). split; [exact A| exact B]. Qed.

(* [comment removed for export] *)
Lemma rt_misc5_agree : forall m m',
  rt_misc5 FSB0 PL0 E0 m -> (forall a, rt_fpc a -> m' (wa a) = m (wa a)) -> rt_misc5 FSB0 PL0 E0 m'.
Proof.
  intros m m' (G2 & (t & EX) & FE & AMS & ATH) AG.
  split; [| split; [| split; [| split]]].
  - (* [comment removed for export] *)
    assert (AG1 : forall a, in_cells icp_globals2_cells a -> m' (wa a) = m (wa a)).
    { intros a Ha. apply AG. left. unfold rt_img_cells. apply (proj2 (in_cells_app _ _ a)). left. exact Ha. }
    clear AG. unfold icp_globals2 in *. unfold icp_globals2_cells in AG1.
    Ltac fp2 a Ha := unfold A_REAL_STRLEN, A_REAL_READ, A_REAL_FWRITE, A_REAL_VPRINTF, A_REAL_VFPRINTF, A_REAL_STRNLEN, A_REAL_MEMCHR,
                       A_GOT_CFLAGS, A_CF_INTERCEPT_STRLEN, A_CF_CHECK_PRINTF, A_CFLAGS in Ha; solve_in_cells.
    agree_xfer AG1 G2 fp2.
  - (* [comment removed for export] *)
    assert (AG1 : forall a, in_cells exit_regions a -> m' (wa a) = m (wa a)).
    { intros a Ha. apply AG. left. unfold rt_img_cells. apply (proj2 (in_cells_app _ _ a)). right. apply (proj2 (in_cells_app _ _ a)). left. exact Ha. }
    clear AG. exists t. unfold exit_statics, fini_statics, unreg_statics, globals_tab in *.
    unfold exit_regions, fini_statics_cells, unreg_statics_cells in AG1.
    Ltac fp3 a Ha := solve_in_cells.
    agree_xfer AG1 EX fp3.
  - (* [comment removed for export] *)
    assert (AG1 : forall a, fsenv_fp E0 FSB0 PL0 a -> m' (wa a) = m (wa a)).
    { intros a Ha. apply AG. right. left. exact Ha. }
    clear AG. unfold FSEnv in *. unfold fsenv_fp, fsenv_ranges in AG1.
    Ltac fp4 a Ha := unfold FS_TP, FS_CF, FS_VB, FS_DTO in *;
                     repeat (apply Exists_cons_hd; cbn [fst snd]; lia) || apply Exists_cons_tl.
    agree_xfer AG1 FE fp4.
  - (* [comment removed for export] *)
    assert (AG1 : forall a, in_cells amalloc_statics_cells a -> m' (wa a) = m (wa a)).
    { intros a Ha. apply AG. left. unfold rt_img_cells. apply (proj2 (in_cells_app _ _ a)). right. apply (proj2 (in_cells_app _ _ a)). right. exact Ha. }
    clear AG. unfold amalloc_statics in *. unfold amalloc_statics_cells in AG1.
    Ltac fp5 a Ha := solve_in_cells.
    agree_xfer AG1 AMS fp5.
  - (* [comment removed for export] *)
    assert (AG1 : forall a, athr_fp a -> m' (wa a) = m (wa a)).
    { intros a Ha. apply AG. right. right. exact Ha. }
    clear AG. unfold athr5 in *. unfold athr_fp in AG1.
    Ltac fp6 a Ha := lia.
    agree_xfer AG1 ATH fp6.
Qed.

Lemma rt_misc5_icp2 : forall m, rt_misc5 FSB0 PL0 E0 m -> icp_globals2 asegs m.
Proof. intros m (A & _ & _ & _). exact A. Qed.
Lemma rt_misc5_exit : forall m, rt_misc5 FSB0 PL0 E0 m -> exists t, exit_statics m t.
Proof. intros m (_ & A & _ & _). exact A. Qed.
Lemma rt_misc5_fsenv : forall m, rt_misc5 FSB0 PL0 E0 m -> FSEnv asegs E0 FSB0 PL0 m.
Proof. intros m (_ & _ & F & _). exact F. Qed.
Lemma rt_misc5_ams : forall m, rt_misc5 FSB0 PL0 E0 m -> amalloc_statics m.
Proof. intros m (_ & _ & _ & A & _). exact A. Qed.
Lemma rt_misc5_athr : forall m, rt_misc5 FSB0 PL0 E0 m -> athr5 PL0 E0 m.
Proof. intros m (_ & _ & _ & _ & A). exact A. Qed.
End InstD.
End RC__1.
