(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages ITreeA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AM_monadx AM_syscalls AM_memset AM_memcpy AM_stdio_lib AX_file AM_fwrite AI_shadow AI_globals2 AI_gtrans AI_region_is_poisoned AI_pcommon AP_policy AP_mjx AP_fwritex AP_fwritex_gen AP_pop_arg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model Printf_mlib Printf_pieces.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AP_printf_iface AP_mlibA AP_piecesA AP_printf_core AP_vfprintf AP_fwritex_stdout AP_vfprintf_stdout AI_fprintf_icp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition vfprintf_icp_entry : Z := 0x46548.
Definition vprintf_icp_entry : Z := 0x459e4.
Definition musl_vprintf_entry : Z := 0x9d588.
Definition VFPRINTF_ICP_DEPTH : Z := 5600.   (* [comment removed for export] *)
Definition VPRINTF_ICP_DEPTH : Z := 5648.    (* [comment removed for export] *)

End RC__1.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Walk.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Variable P : acc -> Prop.
Hypothesis PSTK : POL_STACK P.
Hypothesis PIMG : POL_IMG P.
Hypothesis PHSH : POL_HSH P.
Hypothesis PLSH : POL_LSH P.
Hypothesis PNUL : POL_NUL P.
Hypothesis GS : forall x so, get_so (set_so so x) = so.
Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.

Let OUT := stdout_fwritex get_so set_so.

Definition vprintf_icp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
  fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ stdout_file m' (get_so st')
    /\ ssp_cells m' canary
    /\ mjx m'.

(* [comment removed for export] *)
Theorem vfprintf_icp_stdout_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
         (A VA : Z) (pre post : list Z) (c : Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r lo : Z) (canary : word),
  let fmt := pre ++ 37 :: c :: post in
  let q := bv_unsigned sp in
  a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
  stdout_file m (get_so st) ->
  bytes_at asegs m A (zb fmt ++ [Z_to_bv 8 0]) ->
  Forall (fun x => 0 < x < 256 /\ x <> 37) pre -> Forall (fun x => 0 < x < 256 /\ x <> 37) post ->
  (c = 100 \/ c = 117) -> zlength fmt <= 63 -> 0x10000 <= A -> A + 64 <= 0x21000 -> pass1_ok (fmt ++ [0]) = true ->
  va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 m lo q (q - 48 - VF_FRAME) slots args ->
  printf_pieces (fmt ++ [0]) args = Some (ps, r) -> fp_calls (length (fmt ++ [0])) (fmt ++ [0]) args = [] -> sp_ok (length (fmt ++ [0])) (fmt ++ [0]) args ->
  q <= VA -> VA + 8 * zlength slots <= A_STK_HI -> VA + 8 < A_STK_HI ->
  stk asegs m lo q -> A_CEIL <= lo -> lo <= q - VFPRINTF_ICP_DEPTH -> q <= A_STK_HI ->
  ssp_cells m canary -> mem_inv asegs m -> frm0 fc -> mjx m ->
  implMA asegs P (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
    (vprintf_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 vfprintf_icp_entry) fc None m (seg_rom asegs)).
Proof.
  intros until canary. cbv zeta. intros -> -> -> SF FMT HPRE HPOST HC FL HA0 HA1 P1 VAA AOK PP FPC SPOK QVA VAHI VA8 ST LOC LO SPTOP SSP MI FRM MJ.
  unfold VFPRINTF_ICP_DEPTH, A_CEIL, A_STK_HI, VF_FRAME in *.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
  pose proof (mjx_g _ MJ) as G. pose proof (mjx_g2 _ MJ) as G2.
  pose proof G as G'. icp_globals_open G'.
  pose proof (ig2_vfprintf asegs _ G2) as GRV. pose proof (ig2_cflags asegs _ G2) as GCF. pose proof (ig2_check_printf asegs _ G2) as GCP.
  unfold vfprintf_icp_entry. apply implMA_from_evtA. hideH FMT. hideH VAA.
  carve_frame 48%nat ST.
  do 9 stepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo (bv_unsigned sp + -48) |- _ => rename H into SK1 end.
  stepA. name_sp sp (-48).
  lazymatch goal with E : bv_unsigned ?spv = bv_unsigned sp + -48 |- _ => rewrite <- E in SK1 end.
  callA (tafr_spec P); [ exact SK1 | lia | lia | assumption | exact GINI
        | intros a k H1 H2; apply PSTK; lia | exact PIMG | ].
  unname_sp. stepA. if_false. (* [comment removed for export] *)
  (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. cbv beta. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. if_false. (* [comment removed for export] *)
  stepA. stepA. stepA. stepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (mjx_rodata_window0 m A (zlength (pre ++ 37 :: c :: post) + 1) MJ HA0 ltac:(unfold zlength; rewrite length_app; cbn [length]; lia) ltac:(unfold zlength in *; lia)) as [[FSH FSL] _]. rewrite repeat_length in FSL.
  pose proof (shw_geom 0x7fff8000 A (zlength (pre ++ 37 :: c :: post) + 1) ltac:(lia) ltac:(lia) ltac:(unfold zlength; lia)) as GF; cbv zeta in GF.
  (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into SK3 end.
  stepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (Gx : icp_globals asegs mx 0x7fff8000) by
      (unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
         A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL;
       repeat (split; [assumption|]); assumption);
    pose proof (bytes_at_transport asegs _ m mx _ _ FSH MU ltac:(cbn; rewrite ?repeat_length, ?Z2Nat.id by lia; lia)) as FSHx;
    unhideH FMT;
    pose proof (bytes_at_transport asegs _ m mx _ _ FMT MU ltac:(cbn; rewrite length_app, zb_length'; cbn [length]; unfold zlength in *; lia)) as FMTx;
    hideH FMT
  end.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
  callA (printf_common_call P _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc mx (bv_unsigned sp + -48) lo A VA 0x7fff8000 pre post c _ 0 [] 0%nat);
   [ exact HPRE | exact HPOST | lia | exact FL | exact FMTx | lia | exact FSHx
   | rewrite <- FSL; unfold zlength; rewrite length_app; cbn [length]; lia
   | exact Gx | reflexivity | exact SK3 | unfold alloc_ceiling, sp_window_lo, stack_max_size; lia | lia | lia | assumption
   | right; lia | lia
   | intros Hc; exfalso; lia | intros Hc; exfalso; lia | intros Hc; exfalso; lia | intros Hc; exfalso; lia
   | intros Hc; exfalso; lia | intros Hc; exfalso; lia | intros Hc; exfalso; lia
   | intros a k H1 H2; apply PSTK; lia
   | exact PIMG
   | intros a k H1 H2; apply PLSH; lia
   | intros Hc; exfalso; lia | intros Hc; exfalso; lia | intros Hc; exfalso; lia
   | ]
  end.
  (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into SK4 end.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    unhideH VAA; pose proof (bytes_at_transport asegs _ m mx _ _ VAA MU1 ltac:(cbn; rewrite u64s_length; unfold zlength in *; lia)) as VAAx;
    assert (MJx : mjx mx) by (eapply mjx_transport; [exact MJ | exact MU | exact WM |];
      unfold mjx_ok_iv, A_CEIL, A_STK_HI; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil);
    try clear FMTx; unhideH FMT; pose proof (bytes_at_transport asegs _ m mx _ _ FMT MU ltac:(cbn; rewrite length_app, zb_length'; cbn [length]; unfold zlength in *; lia)) as FMTx;
    assert (SFx : stdout_file mx (get_so st)) by (destruct SF as (fl & md & tl & bb & FC & R1 & BUF & R2 & R3 & R4); exists fl, md, tl, bb;
      split; [eapply rw_cells_transport; [exact FC | exact MU1 | exact WM | cbn; lia]|];
      split; [exact R1|]; split; [eapply rw_cells_transport; [exact BUF | exact MU1 | exact WM | cbn; lia]|]; exact (conj R2 (conj R3 R4)));
    assert (SSPx : ssp_cells mx canary) by (destruct SSP as [Q1 Q2]; unfold ssp_cells, got_ssp, ssp_guard in *;
      split; (eapply rw_cells_transport; [eassumption | exact MU1 | exact WM | cbn; lia]))
  end.
  apply evtA_done. name_sp sp (-48).
  lazymatch goal with E : bv_unsigned ?spv = bv_unsigned sp + -48 |- _ => rewrite <- ?E in SK4 end.
  pose proof (vfprintf_stdout_proof (St:=St) get_so set_so P PSTK PIMG PHSH PLSH PNUL GS SS (fwritex_stdout_proof P PSTK PIMG PHSH PLSH PNUL)) as VF.
  unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
  eapply implMA_post_evt.
  { eapply VF with (A := A) (VA := VA) (fmt := (pre ++ 37 :: c :: post) ++ [0]) (slots := slots) (args := args) (lo := lo) (canary := canary);
      clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, A_STK_HI, zlength; cbn [length].
    all: try reflexivity. all: try lia.
    all: first [ exact SFx
               | unfold zb; rewrite map_app; exact FMTx
               | apply Forall_app; split; [apply Forall_app; split; [eapply Forall_impl; [|exact HPRE]; cbv beta; intros; lia
                                         | constructor; [lia|]; constructor; [lia|]; eapply Forall_impl; [|exact HPOST]; cbv beta; intros; lia]
                                         | constructor; [lia | constructor]]
               | rewrite length_app; cbn [length]; unfold zlength in *; lia
               | exact P1 | exact VAAx
               | lazymatch goal with E : bv_unsigned ?spv = ?rhs |- args_ok _ _ _ _ _ ?spx _ _ _ =>
                   rewrite E; eapply args_ok_vf; [eapply args_ok_eqaddr; [exact AOK | lia | lia] | lia | eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia] end
               | exact PP | exact FPC | exact SPOK | exact SK4 | exact SSPx | exact FRM | exact MJx
               | unfold zlength in *; lia
               | assumption ]. }
  cbv beta. intros [] st4 ms' PO. clear VF MU1.
  unfold vfprintf_stdout_post in PO. rewrite ?unsigned_lit in PO by lia.
  destruct PO as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3 & MJ3).
  unname_sp.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
  ret_pc_lit.
  (* [comment removed for export] *)
  stepA. stepA. stepA. stepA. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  lazymatch goal with FRl : rw_cells _ ?mm (bv_unsigned sp + -48)%Z _ |- _ => release_frame FRl ST3 (bv_unsigned sp) end.
  apply evtA_done. unfold vprintf_icp_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [assumption|]. split; [exact SF3|]. split; [exact SSP3 | exact MJ3].
Qed.

(* [comment removed for export] *)
Theorem vprintf_icp_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
         (A VA : Z) (pre post : list Z) (c : Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r lo : Z) (canary : word),
  let fmt := pre ++ 37 :: c :: post in
  let q := bv_unsigned sp in
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 VA ->
  stdout_file m (get_so st) ->
  bytes_at asegs m A (zb fmt ++ [Z_to_bv 8 0]) ->
  Forall (fun x => 0 < x < 256 /\ x <> 37) pre -> Forall (fun x => 0 < x < 256 /\ x <> 37) post ->
  (c = 100 \/ c = 117) -> zlength fmt <= 63 -> 0x10000 <= A -> A + 64 <= 0x21000 -> pass1_ok (fmt ++ [0]) = true ->
  va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 m lo q (q - 96 - VF_FRAME) slots args ->
  printf_pieces (fmt ++ [0]) args = Some (ps, r) -> fp_calls (length (fmt ++ [0])) (fmt ++ [0]) args = [] -> sp_ok (length (fmt ++ [0])) (fmt ++ [0]) args ->
  q <= VA -> VA + 8 * zlength slots <= A_STK_HI -> VA + 8 < A_STK_HI ->
  stk asegs m lo q -> A_CEIL <= lo -> lo <= q - VPRINTF_ICP_DEPTH -> q <= A_STK_HI ->
  ssp_cells m canary -> mem_inv asegs m -> frm0 fc -> mjx m ->
  implMA asegs P (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
    (vprintf_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 vprintf_icp_entry) fc None m (seg_rom asegs)).
Proof.
  intros until canary. cbv zeta. intros -> -> SF FMT HPRE HPOST HC FL HA0 HA1 P1 VAA AOK PP FPC SPOK QVA VAHI VA8 ST LOC LO SPTOP SSP MI FRM MJ.
  unfold VPRINTF_ICP_DEPTH, A_CEIL, A_STK_HI, VF_FRAME in *.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
  pose proof (mjx_g _ MJ) as G. pose proof (mjx_g2 _ MJ) as G2.
  pose proof G as G'. icp_globals_open G'.
  pose proof (ig2_vprintf asegs _ G2) as GRVP. pose proof (ig2_cflags asegs _ G2) as GCF. pose proof (ig2_check_printf asegs _ G2) as GCP.
  unfold vprintf_icp_entry. apply implMA_from_evtA. hideH FMT. hideH VAA.
  carve_frame 48%nat ST.
  do 7 stepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo (bv_unsigned sp + -48) |- _ => rename H into SK1 end.
  stepA. name_sp sp (-48).
  lazymatch goal with E : bv_unsigned ?spv = bv_unsigned sp + -48 |- _ => rewrite <- E in SK1 end.
  callA (tafr_spec P); [ exact SK1 | lia | lia | assumption | exact GINI
        | intros a k H1 H2; apply PSTK; lia | exact PIMG | ].
  unname_sp. stepA. if_false. (* [comment removed for export] *)
  (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. cbv beta. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. if_false. (* [comment removed for export] *)
  stepA. stepA. stepA. stepA. (* [comment removed for export] *)
  destruct (mjx_rodata_window0 m A (zlength (pre ++ 37 :: c :: post) + 1) MJ HA0 ltac:(unfold zlength; rewrite length_app; cbn [length]; lia) ltac:(unfold zlength in *; lia)) as [[FSH FSL] _]. rewrite repeat_length in FSL.
  pose proof (shw_geom 0x7fff8000 A (zlength (pre ++ 37 :: c :: post) + 1) ltac:(lia) ltac:(lia) ltac:(unfold zlength; lia)) as GF; cbv zeta in GF.
  (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into SK3 end.
  stepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (Gx : icp_globals asegs mx 0x7fff8000) by
      (unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
         A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL;
       repeat (split; [assumption|]); assumption);
    pose proof (bytes_at_transport asegs _ m mx _ _ FSH MU ltac:(cbn; rewrite ?repeat_length, ?Z2Nat.id by lia; lia)) as FSHx;
    unhideH FMT;
    pose proof (bytes_at_transport asegs _ m mx _ _ FMT MU ltac:(cbn; rewrite length_app, zb_length'; cbn [length]; unfold zlength in *; lia)) as FMTx;
    hideH FMT
  end.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
  callA (printf_common_call P _ gp tp _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc mx (bv_unsigned sp + -48) lo A VA 0x7fff8000 pre post c _ 0 [] 0%nat);
   [ exact HPRE | exact HPOST | lia | exact FL | exact FMTx | lia | exact FSHx
   | rewrite <- FSL; unfold zlength; rewrite length_app; cbn [length]; lia
   | exact Gx | reflexivity | exact SK3 | unfold alloc_ceiling, sp_window_lo, stack_max_size; lia | lia | lia | assumption
   | right; lia | lia
   | intros Hc; exfalso; lia | intros Hc; exfalso; lia | intros Hc; exfalso; lia | intros Hc; exfalso; lia
   | intros Hc; exfalso; lia | intros Hc; exfalso; lia | intros Hc; exfalso; lia
   | intros a k H1 H2; apply PSTK; lia
   | exact PIMG
   | intros a k H1 H2; apply PLSH; lia
   | intros Hc; exfalso; lia | intros Hc; exfalso; lia | intros Hc; exfalso; lia
   | ]
  end.
  (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  zstepA. stepA. stepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into SK4 end.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    unhideH VAA; pose proof (bytes_at_transport asegs _ m mx _ _ VAA MU1 ltac:(cbn; rewrite u64s_length; unfold zlength in *; lia)) as VAAx;
    assert (MJx : mjx mx) by (eapply mjx_transport; [exact MJ | exact MU | exact WM |];
      unfold mjx_ok_iv, A_CEIL, A_STK_HI; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil);
    try clear FMTx; unhideH FMT; pose proof (bytes_at_transport asegs _ m mx _ _ FMT MU ltac:(cbn; rewrite length_app, zb_length'; cbn [length]; unfold zlength in *; lia)) as FMTx;
    assert (SFx : stdout_file mx (get_so st)) by (destruct SF as (fl & md & tl & bb & FC & R1 & BUF & R2 & R3 & R4); exists fl, md, tl, bb;
      split; [eapply rw_cells_transport; [exact FC | exact MU1 | exact WM | cbn; lia]|];
      split; [exact R1|]; split; [eapply rw_cells_transport; [exact BUF | exact MU1 | exact WM | cbn; lia]|]; exact (conj R2 (conj R3 R4)));
    assert (SSPx : ssp_cells mx canary) by (destruct SSP as [Q1 Q2]; unfold ssp_cells, got_ssp, ssp_guard in *;
      split; (eapply rw_cells_transport; [eassumption | exact MU1 | exact WM | cbn; lia]));
    assert (AOKx : args_ok RSTDOUT RSTDOUT_BUF 1024 mx lo (bv_unsigned sp) (bv_unsigned sp - 96 - 368) slots args)
      by (eapply args_ok_vf; [exact AOK | lia | eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia])
  end.
  apply evtA_done. name_sp sp (-48).
  lazymatch goal with E : bv_unsigned ?spv = bv_unsigned sp + -48 |- _ => rewrite <- ?E in SK4 end.
  eapply implMA_post_evt.
  { eapply vfprintf_icp_stdout_spec with (A := A) (VA := VA) (pre := pre) (c := c) (post := post) (slots := slots) (args := args) (lo := lo) (canary := canary);
      rewrite ?unsigned_lit by lia; unfold VF_FRAME, VFPRINTF_ICP_DEPTH, A_CEIL, A_STK_HI, zlength.
    all: try reflexivity. all: try lia.
    all: first [ exact SFx | exact FMTx | exact HPRE | exact HPOST | exact P1 | exact VAAx
               | lazymatch goal with E : bv_unsigned ?spv = ?rhs |- args_ok _ _ _ _ _ ?spx _ _ _ =>
                   rewrite E; eapply args_ok_vf; [eapply args_ok_eqaddr; [exact AOKx | lia | lia] | lia | apply munch_refl] end
               | exact PP | exact FPC | exact SPOK | exact SK4 | exact SSPx | exact FRM | exact MJx
               | unfold zlength in *; lia
               | assumption ]. }
  cbv beta. intros [] st4 ms' PO. clear MU1.
  unfold vprintf_icp_post in PO. rewrite ?unsigned_lit in PO by lia.
  destruct PO as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3 & MJ3).
  unname_sp.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
  ret_pc_lit.
  (* [comment removed for export] *)
  stepA. stepA. stepA. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  lazymatch goal with FRl : rw_cells _ ?mm (bv_unsigned sp + -48)%Z _ |- _ => release_frame FRl ST3 (bv_unsigned sp) end.
  apply evtA_done. unfold vprintf_icp_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [assumption|]. split; [exact SF3|]. split; [exact SSP3 | exact MJ3].
Qed.
End Walk.
End RC__2.
