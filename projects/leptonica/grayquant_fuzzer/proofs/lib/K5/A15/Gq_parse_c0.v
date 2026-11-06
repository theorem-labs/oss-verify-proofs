(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Image.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_leaf Lept_chain LeptC_leaf Lept_objkit LeptL_kit D_iface D_defs
  Ed_fp Ed_fpkit Gq_numa Numa_kit Ed_tracekit Gq_gaps Gq_iface Gq_thr_iface Gq_parse_kit Gq_parse_kit2 Gq_parse_defs Gq_parse_case.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section PARSE_C0.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GG : gq_gaps RT.
Hypothesis NUMAC : numaCreate_cps RT.
Hypothesis NADDF : numaAddNumber_fast_cps RT.
Hypothesis SNEW : stringNew_lit_cps RT.
Hypothesis TOK0 : strtokSafe_gq_cps RT true 0 2 3 [52; 53].
Hypothesis TOK1 : strtokSafe_gq_cps RT false 3 2 6 [55; 53].
Hypothesis TOK2 : strtokSafe_gq_cps RT false 6 3 10 [49; 49; 53].
Hypothesis TOK3 : strtokSafe_gq_cps RT false 10 3 0 [49; 56; 53].
Hypothesis TOKE : strtokSafe_end_cps RT.

Theorem parse_c0 : parse_case RT 0.
Proof using AF GP RC GG NUMAC NADDF SNEW TOK0 TOK1 TOK2 TOK3 TOKE.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ras
    FDO MST -> -> -> UC TRS TR ENV RES AL.
  unfold lpost, lpost_f, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_parseStringForNumbers, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, PARSE_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  unfold LIT_EDGEVALS, LIT_SEPS in *.
  hide TRS. hide TR.
  park_disj. carve_frame 96%nat ST.
  walk_to AF MST [(usp - 96, usp)] [e_stack_malloc 0%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_0 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => exact Ha).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof SNEW as SN; unfold stringNew_lit_cps in SN; eapply SN with (lo := lo); rt_side idtac.
    all: lazymatch goal with
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | exact I]).
  lazymatch goal with H : rt_live RT ?S = (?p, 14) :: _ |- _ => rename H into LVS; rename S into Σs; rename p into ns end.
  lazymatch goal with H : rw_cells asegs _ ns _ |- _ => rename H into NSC end.
  cbn [str_cells EDGE_STR app map] in NSC.
  lazymatch goal with H : rt_live RT x = rt_live RT Σ |- _ => rename H into LVX end.
  lazymatch goal with H : rt_frames RT Σs = rt_frames RT x |- _ => rename H into FRSX end.
  assert (LVSs : rt_live RT Σs = (ns, 14) :: rt_live RT Σ) by (rewrite LVS, LVX; reflexivity).
  assert (FRSs : rt_frames RT Σs = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRSX; exact FRS).
  assert (INS : In (ns, 14) (rt_live RT Σs)) by (rewrite LVSs; left; reflexivity).
  lazymatch goal with A : ART RT Σs ?mm |- cps _ (ASTA RT Σs _ _) _ =>
    assert (NCS : forall a, PF a -> a < ns \/ ns + 14 <= a)
      by (intros a Ha; apply (new_chunk_apart RT AF Σs mm ns 14 (rt_live RT Σ) (rt_frames RT Σs) usp a A LVSs eq_refl);
          [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
          | apply (aclient_mono _ _ usp _ _ _ _ Ha); [exact (fun e He => He)| rewrite FRSs; solve [frames_sub_tac]| lia] ]) end.
  chunk_facts RT AF GP ns 14.
  fframe_chunk RT AF fr 0%nat 64 ns 14.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRtop. clear FRrec.
  assert (RAV : 4096 <= bv_unsigned ra).
  { unfold hid in TR. revert TR. clear. generalize (bv_unsigned ra) as r. intros r H.
    vm_compute in H. repeat (destruct H as [H|H]; [first [discriminate | injection H; intros; subst; lia] |]). exact (False_ind _ H). }
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
  assert (UC1 : uctx mc (Z_to_bv 64 (usp + -96)) (Z_to_bv 64 usp) (bv_unsigned ra :: ras)) by
   (unfold uctx in UC |- *; rewrite !unsigned_lit by lia;
    apply (chain_ok_push mc (usp + -96) usp (bv_unsigned ra) (bv_unsigned s0) ras);
    [ lia | lia | unfold USTACK_TOP; lia
    | pose proof (bv_unsigned_in_range 64 ra); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | pose proof (bv_unsigned_in_range 64 s0); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | rewrite !Z_to_bv_bv_unsigned; exact FRtop
    | apply (chain_ok_keep ras m mc _ _ UC); intros aa Haa; apply AGF; subst PF; cbv beta; left; unfold usp in *; ul ]) end.
  eapply cps_seq.
  { eapply NUMAC with (lo := lo) (n := 0) (ras := bv_unsigned ra :: ras).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - split; [lia| reflexivity].
    - lia.
    - exact UC1.
    - unfold hid in TR. exact TR.
    - lenv_tac.
    - unfold lres, numa_cap. cbn [Z.eqb Z.mul Pos.mul]. unfold mcost. cbn. change (4 * 50 <=? 64512) with true. cbv iota. lres_tac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia] | exact I]).
  unfold numa_cap in *. cbn [Z.eqb] in *. change (mcost (4 * 50)) with 0 in *.
  lazymatch goal with H : rt_live RT ?S = numa_live ?p _ ?q _ |- _ => rename H into LVN; rename S into Σn; rename p into na; rename q into arr end.
  lazymatch goal with H : numa_obj _ _ na _ arr [] |- _ => rename H into NOBJ end.
  lazymatch goal with H : rt_frames RT Σn = rt_frames RT Σs |- _ => rename H into FRNS end.
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (_ & NCAP & NA0 & NA16 & AR0 & AR16 & INNA & INAR & NANE).
  assert (FRSn : rt_frames RT Σn = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRNS; exact FRSs).
  assert (LVSH : rt_live RT Σn = (arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ) by (rewrite LVN; unfold numa_live; rewrite LVSs; reflexivity).
  assert (INSn : In (ns, 14) (rt_live RT Σn)) by (rewrite LVSH; right; right; left; reflexivity).
  lazymatch goal with A : ART RT Σn ?mm |- cps _ (ASTA RT Σn _ _) _ =>
    assert (NCA : forall a, PF a -> a < na \/ na + 32 <= a)
      by (intros a Ha; apply (live_chunk_apart RT AF Σn mm [(arr, 200)] na 32 ((ns, 14) :: rt_live RT Σ) (rt_live RT Σ) (rt_frames RT Σn) usp a A);
          [ rewrite LVSH; reflexivity | intros e He; apply in_or_app; right; right; exact He | reflexivity
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
          | apply (aclient_mono _ _ usp _ _ _ _ Ha); [exact (fun e He => He)| rewrite FRSn; solve [frames_sub_tac]| lia] ]);
    assert (NCB : forall a, PF a -> a < arr \/ arr + 200 <= a)
      by (intros a Ha; apply (live_chunk_apart RT AF Σn mm [] arr 200 ((na, 32) :: (ns, 14) :: rt_live RT Σ) (rt_live RT Σ) (rt_frames RT Σn) usp a A);
          [ rewrite LVSH; reflexivity | intros e He; cbn [app In]; right; right; exact He | reflexivity
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
          | apply (aclient_mono _ _ usp _ _ _ _ Ha); [exact (fun e He => He)| rewrite FRSn; solve [frames_sub_tac]| lia] ]) end.
  assert (LVPN : forall q k, In (q, k) ((arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ) -> 0 < k).
  { intros q k Hq. cbn [In] in Hq. destruct Hq as [Hq|[Hq|[Hq|Hq]]]; [injection Hq as <- <-; lia| injection Hq as <- <-; lia| injection Hq as <- <-; lia| exact (LVP q k Hq)]. }
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT Σn ?mm |- cps _ (ASTA RT Σn _ _) _ =>
    pose proof (live_apart2 RT AF Σn mm ns 14 na 32 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DSN;
    pose proof (live_apart2 RT AF Σn mm ns 14 arr 200 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DSA end.
  chunk_facts RT AF GP na 32. chunk_facts RT AF GP arr 200.
  fframe_chunk RT AF fr 0%nat 64 na 32. fframe_chunk RT AF fr 0%nat 64 arr 200.
  (* [comment removed for export] *)
  destruct NOBJ as ((npad & NAC) & (njunk & ARC) & _).
  unfold numa_cells, numa_arr_cells in NAC, ARC. cbn [map app length Z.of_nat Z.mul Z.sub Z.to_nat] in NAC, ARC.
  (* [comment removed for export] *)
  assert (TRF1 : In (0xa85c8 :: bv_unsigned ra :: ras) CLIENT_TRACES).
  { unfold hid in TRS. unfold PARSE_RAS in TRS.
    pose proof (proj1 (Forall_forall _ _) TRS 0xa85c8 ltac:(cbn [In]; clear; tauto)) as [X|X]; [exact X|].
    exfalso. revert X. clear. intros X. apply (In_nth_error) in X. destruct X as (n & X).
    assert (F : ct_mem [0xa85c8] = false) by (vm_compute; reflexivity).
    unfold ct_mem in F. apply Bool.not_true_iff_false in F. apply F. apply existsb_exists. exists [0xa85c8].
    split; [exact (nth_error_In _ _ X)| vm_compute; reflexivity]. }
  assert (TRF2 : In (0xa85e4 :: bv_unsigned ra :: ras) CLIENT_TRACES).
  { unfold hid in TRS. unfold PARSE_RAS in TRS.
    pose proof (proj1 (Forall_forall _ _) TRS 0xa85e4 ltac:(cbn [In]; clear; tauto)) as [X|X]; [exact X|].
    exfalso. revert X. clear. intros X. apply (In_nth_error) in X. destruct X as (n & X).
    assert (F : ct_mem [0xa85e4] = false) by (vm_compute; reflexivity).
    unfold ct_mem in F. apply Bool.not_true_iff_false in F. apply F. apply existsb_exists. exists [0xa85e4].
    split; [exact (nth_error_In _ _ X)| vm_compute; reflexivity]. }
  clear TRS.
  (* [comment removed for export] *)
  assert (SPn : rt_sp0 RT Σn = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity).
  assert (CRn : rt_credit RT Σ - 1 <= rt_credit RT Σn) by credit_tac.
  pose proof LVSH as LVn. pose proof FRSn as FRSn_.
  repeat match goal with H : context [x] |- _ => clear H end. try clear x.
  repeat match goal with H : context [Σs] |- _ => clear H end. try clear Σs.
  rename Σn into Σc. rename LVn into LVc. rename FRSn_ into FRSc. rename SPn into SPc. rename CRn into CRc.
  try clear INNA. try clear INAR. try clear INS.
  assert (INNA : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; left; reflexivity).
  assert (INAR : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; left; reflexivity).
  assert (INS : In (ns, 14) (rt_live RT Σc)) by (rewrite LVc; right; right; left; reflexivity).
  ctx_gc RT.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  split_at FRM 4%nat TLC. split_at TLC 1%nat FRMr.
  eapply cps_seq.
  { pose proof TOK0 as TK; unfold strtokSafe_gq_cps in TK; eapply TK with (lo := lo) (ns := ns) (tl := fr + 32) (w0 := z64).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - solve [in_live_tac].
    - exact NSC.
    - unfold optrF. split.
      2: { split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. unfold SEGTOP_A in *. split; [clear - FRSH; unfold parked in FRSH; lia| lia]. }
      exists fr, 0%nat. rewrite FRSc. change (fs_size 0) with 64.
      split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia).
      pose proof FSH as T; split_at T 4%nat T2; split_at T2 1%nat T3; destruct T2 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 8) with [Z_to_bv 8 0]; exact B.
    - exact TLC.
    - lenv_tac.
    - lres_tac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia | exact I]]).
  change (2 + 1) with 3 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 3) :: rt_live RT Σc |- _ => rename H into LVT0; rename S into Σt0; rename p into tk0 end.
  lazymatch goal with H : rw_cells asegs _ tk0 _ |- _ => rename H into TKC0 end.
  lazymatch goal with H : rw_cells asegs _ (fr + 32) _ |- _ => rename H into TLC end.
  cbv iota in TLC. change (3 =? 0) with false in TLC. cbv iota in TLC.
  cbn [str_cells app map] in TKC0.
  lazymatch goal with H : rt_frames RT Σt0 = rt_frames RT Σc |- _ => rename H into FRT0 end.
  assert (FRSt0 : rt_frames RT Σt0 = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRT0; exact FRSc).
  assert (LVTH0 : rt_live RT Σt0 = (tk0, 3) :: (arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ) by (rewrite LVT0, LVc; reflexivity).
  assert (INT0 : In (tk0, 3) (rt_live RT Σt0)) by (rewrite LVT0; left; reflexivity).
  lazymatch goal with A : ART RT Σt0 ?mm |- cps _ (ASTA RT Σt0 _ _) _ =>
    assert (NCT0 : forall a, PF a -> a < tk0 \/ tk0 + 3 <= a)
      by (intros a Ha; apply (live_chunk_apart RT AF Σt0 mm [] tk0 3 ((arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ) (rt_live RT Σ) (rt_frames RT Σt0) usp a A);
          [ rewrite LVTH0; reflexivity | intros e He; cbn [app In]; right; right; right; exact He | reflexivity
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
          | apply (aclient_mono _ _ usp _ _ _ _ Ha); [exact (fun e He => He)| rewrite FRSt0; solve [frames_sub_tac]| lia] ]);
    (* [comment removed for export] *)
    pose proof (live_apart2 RT AF Σt0 mm tk0 3 na 32 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DTN0;
    pose proof (live_apart2 RT AF Σt0 mm tk0 3 arr 200 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DTA0;
    pose proof (live_apart2 RT AF Σt0 mm tk0 3 ns 14 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DTS0 end.
  lazymatch goal with A : ART RT Σt0 ?mm |- cps _ (ASTA RT Σt0 _ _) _ =>
    pose proof (af_live_range RT AF Σt0 mm tk0 3 A INT0) as (TKP0 & _ & _) end.       (* [comment removed for export] *)
  assert (NETN0 : na <> tk0) by (clear - DTN0; lia).
  assert (NETA0 : arr <> tk0) by (clear - DTA0; lia).
  assert (NETS0 : ns <> tk0) by (clear - DTS0; lia).
  chunk_facts RT AF GP tk0 3.
  fframe_chunk RT AF fr 0%nat 64 tk0 3.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof (gg_atof RT GG) as AT; unfold atof_contract in AT;
    eapply AT with (lo := lo) (s := tk0) (k := 45) (bs := [52; 53; 0]) (d := 0x4046800000000000); rt_side idtac.
    all: lazymatch goal with
         | |- In _ TOKENS => unfold TOKENS; cbn [In]; clear; tauto
         | |- bytes_at _ _ _ _ => destruct TKC0 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; exact B
         | |- own_live _ _ _ => exists tk0, 3; split; [solve [in_live_tac] | cbn [length Z.of_nat]; lia]
         end. }
  unfold ret_st_fa0.
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  lazymatch goal with H : reg_get ?Fx fa0 = _ |- _ => rename H into FA00 end.
  (* [comment removed for export] *)
  lazymatch goal with |- context [ms_fcsr ?E] =>
    lazymatch E with entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?fcx _ _ => change (ms_fcsr E) with (frm_clear fcx) end end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ ?Fx _ _ _ ?mc _))) _ =>
    assert (NOBJ0 : numa_obj (rt_live RT S) mc na 50 arr [])
      by (split; [eexists; exact NAC| split; [eexists; exact ARC|]];
          split; [split; [solve [in_live_tac] | repeat split; first [assumption | lia]]|];
          split; [split; [solve [in_live_tac] | repeat split; first [assumption | lia]]|];
          split; [exact NANE|]; cbn [length Z.of_nat]; lia);
    assert (FV0 : freg_is Fx fa0 (ival_w 45))
      by (unfold freg_is; rewrite freg_get_same by reflexivity;
          lazymatch goal with |- context [fcvt_s_d _ (reg_get ?F0 ?r0)] => change (reg_get F0 r0) with (reg_get F0 fa0) end;
          rewrite FA00; apply bv_eq; vm_compute; reflexivity)
  end.
  eapply cps_seq.
  { eapply NADDF with (lo := lo) (na := na) (cap := 50) (arr := arr) (vals := []) (v := ival_w 45).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - exact FV0.
    - exact NOBJ0.
    - cbn [length Z.of_nat]. lia.
    - lenv_tac.
    - lres_tac. }
  clear NAC ARC NOBJ0 FV0 FA00.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; pose proof (NCA _ Hx); pose proof (NCB _ Hx); repeat split; first [exact I | lia]]).
  lazymatch goal with H : numa_obj _ _ na _ arr _ |- _ => rename H into NOBJ0 end.
  cbn [app] in NOBJ0.
  lazymatch goal with H : rt_live RT ?S = rt_live RT Σt0 |- _ => rename H into LVA0; rename S into Σa0 end.
  lazymatch goal with H : rt_frames RT Σa0 = rt_frames RT Σt0 |- _ => rename H into FRA0 end.
  assert (FRSa0 : rt_frames RT Σa0 = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRA0; exact FRSt0).
  destruct NOBJ0 as ((npad0 & NAC) & (njunk0 & ARC) & _).
  unfold numa_cells, numa_arr_cells in NAC, ARC. cbn [map app length Z.of_nat Z.mul Z.sub Z.to_nat] in NAC, ARC.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
  assert (UC20 : unwind_okC mc (Z_to_bv 64 0xa85c8) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))) by
   (exists (bv_unsigned ra :: ras); split; [| rewrite unsigned_lit by lia; exact TRF1];
    rewrite !unsigned_lit by lia;
    apply (chain_ok_push mc (usp + -96) usp (bv_unsigned ra) (bv_unsigned s0) ras);
    [ lia | lia | unfold USTACK_TOP; lia
    | pose proof (bv_unsigned_in_range 64 ra); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | pose proof (bv_unsigned_in_range 64 s0); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | rewrite !Z_to_bv_bv_unsigned; exact FRtop
    | unfold uctx in UC; apply (chain_ok_keep ras m mc _ _ UC); intros aa Haa; apply AGF; subst PF; cbv beta; left; unfold usp in *; ul ]) end.
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FREE; unfold free_contractC in FREE; eapply FREE with (lo := lo) (p := tk0) (n := 3); rt_side idtac.
    all: lazymatch goal with |- unwind_okC _ _ _ _ => exact UC20 end. }
  clear TKC0 UC20.
  after_call RT AF.
  lazymatch goal with H : rt_live RT ?S = live_remove tk0 _ |- _ => rename H into LVF00; rename S into Σf0 end.
  lazymatch goal with H : rt_frames RT Σf0 = rt_frames RT Σa0 |- _ => rename H into FRFA0 end.
  assert (FRSf0 : rt_frames RT Σf0 = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRFA0; exact FRSa0).
  (* [comment removed for export] *)
  assert (LVF0 : rt_live RT Σf0 = (arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ).
  { lazymatch goal with A : ART RT Σt0 ?mm |- _ =>
      exact (live_after_free RT AF Σt0 mm tk0 3 _ (rt_live RT Σf0) A LVTH0 ltac:(lia) LVPN ltac:(rewrite LVF00, LVA0; reflexivity)) end. }
  clear LVF00.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LVF0; right; right; right; exact He | solve [frames_sub_tac]| lia]).
  (* [comment removed for export] *)
  assert (SPn : rt_sp0 RT Σf0 = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity).
  assert (CRn : rt_credit RT Σ - 1 <= rt_credit RT Σf0) by credit_tac.
  pose proof LVF0 as LVn. pose proof FRSf0 as FRSn_.
  repeat match goal with H : context [Σc] |- _ => clear H end. try clear Σc.
  repeat match goal with H : context [Σt0] |- _ => clear H end. try clear Σt0.
  repeat match goal with H : context [Σa0] |- _ => clear H end. try clear Σa0.
  repeat match goal with H : context [tk0] |- _ => clear H end. try clear tk0.
  rename Σf0 into Σc. rename LVn into LVc. rename FRSn_ into FRSc. rename SPn into SPc. rename CRn into CRc.
  try clear INNA. try clear INAR. try clear INS.
  assert (INNA : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; left; reflexivity).
  assert (INAR : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; left; reflexivity).
  assert (INS : In (ns, 14) (rt_live RT Σc)) by (rewrite LVc; right; right; left; reflexivity).
  ctx_gc RT.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof TOK1 as TK; unfold strtokSafe_gq_cps in TK; eapply TK with (lo := lo) (ns := ns) (tl := fr + 32) (w0 := z64).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - solve [in_live_tac].
    - exact NSC.
    - unfold optrF. split.
      2: { split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. unfold SEGTOP_A in *. split; [clear - FRSH; unfold parked in FRSH; lia| lia]. }
      exists fr, 0%nat. rewrite FRSc. change (fs_size 0) with 64.
      split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia).
      pose proof FSH as T; split_at T 4%nat T2; split_at T2 1%nat T3; destruct T2 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 8) with [Z_to_bv 8 0]; exact B.
    - exact TLC.
    - lenv_tac.
    - lres_tac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia | exact I]]).
  change (2 + 1) with 3 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 3) :: rt_live RT Σc |- _ => rename H into LVT1; rename S into Σt1; rename p into tk1 end.
  lazymatch goal with H : rw_cells asegs _ tk1 _ |- _ => rename H into TKC1 end.
  lazymatch goal with H : rw_cells asegs _ (fr + 32) _ |- _ => rename H into TLC end.
  cbv iota in TLC. change (6 =? 0) with false in TLC. cbv iota in TLC.
  cbn [str_cells app map] in TKC1.
  lazymatch goal with H : rt_frames RT Σt1 = rt_frames RT Σc |- _ => rename H into FRT1 end.
  assert (FRSt1 : rt_frames RT Σt1 = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRT1; exact FRSc).
  assert (LVTH1 : rt_live RT Σt1 = (tk1, 3) :: (arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ) by (rewrite LVT1, LVc; reflexivity).
  assert (INT1 : In (tk1, 3) (rt_live RT Σt1)) by (rewrite LVT1; left; reflexivity).
  lazymatch goal with A : ART RT Σt1 ?mm |- cps _ (ASTA RT Σt1 _ _) _ =>
    assert (NCT1 : forall a, PF a -> a < tk1 \/ tk1 + 3 <= a)
      by (intros a Ha; apply (live_chunk_apart RT AF Σt1 mm [] tk1 3 ((arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ) (rt_live RT Σ) (rt_frames RT Σt1) usp a A);
          [ rewrite LVTH1; reflexivity | intros e He; cbn [app In]; right; right; right; exact He | reflexivity
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
          | apply (aclient_mono _ _ usp _ _ _ _ Ha); [exact (fun e He => He)| rewrite FRSt1; solve [frames_sub_tac]| lia] ]);
    (* [comment removed for export] *)
    pose proof (live_apart2 RT AF Σt1 mm tk1 3 na 32 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DTN1;
    pose proof (live_apart2 RT AF Σt1 mm tk1 3 arr 200 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DTA1;
    pose proof (live_apart2 RT AF Σt1 mm tk1 3 ns 14 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DTS1 end.
  lazymatch goal with A : ART RT Σt1 ?mm |- cps _ (ASTA RT Σt1 _ _) _ =>
    pose proof (af_live_range RT AF Σt1 mm tk1 3 A INT1) as (TKP1 & _ & _) end.       (* [comment removed for export] *)
  assert (NETN1 : na <> tk1) by (clear - DTN1; lia).
  assert (NETA1 : arr <> tk1) by (clear - DTA1; lia).
  assert (NETS1 : ns <> tk1) by (clear - DTS1; lia).
  chunk_facts RT AF GP tk1 3.
  fframe_chunk RT AF fr 0%nat 64 tk1 3.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof (gg_atof RT GG) as AT; unfold atof_contract in AT;
    eapply AT with (lo := lo) (s := tk1) (k := 75) (bs := [55; 53; 0]) (d := 0x4052c00000000000); rt_side idtac.
    all: lazymatch goal with
         | |- In _ TOKENS => unfold TOKENS; cbn [In]; clear; tauto
         | |- bytes_at _ _ _ _ => destruct TKC1 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; exact B
         | |- own_live _ _ _ => exists tk1, 3; split; [solve [in_live_tac] | cbn [length Z.of_nat]; lia]
         end. }
  unfold ret_st_fa0.
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  lazymatch goal with H : reg_get ?Fx fa0 = _ |- _ => rename H into FA01 end.
  (* [comment removed for export] *)
  lazymatch goal with |- context [ms_fcsr ?E] =>
    lazymatch E with entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?fcx _ _ => change (ms_fcsr E) with (frm_clear fcx) end end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ ?Fx _ _ _ ?mc _))) _ =>
    assert (NOBJ1 : numa_obj (rt_live RT S) mc na 50 arr [ival_w 45])
      by (split; [eexists; exact NAC| split; [eexists; exact ARC|]];
          split; [split; [solve [in_live_tac] | repeat split; first [assumption | lia]]|];
          split; [split; [solve [in_live_tac] | repeat split; first [assumption | lia]]|];
          split; [exact NANE|]; cbn [length Z.of_nat]; lia);
    assert (FV1 : freg_is Fx fa0 (ival_w 75))
      by (unfold freg_is; rewrite freg_get_same by reflexivity;
          lazymatch goal with |- context [fcvt_s_d _ (reg_get ?F0 ?r0)] => change (reg_get F0 r0) with (reg_get F0 fa0) end;
          rewrite FA01; apply bv_eq; vm_compute; reflexivity)
  end.
  eapply cps_seq.
  { eapply NADDF with (lo := lo) (na := na) (cap := 50) (arr := arr) (vals := [ival_w 45]) (v := ival_w 75).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - exact FV1.
    - exact NOBJ1.
    - cbn [length Z.of_nat]. lia.
    - lenv_tac.
    - lres_tac. }
  clear NAC ARC NOBJ1 FV1 FA01.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; pose proof (NCA _ Hx); pose proof (NCB _ Hx); repeat split; first [exact I | lia]]).
  lazymatch goal with H : numa_obj _ _ na _ arr _ |- _ => rename H into NOBJ1 end.
  cbn [app] in NOBJ1.
  lazymatch goal with H : rt_live RT ?S = rt_live RT Σt1 |- _ => rename H into LVA1; rename S into Σa1 end.
  lazymatch goal with H : rt_frames RT Σa1 = rt_frames RT Σt1 |- _ => rename H into FRA1 end.
  assert (FRSa1 : rt_frames RT Σa1 = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRA1; exact FRSt1).
  destruct NOBJ1 as ((npad1 & NAC) & (njunk1 & ARC) & _).
  unfold numa_cells, numa_arr_cells in NAC, ARC. cbn [map app length Z.of_nat Z.mul Z.sub Z.to_nat] in NAC, ARC.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
  assert (UC21 : unwind_okC mc (Z_to_bv 64 0xa85c8) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))) by
   (exists (bv_unsigned ra :: ras); split; [| rewrite unsigned_lit by lia; exact TRF1];
    rewrite !unsigned_lit by lia;
    apply (chain_ok_push mc (usp + -96) usp (bv_unsigned ra) (bv_unsigned s0) ras);
    [ lia | lia | unfold USTACK_TOP; lia
    | pose proof (bv_unsigned_in_range 64 ra); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | pose proof (bv_unsigned_in_range 64 s0); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | rewrite !Z_to_bv_bv_unsigned; exact FRtop
    | unfold uctx in UC; apply (chain_ok_keep ras m mc _ _ UC); intros aa Haa; apply AGF; subst PF; cbv beta; left; unfold usp in *; ul ]) end.
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FREE; unfold free_contractC in FREE; eapply FREE with (lo := lo) (p := tk1) (n := 3); rt_side idtac.
    all: lazymatch goal with |- unwind_okC _ _ _ _ => exact UC21 end. }
  clear TKC1 UC21.
  after_call RT AF.
  lazymatch goal with H : rt_live RT ?S = live_remove tk1 _ |- _ => rename H into LVF01; rename S into Σf1 end.
  lazymatch goal with H : rt_frames RT Σf1 = rt_frames RT Σa1 |- _ => rename H into FRFA1 end.
  assert (FRSf1 : rt_frames RT Σf1 = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRFA1; exact FRSa1).
  (* [comment removed for export] *)
  assert (LVF1 : rt_live RT Σf1 = (arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ).
  { lazymatch goal with A : ART RT Σt1 ?mm |- _ =>
      exact (live_after_free RT AF Σt1 mm tk1 3 _ (rt_live RT Σf1) A LVTH1 ltac:(lia) LVPN ltac:(rewrite LVF01, LVA1; reflexivity)) end. }
  clear LVF01.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LVF1; right; right; right; exact He | solve [frames_sub_tac]| lia]).
  (* [comment removed for export] *)
  assert (SPn : rt_sp0 RT Σf1 = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity).
  assert (CRn : rt_credit RT Σ - 1 <= rt_credit RT Σf1) by credit_tac.
  pose proof LVF1 as LVn. pose proof FRSf1 as FRSn_.
  repeat match goal with H : context [Σc] |- _ => clear H end. try clear Σc.
  repeat match goal with H : context [Σt1] |- _ => clear H end. try clear Σt1.
  repeat match goal with H : context [Σa1] |- _ => clear H end. try clear Σa1.
  repeat match goal with H : context [tk1] |- _ => clear H end. try clear tk1.
  rename Σf1 into Σc. rename LVn into LVc. rename FRSn_ into FRSc. rename SPn into SPc. rename CRn into CRc.
  try clear INNA. try clear INAR. try clear INS.
  assert (INNA : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; left; reflexivity).
  assert (INAR : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; left; reflexivity).
  assert (INS : In (ns, 14) (rt_live RT Σc)) by (rewrite LVc; right; right; left; reflexivity).
  ctx_gc RT.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof TOK2 as TK; unfold strtokSafe_gq_cps in TK; eapply TK with (lo := lo) (ns := ns) (tl := fr + 32) (w0 := z64).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - solve [in_live_tac].
    - exact NSC.
    - unfold optrF. split.
      2: { split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. unfold SEGTOP_A in *. split; [clear - FRSH; unfold parked in FRSH; lia| lia]. }
      exists fr, 0%nat. rewrite FRSc. change (fs_size 0) with 64.
      split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia).
      pose proof FSH as T; split_at T 4%nat T2; split_at T2 1%nat T3; destruct T2 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 8) with [Z_to_bv 8 0]; exact B.
    - exact TLC.
    - lenv_tac.
    - lres_tac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia | exact I]]).
  change (3 + 1) with 4 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 4) :: rt_live RT Σc |- _ => rename H into LVT2; rename S into Σt2; rename p into tk2 end.
  lazymatch goal with H : rw_cells asegs _ tk2 _ |- _ => rename H into TKC2 end.
  lazymatch goal with H : rw_cells asegs _ (fr + 32) _ |- _ => rename H into TLC end.
  cbv iota in TLC. change (10 =? 0) with false in TLC. cbv iota in TLC.
  cbn [str_cells app map] in TKC2.
  lazymatch goal with H : rt_frames RT Σt2 = rt_frames RT Σc |- _ => rename H into FRT2 end.
  assert (FRSt2 : rt_frames RT Σt2 = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRT2; exact FRSc).
  assert (LVTH2 : rt_live RT Σt2 = (tk2, 4) :: (arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ) by (rewrite LVT2, LVc; reflexivity).
  assert (INT2 : In (tk2, 4) (rt_live RT Σt2)) by (rewrite LVT2; left; reflexivity).
  lazymatch goal with A : ART RT Σt2 ?mm |- cps _ (ASTA RT Σt2 _ _) _ =>
    assert (NCT2 : forall a, PF a -> a < tk2 \/ tk2 + 4 <= a)
      by (intros a Ha; apply (live_chunk_apart RT AF Σt2 mm [] tk2 4 ((arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ) (rt_live RT Σ) (rt_frames RT Σt2) usp a A);
          [ rewrite LVTH2; reflexivity | intros e He; cbn [app In]; right; right; right; exact He | reflexivity
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
          | apply (aclient_mono _ _ usp _ _ _ _ Ha); [exact (fun e He => He)| rewrite FRSt2; solve [frames_sub_tac]| lia] ]);
    (* [comment removed for export] *)
    pose proof (live_apart2 RT AF Σt2 mm tk2 4 na 32 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DTN2;
    pose proof (live_apart2 RT AF Σt2 mm tk2 4 arr 200 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DTA2;
    pose proof (live_apart2 RT AF Σt2 mm tk2 4 ns 14 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DTS2 end.
  lazymatch goal with A : ART RT Σt2 ?mm |- cps _ (ASTA RT Σt2 _ _) _ =>
    pose proof (af_live_range RT AF Σt2 mm tk2 4 A INT2) as (TKP2 & _ & _) end.       (* [comment removed for export] *)
  assert (NETN2 : na <> tk2) by (clear - DTN2; lia).
  assert (NETA2 : arr <> tk2) by (clear - DTA2; lia).
  assert (NETS2 : ns <> tk2) by (clear - DTS2; lia).
  chunk_facts RT AF GP tk2 4.
  fframe_chunk RT AF fr 0%nat 64 tk2 4.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof (gg_atof RT GG) as AT; unfold atof_contract in AT;
    eapply AT with (lo := lo) (s := tk2) (k := 115) (bs := [49; 49; 53; 0]) (d := 0x405cc00000000000); rt_side idtac.
    all: lazymatch goal with
         | |- In _ TOKENS => unfold TOKENS; cbn [In]; clear; tauto
         | |- bytes_at _ _ _ _ => destruct TKC2 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; exact B
         | |- own_live _ _ _ => exists tk2, 4; split; [solve [in_live_tac] | cbn [length Z.of_nat]; lia]
         end. }
  unfold ret_st_fa0.
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  lazymatch goal with H : reg_get ?Fx fa0 = _ |- _ => rename H into FA02 end.
  (* [comment removed for export] *)
  lazymatch goal with |- context [ms_fcsr ?E] =>
    lazymatch E with entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?fcx _ _ => change (ms_fcsr E) with (frm_clear fcx) end end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ ?Fx _ _ _ ?mc _))) _ =>
    assert (NOBJ2 : numa_obj (rt_live RT S) mc na 50 arr [ival_w 45; ival_w 75])
      by (split; [eexists; exact NAC| split; [eexists; exact ARC|]];
          split; [split; [solve [in_live_tac] | repeat split; first [assumption | lia]]|];
          split; [split; [solve [in_live_tac] | repeat split; first [assumption | lia]]|];
          split; [exact NANE|]; cbn [length Z.of_nat]; lia);
    assert (FV2 : freg_is Fx fa0 (ival_w 115))
      by (unfold freg_is; rewrite freg_get_same by reflexivity;
          lazymatch goal with |- context [fcvt_s_d _ (reg_get ?F0 ?r0)] => change (reg_get F0 r0) with (reg_get F0 fa0) end;
          rewrite FA02; apply bv_eq; vm_compute; reflexivity)
  end.
  eapply cps_seq.
  { eapply NADDF with (lo := lo) (na := na) (cap := 50) (arr := arr) (vals := [ival_w 45; ival_w 75]) (v := ival_w 115).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - exact FV2.
    - exact NOBJ2.
    - cbn [length Z.of_nat]. lia.
    - lenv_tac.
    - lres_tac. }
  clear NAC ARC NOBJ2 FV2 FA02.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; pose proof (NCA _ Hx); pose proof (NCB _ Hx); repeat split; first [exact I | lia]]).
  lazymatch goal with H : numa_obj _ _ na _ arr _ |- _ => rename H into NOBJ2 end.
  cbn [app] in NOBJ2.
  lazymatch goal with H : rt_live RT ?S = rt_live RT Σt2 |- _ => rename H into LVA2; rename S into Σa2 end.
  lazymatch goal with H : rt_frames RT Σa2 = rt_frames RT Σt2 |- _ => rename H into FRA2 end.
  assert (FRSa2 : rt_frames RT Σa2 = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRA2; exact FRSt2).
  destruct NOBJ2 as ((npad2 & NAC) & (njunk2 & ARC) & _).
  unfold numa_cells, numa_arr_cells in NAC, ARC. cbn [map app length Z.of_nat Z.mul Z.sub Z.to_nat] in NAC, ARC.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
  assert (UC22 : unwind_okC mc (Z_to_bv 64 0xa85c8) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))) by
   (exists (bv_unsigned ra :: ras); split; [| rewrite unsigned_lit by lia; exact TRF1];
    rewrite !unsigned_lit by lia;
    apply (chain_ok_push mc (usp + -96) usp (bv_unsigned ra) (bv_unsigned s0) ras);
    [ lia | lia | unfold USTACK_TOP; lia
    | pose proof (bv_unsigned_in_range 64 ra); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | pose proof (bv_unsigned_in_range 64 s0); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | rewrite !Z_to_bv_bv_unsigned; exact FRtop
    | unfold uctx in UC; apply (chain_ok_keep ras m mc _ _ UC); intros aa Haa; apply AGF; subst PF; cbv beta; left; unfold usp in *; ul ]) end.
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FREE; unfold free_contractC in FREE; eapply FREE with (lo := lo) (p := tk2) (n := 4); rt_side idtac.
    all: lazymatch goal with |- unwind_okC _ _ _ _ => exact UC22 end. }
  clear TKC2 UC22.
  after_call RT AF.
  lazymatch goal with H : rt_live RT ?S = live_remove tk2 _ |- _ => rename H into LVF02; rename S into Σf2 end.
  lazymatch goal with H : rt_frames RT Σf2 = rt_frames RT Σa2 |- _ => rename H into FRFA2 end.
  assert (FRSf2 : rt_frames RT Σf2 = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRFA2; exact FRSa2).
  (* [comment removed for export] *)
  assert (LVF2 : rt_live RT Σf2 = (arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ).
  { lazymatch goal with A : ART RT Σt2 ?mm |- _ =>
      exact (live_after_free RT AF Σt2 mm tk2 4 _ (rt_live RT Σf2) A LVTH2 ltac:(lia) LVPN ltac:(rewrite LVF02, LVA2; reflexivity)) end. }
  clear LVF02.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LVF2; right; right; right; exact He | solve [frames_sub_tac]| lia]).
  (* [comment removed for export] *)
  assert (SPn : rt_sp0 RT Σf2 = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity).
  assert (CRn : rt_credit RT Σ - 1 <= rt_credit RT Σf2) by credit_tac.
  pose proof LVF2 as LVn. pose proof FRSf2 as FRSn_.
  repeat match goal with H : context [Σc] |- _ => clear H end. try clear Σc.
  repeat match goal with H : context [Σt2] |- _ => clear H end. try clear Σt2.
  repeat match goal with H : context [Σa2] |- _ => clear H end. try clear Σa2.
  repeat match goal with H : context [tk2] |- _ => clear H end. try clear tk2.
  rename Σf2 into Σc. rename LVn into LVc. rename FRSn_ into FRSc. rename SPn into SPc. rename CRn into CRc.
  try clear INNA. try clear INAR. try clear INS.
  assert (INNA : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; left; reflexivity).
  assert (INAR : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; left; reflexivity).
  assert (INS : In (ns, 14) (rt_live RT Σc)) by (rewrite LVc; right; right; left; reflexivity).
  ctx_gc RT.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof TOK3 as TK; unfold strtokSafe_gq_cps in TK; eapply TK with (lo := lo) (ns := ns) (tl := fr + 32) (w0 := z64).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - solve [in_live_tac].
    - exact NSC.
    - unfold optrF. split.
      2: { split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. unfold SEGTOP_A in *. split; [clear - FRSH; unfold parked in FRSH; lia| lia]. }
      exists fr, 0%nat. rewrite FRSc. change (fs_size 0) with 64.
      split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia).
      pose proof FSH as T; split_at T 4%nat T2; split_at T2 1%nat T3; destruct T2 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 8) with [Z_to_bv 8 0]; exact B.
    - exact TLC.
    - lenv_tac.
    - lres_tac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia | exact I]]).
  change (3 + 1) with 4 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 4) :: rt_live RT Σc |- _ => rename H into LVT3; rename S into Σt3; rename p into tk3 end.
  lazymatch goal with H : rw_cells asegs _ tk3 _ |- _ => rename H into TKC3 end.
  lazymatch goal with H : rw_cells asegs _ (fr + 32) _ |- _ => rename H into TLC end.
  cbv iota in TLC. change (0 =? 0) with true in TLC. cbv iota in TLC.
  cbn [str_cells app map] in TKC3.
  lazymatch goal with H : rt_frames RT Σt3 = rt_frames RT Σc |- _ => rename H into FRT3 end.
  assert (FRSt3 : rt_frames RT Σt3 = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRT3; exact FRSc).
  assert (LVTH3 : rt_live RT Σt3 = (tk3, 4) :: (arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ) by (rewrite LVT3, LVc; reflexivity).
  assert (INT3 : In (tk3, 4) (rt_live RT Σt3)) by (rewrite LVT3; left; reflexivity).
  lazymatch goal with A : ART RT Σt3 ?mm |- cps _ (ASTA RT Σt3 _ _) _ =>
    assert (NCT3 : forall a, PF a -> a < tk3 \/ tk3 + 4 <= a)
      by (intros a Ha; apply (live_chunk_apart RT AF Σt3 mm [] tk3 4 ((arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ) (rt_live RT Σ) (rt_frames RT Σt3) usp a A);
          [ rewrite LVTH3; reflexivity | intros e He; cbn [app In]; right; right; right; exact He | reflexivity
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
          | apply (aclient_mono _ _ usp _ _ _ _ Ha); [exact (fun e He => He)| rewrite FRSt3; solve [frames_sub_tac]| lia] ]);
    (* [comment removed for export] *)
    pose proof (live_apart2 RT AF Σt3 mm tk3 4 na 32 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DTN3;
    pose proof (live_apart2 RT AF Σt3 mm tk3 4 arr 200 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DTA3;
    pose proof (live_apart2 RT AF Σt3 mm tk3 4 ns 14 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DTS3 end.
  lazymatch goal with A : ART RT Σt3 ?mm |- cps _ (ASTA RT Σt3 _ _) _ =>
    pose proof (af_live_range RT AF Σt3 mm tk3 4 A INT3) as (TKP3 & _ & _) end.       (* [comment removed for export] *)
  assert (NETN3 : na <> tk3) by (clear - DTN3; lia).
  assert (NETA3 : arr <> tk3) by (clear - DTA3; lia).
  assert (NETS3 : ns <> tk3) by (clear - DTS3; lia).
  chunk_facts RT AF GP tk3 4.
  fframe_chunk RT AF fr 0%nat 64 tk3 4.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof (gg_atof RT GG) as AT; unfold atof_contract in AT;
    eapply AT with (lo := lo) (s := tk3) (k := 185) (bs := [49; 56; 53; 0]) (d := 0x4067200000000000); rt_side idtac.
    all: lazymatch goal with
         | |- In _ TOKENS => unfold TOKENS; cbn [In]; clear; tauto
         | |- bytes_at _ _ _ _ => destruct TKC3 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; exact B
         | |- own_live _ _ _ => exists tk3, 4; split; [solve [in_live_tac] | cbn [length Z.of_nat]; lia]
         end. }
  unfold ret_st_fa0.
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  lazymatch goal with H : reg_get ?Fx fa0 = _ |- _ => rename H into FA03 end.
  (* [comment removed for export] *)
  lazymatch goal with |- context [ms_fcsr ?E] =>
    lazymatch E with entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?fcx _ _ => change (ms_fcsr E) with (frm_clear fcx) end end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ ?Fx _ _ _ ?mc _))) _ =>
    assert (NOBJ3 : numa_obj (rt_live RT S) mc na 50 arr [ival_w 45; ival_w 75; ival_w 115])
      by (split; [eexists; exact NAC| split; [eexists; exact ARC|]];
          split; [split; [solve [in_live_tac] | repeat split; first [assumption | lia]]|];
          split; [split; [solve [in_live_tac] | repeat split; first [assumption | lia]]|];
          split; [exact NANE|]; cbn [length Z.of_nat]; lia);
    assert (FV3 : freg_is Fx fa0 (ival_w 185))
      by (unfold freg_is; rewrite freg_get_same by reflexivity;
          lazymatch goal with |- context [fcvt_s_d _ (reg_get ?F0 ?r0)] => change (reg_get F0 r0) with (reg_get F0 fa0) end;
          rewrite FA03; apply bv_eq; vm_compute; reflexivity)
  end.
  eapply cps_seq.
  { eapply NADDF with (lo := lo) (na := na) (cap := 50) (arr := arr) (vals := [ival_w 45; ival_w 75; ival_w 115]) (v := ival_w 185).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - exact FV3.
    - exact NOBJ3.
    - cbn [length Z.of_nat]. lia.
    - lenv_tac.
    - lres_tac. }
  clear NAC ARC NOBJ3 FV3 FA03.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; pose proof (NCA _ Hx); pose proof (NCB _ Hx); repeat split; first [exact I | lia]]).
  lazymatch goal with H : numa_obj _ _ na _ arr _ |- _ => rename H into NOBJ3 end.
  cbn [app] in NOBJ3.
  lazymatch goal with H : rt_live RT ?S = rt_live RT Σt3 |- _ => rename H into LVA3; rename S into Σa3 end.
  lazymatch goal with H : rt_frames RT Σa3 = rt_frames RT Σt3 |- _ => rename H into FRA3 end.
  assert (FRSa3 : rt_frames RT Σa3 = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRA3; exact FRSt3).
  destruct NOBJ3 as ((npad3 & NAC) & (njunk3 & ARC) & _).
  unfold numa_cells, numa_arr_cells in NAC, ARC. cbn [map app length Z.of_nat Z.mul Z.sub Z.to_nat] in NAC, ARC.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
  assert (UC23 : unwind_okC mc (Z_to_bv 64 0xa85c8) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))) by
   (exists (bv_unsigned ra :: ras); split; [| rewrite unsigned_lit by lia; exact TRF1];
    rewrite !unsigned_lit by lia;
    apply (chain_ok_push mc (usp + -96) usp (bv_unsigned ra) (bv_unsigned s0) ras);
    [ lia | lia | unfold USTACK_TOP; lia
    | pose proof (bv_unsigned_in_range 64 ra); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | pose proof (bv_unsigned_in_range 64 s0); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | rewrite !Z_to_bv_bv_unsigned; exact FRtop
    | unfold uctx in UC; apply (chain_ok_keep ras m mc _ _ UC); intros aa Haa; apply AGF; subst PF; cbv beta; left; unfold usp in *; ul ]) end.
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FREE; unfold free_contractC in FREE; eapply FREE with (lo := lo) (p := tk3) (n := 4); rt_side idtac.
    all: lazymatch goal with |- unwind_okC _ _ _ _ => exact UC23 end. }
  clear TKC3 UC23.
  after_call RT AF.
  lazymatch goal with H : rt_live RT ?S = live_remove tk3 _ |- _ => rename H into LVF03; rename S into Σf3 end.
  lazymatch goal with H : rt_frames RT Σf3 = rt_frames RT Σa3 |- _ => rename H into FRFA3 end.
  assert (FRSf3 : rt_frames RT Σf3 = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRFA3; exact FRSa3).
  (* [comment removed for export] *)
  assert (LVF3 : rt_live RT Σf3 = (arr, 200) :: (na, 32) :: (ns, 14) :: rt_live RT Σ).
  { lazymatch goal with A : ART RT Σt3 ?mm |- _ =>
      exact (live_after_free RT AF Σt3 mm tk3 4 _ (rt_live RT Σf3) A LVTH3 ltac:(lia) LVPN ltac:(rewrite LVF03, LVA3; reflexivity)) end. }
  clear LVF03.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LVF3; right; right; right; exact He | solve [frames_sub_tac]| lia]).
  (* [comment removed for export] *)
  assert (SPn : rt_sp0 RT Σf3 = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity).
  assert (CRn : rt_credit RT Σ - 1 <= rt_credit RT Σf3) by credit_tac.
  pose proof LVF3 as LVn. pose proof FRSf3 as FRSn_.
  repeat match goal with H : context [Σc] |- _ => clear H end. try clear Σc.
  repeat match goal with H : context [Σt3] |- _ => clear H end. try clear Σt3.
  repeat match goal with H : context [Σa3] |- _ => clear H end. try clear Σa3.
  repeat match goal with H : context [tk3] |- _ => clear H end. try clear tk3.
  rename Σf3 into Σc. rename LVn into LVc. rename FRSn_ into FRSc. rename SPn into SPc. rename CRn into CRc.
  try clear INNA. try clear INAR. try clear INS.
  assert (INNA : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; left; reflexivity).
  assert (INAR : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; left; reflexivity).
  assert (INS : In (ns, 14) (rt_live RT Σc)) by (rewrite LVc; right; right; left; reflexivity).
  ctx_gc RT.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof TOKE as TK; unfold strtokSafe_end_cps in TK; eapply TK with (lo := lo) (tl := fr + 32).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold optrF. split.
      2: { split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. unfold SEGTOP_A in *. split; [clear - FRSH; unfold parked in FRSH; lia| lia]. }
      exists fr, 0%nat. rewrite FRSc. change (fs_size 0) with 64.
      split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia).
      pose proof FSH as T; split_at T 4%nat T2; split_at T2 1%nat T3; destruct T2 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 8) with [Z_to_bv 8 0]; exact B.
    - exact TLC.
    - lenv_tac.
    - lres_tac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia] | exact I]).
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x90f28; 0x91894; 0x91220; 0xd934c; 0x91c0c; 0x62054; 0x90e84; 0x68ab8].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
  assert (UC3 : unwind_okC mc (Z_to_bv 64 0xa85e4) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))) by
   (exists (bv_unsigned ra :: ras); split; [| rewrite unsigned_lit by lia; exact TRF2];
    rewrite !unsigned_lit by lia;
    apply (chain_ok_push mc (usp + -96) usp (bv_unsigned ra) (bv_unsigned s0) ras);
    [ lia | lia | unfold USTACK_TOP; lia
    | pose proof (bv_unsigned_in_range 64 ra); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | pose proof (bv_unsigned_in_range 64 s0); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | rewrite !Z_to_bv_bv_unsigned; exact FRtop
    | unfold uctx in UC; apply (chain_ok_keep ras m mc _ _ UC); intros aa Haa; apply AGF; subst PF; cbv beta; left; unfold usp in *; ul ]) end.
  assert (NENS : na <> ns) by (clear - DSN; unfold parked in DSN; lia).
  assert (NEAS : arr <> ns) by (clear - DSA; unfold parked in DSA; lia).
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FREE; unfold free_contractC in FREE; eapply FREE with (lo := lo) (p := ns) (n := 14); rt_side idtac.
    all: lazymatch goal with |- unwind_okC _ _ _ _ => exact UC3 end. }
  clear NSC UC3.
  after_call RT AF.
  lazymatch goal with H : rt_live RT ?S = live_remove ns _ |- _ => rename H into LVG0; rename S into Σg end.
  lazymatch goal with H : rt_frames RT Σg = rt_frames RT Σc |- _ => rename H into FRGC end.
  assert (FRSg : rt_frames RT Σg = (fr, 0%nat) :: rt_frames RT Σ) by (rewrite FRGC; exact FRSc).
  assert (LVG : rt_live RT Σg = (arr, 200) :: (na, 32) :: rt_live RT Σ).
  { rewrite LVG0, LVc. rewrite !lrm_cons. cbn [fst].
    replace (arr =? ns) with false by (symmetry; apply Z.eqb_neq; exact NEAS).
    replace (na =? ns) with false by (symmetry; apply Z.eqb_neq; exact NENS).
    rewrite Z.eqb_refl. f_equal. f_equal.
    assert (FRESH : forall e, In e (rt_live RT Σ) -> fst e <> ns).
    { intros [q k] He. cbn [fst]. pose proof (LVP q k He) as Hk.
      lazymatch goal with A : ART RT Σc ?mm |- _ =>
        pose proof (af_live_disj RT AF Σc mm ns 14 q k [(arr, 200); (na, 32)] (rt_live RT Σ) A LVc ltac:(cbn [app In]; right; right; exact He)) as D end.
      clear - D Hk. lia. }
    clear - FRESH. induction (rt_live RT Σ) as [|e l IH]; [reflexivity|].
    rewrite lrm_cons. replace (fst e =? ns) with false by (symmetry; apply Z.eqb_neq; apply FRESH; left; reflexivity).
    f_equal. apply IH. intros e' He'. apply FRESH. right. exact He'. }
  clear LVG0.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LVG; right; right; exact He | solve [frames_sub_tac]| lia]).
  (* [comment removed for export] *)
  assert (SPn : rt_sp0 RT Σg = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity).
  assert (CRn : rt_credit RT Σ - 1 <= rt_credit RT Σg) by credit_tac.
  pose proof LVG as LVn. pose proof FRSg as FRSn_.
  repeat match goal with H : context [Σc] |- _ => clear H end. try clear Σc.
  repeat match goal with H : context [ns] |- _ => clear H end. try clear ns.
  rename Σg into Σc. rename LVn into LVc. rename FRSn_ into FRSc. rename SPn into SPc. rename CRn into CRc.
  try clear INNA. try clear INAR. try clear INS.
  assert (INNA : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; left; reflexivity).
  assert (INAR : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; left; reflexivity).
  ctx_gc RT.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0xa866c].
  frame_release RT AF GP MST Σ fr 0%nat 64 PF AGF PFS usp lo 0xa8674
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 96, usp)] (@nil Z).
  try (lazymatch goal with ST' : stk asegs _ lo (usp + -96) |- _ => release_frame FR ST' usp end).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with
  | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
  end.
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (NOBJ : numa_obj (rt_live RT S) mc na 50 arr (map ival_w EDGE_VALS))
      by (split; [eexists; exact NAC| split; [eexists; exact ARC|]];
          split; [split; [solve [in_live_tac] | repeat split; first [assumption | lia]]|];
          split; [split; [solve [in_live_tac] | repeat split; first [assumption | lia]]|];
          split; [exact NANE|]; cbn [length Z.of_nat map EDGE_VALS]; lia) end.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, na, arr end.
  split.
  2: { unfold numa_live. change (4 * 50) with 200.
       split; [rewrite LV2, LVc; reflexivity|]. split; [exact FRS2|].
       split; [first [exact SP2 | rewrite SP2; exact SPc]|].
       rewrite CR2. clear - CRc. lia. }
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| assumption]]| split; assumption]|].
  split; [intros a Ha _; exact (AGF a Ha)| exact NOBJ].
Qed.
End PARSE_C0.
