(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes NodesMM NodesInv Decode Arr MState Mem Cells Frame Exec RegsEquiv ImplEqv ImplBridge.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require PropExec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog MSafe KInv KLink KLinkC MI_Cnt LB_Sum LB_Logic LB_Kernel LB_Inv LB_StmtA LB_Raw LB_Alloc LB_Count LB_Init MPos Path PathQ CtxMono MFail MRefuse MI_Contracts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocRep MallocTree MallocBlocks MallocHINV Malloc_iface MallocFacts_A MallocFacts_B MallocFacts_AM MTight MTight2.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require MallocFacts_inv2 MallocFacts_inv4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.RU Require Import RMallocRep RImage RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec RBridge.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Gap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim ShapeAlg SRealizes ShapeUpto SeqExec Hoare RefMemcpyLib LibIface LibBudget U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ Require Import MallocIfaceStmt MallocInstU1 MallocDrvIfaceU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import AcLia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma AMpre_strip {resv} st : @AMpre_g _ resv st -> @AMpre_g _ resv (strip st).
Proof.
  intros H. destruct H as [A1 A2 A3 A4 A5 A6 A7 [L1 L2 L3 L4] A9 A10 A11 A12 A13 A14 A15 A16 [P1 P2]].
  split; cbn; try assumption.
  - split; cbn; assumption.
  - split; [exact P1|]. intros rid Hrid. split; [exact (proj1 (P2 rid Hrid))|]. apply lookup_empty.
Qed.

Lemma RHEAP_facts s LB m :
  RHEAP s LB m -> exists st LB0, strip st = ps_m s /\ Permutation LB0 LB /\ @MFACTS_g ref_reserved st LB0 /\ @AMpre_g _ ref_reserved (ps_m s).
Proof.
  intros (st & LB0 & HP & Hst & MR & [BLK AR]). exists st, LB0. split; [exact Hst|]. split; [exact HP|]. split.
  - exact (MallocFacts_inv2.areach_facts_proof st LB0 AR).
  - rewrite <- Hst. apply AMpre_strip. exact (MallocFacts_inv4.areach_ampre_proof st LB0 AR).
Qed.

Lemma RHEAP_tight_facts s LB m : RHEAP s LB m ->
  fact_active (ps_m s) /\ fact_slots (ps_m s) /\ @AMpre_g _ ref_reserved (ps_m s) /\ FLH (ps_m s).
Proof.
  intros HH. destruct (RHEAP_facts s LB m HH) as (st & LB0 & Hst & _ & MF & AMP).
  rewrite <- Hst. split; [exact (mf_active _ _ MF)|]. split; [exact (mf_slots _ _ MF)|].
  rewrite Hst. split; [exact AMP| exact (FLH_of_AMpre _ AMP)].
Qed.

Theorem ainv0_owned_proof : ainv0_owned_stmt.
Proof.
  intros A M mo a _ [ST|(OFF & R & _)] NI; [| exact R].
  exfalso. apply NI. rewrite in_ranges_img. pose proof (mng_static_img a ST). unfold RRW_LO, RIMG_LO, RIMG_HI in *. lia.
Qed.

Lemma a_invX_frame A M M' mo mo' : a_invX A M mo ->
  (forall a : word, a_owned A (bv_unsigned a) -> M' a = M a) ->
  (forall a : word, M a <> None -> M' a <> None) ->
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> a_invX A M' mo'.
Proof.
  intros (HH & HL & HK) OW DEF EV EL. split; [| split; [rewrite EL; exact HL| rewrite EV; exact HK]].
  apply (RHEAP_frame_pw _ _ (got_clear M) (got_clear M') HH).
  - intros a Ha. unfold got_clear. destruct (in_gotb (wa a)); [reflexivity|]. apply OW.
    unfold wa. rewrite unsigned_lit; [exact Ha|]. destruct Ha as [ST|(_ & R & _)]; [pose proof (mng_static_img a ST); unfold RRW_LO, RIMG_HI in *; lia| pose proof ac_bounds_lit as ?ACBL; lia].
  - intros a Ha. apply got_clear_on. exact Ha.
  - apply wmono_of_def. intros a. unfold got_clear. destruct (in_gotb a); [auto| apply DEF].
Qed.

Theorem a_inv0_frame_proof : a_inv0_frame_stmt.
Proof.
  intros A M M' mo mo' (AX & E1 & E2 & E3) OW DEF EV EL. split; [| auto]. eapply a_invX_frame; eauto.
Qed.

Theorem mi_free_T_proof : mi_free_T_stmt.
Proof.
  intros fx A R M mo p n sp ret K AI T SM RO CR A0 HP SPC SR SOW HK.
  pose proof AI as (HH & _). destruct (RHEAP_tight_facts _ _ _ HH) as (FA & FS & AMP & FH).
  apply (L_free_gen TIGHT fx A R M mo p n sp ret K AI SM RO CR A0 HP SPC SR SOW T).
  - intros slot g idx SL. destruct (FS slot g idx SL) as (b & GM & _ & _ & IDX).
    pose proof (T g b GM) as (L0 & _). apply (tight_free _ slot g idx b FH T SL GM). lia.
  - intros A' R' M' mo' AI' T'. apply HK; assumption.
Qed.

Lemma lall_and {R0} (P Q : R0 -> Prop) : forall (t : Malloc.M R0), lall P t -> lall Q t -> lall (fun r => P r /\ Q r) t.
Proof.
  induction t as [r|e k IH]; intros HP HQ; cbn in *; [auto|].
  destruct (CtxMono.is_undef e); [exact I|]. intros z. apply IH; auto.
Qed.

Lemma tight_lall_of A M mo n : a_inv A M mo -> a_tight A -> (MNG_BIG <= n \/ (n = 65536 /\ a_fresh44 A)) ->
  lall (fun r => TIGHT (fst r) /\ c_init_done (s_ctx (fst r)) = 1) (cmalloc (ps_m (a_s A)) n).
Proof.
  intros (HH & INIT & _) T CASE. destruct (RHEAP_tight_facts _ _ _ HH) as (FA & FS & AMP & FH).
  destruct CASE as [BIG|[-> (F1 & F2 & _)]].
  - apply lall_and.
    + eapply lall_mono; [| apply (tight_malloc_big _ n AMP T)]; [intros r Hr; exact Hr|]. unfold MNG_BIG in BIG. exact BIG.
    + eapply lall_mono; [| apply (cmalloc_init_kept _ n INIT)]. intros r [_ Hr]. exact Hr.
  - exact (tight_malloc_65536 _ AMP T F1 F2).
Qed.

Theorem mi_malloc_T_proof : mi_malloc_T_stmt.
Proof.
  intros fx A R M mo n sp ret Ks AI T CASE SM RO CR A0 HN SPC SR SOW ROOM KS.
  destruct (a_inv_X A M mo AI) as [AX INIT].
  apply (L_malloc mng_auxv_off TIGHT fx A R M mo n sp ret Ks AX (or_introl INIT) (fun F : False => match F with end)
           (tight_lall_of A M mo n AI T CASE) SM RO CR A0 HN SPC SR ROOM).
  intros A' R' M' mo' q AI' T'. apply KS; assumption.
Qed.

Lemma bytes_at_of_rdn (m : LibIface.mem) : forall bs a,
  CJ.Lib.PropExec.rdn rsegs m (wa a) (length bs) = Some bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at rsegs m a bs.
Proof.
  induction bs as [|b bs IH]; intros a RD A0 A1.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [length] in RD, A1. rewrite rdn_unfold in RD. destruct (mrd rsegs m (wa a)) as [b0|] eqn:E0; [| discriminate RD].
    rewrite wa_succ in RD. destruct (CJ.Lib.PropExec.rdn rsegs m (wa (a + 1)) (length bs)) as [r|] eqn:E1; [| discriminate RD].
    inversion RD; subst. specialize (IH (a + 1) E1 ltac:(lia) ltac:(lia)). destruct IH as (_ & _ & IH).
    split; [lia|]. split; [cbn [length]; lia|]. intros [|i] Hi.
    + rewrite Z.add_0_r. exact E0.
    + cbn [nth_error]. rewrite <- (IH i ltac:(cbn [length] in Hi; lia)). f_equal. f_equal. lia.
Qed.

Lemma dcell_bytes_at (m : LibIface.mem) a v : dcell m a 8 v -> 0 <= a -> a + 8 <= 2 ^ 64 -> bytes_at rsegs m a (le8 (wz v)).
Proof.
  intros D A0 A1. apply bytes_at_of_rdn; [| exact A0| cbn; lia]. unfold dcell in D. change SEGS with rsegs in D. unfold wa.
  rewrite <- CJ.Lib.PropExec.ov_rdn. rewrite <- PropExec.ov_rdn in D. exact D.
Qed.

Lemma wr_at_of_empty (m : LibIface.mem) A n :
  (forall i, (i < n)%nat -> wview rsegs (fun _ => None) (wa (A + Z.of_nat i)) <> None) -> 0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  wr_at rsegs m A (Z.of_nat n).
Proof.
  intros W A0 A1. split; [lia|]. split; [lia|]. intros i Hi. specialize (W (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in W by lia.
  unfold wview in *. destruct (m (wa (A + i))); [discriminate| exact W].
Qed.

Lemma wr_at_auxv_cell (m : LibIface.mem) : wr_at rsegs m RAUXV_CELL 8.
Proof.
  apply (wr_at_of_empty m RAUXV_CELL 8); [| unfold RAUXV_CELL; lia| unfold RAUXV_CELL; lia]. unfold RAUXV_CELL.
  intros i Hi. destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [| | | | | | | | lia];
    match goal with |- ?x <> None => let y := eval vm_compute in x in change x with y end; discriminate.
Qed.

Lemma bytes_at_app (m : LibIface.mem) a bs1 bs2 :
  bytes_at rsegs m a bs1 -> bytes_at rsegs m (a + Z.of_nat (length bs1)) bs2 -> bytes_at rsegs m a (bs1 ++ bs2).
Proof.
  intros (A0 & A1 & R1) (B0 & B1 & R2). split; [lia|]. split; [rewrite length_app; lia|].
  intros i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length bs1)) as [L|G].
  - rewrite nth_error_app1 by exact L. apply R1. exact L.
  - rewrite nth_error_app2 by exact G. rewrite <- (R2 (i - length bs1)%nat ltac:(lia)). f_equal. f_equal. lia.
Qed.

Lemma auxv_bytes (m : LibIface.mem) av ws :
  (forall i, (i < length ws)%nat -> dcell m (av + 8 * Z.of_nat i) 8 (nth i ws 0)) ->
  0 <= av -> av + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  bytes_at rsegs m av (u64s (map wz ws)).
Proof.
  revert av. induction ws as [|w ws IH]; intros av D A0 A1.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [map u64s flat_map]. change (flat_map le8 (map wz ws)) with (u64s (map wz ws)). apply bytes_at_app.
    + apply dcell_bytes_at; [| lia| cbn [length] in A1; lia]. specialize (D 0%nat ltac:(cbn; lia)). cbn [nth Z.of_nat Z.mul] in D. rewrite Z.add_0_r in D. exact D.
    + replace (Z.of_nat (length (le8 (wz w)))) with 8 by reflexivity. apply IH; [| lia| cbn [length] in A1; lia].
      intros i Hi. specialize (D (S i) ltac:(cbn; lia)). cbn [nth] in D. replace (av + 8 + 8 * Z.of_nat i) with (av + 8 * Z.of_nat (S i)) by lia. exact D.
Qed.

Lemma rauxv_full_of_mng_auxv (m : LibIface.mem) sp : mng_auxv m sp -> rauxv_full m sp rr_secret.
Proof.
  intros (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AVC & AVL & RND & CE & SAV & AVH & SR & RH & XS).
  pose proof XS as XS'. rewrite !Forall_cons_iff in XS'. destruct XS' as (X3 & X4 & X5 & X16 & X6 & X11 & X12 & X23 & XR & _).
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd.
  split; [| split; [| split; [| pose proof ac_bounds_lit as ?ACBL; repeat split; lia]]].
  - split; [split; [cbn; exact (conj I I)|]| apply wr_at_auxv_cell].
    cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply dcell_bytes_at; [exact AVC| unfold RAUXV_CELL; lia| unfold RAUXV_CELL; lia].
  - unfold auxv_list. apply (auxv_bytes m av (auxv_words x3 x4 x5 x16 x6 x11 x12 x23 rnd)); [exact AVL| pose proof ac_bounds_lit as ?ACBL; lia| cbn [auxv_words length]; lia].

  - apply dcell_bytes_at; [exact RND| pose proof ac_bounds_lit as ?ACBL; lia| lia].
Qed.

Theorem mi_malloc_first_proof : mi_malloc_first_stmt.
Proof.
  intros fx A R M mo n sp ret Ks (AX & LB0 & P0 & B0) AUXV T -> F44 LIVE0 SM RO CR A0 SPC SR SOW KS.
  pose proof AX as (HH & _). destruct (RHEAP_tight_facts _ _ _ HH) as (FA & FS & AMP & FH).
  pose proof F44 as (F1 & F2 & _).
  assert (HN : 0 <= 65536 <= MNG_NMAX) by (unfold MNG_NMAX, LIB_NMAX; lia).
  assert (ROOM : a_room A 65536).
  { left. unfold a_live. rewrite LB0, P0. change (mng_size_class 65536) with 44. cbn [map count_class_f]. unfold MNG_BIG, MMAP_THRESHOLD, lib_caps, CAP_SMALL. change (44 + 1 <? 4) with false. cbn. lia. }
  apply (L_malloc (AuxvMode True) TIGHT fx A R M mo 65536 sp ret Ks AX (or_intror I)
           (fun _ => rauxv_full_of_mng_auxv M sp AUXV) (tight_malloc_65536 _ AMP T F1 F2) SM RO CR A0 HN SPC SR ROOM).
  intros A' R' M' mo' q AI' T'. apply KS; assumption.
Qed.

Definition PL0 : Z -> Z := fun c => if c =? 63 then LIB_BIGCAP / BIGUNIT + 1 else lib_caps c.
Definition NR0 : Z := 4.
Definition RBY0 : Z := Gap.zsum (fun e => bv_unsigned (snd e)) (segments_reserved SEGS).
Lemma RBY0_small : 0 <= RBY0 <= 2 ^ 21. Proof. unfold RBY0. vm_compute. split; discriminate. Qed.
Definition ETOT0 : Z := NE PL0 + Z.of_nat (MALLOC_DEPTH + 0).

Lemma NE_PL0 : NE PL0 = 128978. Proof. vm_compute. reflexivity. Qed.
Lemma NMETA_PL0 : NMETA PL0 = 15. Proof. vm_compute. reflexivity. Qed.
Lemma PHI_PL0 : PHI PL0 = 3606013952. Proof. vm_compute. reflexivity. Qed.
Lemma DEPTH_val : Z.of_nat (MALLOC_DEPTH + 0) = 528. Proof. vm_compute. reflexivity. Qed.

Lemma CEIL_FLOOR : 93822836363264 <= alloc_ceiling - bottomup_floor.
Proof. pose proof ac_bounds_lit. rewrite bottomup_floor_val. lia. Qed.

Lemma mmap_len_mono a b : a <= b -> mmap_len a <= mmap_len b.
Proof. intros H. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

Lemma GAPOK_PL0 n : 0 <= n <= MNG_NMAX -> GAPOK n 15 ETOT0 NR0 RBY0.
Proof.
  intros Hn n' Hn'. pose proof RBY0_small as HR. unfold ETOT0, NR0 in *. rewrite NE_PL0, DEPTH_val. unfold LBUDGET.
  assert (B : n' <= 276824064).
  { destruct Hn' as [_ Hn']. eapply Z.le_trans; [exact Hn'|].
    change 276824064 with (mmap_len (LENMAX (2 ^ 28) 15)). apply mmap_len_mono.
    unfold LENMAX, LRW, MNG_NMAX, LIB_NMAX in *. lia. }
  assert (STEP : (RBY0 + 2 ^ 34) / n' + (2 * (4 + (128978 + 528)) + 1) <= 93822836363264 / n').
  { rewrite <- Z.div_add by lia. apply Z.div_le_mono; [lia|]. nia. }
  assert (MONO : 93822836363264 / n' <= (alloc_ceiling - bottomup_floor) / n').
  { apply Z.div_le_mono; [lia| exact CEIL_FLOOR]. }
  lia.
Qed.

Lemma caps_ok_PL0 : caps_ok PL0 LIB_BIGCAP NR0 RBY0.
Proof.
  exists 15, ETOT0. pose proof RBY0_small as HR. unfold ETOT0, NR0. rewrite NMETA_PL0, NE_PL0, PHI_PL0, DEPTH_val.
  repeat split; try (unfold LIB_BIGCAP, LBUDGET, BIGUNIT; try rewrite BIGUNIT_val; lia).
  - intros n Hn. pose proof (GAPOK_PL0 n Hn) as G. unfold ETOT0, NR0, RBY0 in G. rewrite NE_PL0, DEPTH_val in G. exact G.
  - rewrite BIGUNIT_val. unfold LIB_BIGCAP, LBUDGET. lia.
  - intros c. unfold PL0, lib_caps, CAP_NODE, CAP_SMALL, LIB_BIGCAP. rewrite BIGUNIT_val. destruct (c =? 63); [| destruct (c <? 4)]; cbn; lia.
Qed.

Definition A0 : mstateA := MKA (ps_init (reservedZ rsegs)) [] lib_caps LIB_BIGCAP.

Lemma RSV_main mo : mng_main_model mo -> RSV NR0 RBY0 (m_vmmaps mo) /\ LBUDGET <= vm_limit (m_vmmaps mo).
Proof.
  intros MM. unfold RSV. rewrite (mo_resv mo MM). split; [| unfold LBUDGET; exact (mo_lim mo MM)].
  split; [vm_compute; discriminate| unfold RBY0; lia].
Qed.

Lemma KL_main mo : mng_main_model mo -> mstd' mo -> KInv.KL (led_init (reservedZ rsegs)) 0 mo.
Proof.
  intros MM (Hh & Hl & Hm & _). pose proof (mo_sb mo MM) as (Blo & Bhi & Bal). pose proof (mo_sbhi mo MM) as SBH.
  assert (RT : reserved_top (segments_reserved SEGS) = RIMG_HI) by (vm_compute; reflexivity). unfold RIMG_HI in RT.
  constructor.
  - split; assumption.
  - exact Hh.
  - rewrite (mo_maps mo MM). split; [intros e []| apply pwdisj_nil].
  - rewrite (mo_resv mo MM). reflexivity.
  - rewrite (mo_resv mo MM). intros e Hin. pose proof (reserved_top_ge' _ _ Hin) as G. change SEGS with rsegs in RT. unfold ehi. change Ubsan.M.loaded_segments with rsegs in Blo. lia.
  - change SEGS with rsegs in RT. change Ubsan.M.loaded_segments with rsegs in Blo. rewrite RT in Blo. rewrite (mo_brk mo MM).
    unfold PGSZ, page_size in *. lia.
  - intros b l [].
  - intros b l k [].
  - apply List.NoDup_nil.
  - intros b l H. discriminate H.
  - cbn. split; [exact (mo_brk mo MM)| reflexivity].
Qed.

Lemma kpart_main mo : mng_main_model mo -> kpart (ps_init (reservedZ rsegs)) [] PL0 NR0 RBY0 (m_vmmaps mo).
Proof.
  intros MM. destruct (RSV_main mo MM) as [RS LIM]. split; [| split; [exact LIM| exact RS]].
  intros mo' EV SM'.
  assert (MM' : mng_main_model mo').
  { destruct SM' as (Hh & Hl & Hm & Hc). destruct MM; constructor; rewrite ?EV; auto. }
  pose proof (KL_main mo' MM' SM') as HK.
  split.
  - split; [| split; [apply List.NoDup_nil| exact I]]. exists (led_init (reservedZ rsegs)). split; [apply creach_init|]. split; [exact HK|]. intros c [].
  - split.
    + exists (minit rr_secret (reservedZ rsegs)), (led_init (reservedZ rsegs)), [], (fun _ => []).
      split; [reflexivity|]. split; [apply INVL_init; pose proof rr_secret_range; lia|]. split; [apply SINV_minit|]. split; [apply AQ_minit; intros c; unfold PL0, lib_caps, CAP_NODE, CAP_SMALL, LIB_BIGCAP; rewrite BIGUNIT_val; destruct (c =? 63); [| destruct (c <? 4)]; cbn; lia|].
      split; [exact HK|]. split; [| apply Permutation_refl].
      unfold LI, nmaps, vm_live_bytes. rewrite (mo_maps mo' MM'). vm_compute. split; discriminate.
    + rewrite PHI_PL0. unfold R63X, zsum, LBUDGET. cbn. lia.
Qed.

Lemma length_w2le n (w : word) : length (word_to_le_bytes n w) = n.
Proof. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

Lemma dcell_bytes (m : LibIface.mem) a n v : dcell m a n v -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  bytes_at rsegs m a (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros D A0 A1. apply bytes_at_of_rdn; [| exact A0| rewrite length_w2le; exact A1]. rewrite length_w2le.
  unfold dcell in D. change SEGS with rsegs in D. unfold wa. rewrite <- CJ.Lib.PropExec.ov_rdn. rewrite <- PropExec.ov_rdn in D. exact D.
Qed.

Lemma bytes_at_got_clear (m : LibIface.mem) a bs :
  bytes_at rsegs m a bs -> (a + Z.of_nat (length bs) <= RGOT_SSP \/ RGOT_SSP + 8 <= a) -> bytes_at rsegs (got_clear m) a bs.
Proof.
  intros (A0 & A1 & RD) OFF. split; [exact A0|]. split; [exact A1|]. intros i Hi. rewrite <- (RD i Hi).
  unfold mrd. rewrite got_clear_off; [reflexivity|]. unfold wa. rewrite unsigned_lit by lia. lia.
Qed.

Definition wview_okb (A : Z) (n : nat) : bool :=
  forallb (fun i => match wview rsegs (fun _ => None) (wa (A + Z.of_nat i)) with Some _ => true | None => false end) (seq 0 n).

Lemma wr_at_img_check (m : LibIface.mem) A n : wview_okb A n = true -> 0 <= A -> A + Z.of_nat n <= 2 ^ 64 -> wr_at rsegs m A (Z.of_nat n).
Proof.
  intros C A0 A1. apply wr_at_of_empty; [| exact A0| exact A1]. intros i Hi. unfold wview_okb in C. rewrite forallb_forall in C.
  specialize (C i ltac:(apply in_seq; lia)). destruct (wview rsegs (fun _ => None) (wa (A + Z.of_nat i))); [discriminate| discriminate C].
Qed.

Definition rom_okb (A : Z) (bs : list byte) : bool :=
  forallb (fun i => match CJ.Lib.PropExec.seg_rom rsegs (wa (A + Z.of_nat i)), nth_error bs i with Some b, Some b' => bv_eqb b b' | _, _ => false end) (seq 0 (length bs)).

Lemma bytes_at_rom (m : LibIface.mem) A bs : rom_okb A bs = true -> (forall i, (i < length bs)%nat -> m (wa (A + Z.of_nat i)) = None) ->
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at rsegs m A bs.
Proof.
  intros C NONE A0 A1. split; [exact A0|]. split; [exact A1|]. intros i Hi. unfold mrd. rewrite (NONE i Hi).
  unfold rom_okb in C. rewrite forallb_forall in C. specialize (C i ltac:(apply in_seq; lia)).
  destruct (CJ.Lib.PropExec.seg_rom rsegs (wa (A + Z.of_nat i))) as [b|]; [| discriminate C]. destruct (nth_error bs i) as [b'|]; [| discriminate C].
  apply bv_eqb_eq in C. subst. reflexivity.
Qed.

Lemma rw_cells_intro (m : LibIface.mem) A cs :
  cells_wf cs -> bytes_at rsegs m A (cells_bytes cs) -> wr_at rsegs m A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m A cs.
Proof. intros. split; [split|]; assumption. Qed.

Lemma main_mem_cells M : mng_main_mem M -> exists auxv : Z,
  (forall a : word, 0x122820 <= bv_unsigned a < 0x122bc8 -> got_clear M a = None)
  /\ rw_cells rsegs (got_clear M) 0x1226a8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)]
  /\ rw_cells rsegs (got_clear M) 0x1226b0 [C8 (wz auxv); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                          C8 (Z_to_bv 64 4096); Cells.CB 48 (repeat (Z_to_bv 8 0) 48)]
  /\ rw_cells rsegs (got_clear M) 0xeee10 [C8 (Z_to_bv 64 0x122688)]
  /\ rw_cells rsegs (got_clear M) 0x122688 [C8 (Z_to_bv 64 rr_canary)]
  /\ (forall a : word, RVMLOCK <= bv_unsigned a < RVMLOCK + 4 -> got_clear M a = None)
  /\ mem_inv rsegs (got_clear M).
Proof.
  intros MM. destruct (mm_auxv M MM) as (auxv & AR & AUXC). exists auxv.
  assert (GC : forall a : word, M a = None -> got_clear M a = None) by (intros a Ha; unfold got_clear; destruct (in_gotb a); [reflexivity| exact Ha]).
  assert (D8 : forall a v, dcell M a 8 v -> 0 <= a -> a + 8 <= RGOT_SSP \/ RGOT_SSP + 8 <= a -> a + 8 <= 2 ^ 64 -> bytes_at rsegs (got_clear M) a (le8 (wz v))).
  { intros a v D A0 OFF A1. apply bytes_at_got_clear; [| cbn [length le8 word_to_le_bytes]; rewrite ?length_Z_to_le_bytes; exact OFF].
    exact (dcell_bytes M a 8 v D A0 ltac:(lia)). }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - intros a Ha. apply GC. apply (mm_ctx M MM (bv_unsigned a)) in Ha. rewrite Z_to_bv_bv_unsigned in Ha. exact Ha.
  - apply rw_cells_intro; [cbn; first [solve [repeat split] | tauto]| |apply wr_at_img_check; [vm_compute; reflexivity| lia| cbn; lia]].
    apply bytes_at_got_clear; [| cbn; unfold RGOT_SSP; lia].
    change (bytes_at rsegs M 1189544 (word_to_le_bytes 1 (Z_to_bv 64 1) ++ (word_to_le_bytes 1 (Z_to_bv 64 0) ++ (word_to_le_bytes 1 (Z_to_bv 64 0) ++ (word_to_le_bytes 1 (Z_to_bv 64 0) ++ word_to_le_bytes 4 (Z_to_bv 64 0)))))).
    pose proof (mm_libc0 M MM) as L0. pose proof (mm_libc1 M MM) as L1. pose proof (mm_libc2 M MM) as L2. pose proof (mm_libc3 M MM) as L3. pose proof (mm_libc4 M MM) as L4. unfold RLIBC in *.
    Ltac step1 H := apply bytes_at_app; [apply dcell_bytes; [exact H| lia| cbn; lia]| rewrite length_w2le; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite <- ?Z.add_assoc; cbn [Z.add Pos.add]].
    step1 L0. step1 L1. step1 L2. step1 L3. apply dcell_bytes; [exact L4| lia| cbn; lia].
  - apply rw_cells_intro; [cbn; repeat split; auto| |apply wr_at_img_check; [vm_compute; reflexivity| lia| cbn; lia]].
    cbn [cells_bytes cbytes app]. rewrite app_nil_r.
    pose proof (mm_tlshd M MM) as L0. pose proof (mm_tlssz M MM) as L1. pose proof (mm_tlsal M MM) as L2. pose proof (mm_tlscnt M MM) as L3. pose proof (mm_pgsz M MM) as L4. unfold RLIBC in *.
    Ltac step8 D H := apply bytes_at_app; [apply (D _ _ H); [lia| unfold RGOT_SSP; lia| lia]| change (length (le8 ?x)) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite <- ?Z.add_assoc; cbn [Z.add Pos.add]].
    step8 D8 AUXC. step8 D8 L0. step8 D8 L1. step8 D8 L2. step8 D8 L3. step8 D8 L4.

    split; [lia|]. split; [rewrite repeat_length; lia|]. intros i Hi. rewrite repeat_length in Hi.
    destruct (mm_gloc M MM (Z.of_nat i) ltac:(lia)) as (b & RD & ->).
    rewrite (nth_error_repeat _ Hi). unfold mrd. rewrite got_clear_off by (unfold wa; rewrite unsigned_lit by lia; unfold RGOT_SSP; lia).
    rewrite <- PropExec.ov_rdn in RD. change SEGS with rsegs in RD. rewrite CJ.Lib.PropExec.ov_rdn in RD. rewrite rdn_unfold in RD.
    unfold mrd in RD. replace (1189552 + (Z.of_nat 8 + (Z.of_nat 8 + (Z.of_nat 8 + (Z.of_nat 8 + (Z.of_nat 8 + Z.of_nat 8))))) + Z.of_nat i) with (1189544 + 56 + Z.of_nat i) by lia. unfold wa. unfold RLIBC in RD. cbn [CJ.Lib.PropExec.rdn] in RD.
    destruct (M (Z_to_bv 64 (1189544 + 56 + Z.of_nat i))) as [b|]; [| destruct (CJ.Lib.PropExec.seg_rom rsegs (Z_to_bv 64 (1189544 + 56 + Z.of_nat i))); [| discriminate RD]];
      cbn in RD; inversion RD; reflexivity.
  - apply rw_cells_intro; [cbn; first [solve [repeat split] | tauto]| | apply wr_at_img_check; [vm_compute; reflexivity| lia| cbn; lia]].
    cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply bytes_at_rom; [vm_compute; reflexivity| | lia| cbn; lia].
    intros i Hi. apply got_clear_on. unfold wa. cbn in Hi. rewrite unsigned_lit by lia. unfold RGOT_SSP. lia.
  - apply rw_cells_intro; [cbn; first [solve [repeat split] | tauto]| | apply wr_at_img_check; [vm_compute; reflexivity| lia| cbn; lia]].
    cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply (D8 0x122688 rr_canary); [exact (mm_guard M MM)| lia| unfold RGOT_SSP; lia| lia].
  - intros a Ha. apply GC. apply (mm_vmlock M MM (bv_unsigned a)) in Ha. rewrite Z_to_bv_bv_unsigned in Ha. exact Ha.
  - apply mem_inv_of_clear. intros w H1 H2. apply GC. apply (img_ro_clear_num M (mm_ro M MM) w H1 H2).
Qed.

Theorem ainv_init_proof : ainv_init_stmt.
Proof.
  intros M mo MM MO. exists A0.
  destruct (main_mem_cells M MM) as (auxv & H1 & H2 & H3 & H4 & H5 & H6 & H7).
  pose proof (RHEAP_init_proof (got_clear M) (wz auxv) H1 H2 H3 H4 H5 H6 H7) as [RH _].
  split; [split; [split; [exact RH| split; [exact (mo_lazy mo MO)| exists NR0, RBY0; split; [exact (kpart_main mo MO)| exact caps_ok_PL0]]]| repeat split; reflexivity]|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [| split].
  - intros a [ST|(OFF & _)] Hin; [exact ST|]. exfalso. rewrite in_ranges_img in Hin. unfold RIMG_LO, RIMG_HI in *. lia.
  - intros g b Hb. cbn in Hb. unfold get_meta_rec in Hb. cbn in Hb. rewrite lookup_empty in Hb. discriminate Hb.
  - unfold a_fresh44, active, usage, bounces, ctx. cbn. rewrite !lookup_empty. repeat split; reflexivity.
Qed.

Lemma mng_round_big_bounds n : 0 <= n -> n <= mng_round_big n <= n + 4116.
Proof. intros Hn. unfold mng_round_big. pose proof (mng_round_up_pg_spec (n + MNG_IB + MNG_UNIT)). unfold MNG_IB, MNG_UNIT in *. lia. Qed.

Lemma mng_consts_drv :
  MALLOC_STACK MI_U1 = 8192 /\ BIG MI_U1 = 131052 /\ NMAX MI_U1 = 2 ^ 28
  /\ (forall n, 0 <= n -> n <= round_big MI_U1 n <= n + 4116)
  /\ In (0x122688, map bv_unsigned (le8 (wz rr_canary))) (static_cells MI_U1)
  /\ In (0x1226ab, [0]) (static_cells MI_U1).
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact mng_round_big_bounds|].
  split; cbn; auto.
Qed.

End AC_1.
