(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BSimInv BExitSim BPropExec BCatSim BMmapSim BAllocSim BRelSpec BShapeAlg BNodes BAgentNodes Bap04 BRefNodes BReach BllocNodes BazyRestrict BazyRestrictRun BazyRestrictAlg BazyLedger BazySR BazyNodes.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma syscall_spec_233 : forall i m o,
  bv_unsigned (in_sysno i) = 233%Z ->
  syscall_spec i m o <-> madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma injected_arm_none_233 : Run.injected_arm 233 = None.
Proof. reflexivity. Qed.

Lemma madvise_dontneed_b_int32 : forall w : word,
  (bv_unsigned w mod 2 ^ 32 = 4)%Z -> madvise_dontneed_b (int32 w) = true.
Proof.
  intros w H. unfold madvise_dontneed_b, int32, abi_low32, MADV_DONTNEED. rewrite H.
  apply Z.eqb_eq. reflexivity.
Qed.

Lemma madvise_dontneed_outcome : forall addr len advice i m o,
  (bv_unsigned addr mod page_size = 0)%Z ->
  madvise_dontneed_b advice = true ->
  w_is0 len = false ->
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ < two_pow_64)%Z ->
  madvise_dontneed_ok (m_vmmaps m) addr n = true ->
  madvise_spec addr len advice i m o <->
  o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (madvise_dontneed_next m addr n) [].
Proof.
  intros addr len advice i m o Hal Hadv Hlen. cbv zeta. intros Hnw Hok.
  unfold madvise_spec. rewrite (proj2 (Z.eqb_eq _ _) Hal), Hadv, Hlen. cbn [negb].
  rewrite (proj2 (Z.leb_gt _ _) Hnw). rewrite bind_get_model. cbv beta zeta. rewrite Hok.
  sys_unfold. split.
  - destruct o as [x m' evs|]; intros H; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma madvise_dontneed_next_sbm : forall m addr n, same_but_materialized m (madvise_dontneed_next m addr n).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_lazy : forall m addr n, m_vm_lazy (madvise_dontneed_next m addr n) = m_vm_lazy m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_materialized : forall m addr n,
  m_vm_materialized (madvise_dontneed_next m addr n)
  = List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized m).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_vmmaps : forall m addr n, m_vmmaps (madvise_dontneed_next m addr n) = m_vmmaps m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_halted : forall m addr n, m_halted (madvise_dontneed_next m addr n) = m_halted m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_eager : forall m addr n, eager_used (madvise_dontneed_next m addr n) = eager_used m.
Proof. intros m addr n. apply same_but_materialized_eager. apply madvise_dontneed_next_sbm. Qed.

Lemma apply_effect_mem_zeros_ret : forall ms r a n,
  ms_mem (apply_effect ms (mkEffect r [] [(a, n)])) = zfill a n (ms_mem ms).
Proof.
  intros ms r a n. cbn. apply functional_extensionality. intros x.
  unfold zfill, zmem, zeros_cover. cbn.
  destruct ((bv_unsigned a <=? bv_unsigned x)%Z && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z); reflexivity.
Qed.

Local Lemma u64_small : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. exact Hz. Qed.

Lemma region_free_maps_subtract : forall X (a n : word) (lo hi : Z),
  entries_nowrap X -> region_free X a n = true -> region_free (maps_subtract X lo hi) a n = true.
Proof.
  induction X as [|[b s] X IH]; intros a n lo hi HX HF; [reflexivity|].
  apply entries_nowrap_cons in HX. destruct HX as [Hb HX]. unfold entry_nowrap, BazyLedger.hi in Hb. cbn [fst snd] in Hb.
  cbn [region_free] in HF. apply andb_true_iff in HF. destruct HF as [H1 H2].
  apply negb_true_iff in H1. unfold iv_overlap in H1.
  pose proof (word_unsigned_range b) as Rb. pose proof (word_unsigned_range s) as Rs. unfold two_pow_64 in *.
  cbn [maps_subtract]. unfold iv_subtract.
  assert (HT : region_free (maps_subtract X lo hi) a n = true) by (apply IH; assumption).
  assert (NOV : ~ ((bv_unsigned a < bv_unsigned b + bv_unsigned s) /\ (bv_unsigned b < bv_unsigned a + bv_unsigned n))%Z).
  { intros [C1 C2]. apply andb_false_iff in H1. destruct H1 as [D|D]; apply Z.ltb_ge in D; lia. }
  destruct (Z.ltb_spec (bv_unsigned b) lo) as [L1|L1]; destruct (Z.ltb_spec hi (bv_unsigned b + bv_unsigned s)) as [R1|R1];
    cbn [app region_free]; rewrite ?HT, ?andb_true_r.
  - apply andb_true_iff. split; apply negb_true_iff; unfold iv_overlap.
    + rewrite u64_small by lia.
      apply andb_false_iff. destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned b + Z.min (bv_unsigned s) (lo - bv_unsigned b))); [|left; reflexivity].
      right. apply Z.ltb_ge. lia.
    + rewrite !u64_small by lia.
      apply andb_false_iff. destruct (Z.ltb_spec (bv_unsigned a) (Z.max (bv_unsigned b) hi + (bv_unsigned b + bv_unsigned s - Z.max (bv_unsigned b) hi))); [|left; reflexivity].
      right. apply Z.ltb_ge. lia.
  - apply negb_true_iff; unfold iv_overlap. rewrite u64_small by lia.
    apply andb_false_iff. destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned b + Z.min (bv_unsigned s) (lo - bv_unsigned b))); [|left; reflexivity].
    right. apply Z.ltb_ge. lia.
  - apply negb_true_iff; unfold iv_overlap. rewrite !u64_small by lia.
    apply andb_false_iff. destruct (Z.ltb_spec (bv_unsigned a) (Z.max (bv_unsigned b) hi + (bv_unsigned b + bv_unsigned s - Z.max (bv_unsigned b) hi))); [|left; reflexivity].
    right. apply Z.ltb_ge. lia.
  - reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.

Local Open Scope Z_scope.

Lemma in_arg0_sys_input_m : forall ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

Definition mzero (L S : list (word * word)) (r : word * word) (M : word -> option byte) : word -> option byte :=
  fun x => if zin_rangeb (bv_unsigned x) r && negb (hiddenb L S x) then Some (Z_to_bv 8 0) else M x.

Lemma mzero_zfill : forall L S (a n : word) M,
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> hiddenb L S x = false) ->
  mzero L S (a, n) M = zfill a n M.
Proof.
  intros L S a n M WIN. apply functional_extensionality. intros x. unfold mzero, zfill, zmem, zin_rangeb. cbn [fst snd].
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n));
    cbn [andb]; try reflexivity.
  rewrite WIN by lia. reflexivity.
Qed.

Lemma mzero_zfill_S : forall L S (a n : word) M,
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> in_rangesb x S = true) ->
  mzero L S (a, n) M = zfill a n M.
Proof.
  intros L S a n M WIN. apply mzero_zfill. intros x Hx. unfold hiddenb. rewrite (WIN x Hx).
  destruct (in_rangesb x L); reflexivity.
Qed.

Lemma lzok_after_madvise : forall L S Zr msF mo (addr n : word),
  lzok segs L S Zr (mkCfg msF mo) ->
  (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + bv_unsigned n ->
                    hiddenb L S x = true -> in_rangesb x Zr = true) ->
  let mo' := madvise_dontneed_next mo addr n in
  let msF' := advance_past_svc (apply_effect msF (mkEffect (Z_to_bv 64 0) [] [(addr, n)])) in
  lzok segs L S Zr (mkCfg msF' mo')
  /\ restrict L S msF' = sysret (restrict L S msF) (Z_to_bv 64 0) (mzero L S (addr, n) (ms_mem (restrict L S msF)))
  /\ hid_same L S msF msF'.
Proof.
  intros L S Zr msF mo addr n Hok HZ. cbv zeta.
  destruct Hok as [HL Hinv Hh HZr HSZ HZL HLM]. cbn [cfg_model cfg_ms] in *.
  assert (Emem : ms_mem (apply_effect msF (mkEffect (Z_to_bv 64 0) [] [(addr, n)])) = zfill addr n (ms_mem msF))
    by apply apply_effect_mem_zeros_ret.

  assert (Hhid : forall x, hiddenb L S x = true ->
                 ms_mem (apply_effect msF (mkEffect (Z_to_bv 64 0) [] [(addr, n)])) x = ms_mem msF x).
  { intros x Hx. rewrite Emem. unfold zfill, zmem.
    destruct (Z.leb_spec (bv_unsigned addr) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned addr + bv_unsigned n));
      cbn [andb]; try reflexivity.
    symmetry. apply HZr; [exact Hx|]. apply HZ; [lia | exact Hx]. }
  split; [|split].
  - split; cbn [cfg_model cfg_ms].
    + exact HL.
    + destruct Hinv as [Hl Hnd Hincl Hbud]. split.
      * rewrite madvise_dontneed_next_lazy. exact Hl.
      * rewrite madvise_dontneed_next_materialized. apply NoDup_filter. exact Hnd.
      * rewrite madvise_dontneed_next_materialized. intros p Hp. apply filter_In in Hp. apply Hincl. tauto.
      * rewrite madvise_dontneed_next_eager, madvise_dontneed_next_vmmaps. exact Hbud.
    + rewrite madvise_dontneed_next_halted. exact Hh.
    + intros x Hx Hz. cbn [ms_mem advance_past_svc]. rewrite (Hhid x Hx). apply HZr; assumption.
    + exact HSZ.
    + exact HZL.
    + rewrite madvise_dontneed_next_vmmaps. exact HLM.
  - rewrite (restrict_sysret L S). cbn [eff_ret]. f_equal.
    apply functional_extensionality. intros x.
    unfold mzero. rewrite Emem.
    change (ms_mem (restrict L S msF) x) with (restrict_mem L S (ms_mem msF) x).
    unfold restrict_mem, restrict_mem_by.
    destruct (hiddenb L S x) eqn:Eh; cbn [negb]; [rewrite andb_false_r; reflexivity|]. rewrite andb_true_r.
    unfold zfill, zmem, zin_rangeb. cbn [fst snd].
    destruct ((bv_unsigned addr <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned addr + bv_unsigned n)); reflexivity.
  - apply hid_frame_sysret. exact Hhid.
Qed.

Theorem sreach_madvise_dontneed_lazy : forall L S Zr msF ms mo x8 (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 233 ->
  let addr := ms_gpr ms 0 in
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  bv_unsigned addr mod page_size = 0 ->
  bv_unsigned (ms_gpr ms 2) mod 2 ^ 32 = 4 ->
  len <> Z_to_bv 64 0 ->
  bv_unsigned addr + nZ < 2 ^ 64 ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  region_free (vm_noaccess h) addr n = true ->
  (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ ->
                    hiddenb L S x = true -> in_rangesb x Zr = true) ->
  (forall msF' : machine_state,
     let mo' := madvise_dontneed_next mo addr n in
     lzok segs L S Zr (mkCfg msF' mo') ->
     restrict L S msF' = sysret ms (Z_to_bv 64 0) (mzero L S (addr, n) (ms_mem ms)) ->
     hid_same L S msF msF' ->
     same_but_materialized mo mo' ->
     sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hal Hadv Hlen Hnw Hrf Hmc Hna HZ Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (addr := ms_gpr msF 0) in *.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr msF 1))) in *.
  set (n := Z_to_bv 64 nZ) in *.
  destruct (page_round_up_n_facts (ms_gpr msF 1) Hlen
              ltac:(pose proof (word_unsigned_range addr); fold nZ; unfold two_pow_64; lia)) as (HnZpos & HnZal & Hun).
  fold nZ in HnZpos, HnZal, Hun. fold n in Hun.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 233) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite <- Hun in HZ.
  destruct (lzok_after_madvise L S Zr msF mo addr n Hok HZ) as (Hok' & Hvis & Hhs).
  assert (Hsp : forall o, syscall_spec (sys_input segs msF x8) mo o <->
                          o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (madvise_dontneed_next mo addr n) []).
  { intros o. rewrite (syscall_spec_233 _ mo o Hno').
    rewrite in_arg0_sys_input_m, in_arg1_sys_input', in_arg2_sys_input'.
    apply (madvise_dontneed_outcome addr (ms_gpr msF 1) (int32 (ms_gpr msF 2)) _ mo o Hal
             (madvise_dontneed_b_int32 _ Hadv) (w_is0_false _ Hlen)).
    - fold nZ. unfold two_pow_64. exact Hnw.
    - fold nZ. fold n. unfold madvise_dontneed_ok. rewrite Hrf, Hmc, Hna. reflexivity. }
  assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                    (fun _ => mkCfg (advance_past_svc (apply_effect msF (mkEffect (Z_to_bv 64 0) [] [(addr, n)])))
                                    (madvise_dontneed_next mo addr n))).
  { apply (node_family_noacc segs msF mo x8 unit (fun _ => mkEffect (Z_to_bv 64 0) [] [(addr, n)])
             (fun _ => madvise_dontneed_next mo addr n) (fun _ => []) _ (lzok_halted Hok) Hsvc Hsp).
    - intros []. reflexivity.
    - intros []. apply not_spurious_none. rewrite Hno'. exact injected_arm_none_233.
    - intros o Ho. exists tt. exact Ho.
    - intros []. exact (lzok_halted Hok').
    - intros []. reflexivity. }
  apply (sreach_node segs _ unit _ tt _ Hnode). intros [].
  apply (Hk _ Hok' Hvis Hhs). apply madvise_dontneed_next_sbm.
Qed.

Local Close Scope Z_scope.
End WithSegs.
