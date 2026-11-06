(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsAinvFacts3b.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FsFlags.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, PTRHI in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.

  Theorem FS_NOLAZY : forall st Lc FF M mdl z, WF bt st Lc FF -> Rep bt st Lc FF M mdl ->
    bt_fs bt + 0x1000 <= z < bt_fs bt + 0x9000 -> lzb mdl z = false.
  Proof using.
    intros st Lc FF M mdl z W R Hz. apply (rep_nolazy_fs bt st Lc FF M mdl W R z). (lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end). lia.
  Qed.

  Theorem FS_PRIV : forall st Lc FF z, WF bt st Lc FF ->
    bt_fs bt + 0x1000 <= z < bt_fs bt + 0x9000 -> rt_priv IA Lc FF z.
  Proof using.
    intros st Lc FF z W Hz.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & _) & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INFS)) as ((D1 & D2 & D3 & D4 & D5) & _).
    assert (HZ : z < CEIL /\ ~ (ia_img_lo IA <= z < ia_img_hi IA) /\ (z < AS_LO \/ AS_HEAPLO <= z)).
    { clear -Hz D1 D2 D3 D4 D5. dsj; ulia. }
    clear D4 D5. destruct HZ as (HZ1 & HZ2 & HZ3). split; [exact HZ1|]. split; [exact HZ2|].
    destruct (heap_not_shadowish bt st Lc FF W Lc z ltac:(intros p n H; exact H) HZ3) as (N1 & N2 & N3 & N4). clear HZ3.
    intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
    - destruct V as (p & n & Hin & Hpa).
      destruct (live_ext bt st Lc FF W p n Hin) as (lo & hi & E & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
      pose proof (up8_facts n ltac:(lia)) as (U1 & _). pose proof (rz_range n) as RZ.
      destruct (live_ext_vs_fixed bt st Lc FF W p n lo hi _ _ Hin E INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, KSPACE in G in change_no_check G' end); lia)); ulia.
    - destruct V as (f & k & Hf & Hfa). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & _). lia.
  Qed.
End FsFlags.
End AsAinvFacts3b.
Module AsRtStkCount.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

(* [comment removed for export] *)
Lemma least_below : forall (P : nat -> bool) (n : nat),
  (exists i, (i < n)%nat /\ P i = true) ->
  exists i0, (i0 < n)%nat /\ P i0 = true /\ forall j, (j < i0)%nat -> P j = false.
Proof.
  intros P n. induction n as [|n IH]; intros (i & Hi & Pi); [lia|].
  destruct (existsb P (seq 0 n)) eqn:E.
  - apply existsb_exists in E. destruct E as (x & Hx & Px). apply in_seq in Hx.
    assert (Hxn : (x < n)%nat) by lia.
    destruct (IH (ex_intro _ x (conj Hxn Px))) as (i0 & H0 & P0 & L0).
    exists i0. split; [lia|]. split; [exact P0 | exact L0].
  - assert (NP : forall j, (j < n)%nat -> P j = false).
    { intros j Hj. destruct (P j) eqn:Pj; [|reflexivity]. exfalso.
      assert (X : existsb P (seq 0 n) = true) by (apply existsb_exists; exists j; split; [apply in_seq; lia | exact Pj]).
      rewrite X in E. discriminate E. }
    assert (i = n) by (destruct (Nat.eq_dec i n) as [->|NE]; [reflexivity|]; rewrite (NP i ltac:(lia)) in Pi; discriminate Pi). subst i.
    exists n. split; [lia|]. split; [exact Pi | exact NP].
Qed.

(* [comment removed for export] *)
Lemma first_free_probe : forall (N hint : Z) (busy : Z -> bool),
  0 < N -> 0 <= hint ->
  (exists p, 0 <= p < N /\ busy p = false) ->
  exists i0, 0 <= i0 < N /\ busy ((hint + i0) mod N) = false /\ forall j, 0 <= j < i0 -> busy ((hint + j) mod N) = true.
Proof.
  intros N hint busy HN Hh (p & Hp & Fp).
  set (P := fun i : nat => negb (busy ((hint + Z.of_nat i) mod N))).
  assert (EX : exists i, (i < Z.to_nat N)%nat /\ P i = true).
  { exists (Z.to_nat ((p - hint) mod N)). pose proof (Z.mod_pos_bound (p - hint) N HN) as B.
    split; [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold P in G in change_no_check G' end). rewrite Z2Nat.id by lia.
    replace ((hint + (p - hint) mod N) mod N) with p; [rewrite Fp; reflexivity|].
    rewrite Zplus_mod_idemp_r. replace (hint + (p - hint)) with p by lia. symmetry. apply Z.mod_small. exact Hp. }
  destruct (least_below P (Z.to_nat N) EX) as (i0 & H0 & P0 & L0).
  exists (Z.of_nat i0). split; [lia|]. split.
  - unfold P in P0. apply negb_true_iff in P0. exact P0.
  - intros j Hj. specialize (L0 (Z.to_nat j) ltac:(lia)). unfold P in L0. rewrite Z2Nat.id in L0 by lia.
    apply negb_false_iff in L0. exact L0.
Qed.

(* [comment removed for export] *)
Fixpoint kcount (k : Z) (FF : list (Z * Z)) : Z :=
  match FF with [] => 0 | f :: r => (if Z.eqb (snd f) k then 1 else 0) + kcount k r end.

Lemma kcount_filter : forall k FF, kcount k FF = Z.of_nat (length (filter (fun f => Z.eqb (snd f) k) FF)).
Proof.
  intros k FF. induction FF as [|f r IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [kcount filter] in G in change_no_check G' end).
  destruct (Z.eqb (snd f) k); (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia.
Qed.

Lemma NoDup_map_seq : forall (A : Type) (g : nat -> A) (n s : nat),
  (forall i j, (s <= i < s + n)%nat -> (s <= j < s + n)%nat -> g i = g j -> i = j) -> NoDup (map g (seq s n)).
Proof.
  intros A g n. induction n as [|n IH]; intros s INJ; [constructor|].
  (lazymatch goal with |- ?G => let G' := eval cbn [seq map] in G in change_no_check G' end). constructor.
  - intros HIn. apply in_map_iff in HIn. destruct HIn as (j & Ej & Hj). apply in_seq in Hj.
    specialize (INJ j s ltac:(lia) ltac:(lia) Ej). lia.
  - apply IH. intros i j Hi Hj E. apply INJ; [lia | lia | exact E].
Qed.

(* [comment removed for export] *)
Lemma busy_all_count : forall (k N : Z) (frame : Z -> Z) (FF : list (Z * Z)),
  0 <= N ->
  (forall p q, 0 <= p < N -> 0 <= q < N -> frame p = frame q -> p = q) ->
  (forall p, 0 <= p < N -> In (frame p, k) FF) ->
  N <= kcount k FF.
Proof.
  intros k N frame FF HN INJ ALL. rewrite kcount_filter.
  set (g := fun i : nat => (frame (Z.of_nat i), k)).
  assert (ND : NoDup (map g (seq 0 (Z.to_nat N)))).
  { apply NoDup_map_seq. intros i j Hi Hj E. unfold g in E. injection E as E.
    specialize (INJ (Z.of_nat i) (Z.of_nat j) ltac:(lia) ltac:(lia) E). lia. }
  assert (IC : incl (map g (seq 0 (Z.to_nat N))) (filter (fun f => Z.eqb (snd f) k) FF)).
  { intros x Hx. apply in_map_iff in Hx. destruct Hx as (i & <- & Hi). apply in_seq in Hi.
    apply filter_In. split; [apply ALL; lia | (lazymatch goal with |- ?G => let G' := eval cbn [snd g] in G in change_no_check G' end); apply Z.eqb_refl]. }
  pose proof (NoDup_incl_length ND IC) as LE. rewrite length_map, length_seq in LE. lia.
Qed.

(* [comment removed for export] *)
Theorem free_probe_of_count : forall (k N hint : Z) (busy : Z -> bool) (frame : Z -> Z) (FF : list (Z * Z)),
  0 < N -> 0 <= hint ->
  (forall p q, 0 <= p < N -> 0 <= q < N -> frame p = frame q -> p = q) ->
  (forall p, 0 <= p < N -> busy p = true -> In (frame p, k) FF) ->
  kcount k FF + 1 <= N ->
  exists i0, 0 <= i0 < N /\ busy ((hint + i0) mod N) = false /\ forall j, 0 <= j < i0 -> busy ((hint + j) mod N) = true.
Proof.
  intros k N hint busy frame FF HN Hh INJ BUSY CNT.
  apply first_free_probe; [exact HN | exact Hh|].
  destruct (forallb busy (map Z.of_nat (seq 0 (Z.to_nat N)))) eqn:E.
  - exfalso. assert (ALL : forall p, 0 <= p < N -> In (frame p, k) FF).
    { intros p Hp. apply BUSY; [exact Hp|]. rewrite forallb_forall in E. apply E.
      apply in_map_iff. exists (Z.to_nat p). split; [lia | apply in_seq; lia]. }
    pose proof (busy_all_count k N frame FF ltac:(lia) INJ ALL). lia.
  - assert (X : exists x, In x (map Z.of_nat (seq 0 (Z.to_nat N))) /\ busy x = false).
    { clear -E. induction (map Z.of_nat (seq 0 (Z.to_nat N))) as [|a l IH]; [discriminate E|].
      cbn [forallb] in E. apply andb_false_iff in E. destruct E as [E|E].
      - exists a. split; [left; reflexivity | exact E].
      - destruct (IH E) as (x & Hx & Fx). exists x. split; [right; exact Hx | exact Fx]. }
    destruct X as (x & Hx & Fx). apply in_map_iff in Hx. destruct Hx as (i & <- & Hi). apply in_seq in Hi.
    exists (Z.of_nat i). split; [lia | exact Fx].
Qed.
End AsRtStkCount.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtAMemcpy.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Definition amcpy_words : list (option (bv 32)) :=
  [
   Some W_6c764; Some W_6c768; Some W_6c76c; Some W_6c770; Some W_6c774; Some W_6c778; Some W_6c77c; Some W_6c780;
   Some W_6c784; Some W_6c788; Some W_6c78c; Some W_6c790; None; None; Some W_6c79c; Some W_6c7a0; Some W_6c7a4;
   Some W_6c7a8; Some W_6c7ac; Some W_6c7b0; Some W_6c7b4; Some W_6c7b8; Some W_6c7bc; Some W_6c7c0; Some W_6c7c4;
   Some W_6c7c8; Some W_6c7cc; Some W_6c7d0; None; None; Some W_6c7dc; Some W_6c7e0; Some W_6c7e4; Some W_6c7e8;
   Some W_6c7ec; Some W_6c7f0; Some W_6c7f4; Some W_6c7f8; Some W_6c7fc; Some W_6c800; Some W_6c804; Some W_6c808;
   Some W_6c80c; Some W_6c810; Some W_6c814; Some W_6c818; None; None; Some W_6c824; Some W_6c828; Some W_6c82c;
   Some W_6c830; Some W_6c834; Some W_6c838; Some W_6c83c; Some W_6c840; Some W_6c844; Some W_6c848; Some W_6c84c;
   Some W_6c850; None; None; Some W_6c85c; Some W_6c860; Some W_6c864; Some W_6c868; Some W_6c86c; Some W_6c870;
   Some W_6c874; Some W_6c878; Some W_6c87c; Some W_6c880; Some W_6c884; Some W_6c888; Some W_6c88c; Some W_6c890;
   Some W_6c894; Some W_6c898; Some W_6c89c; Some W_6c8a0; Some W_6c8a4; Some W_6c8a8; Some W_6c8ac; Some W_6c8b0;
   Some W_6c8b4; Some W_6c8b8; Some W_6c8bc; Some W_6c8c0; Some W_6c8c4; Some W_6c8c8; Some W_6c8cc; Some W_6c8d0;
   Some W_6c8d4; Some W_6c8d8; Some W_6c8dc; Some W_6c8e0; Some W_6c8e4; Some W_6c8e8; Some W_6c8ec; Some W_6c8f0;
   Some W_6c8f4; Some W_6c8f8; Some W_6c8fc; Some W_6c900; Some W_6c904; Some W_6c908; Some W_6c90c; Some W_6c910;
   Some W_6c914; None; None; Some W_6c920; Some W_6c924; Some W_6c928; Some W_6c92c; Some W_6c930; Some W_6c934;
   Some W_6c938; Some W_6c93c; Some W_6c940; Some W_6c944; Some W_6c948; Some W_6c94c; Some W_6c950; Some W_6c954;
   Some W_6c958; Some W_6c95c; Some W_6c960; Some W_6c964; Some W_6c968; Some W_6c96c; Some W_6c970; Some W_6c974;
   Some W_6c978; Some W_6c97c; Some W_6c980; Some W_6c984; Some W_6c988; Some W_6c98c; Some W_6c990; Some W_6c994;
   Some W_6c998; Some W_6c99c; Some W_6c9a0; None; None; Some W_6c9ac; Some W_6c9b0; Some W_6c9b4; Some W_6c9b8;
   Some W_6c9bc; Some W_6c9c0; Some W_6c9c4; Some W_6c9c8; None; None; Some W_6c9d4; Some W_6c9d8; Some W_6c9dc;
   Some W_6c9e0; Some W_6c9e4; Some W_6c9e8; Some W_6c9ec; Some W_6c9f0; None; None; Some W_6c9fc; Some W_6ca00;
   Some W_6ca04; Some W_6ca08; Some W_6ca0c; Some W_6ca10; Some W_6ca14; Some W_6ca18; Some W_6ca1c; Some W_6ca20;
   Some W_6ca24; Some W_6ca28; Some W_6ca2c; Some W_6ca30; Some W_6ca34; Some W_6ca38; Some W_6ca3c; Some W_6ca40;
   Some W_6ca44; Some W_6ca48; Some W_6ca4c; Some W_6ca50; Some W_6ca54; Some W_6ca58; Some W_6ca5c; None; None;
   Some W_6ca68; Some W_6ca6c; Some W_6ca70; Some W_6ca74; Some W_6ca78; Some W_6ca7c; Some W_6ca80; Some W_6ca84;
   Some W_6ca88; Some W_6ca8c; Some W_6ca90; Some W_6ca94; Some W_6ca98; Some W_6ca9c; Some W_6caa0; Some W_6caa4;
   Some W_6caa8; Some W_6caac; Some W_6cab0; Some W_6cab4; Some W_6cab8; Some W_6cabc; Some W_6cac0; Some W_6cac4;
   Some W_6cac8; Some W_6cacc; Some W_6cad0; Some W_6cad4; Some W_6cad8; Some W_6cadc; Some W_6cae0; Some W_6cae4;
   Some W_6cae8; Some W_6caec; Some W_6caf0; Some W_6caf4; Some W_6caf8; Some W_6cafc; Some W_6cb00; Some W_6cb04;
   Some W_6cb08; Some W_6cb0c; Some W_6cb10; Some W_6cb14; Some W_6cb18; Some W_6cb1c; None; None; Some W_6cb28;
   Some W_6cb2c; Some W_6cb30; Some W_6cb34; Some W_6cb38; Some W_6cb3c; Some W_6cb40; Some W_6cb44; Some W_6cb48;
   Some W_6cb4c; Some W_6cb50; Some W_6cb54; Some W_6cb58; Some W_6cb5c; Some W_6cb60; Some W_6cb64; Some W_6cb68;
   Some W_6cb6c; Some W_6cb70; Some W_6cb74; Some W_6cb78; Some W_6cb7c; Some W_6cb80; Some W_6cb84; Some W_6cb88;
   Some W_6cb8c; Some W_6cb90; Some W_6cb94; Some W_6cb98; Some W_6cb9c; Some W_6cba0; Some W_6cba4; Some W_6cba8;
   Some W_6cbac; Some W_6cbb0; Some W_6cbb4; Some W_6cbb8; Some W_6cbbc; None; None; Some W_6cbc8; Some W_6cbcc;
   Some W_6cbd0; Some W_6cbd4; Some W_6cbd8; Some W_6cbdc; Some W_6cbe0; Some W_6cbe4; Some W_6cbe8; Some W_6cbec;
   Some W_6cbf0; Some W_6cbf4; Some W_6cbf8; Some W_6cbfc
  ]%list.


(* [comment removed for export] *)
Record amcpy_tab : Type := AMCT {
  ac_base : word;          (* [comment removed for export] *)
  ac_rip : rip_tab;        (* [comment removed for export] *)
  ac_mcp : word;           (* [comment removed for export] *)
  ac_g_flag : Z; ac_p_flag : Z;   (* [comment removed for export] *)
  ac_c_rmc : Z }.          (* [comment removed for export] *)

Record amcpy_tab_ok (segs : list Segment) (t : amcpy_tab) : Prop := AMCTOK {
  cto_code : code_ato segs (ac_base t) 0 amcpy_words;
  cto_rip : rip_tab_ok segs (ac_rip t);
  cto_rip_base : rt_base (ac_rip t) = at_ (ac_base t) 14380;
  cto_mcp : code_at segs (ac_mcp t) 0 mmemcpy_words;
  cto_qcf1 : code_ato segs (at_ (ac_base t) 112) 0 (qc2f_words 11 21);
  cto_qcs1 : code_ato segs (at_ (ac_base t) 856) 0 (qc2s_words 21);
  cto_qcf2 : code_ato segs (at_ (ac_base t) 184) 0 (qc2f_words 10 19);
  cto_qcs2 : code_ato segs (at_ (ac_base t) 1020) 0 (qc2s_words 19);
  cto_g48 : gload segs (ac_base t) 48 13 (ac_g_flag t);
  cto_g112 : gload segs (at_ (ac_base t) 112) 0 13 (mt_g_shoff (rt_m2s (ac_rip t)));
  cto_g184 : gload segs (at_ (ac_base t) 184) 0 13 (mt_g_shoff (rt_m2s (ac_rip t)));
  cto_g240 : gload segs (ac_base t) 240 13 (ac_c_rmc t);
  cto_b164 : gbnez segs (at_ (ac_base t) 164) 15 (at_ (ac_base t) 856);
  cto_b904 : gbeqz segs (at_ (ac_base t) 904) 13 (at_ (ac_base t) 168);
  cto_b236 : gbnez segs (at_ (ac_base t) 236) 15 (at_ (ac_base t) 1020);
  cto_b1110 : gbeqz segs (at_ (ac_base t) 1068) 13 (at_ (ac_base t) 240);
  cto_base : (U (ac_base t) mod 2 = 0)%Z /\ (U (ac_base t) + 20000 < 2 ^ 64)%Z;
  cto_mcp_ok : ret_ok (ac_mcp t) }.

(* [comment removed for export] *)
Definition amc_frame (mem : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (word_to_le_bytes 8 ra))
    (at_ sp (-16)) (word_to_le_bytes 8 s0))
    (at_ sp (-24)) (word_to_le_bytes 8 s1))
    (at_ sp (-32)) (word_to_le_bytes 8 s2))
    (at_ sp (-40)) (word_to_le_bytes 8 s3))
    (at_ sp (-48)) (word_to_le_bytes 8 s4))
    (at_ sp (-56)) (word_to_le_bytes 8 s5))
    (at_ sp (-64)) (word_to_le_bytes 8 s6))
    (at_ sp (-72)) (word_to_le_bytes 8 s7).

Section AMCPY.
  Variable segs : list Segment.
  Variable base : word.
  Variable rt : rip_tab.
  Variable mcp : word.
  Variables g_flag p_flag c_rmc : Z.
  #[local] Abbreviation g_shoff := (mt_g_shoff (rt_m2s rt)).
  #[local] Abbreviation p_shoff := (mt_p_shoff (rt_m2s rt)).
  Hypothesis HCODE : code_ato segs base 0 amcpy_words.
  Hypothesis RTOK : rip_tab_ok segs rt.
  Hypothesis RTB : rt_base rt = at_ base 14380.
  Hypothesis MCP : code_at segs mcp 0 mmemcpy_words.
  Hypothesis QCF1 : code_ato segs (at_ base 112) 0 (qc2f_words 11 21).
  Hypothesis QCS1 : code_ato segs (at_ base 856) 0 (qc2s_words 21).
  Hypothesis QCF2 : code_ato segs (at_ base 184) 0 (qc2f_words 10 19).
  Hypothesis QCS2 : code_ato segs (at_ base 1020) 0 (qc2s_words 19).
  Hypothesis G48 : gload segs base 48 13 g_flag.
  Hypothesis G112 : gload segs (at_ base 112) 0 13 g_shoff.
  Hypothesis G184 : gload segs (at_ base 184) 0 13 g_shoff.
  Hypothesis G240 : gload segs base 240 13 c_rmc.
  Hypothesis B164 : gbnez segs (at_ base 164) 15 (at_ base 856).
  Hypothesis B904 : gbeqz segs (at_ base 904) 13 (at_ base 168).
  Hypothesis B236 : gbnez segs (at_ base 236) 15 (at_ base 1020).
  Hypothesis B1068 : gbeqz segs (at_ base 1068) 13 (at_ base 240).
  Hypothesis Hbase : (U base mod 2 = 0)%Z /\ (U base + 20000 < 2 ^ 64)%Z.
  Hypothesis Hmcp : ret_ok mcp.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_6c764.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_6c768.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_6c76c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_6c770.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_6c774.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_6c778.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_6c77c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_6c780.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_6c784.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_6c788.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_6c78c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 10 _ HCODE eq_refl). Qed.
  Lemma Fo44 : fetch_word segs (at_ base 44) = Some W_6c790.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 11 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_6c79c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 14 _ HCODE eq_refl). Qed.
  Lemma Fo60 : fetch_word segs (at_ base 60) = Some W_6c7a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 15 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_6c7a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_6c7a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_6c7ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_6c7b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_6c7b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo84 : fetch_word segs (at_ base 84) = Some W_6c7b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 21 _ HCODE eq_refl). Qed.
  Lemma Fo88 : fetch_word segs (at_ base 88) = Some W_6c7bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 22 _ HCODE eq_refl). Qed.
  Lemma Fo92 : fetch_word segs (at_ base 92) = Some W_6c7c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 23 _ HCODE eq_refl). Qed.
  Lemma Fo96 : fetch_word segs (at_ base 96) = Some W_6c7c4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 24 _ HCODE eq_refl). Qed.
  Lemma Fo100 : fetch_word segs (at_ base 100) = Some W_6c7c8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 25 _ HCODE eq_refl). Qed.
  Lemma Fo104 : fetch_word segs (at_ base 104) = Some W_6c7cc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 26 _ HCODE eq_refl). Qed.
  Lemma Fo108 : fetch_word segs (at_ base 108) = Some W_6c7d0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 27 _ HCODE eq_refl). Qed.












  Lemma Fo168 : fetch_word segs (at_ base 168) = Some W_6c80c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 42 _ HCODE eq_refl). Qed.
  Lemma Fo172 : fetch_word segs (at_ base 172) = Some W_6c810.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 43 _ HCODE eq_refl). Qed.
  Lemma Fo176 : fetch_word segs (at_ base 176) = Some W_6c814.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 44 _ HCODE eq_refl). Qed.
  Lemma Fo180 : fetch_word segs (at_ base 180) = Some W_6c818.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 45 _ HCODE eq_refl). Qed.












  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo248 : fetch_word segs (at_ base 248) = Some W_6c85c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 62 _ HCODE eq_refl). Qed.
  Lemma Fo252 : fetch_word segs (at_ base 252) = Some W_6c860.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 63 _ HCODE eq_refl). Qed.
  Lemma Fo256 : fetch_word segs (at_ base 256) = Some W_6c864.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 64 _ HCODE eq_refl). Qed.
  Lemma Fo260 : fetch_word segs (at_ base 260) = Some W_6c868.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 65 _ HCODE eq_refl). Qed.
  Lemma Fo264 : fetch_word segs (at_ base 264) = Some W_6c86c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 66 _ HCODE eq_refl). Qed.
  Lemma Fo268 : fetch_word segs (at_ base 268) = Some W_6c870.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 67 _ HCODE eq_refl). Qed.
  Lemma Fo272 : fetch_word segs (at_ base 272) = Some W_6c874.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 68 _ HCODE eq_refl). Qed.
  Lemma Fo276 : fetch_word segs (at_ base 276) = Some W_6c878.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 69 _ HCODE eq_refl). Qed.
  Lemma Fo280 : fetch_word segs (at_ base 280) = Some W_6c87c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 70 _ HCODE eq_refl). Qed.
  Lemma Fo284 : fetch_word segs (at_ base 284) = Some W_6c880.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 71 _ HCODE eq_refl). Qed.
  Lemma Fo288 : fetch_word segs (at_ base 288) = Some W_6c884.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 72 _ HCODE eq_refl). Qed.
  Lemma Fo292 : fetch_word segs (at_ base 292) = Some W_6c888.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 73 _ HCODE eq_refl). Qed.
  Lemma Fo296 : fetch_word segs (at_ base 296) = Some W_6c88c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 74 _ HCODE eq_refl). Qed.




















































  Lemma Fo516 : fetch_word segs (at_ base 516) = Some W_6c968.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 129 _ HCODE eq_refl). Qed.
  Lemma Fo520 : fetch_word segs (at_ base 520) = Some W_6c96c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 130 _ HCODE eq_refl). Qed.









































































  Lemma Fo848 : fetch_word segs (at_ base 848) = Some W_6cab4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 212 _ HCODE eq_refl). Qed.
  Lemma Fo852 : fetch_word segs (at_ base 852) = Some W_6cab8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 213 _ HCODE eq_refl). Qed.













  Lemma Fo908 : fetch_word segs (at_ base 908) = Some W_6caf0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 227 _ HCODE eq_refl). Qed.
  Lemma Fo912 : fetch_word segs (at_ base 912) = Some W_6caf4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 228 _ HCODE eq_refl). Qed.
  Lemma Fo916 : fetch_word segs (at_ base 916) = Some W_6caf8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 229 _ HCODE eq_refl). Qed.
  Lemma Fo920 : fetch_word segs (at_ base 920) = Some W_6cafc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 230 _ HCODE eq_refl). Qed.
  Lemma Fo924 : fetch_word segs (at_ base 924) = Some W_6cb00.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 231 _ HCODE eq_refl). Qed.
  Lemma Fo928 : fetch_word segs (at_ base 928) = Some W_6cb04.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 232 _ HCODE eq_refl). Qed.
  Lemma Fo932 : fetch_word segs (at_ base 932) = Some W_6cb08.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 233 _ HCODE eq_refl). Qed.
  Lemma Fo936 : fetch_word segs (at_ base 936) = Some W_6cb0c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 234 _ HCODE eq_refl). Qed.
  Lemma Fo940 : fetch_word segs (at_ base 940) = Some W_6cb10.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 235 _ HCODE eq_refl). Qed.
  Lemma Fo944 : fetch_word segs (at_ base 944) = Some W_6cb14.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 236 _ HCODE eq_refl). Qed.
  Lemma Fo948 : fetch_word segs (at_ base 948) = Some W_6cb18.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 237 _ HCODE eq_refl). Qed.




























  Lemma Fo1072 : fetch_word segs (at_ base 1072) = Some W_6cb94.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 268 _ HCODE eq_refl). Qed.
  Lemma Fo1076 : fetch_word segs (at_ base 1076) = Some W_6cb98.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 269 _ HCODE eq_refl). Qed.
  Lemma Fo1080 : fetch_word segs (at_ base 1080) = Some W_6cb9c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 270 _ HCODE eq_refl). Qed.
  Lemma Fo1084 : fetch_word segs (at_ base 1084) = Some W_6cba0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 271 _ HCODE eq_refl). Qed.
  Lemma Fo1088 : fetch_word segs (at_ base 1088) = Some W_6cba4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 272 _ HCODE eq_refl). Qed.
  Lemma Fo1092 : fetch_word segs (at_ base 1092) = Some W_6cba8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 273 _ HCODE eq_refl). Qed.
  Lemma Fo1096 : fetch_word segs (at_ base 1096) = Some W_6cbac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 274 _ HCODE eq_refl). Qed.
  Lemma Fo1100 : fetch_word segs (at_ base 1100) = Some W_6cbb0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 275 _ HCODE eq_refl). Qed.
  Lemma Fo1104 : fetch_word segs (at_ base 1104) = Some W_6cbb4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 276 _ HCODE eq_refl). Qed.
  Lemma Fo1108 : fetch_word segs (at_ base 1108) = Some W_6cbb8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amcpy_words 277 _ HCODE eq_refl). Qed.
















  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables dst src ra sp : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable fl : byte.
  Variable regs : bvmap 5 word.
  Hypothesis Hsp : (0x10007fff8000 + 2304 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  (* [comment removed for export] *)
  Definition CM1 : word -> option byte :=
    amc_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
              (getr regs 22) (getr regs 23).
  (* [comment removed for export] *)
  Definition CM2 : word -> option byte :=
    rip_mem rt CM1 (at_ sp (-2144)) (at_ base 932) sp (Z_to_bv 64 n) (getr regs 18) (Z_to_bv 64 (U dst + n))
            (at_ sp (-2144)) dst src (Z_to_bv 64 n).
  Definition CM3 : word -> option byte :=
    rip_mem rt CM2 (at_ sp (-2144)) (at_ base 1092) sp dst (Z_to_bv 64 n) (Z_to_bv 64 (U dst + n))
            (at_ sp (-2144)) src dst (Z_to_bv 64 n).
  Definition amcpy_post (M : word -> option byte) : word -> option byte := wbytes M dst bs.

  Lemma CM1_out : forall x : word, (U x < U sp - 72 \/ U sp <= U x)%Z -> CM1 x = mem x.
  Proof using Hsp base.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold CM1, amc_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma CM1_low : forall x : word, (U x < U sp - 2224)%Z -> CM1 x = mem x.
  Proof using Hsp base. intros x Hx. apply CM1_out. lia. Qed.
  Lemma CM1_agree : forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> CM1 x = mem x.
  Proof using Hsp base. intros x Hx. apply CM1_out. lia. Qed.
  Lemma CM1_grows : mem_grows mem CM1.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold CM1, amc_frame in G in change_no_check G' end).
    repeat (lazymatch goal with
            | |- mem_grows ?a ?a => apply mem_grows_refl
            | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
            end).
  Qed.
  Lemma CM2_agree : forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> CM2 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold CM2 in G in change_no_check G' end). rewrite rip_mem_outside; [apply CM1_agree; exact Hx | rewrite at_u; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  Qed.

  Lemma CM3_agree : forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> CM3 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold CM3 in G in change_no_check G' end). rewrite rip_mem_outside; [apply CM2_agree; exact Hx | rewrite at_u; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  Qed.

  Lemma rip_mem_grows' : forall t M (sp' raX s0 s1 s2 s3 s4 s5 b z : word), mem_grows M (rip_mem t M sp' raX s0 s1 s2 s3 s4 s5 b z).
  Proof using.
    intros. (lazymatch goal with |- ?G => let G' := eval unfold rip_mem, ps_frame in G in change_no_check G' end).
    destruct (Z.ltb _ _);
      repeat (lazymatch goal with
              | |- mem_grows ?a ?a => apply mem_grows_refl
              | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
              end).
  Qed.
  Lemma CM2_grows : mem_grows mem CM2.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold CM2 in G in change_no_check G' end). eapply mem_grows_trans; [apply CM1_grows | apply rip_mem_grows']. Qed.
  Lemma CM3_grows : mem_grows mem CM3.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold CM3 in G in change_no_check G' end). eapply mem_grows_trans; [apply CM2_grows | apply rip_mem_grows']. Qed.

  Lemma rd_o : forall (M : word -> option byte) (B : Z) (a : word) k bs0,
    (forall x : word, (U x < B)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= B)%Z -> (B <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M B a k bs0 HM Ha HB Hr. rewrite <- Hr. apply rdn_ext; [lia|].
    intros x Hx. apply HM. lia.
  Qed.
  Lemma rd_outF : forall (M : word -> option byte) (a : word) k bs0,
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= U sp - 2224 \/ U sp <= U a)%Z -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M a k bs0 HM Ha Hnw Hr. rewrite <- Hr. apply rdn_ext; [exact Hnw|].
    intros x Hx. apply HM. lia.
  Qed.
  Lemma rd_outZ : forall (M : word -> option byte) (c : Z) k bs0,
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) ->
    (0 <= c)%Z -> (c + Z.of_nat k <= U sp - 2224)%Z ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs0 -> rdn segs M (Z_to_bv 64 c) k = Some bs0.
  Proof using Hsp base.
    intros M c k bs0 HM Hc Hk Hr. pose proof (u64_range sp). apply (rd_outF M); try assumption; wd_ulia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MC : mcH segs mem dst src n bs.
  Hypothesis Hends : (U src + n <= 2 ^ 47)%Z /\ (U dst + n <= 2 ^ 47)%Z.
  Hypothesis Rgf : rdn segs mem (Z_to_bv 64 g_flag) 8 = Some (LE8 (Z_to_bv 64 p_flag)).
  Hypothesis Rfl : rdn segs mem (Z_to_bv 64 p_flag) 1 = Some [fl].
  Hypothesis Hfl : U fl <> 0%Z.
  Hypothesis Rrmc : rdn segs mem (Z_to_bv 64 c_rmc) 8 = Some (LE8 mcp).
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 2224)%Z (g_flag :: p_flag :: c_rmc :: m2s_cells (rt_m2s rt)).
  Hypothesis Hstk : store_ok segs mem (at_ sp (-2224)) 2224 = true.
  Hypothesis Hsrc_stk : (n = 0 \/ U src + n <= U sp - 2224 \/ U sp <= U src)%Z.
  Hypothesis Hdst_stk : (n = 0 \/ U dst + n <= U sp - 2224 \/ U sp <= U dst)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis R1 : getr regs 1 = ra.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R10 : getr regs 10 = dst.
  Hypothesis R11 : getr regs 11 = src.
  Hypothesis R12 : getr regs 12 = Z_to_bv 64 n.

  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC; unfold m2s_cells in HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ sp (-2224)) _ 2224);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac addr_n := gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; rewrite ?at_addi; zlit_at;
                 try (progress ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end)); unorm).
  Ltac rd_close LOW Hr :=
    apply (rd_o _ _ _ _ _ LOW);
    [ rewrite ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ]
    | lia
    | first [ exact Hr | rewrite <- Hr; f_equal; apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ] ] ].
  Ltac cldb F D bb LOW Hr :=
    chain_step; [reflexivity
      | eapply step_lbu with (b := bb);
        [exact F | reflexivity | exact D | addr_n; rd_close LOW Hr]
      | step_simpl]; vn.
  Ltac gl G LOW Hr :=
    eapply msteps_trans; [ eapply G; apply (rd_o _ _ _ _ _ LOW); [(lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia | lia | exact Hr] | ]; zlit_at.

  (* [comment removed for export] *)
  #[local] Abbreviation CLX := (fun r : reg => In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cblkA :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 100) CM1 rom)
      /\ getr r 1 = ra /\ getr r 2 = at_ sp (-2144) /\ getr r 8 = sp /\ getr r 10 = dst /\ getr r 11 = src
      /\ getr r 12 = Z_to_bv 64 n /\ getr r 20 = at_ sp (-2144) /\ getr r 21 = Z_to_bv 64 (U src + n) /\ getr r 19 = Z_to_bv 64 (U dst + n)
      /\ (forall i : reg, In i [9; 18; 22; 23; 24; 25; 26; 27; 3; 4]%list -> getr r i = getr regs i)
      /\ regs_agree CLX regs r.
  Proof using R12 R11 R10 R2 R1 Hdst_stk Hsrc_stk Hstk Hcells Hfl Rfl Rgf Hends MC Hsp fl bs G48 HCODE c_rmc p_flag g_flag rt.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs. pose proof (u8_range fl) as Hflr.
    destruct MC as [Mn Mlen Msrc Mdst Mdisj Mnws Mnwd]. cells_split.
    Ltac pro G48 CM1_low Rgf Rfl :=
      an Fo0 D_6c764;                                    (* [comment removed for export] *)
      fsd Fo4 D_6c768 (at_ sp (-8));                     (* [comment removed for export] *)
      fsd Fo8 D_6c76c (at_ sp (-16));                    (* [comment removed for export] *)
      fsd Fo12 D_6c770 (at_ sp (-24));
      fsd Fo16 D_6c774 (at_ sp (-32));
      fsd Fo20 D_6c778 (at_ sp (-40));
      fsd Fo24 D_6c77c (at_ sp (-48));
      fsd Fo28 D_6c780 (at_ sp (-56));
      fsd Fo32 D_6c784 (at_ sp (-64));
      fsd Fo36 D_6c788 (at_ sp (-72));
      change (wbytes _ _ _) with CM1;
      an Fo40 D_6c78c;                                   (* [comment removed for export] *)
      an Fo44 D_6c790;                                   (* [comment removed for export] *)
      gl G48 CM1_low Rgf;                                  (* [comment removed for export] *)
      cldb Fo56 D_6c79c fl CM1_low Rfl;                  (* [comment removed for export] *)
      ab_ft Fo60 D_6c7a0 ltac:(condz);                 (* [comment removed for export] *)
      an Fo64 D_6c7a4; an Fo68 D_6c7a8;                  (* [comment removed for export] *)
      av Fo72 D_6c7ac (Z_to_bv 64 (U src + n)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      av Fo76 D_6c7b0 (Z_to_bv 64 (U dst + n)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
    Ltac tailA :=
      av Fo92 D_6c7c0 (Z_to_bv 64 (2 ^ 64 - 1 - U src)) ltac:(apply v_not_word);         (* [comment removed for export] *)
      ab_ft Fo96 D_6c7c4 ltac:(condz);                 (* [comment removed for export] *)
      wd_refl.
    Ltac fin := post; rewrite ?at_0; try reflexivity;
      [ intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi | ra_solve ].
    destruct (decide (dst = src)) as [EQ | NEQ].
    - (* [comment removed for export] *)
      wd_eexists. split.
      + pro G48 CM1_low Rgf Rfl.
        ab_tk Fo80 D_6c7b4 ltac:(rewrite EQ; apply c_eq_refl).     (* [comment removed for export] *)
        tailA.
      + fin.
    - assert (NE' : U dst <> U src) by (intros E; apply NEQ; apply bv_eq; exact E).
      destruct (Z_le_gt_dec (U dst + n) (U src)) as [LE | GT].
      + wd_eexists. split.
        * pro G48 CM1_low Rgf Rfl.
          ab_ft Fo80 D_6c7b4 ltac:(condz).                (* [comment removed for export] *)
          ab_tk Fo84 D_6c7b8 ltac:(condz).                (* [comment removed for export] *)
          tailA.
        * fin.
      + wd_eexists. split.
        * pro G48 CM1_low Rgf Rfl.
          ab_ft Fo80 D_6c7b4 ltac:(condz).                (* [comment removed for export] *)
          ab_ft Fo84 D_6c7b8 ltac:(condz).                (* [comment removed for export] *)
          ab_ft Fo88 D_6c7bc ltac:(condz).                (* [comment removed for export] *)
          tailA.
        * fin.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cblkSs : forall M r0, (1 <= n <= 64)%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 100) M rom) (mkst r (at_ base 112) M rom)
      /\ getr r 22 = Z_to_bv 64 (2 ^ 64 + n - 65) /\ regs_agree (fun x => In x [13; 22]%list) r0 r.
  Proof using HCODE.
    intros M r0 Hs R12'. wd_eexists. split.
    - av Fo100 D_6c7c8 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm (2 ^ 64 + n - 65) (-1)); f_equal; lia).
      an Fo104 D_6c7cc.
      ab_ft Fo108 D_6c7d0 ltac:(condz).
      wd_refl.
    - post. ra_solve.
  Qed.
  Lemma cblkSz : forall M r0, n = 0%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 100) M rom) (mkst r (at_ base 168) M rom)
      /\ getr r 22 = Z_to_bv 64 (2 ^ 64 + n - 65) /\ regs_agree (fun x => In x [13; 22]%list) r0 r.
  Proof using HCODE.
    intros M r0 Hz R12'. wd_eexists. split.
    - av Fo100 D_6c7c8 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm (2 ^ 64 + n - 65) (-1)); f_equal; lia).
      an Fo104 D_6c7cc.
      ab_tk Fo108 D_6c7d0 ltac:(condz).
      ab_ft Fo848 D_6cab4 ltac:(condz).
      an Fo852 D_6cab8.
      wd_refl.
    - post. ra_solve.
  Qed.
  Lemma cblkSb : forall M r0, (65 <= n)%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 100) M rom) (mkst r (at_ base 908) M rom)
      /\ getr r 22 = Z_to_bv 64 (n - 65) /\ regs_agree (fun x => In x [13; 22]%list) r0 r.
  Proof using Hdst_stk Hends Hsp sp src dst HCODE.
    intros M r0 Hb R12'. pose proof (u64_range dst) as Hd. wd_eexists. split.
    - av Fo100 D_6c7c8 (Z_to_bv 64 (n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).
      an Fo104 D_6c7cc.
      ab_tk Fo108 D_6c7d0 ltac:(condz).
      ab_tk Fo848 D_6cab4 ltac:(condz).
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cblkDs : forall M r0, (1 <= n <= 64)%Z -> getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n -> getr r0 22 = Z_to_bv 64 (2 ^ 64 + n - 65) ->
    exists r, msteps segs (mkst r0 (at_ base 168) M rom) (mkst r (at_ base 184) M rom)
      /\ regs_agree (fun x => In x [13]%list) r0 r.
  Proof using Hends src HCODE.
    intros M r0 Hs R10' R12' R22'. pose proof (u64_range dst) as Hd. wd_eexists. split.
    - av Fo168 D_6c80c (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).
      ab_ft Fo172 D_6c810 ltac:(condz).
      an Fo176 D_6c814.
      ab_ft Fo180 D_6c818 ltac:(condz).
      wd_refl.
    - ra_solve.
  Qed.
  Lemma cblkDz : forall M r0, n = 0%Z -> getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n -> getr r0 22 = Z_to_bv 64 (2 ^ 64 + n - 65) ->
    exists r, msteps segs (mkst r0 (at_ base 168) M rom) (mkst r (at_ base 240) M rom)
      /\ regs_agree (fun x => In x [13]%list) r0 r.
  Proof using Hends src HCODE.
    intros M r0 Hz R10' R12' R22'. pose proof (u64_range dst) as Hd. wd_eexists. split.
    - av Fo168 D_6c80c (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).
      ab_ft Fo172 D_6c810 ltac:(condz).
      an Fo176 D_6c814.
      ab_tk Fo180 D_6c818 ltac:(condz).
      ab_ft Fo516 D_6c968 ltac:(condz).
      an Fo520 D_6c96c.
      wd_refl.
    - ra_solve.
  Qed.
  Lemma cblkDb : forall M r0, (65 <= n)%Z -> getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n -> getr r0 22 = Z_to_bv 64 (n - 65) ->
    exists r, msteps segs (mkst r0 (at_ base 168) M rom) (mkst r (at_ base 1072) M rom)
      /\ regs_agree (fun x => In x [13]%list) r0 r.
  Proof using Hdst_stk Hends Hsp sp src HCODE.
    intros M r0 Hb R10' R12' R22'. pose proof (u64_range dst) as Hd. wd_eexists. split.
    - av Fo168 D_6c80c (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).
      ab_ft Fo172 D_6c810 ltac:(condz).
      an Fo176 D_6c814.
      ab_tk Fo180 D_6c818 ltac:(condz).
      ab_tk Fo516 D_6c968 ltac:(condz).
      wd_refl.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma qc1H_CM1 : forall (b : word) w0 w1 s1,
    (U b + n <= 2 ^ 47)%Z ->
    qc1H segs mem b n g_shoff p_shoff w0 w1 s1 -> qc1H segs CM1 b n g_shoff p_shoff w0 w1 s1.
  Proof using Hcells Hsp c_rmc p_flag g_flag base.
    intros b w0 w1 s1 Hb [Q1 Q2 Q3 Q4 [Q5 Q6] Q7 Q8 Q9 Q10 Q11].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range b) as Hbr. cells_split.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos a 8).
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U b) ltac:(lia)) as S0. pose proof (HSh (U b + n - 1)%Z ltac:(lia)) as S1.
    assert (D0 : (Sh (U b) - 7 <= down8 (Sh (U b)) <= Sh (U b))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U b)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U b)) 8 ltac:(lia)); lia).
    assert (D1 : (Sh (U b + n - 1) - 7 <= down8 (Sh (U b + n - 1)) <= Sh (U b + n - 1))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U b + n - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U b + n - 1)) 8 ltac:(lia)); lia).
    Ltac ro Hr := apply (rd_o _ _ _ _ _ CM1_low); [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | lia | exact Hr].
    split; try assumption.
    - ro Q3. - ro Q4. - split; assumption. - ro Q7. - ro Q8. - ro Q9.
    - intros a Ha. pose proof (u64_range a). apply (rd_o _ _ _ _ _ CM1_low); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia | exact (Q11 a Ha)].
  Qed.

  Lemma cblkQ1 : forall r0 w0 w1 s1,
    qc1H segs mem src n g_shoff p_shoff w0 w1 s1 ->
    getr r0 11 = src -> getr r0 21 = Z_to_bv 64 (U src + n) ->
    exists r, msteps segs (mkst r0 (at_ base 112) CM1 rom) (mkst r (at_ base 168) CM1 rom)
      /\ regs_agree (fun x => In x qc2_clob \/ x = 21) r0 r.
  Proof using Hcells Hends Hsp dst B904 B164 G112 QCS1 QCF1 c_rmc p_flag g_flag.
    intros r0 w0 w1 s1 QH R11' R21'. pose proof (u64_range base).
    destruct (qc2_pass segs (at_ base 112) (at_ base 856) (at_ base 168) 11 21 g_shoff p_shoff QCF1 QCS1 G112
             ltac:(rewrite at_at; exact B164) ltac:(rewrite at_at; exact B904) ltac:(rewrite at_at; reflexivity)
             (or_intror eq_refl) (or_intror (or_intror eq_refl))
             r0 CM1 rom src n w0 w1 s1 (qc1H_CM1 _ _ _ _ (proj1 Hends) QH) R11' R21') as (r & RUN & _ & AG).
    exists r. split; [|exact AG]. rewrite at_at, Z.add_0_r in RUN. exact RUN.
  Qed.

  Lemma cblkQ2 : forall r0 w0 w1 s1,
    qc1H segs mem dst n g_shoff p_shoff w0 w1 s1 ->
    getr r0 10 = dst -> getr r0 19 = Z_to_bv 64 (U dst + n) ->
    exists r, msteps segs (mkst r0 (at_ base 184) CM1 rom) (mkst r (at_ base 240) CM1 rom)
      /\ regs_agree (fun x => In x qc2_clob \/ x = 19) r0 r.
  Proof using Hcells Hends Hsp src B1068 B236 G184 QCS2 QCF2 c_rmc p_flag g_flag.
    intros r0 w0 w1 s1 QH R10' R19'. pose proof (u64_range base).
    destruct (qc2_pass segs (at_ base 184) (at_ base 1020) (at_ base 240) 10 19 g_shoff p_shoff QCF2 QCS2 G184
             ltac:(rewrite at_at; exact B236) ltac:(rewrite at_at; exact B1068) ltac:(rewrite at_at; reflexivity)
             (or_introl eq_refl) (or_introl eq_refl)
             r0 CM1 rom dst n w0 w1 s1 (qc1H_CM1 _ _ _ _ (proj2 Hends) QH) R10' R19') as (r & RUN & _ & AG).
    exists r. split; [|exact AG]. rewrite at_at, Z.add_0_r in RUN. exact RUN.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ripH_on : forall (M : word -> option byte) (b raX : word) (s0 s1 : byte) (midend : word),
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) -> mem_grows mem M ->
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem b midend ->
    ((0x10007fff8000 <= U b /\ U b + n + 1 <= 0x800000000000) \/ U b + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U b))) 1 = Some [s0] -> (U s0 = 0 \/ U b mod 8 < U s0 < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U b + n - 1))) 1 = Some [s1] -> (U s1 = 0 \/ (U b + n - 1) mod 8 < U s1 < 128)%Z ->
    (forall a : word, (Sh (up8 (U b)) <= U a < Sh (down8 (U b + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok raX ->
    ripH segs rt M b (Z_to_bv 64 n) raX (at_ sp (-2144)) s0 s1 midend.
  Proof using Hstk Hcells Hsp c_rmc p_flag g_flag base.
    intros M b raX s0 s1 midend HM HG Hn65 CH Hrng R0 H0 R1' H1' RZ HR.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range b) as Hb.
    destruct CH as [C1 C2 C3 C4 C5 C6 C7 C8 CC Clo Chi]. cells_split.
    assert (SH : forall x, (0 <= x < 0x800000000000)%Z -> (0x7fff8000 <= Sh x < 0x10007fff8000)%Z).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos x 8). pose proof (Z.div_lt_upper_bound x 8 0x100000000000 ltac:(lia) ltac:(lia)). lia. }
    pose proof (SH (U b) ltac:(lia)) as S0'.
    pose proof (SH (U b + n - 1)%Z ltac:(lia)) as S1'.
    assert (UP : (U b <= up8 (U b) <= U b + 7)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end); pose proof (Z.div_mod (U b + 7) 8); pose proof (Z.mod_pos_bound (U b + 7) 8); lia).
    assert (DN : (U b + n - 7 <= down8 (U b + n) <= U b + n)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (U b + n) 8); pose proof (Z.mod_pos_bound (U b + n) 8); lia).
    pose proof (SH (up8 (U b)) ltac:(lia)) as S2. pose proof (SH (down8 (U b + n)) ltac:(lia)) as S3.
    assert (Un : U (Z_to_bv 64 n) = n) by (apply u_Z2bv; lia).
    Ltac rdo HMx Hr := apply (rd_outZ _ _ _ _ HMx); [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr].
    split.
    - split; [rdo HM C1 | rdo HM C2 | rdo HM C3 | rdo HM C4 | rdo HM C5 | rdo HM C6 | rdo HM C7 | rdo HM C8 | exact CC | lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat constructor; rewrite ?at_u; lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rdo HM R0.
    - exact H0.
    - rewrite Un. rdo HM R1'.
    - rewrite Un. exact H1'.
    - rewrite Un. intros a Ha. pose proof (u64_range a). pose proof (RZ a Ha) as Ra.
      rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ra |- *. rdo HM Ra.
    - rewrite at_u by lia. lia.
    - rewrite at_at. replace (-2144 + -80)%Z with (-2224)%Z by lia. eapply store_ok_mono; [exact HG|].
      eapply (store_ok_sub segs mem (at_ sp (-2224)) _ 2224); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - exact HR.
  Qed.

  Lemma cblkR1 : forall r0 (s0b s1b : byte) (midend : word),
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem src midend ->
    ((0x10007fff8000 <= U src /\ U src + n + 1 <= 0x800000000000) \/ U src + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0b] -> (U s0b = 0 \/ U src mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U src + n - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 8 = sp -> getr r0 10 = dst -> getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    getr r0 18 = getr regs 18 -> getr r0 19 = Z_to_bv 64 (U dst + n) -> getr r0 20 = at_ sp (-2144) ->
    exists r, msteps segs (mkst r0 (at_ base 908) CM1 rom) (mkst r (at_ base 168) CM2 rom)
      /\ getr r 2 = at_ sp (-2144) /\ getr r 8 = sp /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 n
      /\ getr r 19 = Z_to_bv 64 (U dst + n)
      /\ regs_agree (fun x => In x ([1; 9; 18; 21; 23]%list ++ rip_clob)) r0 r.
  Proof using Hstk Hcells Hsp Hbase RTB RTOK HCODE c_rmc p_flag g_flag.
    intros r0 s0b s1b midend Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz R2' R8' R10' R11' R12' R18' R19' R20'.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    assert (RA : ret_ok (at_ base 932)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    set (r1 := regupd (regupd (regupd (regupd (regupd (regupd r0 21 dst) 10 src) 23 src) 11 (Z_to_bv 64 n)) 9 (Z_to_bv 64 n)) 1 (at_ base 932)).
    destruct (region_clear segs rt RTOK CM1 rom src (Z_to_bv 64 n) (at_ base 932) (at_ sp (-2144)) s0b s1b midend r1
                (ripH_on CM1 src (at_ base 932) s0b s1b midend CM1_agree CM1_grows Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz RA))
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; reflexivity | subst r1; gres; exact R2' | subst r1; gres; reflexivity | subst r1; gres; reflexivity |].
    wd_eexists. split.
    - an Fo908 D_6caf0.                                  (* [comment removed for export] *)
      an Fo912 D_6caf4.                                  (* [comment removed for export] *)
      an Fo916 D_6caf8.                                  (* [comment removed for export] *)
      an Fo920 D_6cafc.                                  (* [comment removed for export] *)
      an Fo924 D_6cb00.                                  (* [comment removed for export] *)
      an Fo928 D_6cb04.                                  (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- RTB.
      eapply msteps_trans; [exact RUN2|].
      replace (rip_mem rt CM1 (at_ sp (-2144)) (at_ base 932) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) src (Z_to_bv 64 n))
         with CM2.
      2:{ (lazymatch goal with |- ?G => let G' := eval unfold CM2 in G in change_no_check G' end). subst r1. gres. rewrite R8', R18', R19', R20'. reflexivity. }
      assert (A23 : getr r2 23 = src) by (rewrite (AG2 23) by notin; subst r1; gres; reflexivity).
      assert (A9 : getr r2 9 = Z_to_bv 64 n) by (rewrite (AG2 9) by notin; subst r1; gres; reflexivity).
      assert (A21 : getr r2 21 = dst) by (rewrite (AG2 21) by notin; subst r1; gres; reflexivity).
      an Fo932 D_6cb08.                                  (* [comment removed for export] *)
      an Fo936 D_6cb0c.                                  (* [comment removed for export] *)
      an Fo940 D_6cb10.                                  (* [comment removed for export] *)
      an Fo944 D_6cb14.                                  (* [comment removed for export] *)
      ab_tk Fo948 D_6cb18 ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
      assert (A8 : getr r2 8 = sp) by (rewrite (AG2 8) by notin; subst r1; gres; exact R8').
      assert (A19 : getr r2 19 = Z_to_bv 64 (U dst + n)) by (rewrite (AG2 19) by notin; subst r1; gres; exact R19').
      post; try assumption.
      intros x Hx. gres.
      assert (X : x <> 10 /\ x <> 18 /\ x <> 12 /\ x <> 11) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct X as (X1 & X2 & X3 & X4). rewrite !getr_other by assumption.
      rewrite (AG2 x) by (intros Hc; apply Hx; apply in_or_app; right; exact Hc).
      subst r1. assert (Y : x <> 1 /\ x <> 9 /\ x <> 11 /\ x <> 23 /\ x <> 10 /\ x <> 21) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct Y as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). rewrite !getr_other by assumption. reflexivity.
  Qed.

  Lemma cblkR2 : forall r0 (s0b s1b : byte) (midend : word),
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0b] -> (U s0b = 0 \/ U dst mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U dst + n - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 8 = sp -> getr r0 10 = dst -> getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    getr r0 19 = Z_to_bv 64 (U dst + n) -> getr r0 20 = at_ sp (-2144) ->
    exists r, msteps segs (mkst r0 (at_ base 1072) CM2 rom) (mkst r (at_ base 240) CM3 rom)
      /\ getr r 2 = at_ sp (-2144) /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 n
      /\ regs_agree (fun x => In x ([1; 9; 18; 19; 21]%list ++ rip_clob)) r0 r.
  Proof using Hstk Hcells Hsp Hbase RTB RTOK HCODE c_rmc p_flag g_flag.
    intros r0 s0b s1b midend Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz R2' R8' R10' R11' R12' R19' R20'.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    assert (RA : ret_ok (at_ base 1092)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    set (r1 := regupd (regupd (regupd (regupd (regupd r0 9 dst) 21 src) 11 (Z_to_bv 64 n)) 18 (Z_to_bv 64 n)) 1 (at_ base 1092)).
    destruct (region_clear segs rt RTOK CM2 rom dst (Z_to_bv 64 n) (at_ base 1092) (at_ sp (-2144)) s0b s1b midend r1
                (ripH_on CM2 dst (at_ base 1092) s0b s1b midend CM2_agree CM2_grows Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz RA))
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; reflexivity | subst r1; gres; exact R2' | subst r1; gres; exact R10' | subst r1; gres; reflexivity |].
    wd_eexists. split.
    - an Fo1072 D_6cb94.                                 (* [comment removed for export] *)
      an Fo1076 D_6cb98.                                 (* [comment removed for export] *)
      an Fo1080 D_6cb9c.                                 (* [comment removed for export] *)
      an Fo1084 D_6cba0.                                 (* [comment removed for export] *)
      an Fo1088 D_6cba4.                                 (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- RTB.
      eapply msteps_trans; [exact RUN2|].
      replace (rip_mem rt CM2 (at_ sp (-2144)) (at_ base 1092) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) dst (Z_to_bv 64 n))
         with CM3.
      2:{ (lazymatch goal with |- ?G => let G' := eval unfold CM3 in G in change_no_check G' end). subst r1. gres. rewrite R8', R19', R20'. reflexivity. }
      assert (A21 : getr r2 21 = src) by (rewrite (AG2 21) by notin; subst r1; gres; reflexivity).
      assert (A18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (AG2 18) by notin; subst r1; gres; reflexivity).
      assert (A9 : getr r2 9 = dst) by (rewrite (AG2 9) by notin; subst r1; gres; reflexivity).
      an Fo1092 D_6cba8.                                 (* [comment removed for export] *)
      an Fo1096 D_6cbac.                                 (* [comment removed for export] *)
      an Fo1100 D_6cbb0.                                 (* [comment removed for export] *)
      an Fo1104 D_6cbb4.                                 (* [comment removed for export] *)
      ab_tk Fo1108 D_6cbb8 ltac:(condz).               (* [comment removed for export] *)
      wd_refl.
    - assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
      post; try assumption.
      intros x Hx. gres.
      assert (X : x <> 10 /\ x <> 19 /\ x <> 12 /\ x <> 11) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct X as (X1 & X2 & X3 & X4). rewrite !getr_other by assumption.
      rewrite (AG2 x) by (intros Hc; apply Hx; apply in_or_app; right; exact Hc).
      subst r1. assert (Y : x <> 1 /\ x <> 18 /\ x <> 11 /\ x <> 21 /\ x <> 9) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct Y as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition amc_slots : list (Z * word) :=
    [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20);
     (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23)]%Z.

  Lemma slots_CM1 : forall (k : Z) (v : word), In (k, v) amc_slots -> rdn segs CM1 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp base.
    intros k v Hin. pose proof (u64_range sp). unfold amc_slots in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval unfold CM1, amc_frame in G in change_no_check G' end); rd8_chain|]). destruct Hin.
  Qed.
  Lemma slots_CM3 : forall (k : Z) (v : word), In (k, v) amc_slots -> rdn segs CM3 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp).
    assert (Hk : (-72 <= k /\ k + 8 <= 0)%Z).
    { unfold amc_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    rewrite <- (slots_CM1 k v Hin). apply rdn_ext; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    intros x Hx. rewrite at_u in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold CM3, CM2 in G in change_no_check G' end).
    rewrite !rip_mem_outside; first [reflexivity | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u; lia].
  Qed.
  Lemma slots_post : forall (M : word -> option byte) (k : Z) (v : word),
    (forall k' v', In (k', v') amc_slots -> rdn segs M (at_ sp k') 8 = Some (word_to_le_bytes 8 v')) ->
    In (k, v) amc_slots -> rdn segs (amcpy_post M) (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hdst_stk Hsrc_stk Hends MC Hsp n src mem base.
    intros M k v HM Hin. pose proof (u64_range sp). pose proof (u64_range dst).
    destruct MC as [Mn Mlen Msrc Mdst Mdisj Mnws Mnwd].
    assert (Hk : (-72 <= k /\ k + 8 <= 0)%Z).
    { unfold amc_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    (lazymatch goal with |- ?G => let G' := eval unfold amcpy_post in G in change_no_check G' end). destruct (Z.eq_dec n 0) as [E0 | NZ0].
    { assert (bs = []%list) as -> by (destruct bs; [reflexivity | rewrite E0 in Mlen; cbn in Mlen; lia]). (lazymatch goal with |- ?G => let G' := eval cbn [wbytes] in G in change_no_check G' end). exact (HM k v Hin). }
    rewrite rdn_wbytes_out; [exact (HM k v Hin) | rewrite Mlen, at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Mlen; lia].
  Qed.

  Lemma cblkC : forall (M : word -> option byte) r0,
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) -> mem_grows mem M ->
    (forall k v, In (k, v) amc_slots -> rdn segs M (at_ sp k) 8 = Some (word_to_le_bytes 8 v)) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 10 = dst -> getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 240) M rom) (mkst r ra (amcpy_post M) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R2 Hret Hdst_stk Hsrc_stk Hcells Rrmc Hends MC Hsp Hmcp Hbase G240 MCP HCODE c_rmc p_flag g_flag mcp rt.
    intros M r0 HMA HG SL R2' R10' R11' R12' AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs. cells_split.
    assert (HM : forall x : word, (U x < U sp - 2224)%Z -> M x = mem x) by (intros x Hx; apply HMA; lia).
    assert (RA : ret_ok (at_ base 252)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    assert (MCM : mcH segs M dst src n bs).
    { destruct MC as [Mn Mlen Msrc Mdst Mdisj Mnws Mnwd]. split; try assumption.
      - rewrite <- Msrc. apply rdn_ext; [rewrite Mlen; lia|]. intros x Hx. apply HMA. rewrite Mlen in Hx. lia.
      - eapply store_ok_mono; [exact HG | exact Mdst]. }
    set (r1 := regupd (regupd r0 13 mcp) 1 (at_ base 252)).
    destruct (mmemcpy_run segs mcp MCP M dst src n bs rom MCM r1 (at_ base 252) RA)
      as (r2 & RUN2 & KP); [subst r1; gres; reflexivity | subst r1; gres; exact R10' | subst r1; gres; exact R11' | subst r1; gres; exact R12' |].
    assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (KP 2) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); subst r1; gres; exact R2').
    assert (A10 : getr r2 10 = dst) by (rewrite (KP 10) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); subst r1; gres; exact R10').
    pose proof (fun k v H => slots_post M k v SL H) as SLP. unfold amc_slots in SLP.
    Ltac fldM F D vv SLP :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply SLP; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    wd_eexists. split; [|split].
    - gl G240 HM Rrmc.                                   (* [comment removed for export] *)
      aret Fo248 D_6c85c mcp.                            (* [comment removed for export] *)
      rewrite at_addi; zlit_at. change (regupd _ 1 _) with r1. rewrite <- (at_0 mcp).
      eapply msteps_trans; [exact RUN2|].
      an Fo252 D_6c860.                                  (* [comment removed for export] *)
      fldM Fo256 D_6c864 ra SLP.
      fldM Fo260 D_6c868 (getr regs 8) SLP.
      fldM Fo264 D_6c86c (getr regs 9) SLP.
      fldM Fo268 D_6c870 (getr regs 18) SLP.
      fldM Fo272 D_6c874 (getr regs 19) SLP.
      fldM Fo276 D_6c878 (getr regs 20) SLP.
      fldM Fo280 D_6c87c (getr regs 21) SLP.
      fldM Fo284 D_6c880 (getr regs 22) SLP.
      fldM Fo288 D_6c884 (getr regs 23) SLP.
      an Fo292 D_6c888.                                  (* [comment removed for export] *)
      aret Fo296 D_6c88c ra.                             (* [comment removed for export] *)
      wd_refl.
    - gres. exact A10.
    - intros x Hx. unfold amset_saved in Hx. cbn [In] in Hx. gres.
      repeat (destruct Hx as [<-|Hx];
        [ gres; rwH; rewrite ?at_addi, ?at_0; first
            [ reflexivity
            | f_equal; lia
            | rewrite (KP _) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); subst r1; gres; rewrite ?(AG0 _) by notin; first [reflexivity | assumption | rwH; rewrite ?at_addi; f_equal; lia] ]
        |]).
      destruct Hx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac regx AG x := rewrite (AG x) by notin.
  Ltac notin2 := let Hc := fresh "Hin" in intros Hc; cbn [In app qc2_clob rip_clob] in Hc;
    decompose [or] Hc; first [discriminate | contradiction].
  Ltac regxi AG x := rewrite (AG x) by notin2.
  Ltac in_lit := (lazymatch goal with |- ?G => let G' := eval cbn [In app amset_saved] in G in change_no_check G' end); repeat (first [left; reflexivity | right]).
  Ltac from_or Hc := cbn [In app qc2_clob rip_clob] in Hc; decompose [or] Hc; first [contradiction | subst; in_lit; fail].

  Theorem amcpy_zero : n = 0%Z ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (amcpy_post CM1) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hsrc_stk Hstk Hcells Rrmc Hfl Rfl Rgf Hends MC Hsp fl src Hmcp Hbase G240 G48 MCP HCODE c_rmc p_flag g_flag mcp rt.
    intros Hz.
    destruct cblkA as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A20 & A21 & A19 & AK & AG1).
    destruct (cblkSz CM1 r1 Hz A12) as (r2 & RUN2 & B22 & AG2).
    destruct (cblkDz CM1 r2 Hz) as (r3 & RUN3 & AG3); [regx AG2 (10:reg); exact A10 | regx AG2 (12:reg); exact A12 | exact B22 |].
    destruct (cblkC CM1 r3 CM1_agree CM1_grows slots_CM1) as (r4 & RUN4 & C10 & CK);
      [ regx AG3 (2:reg); regx AG2 (2:reg); exact A2 | regx AG3 (10:reg); regx AG2 (10:reg); exact A10
      | regx AG3 (11:reg); regx AG2 (11:reg); exact A11 | regx AG3 (12:reg); regx AG2 (12:reg); exact A12
      | intros x Hx; rewrite (AG3 x); [rewrite (AG2 x); [exact (AG1 x Hx) | intros Hc; apply Hx; from_or Hc] | intros Hc; apply Hx; from_or Hc] |].
    exists r4. split; [|split; [exact C10 | exact CK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
  Qed.

  Theorem amcpy_small : forall w0s w1s s1s w0d w1d s1d, (1 <= n <= 64)%Z ->
    qc1H segs mem src n g_shoff p_shoff w0s w1s s1s ->
    qc1H segs mem dst n g_shoff p_shoff w0d w1d s1d ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (amcpy_post CM1) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hsrc_stk Hstk Hcells Rrmc Hfl Rfl Rgf Hends MC Hsp fl Hmcp Hbase B1068 B236 B904 B164 G240 G184 G112 G48 QCS2 QCF2 QCS1 QCF1 MCP HCODE c_rmc p_flag g_flag mcp.
    intros w0s w1s s1s w0d w1d s1d Hs QS QD.
    destruct cblkA as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A20 & A21 & A19 & AK & AG1).
    destruct (cblkSs CM1 r1 Hs A12) as (r2 & RUN2 & B22 & AG2).
    destruct (cblkQ1 r2 w0s w1s s1s QS) as (r3 & RUN3 & AG3); [regx AG2 (11:reg); exact A11 | regx AG2 (21:reg); exact A21 |].
    assert (C10 : getr r3 10 = dst) by (regxi AG3 (10:reg); regx AG2 (10:reg); exact A10).
    assert (C12 : getr r3 12 = Z_to_bv 64 n) by (regxi AG3 (12:reg); regx AG2 (12:reg); exact A12).
    assert (C22 : getr r3 22 = Z_to_bv 64 (2 ^ 64 + n - 65)) by (regxi AG3 (22:reg); exact B22).
    destruct (cblkDs CM1 r3 Hs C10 C12 C22) as (r4 & RUN4 & AG4).
    destruct (cblkQ2 r4 w0d w1d s1d QD) as (r5 & RUN5 & AG5);
      [regx AG4 (10:reg); exact C10 | regx AG4 (19:reg); regxi AG3 (19:reg); regx AG2 (19:reg); exact A19 |].
    destruct (cblkC CM1 r5 CM1_agree CM1_grows slots_CM1) as (r6 & RUN6 & D10 & DK).
    { regxi AG5 (2:reg). regx AG4 (2:reg). regxi AG3 (2:reg). regx AG2 (2:reg). exact A2. }
    { regxi AG5 (10:reg). regx AG4 (10:reg). exact C10. }
    { regxi AG5 (11:reg). regx AG4 (11:reg). regxi AG3 (11:reg). regx AG2 (11:reg). exact A11. }
    { regxi AG5 (12:reg). regx AG4 (12:reg). exact C12. }
    { intros x Hx.
      rewrite (AG5 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG4 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG3 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG2 x) by (intros Hc; apply Hx; from_or Hc). exact (AG1 x Hx). }
    exists r6. split; [|split; [exact D10 | exact DK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
    eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN6.
  Qed.

  Theorem amcpy_big : forall (s0s s1s s0d s1d : byte) (midend : word), (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem src midend -> m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U src /\ U src + n + 1 <= 0x800000000000) \/ U src + n <= 0x7fff7fff)%Z ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0s] -> (U s0s = 0 \/ U src mod 8 < U s0s < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1s] -> (U s1s = 0 \/ (U src + n - 1) mod 8 < U s1s < 128)%Z ->
    (forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0d] -> (U s0d = 0 \/ U dst mod 8 < U s0d < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1d] -> (U s1d = 0 \/ (U dst + n - 1) mod 8 < U s1d < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (amcpy_post CM3) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hsrc_stk Hstk Hcells Rrmc Hfl Rfl Rgf Hends MC Hsp fl Hmcp Hbase G240 G48 MCP RTB RTOK HCODE c_rmc p_flag g_flag mcp.
    intros s0s s1s s0d s1d midend Hb CHs CHd Rgs Rgd Rs0s Hs0s Rs1s Hs1s Rzs Rs0d Hs0d Rs1d Hs1d Rzd.
    destruct cblkA as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A20 & A21 & A19 & AK & AG1).
    destruct (cblkSb CM1 r1 ltac:(lia) A12) as (r2 & RUN2 & B22 & AG2).
    destruct (cblkR1 r2 s0s s1s midend Hb CHs Rgs Rs0s Hs0s Rs1s Hs1s Rzs) as (r3 & RUN3 & C2 & C8 & C10 & C11 & C12 & C19 & AG3);
      [ regx AG2 (2:reg); exact A2 | regx AG2 (8:reg); exact A8 | regx AG2 (10:reg); exact A10 | regx AG2 (11:reg); exact A11
      | regx AG2 (12:reg); exact A12 | regx AG2 (18:reg); apply AK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | regx AG2 (19:reg); exact A19 | regx AG2 (20:reg); exact A20 |].
    assert (C22 : getr r3 22 = Z_to_bv 64 (n - 65)) by (regxi AG3 (22:reg); exact B22).
    assert (C20 : getr r3 20 = at_ sp (-2144)) by (regxi AG3 (20:reg); regx AG2 (20:reg); exact A20).
    destruct (cblkDb CM2 r3 ltac:(lia) C10 C12 C22) as (r4 & RUN4 & AG4).
    destruct (cblkR2 r4 s0d s1d midend Hb CHd Rgd Rs0d Hs0d Rs1d Hs1d Rzd) as (r5 & RUN5 & D2 & D10 & D11 & D12 & AG5);
      [ regx AG4 (2:reg); exact C2 | regx AG4 (8:reg); exact C8 | regx AG4 (10:reg); exact C10 | regx AG4 (11:reg); exact C11
      | regx AG4 (12:reg); exact C12 | regx AG4 (19:reg); exact C19 | regx AG4 (20:reg); exact C20 |].
    destruct (cblkC CM3 r5 CM3_agree CM3_grows slots_CM3 D2 D10 D11 D12) as (r6 & RUN6 & E10 & EK).
    { intros x Hx.
      rewrite (AG5 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG4 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG3 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG2 x) by (intros Hc; apply Hx; from_or Hc). exact (AG1 x Hx). }
    exists r6. split; [|split; [exact E10 | exact EK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
    eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN6.
  Qed.

End AMCPY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record amcpyH (segs : list Segment) (t : amcpy_tab) (mem : word -> option byte)
       (dst src : word) (n : Z) (bs : list byte) (ra sp : word) (fl : byte) : Prop := AMCPYH {
  ach_sp : (0x10007fff8000 + 2304 <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 <= 2 ^ 47)%Z;
  ach_mc : mcH segs mem dst src n bs;
  ach_ends : (bv_unsigned src + n <= 2 ^ 47)%Z /\ (bv_unsigned dst + n <= 2 ^ 47)%Z;
  ach_gf : rdn segs mem (Z_to_bv 64 (ac_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (ac_p_flag t)));
  ach_fl : rdn segs mem (Z_to_bv 64 (ac_p_flag t)) 1 = Some [fl];
  ach_flnz : bv_unsigned fl <> 0%Z;
  ach_rmc : rdn segs mem (Z_to_bv 64 (ac_c_rmc t)) 8 = Some (word_to_le_bytes 8 (ac_mcp t));
  ach_cells : Forall (fun c => 0 <= c /\ c + 8 <= bv_unsigned sp - 2224)%Z
                (ac_g_flag t :: ac_p_flag t :: ac_c_rmc t :: m2s_cells (rt_m2s (ac_rip t)));
  ach_stk : store_ok segs mem (at_ sp (-2224)) 2224 = true;
  ach_src_stk : (n = 0 \/ bv_unsigned src + n <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= bv_unsigned src)%Z;
  ach_dst_stk : (n = 0 \/ bv_unsigned dst + n <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= bv_unsigned dst)%Z;
  ach_ret : ret_ok ra }.

Section PKG.
  Variable segs : list Segment.
  Variable t : amcpy_tab.
  Hypothesis TOK : amcpy_tab_ok segs t.
  #[local] Abbreviation U := bv_unsigned.

  Ltac pkg_finish P9 P8 :=
    lazymatch goal with
    | |- store_ok _ _ (at_ _ _) _ = true => exact P9
    | |- Forall _ _ => exact P8
    | _ => first [eassumption | reflexivity]
    end.

  Theorem asan_memcpy_intrin_zero : forall mem rom (dst src ra sp : word) (n : Z) (bs : list byte) (fl : byte) regs,
    amcpyH segs t mem dst src n bs ra sp fl -> n = 0%Z ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (ac_base t) mem rom) (mkst r ra (amcpy_post dst bs (CM1 mem ra sp regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst src ra sp n bs fl regs [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12] Hz R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18].
    replace (mkst regs (ac_base t) mem rom) with (mkst regs (at_ (ac_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply amcpy_zero. all: pkg_finish P9 P8.
  Qed.

  Theorem asan_memcpy_intrin_small : forall mem rom (dst src ra sp : word) (n : Z) (bs : list byte) (fl : byte) regs w0s w1s s1s w0d w1d s1d,
    amcpyH segs t mem dst src n bs ra sp fl -> (1 <= n <= 64)%Z ->
    qc1H segs mem src n (mt_g_shoff (rt_m2s (ac_rip t))) (mt_p_shoff (rt_m2s (ac_rip t))) w0s w1s s1s ->
    qc1H segs mem dst n (mt_g_shoff (rt_m2s (ac_rip t))) (mt_p_shoff (rt_m2s (ac_rip t))) w0d w1d s1d ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (ac_base t) mem rom) (mkst r ra (amcpy_post dst bs (CM1 mem ra sp regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst src ra sp n bs fl regs w0s w1s s1s w0d w1d s1d [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12] Hs QS QD R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18].
    replace (mkst regs (ac_base t) mem rom) with (mkst regs (at_ (ac_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply amcpy_small. all: pkg_finish P9 P8.
  Qed.

  Theorem asan_memcpy_intrin_big : forall mem rom (dst src ra sp : word) (n : Z) (bs : list byte) (fl : byte) regs
      (s0s s1s s0d s1d : byte) (midend : word),
    amcpyH segs t mem dst src n bs ra sp fl -> (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s (ac_rip t)) mem src midend -> m2sH segs (rt_m2s (ac_rip t)) mem dst midend ->
    ((0x10007fff8000 <= U src /\ U src + n + 1 <= 0x800000000000) \/ U src + n <= 0x7fff7fff)%Z ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0s] -> (U s0s = 0 \/ U src mod 8 < U s0s < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1s] -> (U s1s = 0 \/ (U src + n - 1) mod 8 < U s1s < 128)%Z ->
    (forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0d] -> (U s0d = 0 \/ U dst mod 8 < U s0d < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1d] -> (U s1d = 0 \/ (U dst + n - 1) mod 8 < U s1d < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (ac_base t) mem rom)
                  (mkst r ra (amcpy_post dst bs (CM3 (ac_base t) (ac_rip t) mem dst src ra sp n regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst src ra sp n bs fl regs s0s s1s s0d s1d midend [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12]
           Hb CHs CHd Rgs Rgd Rs0s Hs0s Rs1s Hs1s Rzs Rs0d Hs0d Rs1d Hs1d Rzd R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18].
    replace (mkst regs (ac_base t) mem rom) with (mkst regs (at_ (ac_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply amcpy_big. all: pkg_finish P9 P8.
  Qed.
End PKG.
End FPGen1.
End AsRtAMemcpy.
Require Stdlib.Logic.FunctionalExtensionality OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsIcptMemcpy.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsRtAccess.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset AsRtAMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.

Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.


Section CONTRACT.
  Context {fx0 : FPState}.   (* [comment removed for export] *)
  Context {RC : run_ceil}.   (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  (* [comment removed for export] *)
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props IA (AAINVH h) fsbase SEGS.
  (* [comment removed for export] *)
  Hypothesis SEGS_hull : forall a, find_segment SEGS a 1 <> None -> ia_img_lo IA <= a < ia_img_hi IA.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis IMG_HI : ia_img_hi IA <= AS_LO.
  Hypothesis IMG_LO : 0 <= ia_img_lo IA.
  Hypothesis FSB0 : 0 <= fsbase.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable t : amcpy_tab.
  Hypothesis TOK : forall fx : FPState, @amcpy_tab_ok fx SEGS t.
  Hypothesis T_entry : ac_base t = Z_to_bv 64 (ia_asan_memcpy IA).
  (* [comment removed for export] *)
  Definition amcpy_cells : list (Z * nat * Z) :=
    [(ac_g_flag t, 8%nat, ac_p_flag t); (ac_p_flag t, 1%nat, 1); (ac_c_rmc t, 8%nat, U (ac_mcp t));
     (mt_g_shoff (rt_m2s (ac_rip t)), 8%nat, mt_p_shoff (rt_m2s (ac_rip t))); (mt_p_shoff (rt_m2s (ac_rip t)), 8%nat, SB);
     (mt_g_midbeg (rt_m2s (ac_rip t)), 8%nat, mt_p_midbeg (rt_m2s (ac_rip t))); (mt_p_midbeg (rt_m2s (ac_rip t)), 8%nat, 0);
     (mt_g_midend (rt_m2s (ac_rip t)), 8%nat, mt_p_midend (rt_m2s (ac_rip t))); (mt_p_midend (rt_m2s (ac_rip t)), 8%nat, 0);
     (mt_g_hiend (rt_m2s (ac_rip t)), 8%nat, mt_p_hiend (rt_m2s (ac_rip t))); (mt_p_hiend (rt_m2s (ac_rip t)), 8%nat, 0x7fffffffffff)].
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN SEGS M (fst (fst c)) (snd (fst c)) (snd c)) amcpy_cells.
  (* [comment removed for export] *)
  Hypothesis CELLS_img : Forall (fun c => ia_img_lo IA <= fst (fst c) /\ fst (fst c) + 8 <= ia_img_hi IA) amcpy_cells.

  #[local] Abbreviation cfg := (AsIface3.cfg SEGS).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem C_asan_memcpy : MEMCPY_AT SEGS FXOK IA AAINVH (ia_asan_memcpy IA).
  Proof using CELLS_img CELLS T_entry TOK t FSB0 IMG_LO IMG_HI SEGS_wx SEGS_hull HP fsbase.
    (lazymatch goal with |- ?G => let G' := eval unfold MEMCPY_AT in G in change_no_check G' end).
    intros h fx R M mdl Lc FF W B C K ret sp dst src n bs HFX HH AI CP Hdst Hsrc Hn [Hn0 HnN] OV AIM1 AIM2 AIM3 AIM4
           ACCs ACCd SVs SVd HBS DO DSJ SSJ DOK.
    pose proof (HP h) as HPh.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk).
    destruct (aap_lazy _ _ _ _ HPh _ _ _ _ _ _ _ AI) as (AA & Awf & MI & SHCok & BLKok & PRES).
    set (Hd := HL mdl AA).
    pose proof (HL_off_segments SEGS IA (AAINVH h) fsbase HPh SEGS_hull _ _ _ _ _ _ _ AA AI) as HOFF. fold Hd in HOFF.
    pose proof (@ceil_rng RC) as CR.
    assert (NZ : forall z, 0 <= z < 2 ^ 64 -> (ia_img_lo IA <= z < ia_img_hi IA) \/ CEIL <= z -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HL_zone SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI Hz). tauto. }
    unfold AS_HEAPLO, PTRHI, SB, AS_LO, MSTK_M, NMAX in *.
    assert (RNGd : (0x10007fff8000 <= dst /\ dst + n < 2 ^ 47) \/ (0 <= dst /\ dst + n <= 0x7fff7fff)).
    { unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM1, AIM2. lia. }
    assert (RNGs : (0x10007fff8000 <= src /\ src + n < 2 ^ 47) \/ (0 <= src /\ src + n <= 0x7fff7fff)).
    { unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM3, AIM4. lia. }
    assert (Hdn2 : 0 <= dst /\ dst + n < 2 ^ 47) by lia. assert (Hsn2 : 0 <= src /\ src + n < 2 ^ 47) by lia.
    (* [comment removed for export] *)
    assert (NVIS : forall b m, shadow_visible IA Lc FF b m -> forall z, b <= z < b + m -> 0 <= z < 2 ^ 64 -> Hd (Z_to_bv 64 z) = false).
    { intros b m SV z Hz Hz64. destruct (SV z Hz) as [IB | [(f & k & Hf & Hfz) | [ST | IM]]].
      - apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [left; exact IB | exact Hz64].
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [right; exists f, k; split; [exact Hf | lia] | exact Hz64].
      - apply NZ; [lia | right; lia].
      - apply NZ; [lia | left; lia]. }
    assert (NDST : forall z, dst <= z < dst + n -> Hd (Z_to_bv 64 z) = false) by (intros z Hz; apply (NVIS _ _ SVd z Hz); lia).
    assert (NSRC : forall z, src <= z < src + n -> Hd (Z_to_bv 64 z) = false) by (intros z Hz; apply (NVIS _ _ SVs z Hz); lia).
    (* [comment removed for export] *)
    assert (NSH : forall b m, shadow_visible IA Lc FF b m ->
              forall z, b <= z < b + m -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false).
    { intros b m SV z Hz y Hy.
      destruct (SV z Hz) as [(p & pm & Hp & Hpz) | [(f & k & Hf & Hfz) | [ST | IM]]].
      - pose proof (aap_zone _ _ _ _ HPh _ _ _ _ _ _ _ p pm AI Hp) as ((Z1 & Z2 & Z3 & Z4) & Zn & Z16).
        apply (HL_allowed_page mdl AA (sh_lo p) (sh_hi p pm) (sh_lo z) y (BLKok p pm Hp)); [|exact Hy].
        apply sh_lo_in; unfold PTRLO in *; lia.
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_allowed_page mdl AA (sh_lo fsbase) (sh_hi fsbase FAKE_SIZE) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; unfold FAKE_SIZE in *; lia.
      - unfold PTRHI in ST.
        apply (HL_allowed_page mdl AA (sh_lo CEIL) (SB + 2 ^ 44) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + split; [apply sh_lo_mono; lia | apply sh_lo_lt47; lia].
      - apply (HL_allowed_page mdl AA (sh_lo (ia_img_lo IA)) (sh_hi (ia_img_lo IA) (ia_img_hi IA - ia_img_lo IA)) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; lia. }
    pose proof (NSH _ _ SVd) as NSHd. pose proof (NSH _ _ SVs) as NSHs.
    (* [comment removed for export] *)
    set (dstw := getr R 10) in *. set (srcw := getr R 11) in *. set (spw := getr R 2) in *.
    pose proof (u64_range dstw) as Hdr. pose proof (u64_range srcw) as Hsr0. pose proof (u64_range spw) as Hsr. pose proof (u64_range (getr R 12)) as H12r.
    assert (R12 : getr R 12 = Z_to_bv 64 n) by (apply bv_eq; rewrite u_Z2bv by lia; exact Hn).
    assert (RET : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u_Z2bv by lia; exact CPe).
    clear CPe CP16.   (* [comment removed for export] *)
    set (Mr := mrestrict Hd M).
    (* [comment removed for export] *)
    pose proof (CELLS _ _ _ _ _ _ _ _ AI) as CE. pose proof CELLS_img as CI. unfold amcpy_cells in CE, CI.
    apply Forall_cons_iff in CE; destruct CE as [C1 CE]. apply Forall_cons_iff in CE; destruct CE as [C2 CE]. apply Forall_cons_iff in CE; destruct CE as [C3 CE]. apply Forall_cons_iff in CE; destruct CE as [C4 CE]. apply Forall_cons_iff in CE; destruct CE as [C5 CE]. apply Forall_cons_iff in CE; destruct CE as [C6 CE]. apply Forall_cons_iff in CE; destruct CE as [C7 CE]. apply Forall_cons_iff in CE; destruct CE as [C8 CE]. apply Forall_cons_iff in CE; destruct CE as [C9 CE]. apply Forall_cons_iff in CE; destruct CE as [C10 CE]. apply Forall_cons_iff in CE; destruct CE as [C11 CE].
    apply Forall_cons_iff in CI; destruct CI as [D1 CI]. apply Forall_cons_iff in CI; destruct CI as [D2 CI]. apply Forall_cons_iff in CI; destruct CI as [D3 CI]. apply Forall_cons_iff in CI; destruct CI as [D4 CI]. apply Forall_cons_iff in CI; destruct CI as [D5 CI]. apply Forall_cons_iff in CI; destruct CI as [D6 CI]. apply Forall_cons_iff in CI; destruct CI as [D7 CI]. apply Forall_cons_iff in CI; destruct CI as [D8 CI]. apply Forall_cons_iff in CI; destruct CI as [D9 CI]. apply Forall_cons_iff in CI; destruct CI as [D10 CI]. apply Forall_cons_iff in CI; destruct CI as [D11 CI].
    cbn [fst snd] in *.
    Ltac hoz NZ := apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NZ; lia].
    Ltac konst NZ MM C := apply (cellN_mrestrict SEGS _ MM _ _ _ C); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); hoz NZ].
    assert (K1 : rdn SEGS Mr (Z_to_bv 64 (ac_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (ac_p_flag t)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C1).
    assert (K2 : rdn SEGS Mr (Z_to_bv 64 (ac_p_flag t)) 1 = Some [Z_to_bv 8 1]).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C2); [vm_compute; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K3 : rdn SEGS Mr (Z_to_bv 64 (ac_c_rmc t)) 8 = Some (word_to_le_bytes 8 (ac_mcp t))).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C3); [rewrite Z_to_bv_bv_unsigned; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K4 : rdn SEGS Mr (Z_to_bv 64 (mt_g_shoff (rt_m2s (ac_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_shoff (rt_m2s (ac_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C4).
    assert (K5 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midbeg (rt_m2s (ac_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midbeg (rt_m2s (ac_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C6).
    assert (K6 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midbeg (rt_m2s (ac_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C7).
    assert (K7 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midend (rt_m2s (ac_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midend (rt_m2s (ac_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C8).
    assert (K8 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midend (rt_m2s (ac_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C9).
    assert (K9 : rdn SEGS Mr (Z_to_bv 64 (mt_g_hiend (rt_m2s (ac_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_hiend (rt_m2s (ac_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C10).
    assert (K10 : rdn SEGS Mr (Z_to_bv 64 (mt_p_hiend (rt_m2s (ac_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C11).
    assert (K11 : rdn SEGS Mr (Z_to_bv 64 (mt_p_shoff (rt_m2s (ac_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C5).
    (* [comment removed for export] *)
    assert (WV : forall (m : mem) (x : word), store_ok SEGS m x 1%nat = true -> wview SEGS m x <> None).
    { intros m x Hx. cbn [store_ok] in Hx. destruct (wview SEGS m x); [discriminate | discriminate Hx]. }
    assert (STK : store_ok SEGS Mr (at_ spw (-2224)) 2224 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ].
      apply store_ok_of_all; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. apply WV. apply CPstk. cbn in Hx. lia. }
    assert (DOKr : store_ok SEGS Mr dstw (Z.to_nat n) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite Z2Nat.id; lia | rewrite Z2Nat.id by lia; apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NDST; lia]].
      apply store_ok_of_all; [rewrite Z2Nat.id; lia|]. intros x Hx. rewrite Z2Nat.id in Hx by lia. apply WV. apply DOK. lia. }
    assert (OFFS : forall b, off_scratch sp b (b + n) -> n = 0 \/ b + n <= U spw - 2224 \/ U spw <= b).
    { intros b BSJ. destruct (Z.eq_dec n 0) as [E0|NE0]; [left; exact E0 | right]. unfold off_scratch, MSTK_M in BSJ.
      pose proof (BSJ b ltac:(lia)) as X1. pose proof (BSJ (b + n - 1) ltac:(lia)) as X2.
      destruct (Z_lt_le_dec b (sp - 2304)) as [L|Ge]; [|lia].
      destruct (Z_lt_le_dec (b + n - 1) (sp - 2304)) as [L2|Ge2]; [lia|].
      exfalso. apply (BSJ (sp - 1)); lia. }
    pose proof (OFFS dst DSJ) as DSTK. pose proof (OFFS src SSJ) as SSTK. clear OFFS.
    (* [comment removed for export] *)
    assert (BS : rdn SEGS M srcw (Z.to_nat n) = Some bs).
    { replace srcw with (Z_to_bv 64 src) by (apply bv_eq; rewrite u_Z2bv by lia; symmetry; exact Hsrc). exact HBS. }
    pose proof (rdn_length _ _ _ _ _ BS) as LBS.
    assert (SR : hid_off Hd (U srcw) n) by (apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NSRC; lia]).
    assert (BSr : rdn SEGS Mr srcw (Z.to_nat n) = Some bs).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact BS | lia | rewrite Z2Nat.id by lia; exact SR]. }
    assert (MC : mcH SEGS Mr dstw srcw n bs).
    { split.
      - lia. - exact LBS. - rewrite LBS. exact BSr. - rewrite LBS. exact DOKr.
      - destruct OV as [O0 | O1]; [|lia]. destruct (Z_le_gt_dec (U dstw) (U srcw)); lia.
      - lia. - lia. }
    clear OV.
    assert (PRE : amcpyH SEGS t Mr dstw srcw n bs (Z_to_bv 64 ret) spw (Z_to_bv 8 1)).
    { split.
      - lia. - exact MC. - lia. - exact K1. - exact K2. - vm_compute; discriminate. - exact K3.
      - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); (nodisj; lia).
      - exact STK. - rewrite Hsrc; exact SSTK. - rewrite Hdst; exact DSTK. - exact RET. }
    clear DSTK SSTK.
    (* [comment removed for export] *)
    set (raw := Z_to_bv 64 ret) in *.
    assert (FR : hid_off Hd (U spw - 2224) 2224) by (hoz NZ).
    assert (DR : hid_off Hd (U dstw) n) by (apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NDST; lia]).
    assert (CM1_r : CM1 Mr raw spw R = mrestrict Hd (CM1 M raw spw R)).
    { clear - FR CP2 CPlo CPhi CR. (lazymatch goal with |- ?G => let G' := eval unfold Mr, CM1, amc_frame in G in change_no_check G' end).
      rewrite !(wbytes_mrestrict Hd) by
        (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
         first [hs_arith_goal; rewrite at_u by (nodisj; lia); (nodisj; lia) | rewrite at_u by (nodisj; lia); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]).
      reflexivity. }
    assert (POST_r : forall X, amcpy_post dstw bs (mrestrict Hd X) = mrestrict Hd (amcpy_post dstw bs X)).
    { intros X. (lazymatch goal with |- ?G => let G' := eval unfold amcpy_post in G in change_no_check G' end). apply (wbytes_mrestrict_at Hd _ X dstw n); [exact LBS | lia | lia | exact DR]. }
    (* [comment removed for export] *)
    assert (SEGnone : forall a : word, CEIL <= U a -> find_segment SEGS (U a) 1 = None).
    { intros a Ha. destruct (find_segment SEGS (U a) 1) eqn:E; [|reflexivity]. exfalso.
      pose proof (SEGS_hull (U a) ltac:(rewrite E; discriminate)). lia. }
    assert (FIN : forall (M' : mem) (r : bvmap 5 word),
      msteps SEGS (mkst R (ac_base t) Mr (seg_rom SEGS)) (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) ->
      getr r 10 = dstw -> (forall x, In x amset_saved -> getr r x = getr R x) ->
      (forall a : word, M' a <> M a -> dst <= U a < dst + n \/ sp - 2304 <= U a < sp) ->
      (forall i, 0 <= i < n -> M' (Z_to_bv 64 (dst + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
      mem_grows M M' ->
      katD SEGS (cfg fx R (ia_asan_memcpy IA) M mdl) (mem_post SEGS FXOK AAINVH h R M mdl Lc FF B C K ret sp dst n (fun i => Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))))).
    { intros M' r RUN A10 SAVED CHG BYTES GR.
      assert (NH' : forall a : word, Hd a = true -> M' a = M a).
      { intros a Ha. destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso.
        pose proof (u64_range a) as Har. destruct (CHG a NE) as [X|X].
        - rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NDST (U a) X) in Ha. discriminate Ha.
        - rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NZ (U a)) in Ha; [discriminate Ha | lia | right; lia]. }
      (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.cfg in G in change_no_check G' end). rewrite <- T_entry.
      apply (katD_msteps_acct SEGS Hd HOFF SEGS_wx AA (mkst R (ac_base t) M (seg_rom SEGS))
               (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) mdl _ (lazy_cover_HL mdl AA) Awf MI HH).
      - rewrite restrict_mkst'. exact RUN.
      - intros mdl' MI' SBM HC. rewrite unrestrict_mkst. (lazymatch goal with |- ?G => let G' := eval cbn [RiscvSemantics.ms_mem mkst] in G in change_no_check G' end).
        rewrite (munrestrict_mrestrict_same Hd M M' NH').
        assert (SCR : scratch_ok SEGS M' sp MSTK_M).
        { intros a Ha. unfold MSTK_M in Ha. split.
          - apply GR. apply (store_ok1_defined SEGS M a); [apply SEGnone; lia | apply CPstk; lia].
          - eapply store_ok_mono; [exact GR | apply CPstk; lia]. }
        apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold mem_post in G in change_no_check G' end). exists fx, r, M', mdl'.
        split; [reflexivity|]. split; [exact HFX|].
        split; [apply regs_kept_of_list; exact SAVED|].
        split; [rewrite A10; exact Hdst|].
        split; [exact BYTES|].
        split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); exact (CHG a Ha)|].
        split; [exact SCR|].
        split; [|exact SBM].
        destruct DO as [WOK OWN].
        apply (aap_frame _ _ _ _ HPh W Lc FF B C K M M' mdl' WOK (PRES mdl' MI' SBM)).
        intros a Ha. destruct (CHG a Ha) as [X|X].
        * split; [apply OWN; exact X|].
          replace a with (Z_to_bv 64 (dst + (U a - dst))) by (apply bv_eq; rewrite u_Z2bv; lia).
          rewrite (BYTES (U a - dst)) by lia. discriminate.
        * split; [right; right; left; lia|]. apply (proj1 (SCR a ltac:((lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); lia))). }
    (* [comment removed for export] *)
    assert (HSP' : (0x10007fff8000 + 2304 <= U spw)%Z /\ (U spw + 16 <= 2 ^ 47)%Z) by lia.
    assert (R1' : getr R 1 = raw) by exact CP1.
    assert (BY : forall X i, 0 <= i < n -> amcpy_post dstw bs X (Z_to_bv 64 (dst + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
    { intros X i Hi. (lazymatch goal with |- ?G => let G' := eval unfold amcpy_post in G in change_no_check G' end). rewrite (AsRtIMemmove.wbytes_get_g) by (rewrite LBS; lia).
      rewrite LBS, u_Z2bv by lia.
      replace (inrng (U dstw) (Z.of_nat (Z.to_nat n)) (dst + i)) with true by (symmetry; apply inrng_true; lia).
      f_equal. f_equal. lia. }
    assert (RDi : forall i, 0 <= i < n -> AsIface3.rd1 SEGS M (src + i) = Some [nth (Z.to_nat i) bs (Z_to_bv 8 0)]).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.rd1 in G in change_no_check G' end).
      replace (Z_to_bv 64 (src + i)) with (srcw + nat_to_word (Z.to_nat i))%bv
        by (rewrite at_nat; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); apply bv_eq; rewrite !Z_to_bv_unsigned; f_equal; lia).
      apply (rdn_nth SEGS M (Z.to_nat n) srcw bs (Z.to_nat i) BS). lia. }
    assert (OUT1 : forall a : word, ~ (dst <= U a < dst + n) -> ~ (sp - 2304 <= U a < sp) ->
                   amcpy_post dstw bs (CM1 M raw spw R) a = M a).
    { intros a N1 N2. (lazymatch goal with |- ?G => let G' := eval unfold amcpy_post in G in change_no_check G' end). pose proof (u64_range a).
      rewrite wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite LBS; lia | rewrite LBS; lia].
      apply (CM1_agree dstw M raw spw R HSP'). lia. }
    assert (GR1 : mem_grows M (amcpy_post dstw bs (CM1 M raw spw R))).
    { (lazymatch goal with |- ?G => let G' := eval unfold amcpy_post in G in change_no_check G' end). eapply mem_grows_trans; [apply CM1_grows | apply wbytes_grows]. }
    pose proof (fun z => aap_shdef _ _ _ _ HPh _ _ _ _ _ _ _ z AI) as SHD.
    assert (SH8 : sh_lo AS_HEAPLO mod 8 = 0 /\ AS_HEAPLO mod 8 = 0 /\ sh_lo AS_HEAPLO = 2201439137792) by (repeat split; reflexivity).
    (* [comment removed for export] *)
    assert (GRAN : forall b g, 0 <= b -> 1 <= n -> Sh b <= g < Sh (b + n - 1) + 1 -> exists z, b <= z < b + n /\ sh_lo z = g).
    { intros b g Hb Hn1 Hg. unfold Sh, sh_lo, SB in *.
      pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
      pose proof (Z.div_mod (b + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)).
      destruct (Z_lt_le_dec g (Sh (b + n - 1))) as [L|Ge]; unfold Sh in *.
      - exists (8 * (g - 2147450880) + 7). split; [lia|].
        replace (8 * (g - 2147450880) + 7) with ((g - 2147450880) * 8 + 7) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small 7 8) by lia. lia.
      - exists (b + n - 1). split; [lia|]. lia. }
    (* [comment removed for export] *)
    assert (RD1 : forall b, (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
                  forall (a : word) bs0, rdn SEGS M a 1%nat = Some bs0 -> (exists z, b <= z < b + n /\ sh_lo z = U a) ->
                  rdn SEGS Mr a 1%nat = Some bs0).
    { intros b NSHb a bs0 Hr (z & Hz & Ez). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). pose proof (u64_range a). rewrite rdn_mrestrict; [exact Hr | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      intros x Hx. cbn in Hx. replace x with a by (apply bv_eq; lia). apply (NSHb z Hz a). rewrite Ez. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    assert (RD8 : forall b, (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
                  ((0x10007fff8000 <= b /\ b + n < 2 ^ 47) \/ (0 <= b /\ b + n <= 0x7fff7fff)) ->
                  forall (w : Z) (z : Z), b <= z < b + n -> w = down8 (sh_lo z) ->
                  exists bs0, rdn SEGS Mr (Z_to_bv 64 w) 8%nat = Some bs0).
    { intros b NSHb RNG w z Hz Ew. pose proof (sh_lo_lt47 z ltac:(lia)) as SZ. pose proof (down8_le (sh_lo z) ltac:(unfold SB in SZ; lia)) as [DL DM].
      assert (LS8 : sh_lo SB = 2415882240 /\ sh_lo SB mod 8 = 0) by (split; reflexivity).
      assert (DEF8 : forall i, w <= i < w + 8 -> M (Z_to_bv 64 i) <> None).
      { destruct RNG as [[RH _] | [_ RL]].
        - assert (LO : sh_lo AS_HEAPLO <= w).
          { subst w. apply down8_ge; [exact (proj1 SH8)|]. apply sh_lo_mono. (lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia. }
          assert (HI : w + 8 <= AS_HEAPLO).
          { subst w. apply down8_lt_top; [exact (proj1 (proj2 SH8))|]. unfold AS_HEAPLO, SB in *. lia. }
          rewrite (proj2 (proj2 SH8)) in LO. unfold AS_HEAPLO in HI.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). right. (lazymatch goal with |- ?G => let G' := eval unfold AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). lia.
        - assert (LO : SB <= w).
          { subst w. apply down8_ge; [reflexivity|]. unfold SB in *. lia. }
          assert (HI : w + 8 <= sh_lo SB).
          { subst w. apply down8_lt_top; [exact (proj2 LS8)|]. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end).
            pose proof (Z.div_le_mono z 2147450879 8 ltac:(lia) ltac:(lia)). change (2147450879 / 8) with 268431359 in *. change (2147450880 / 8) with 268431360 in *. lia. }
          rewrite (proj1 LS8) in HI. unfold SB in LO.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). left. (lazymatch goal with |- ?G => let G' := eval unfold AS_LO, AS_GAPLO in G in change_no_check G' end). lia. }
      unfold SB in SZ.
      destruct (rdn_defined_ex SEGS M (Z_to_bv 64 w) 8) as (bs0 & Hbs & _).
      { intros i Hi. rewrite u_Z2bv in Hi by (nodisj; lia). apply DEF8. cbn in Hi. lia. }
      { rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
      exists bs0. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hbs | rewrite u_Z2bv by (nodisj; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (nodisj; lia) |].
      rewrite u_Z2bv by (nodisj; lia). intros x Hx. cbn in Hx. apply (NSHb z Hz x).
      apply (page_base_word8 w); [rewrite Ew; exact DM | (nodisj; lia) | (nodisj; lia) | rewrite u_Z2bv by (nodisj; lia); (nodisj; lia)]. }
    (* [comment removed for export] *)
    assert (QCH : forall (b : Z) (bw : word), U bw = b -> accessible M b n -> 1 <= n <= 64 ->
              (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
              ((0x10007fff8000 <= b /\ b + n < 2 ^ 47) \/ (0 <= b /\ b + n <= 0x7fff7fff)) ->
              exists w0 w1 s1, qc1H SEGS Mr bw n (mt_g_shoff (rt_m2s (ac_rip t))) (mt_p_shoff (rt_m2s (ac_rip t))) w0 w1 s1).
    { intros b bw Hb ACC Hs NSHb RNG.
      destruct (acc_last SEGS M b n ACC ltac:(lia)) as (s1 & Rs1 & Hs1).
      destruct (RD8 b NSHb RNG (down8 (sh_lo b)) b ltac:(lia) eq_refl) as (w0 & Rw0).
      destruct (RD8 b NSHb RNG (down8 (sh_lo (b + n - 1))) (b + n - 1) ltac:(lia) eq_refl) as (w1 & Rw1).
      exists w0, w1, s1. split; rewrite ?Hb.
      - lia. - lia. - exact K4. - exact K11. - lia.
      - rewrite Sh_is_sh_lo. exact Rw0.
      - rewrite Sh_is_sh_lo. exact Rw1.
      - apply (RD1 b NSHb _ _ Rs1). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (b + n - 1) ltac:(lia)). pose proof (sh_lo_mono b (b + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - exact Hs1.
      - intros a Ha. apply (RD1 b NSHb a _ (acc_zero SEGS M b n ACC ltac:(lia) a Ha)). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo in Ha |- *. lia. }
    (* [comment removed for export] *)
    assert (RGH : forall (b : Z) (bw : word), U bw = b -> accessible M b n -> 65 <= n ->
              (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
              ((0x10007fff8000 <= b /\ b + n < 2 ^ 47) \/ (0 <= b /\ b + n <= 0x7fff7fff)) ->
              exists s0b s1b : byte,
                rdn SEGS Mr (Z_to_bv 64 (Sh (U bw))) 1 = Some [s0b] /\ (U s0b = 0 \/ U bw mod 8 < U s0b < 128)
                /\ rdn SEGS Mr (Z_to_bv 64 (Sh (U bw + n - 1))) 1 = Some [s1b] /\ (U s1b = 0 \/ (U bw + n - 1) mod 8 < U s1b < 128)
                /\ (forall a : word, Sh (up8 (U bw)) <= U a < Sh (down8 (U bw + n)) -> rdn SEGS Mr a 1 = Some [Z_to_bv 8 0])).
    { intros b bw Hb ACC Hbg NSHb RNG. rewrite Hb.
      destruct (acc_first SEGS M b n ACC ltac:(lia)) as (s0b & Rs0 & Hs0).
      destruct (acc_last SEGS M b n ACC ltac:(lia)) as (s1b & Rs1 & Hs1).
      exists s0b, s1b. repeat split.
      - apply (RD1 b NSHb _ _ Rs0). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 b ltac:(lia)). pose proof (sh_lo_mono b (b + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - exact Hs0.
      - apply (RD1 b NSHb _ _ Rs1). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (b + n - 1) ltac:(lia)). pose proof (sh_lo_mono b (b + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - exact Hs1.
      - intros a Ha. apply (RD1 b NSHb a _ (acc_zero_mid SEGS M b n ACC ltac:(lia) a Ha)). apply GRAN; [lia|lia|].
        unfold Sh, up8, down8 in Ha |- *. clear - Ha.
        pose proof (Z.div_mod (b + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + 7) 8 ltac:(lia)).
        pose proof (Z.div_mod (b + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n) 8 ltac:(lia)).
        rewrite !Z.div_mul in Ha by lia.
        pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
        pose proof (Z.div_mod (b + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)). (nodisj; lia). }
    (* [comment removed for export] *)
    destruct (Z.eq_dec n 0) as [N0 | Nn0].
    { (* [comment removed for export] *)
      destruct (asan_memcpy_intrin_zero SEGS t (TOK fx) Mr (seg_rom SEGS) dstw srcw raw spw n bs (Z_to_bv 8 1) R PRE N0 R1' eq_refl eq_refl eq_refl R12)
        as (r & RUN & A10 & SAVED).
      rewrite CM1_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. apply OUT1; assumption.
      - intros i Hi. apply BY. exact Hi.
      - exact GR1. }
    destruct (Z_le_gt_dec n 64) as [Ns | Nb].
    { (* [comment removed for export] *)
      destruct (QCH src srcw Hsrc ACCs ltac:(lia) NSHs RNGs) as (w0s & w1s & s1s & QS).
      destruct (QCH dst dstw Hdst ACCd ltac:(lia) NSHd RNGd) as (w0d & w1d & s1d & QD).
      destruct (asan_memcpy_intrin_small SEGS t (TOK fx) Mr (seg_rom SEGS) dstw srcw raw spw n bs (Z_to_bv 8 1) R w0s w1s s1s w0d w1d s1d
                 PRE ltac:(lia) QS QD R1' eq_refl eq_refl eq_refl R12)
        as (r & RUN & A10 & SAVED).
      rewrite CM1_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. apply OUT1; assumption.
      - intros i Hi. apply BY. exact Hi.
      - exact GR1. }
    { (* [comment removed for export] *)
      assert (CH : forall bw : word, (0x10007fff8000 <= U bw \/ U bw <= 0x7fff7fff) -> U bw <= 0x7fffffffffff ->
                 m2sH SEGS (rt_m2s (ac_rip t)) Mr bw (Z_to_bv 64 0)).
      { intros bw H1 H2. split.
        - exact K4. - exact K11. - exact K5. - exact K6. - exact K7. - exact K8. - exact K9. - exact K10.
        - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); (nodisj; lia).
        - exact H1. - exact H2. }
      assert (Hn43 : 65 <= n <= 2 ^ 43) by (unfold NMAX in *; lia).
      assert (RUNx : exists r,
        msteps SEGS (mkst R (ac_base t) Mr (seg_rom SEGS))
                    (mkst r raw (amcpy_post dstw bs (CM3 (ac_base t) (ac_rip t) Mr dstw srcw raw spw n R)) (seg_rom SEGS))
        /\ getr r 10 = dstw /\ (forall x, In x amset_saved -> getr r x = getr R x)).
      { pose proof (CH srcw ltac:(lia) ltac:(lia)) as CHs. pose proof (CH dstw ltac:(lia) ltac:(lia)) as CHd.
        assert (Rgs : (0x10007fff8000 <= U srcw /\ U srcw + n + 1 <= 0x800000000000) \/ U srcw + n <= 0x7fff7fff) by lia.
        assert (Rgd : (0x10007fff8000 <= U dstw /\ U dstw + n + 1 <= 0x800000000000) \/ U dstw + n <= 0x7fff7fff) by lia.
        destruct (RGH src srcw Hsrc ACCs ltac:(lia) NSHs RNGs) as (s0s & s1s & Rs0s & Hs0s & Rs1s & Hs1s & Rzs).
        destruct (RGH dst dstw Hdst ACCd ltac:(lia) NSHd RNGd) as (s0d & s1d & Rs0d & Hs0d & Rs1d & Hs1d & Rzd).
        exact (asan_memcpy_intrin_big SEGS t (TOK fx) Mr (seg_rom SEGS) dstw srcw raw spw n bs (Z_to_bv 8 1) R s0s s1s s0d s1d (Z_to_bv 64 0)
                 PRE Hn43 CHs CHd Rgs Rgd Rs0s Hs0s Rs1s Hs1s Rzs Rs0d Hs0d Rs1d Hs1d Rzd R1' eq_refl eq_refl eq_refl R12). }
      destruct RUNx as (r & RUN & A10 & SAVED).
      (* [comment removed for export] *)
      assert (CM3_r : CM3 (ac_base t) (ac_rip t) Mr dstw srcw raw spw n R = mrestrict Hd (CM3 (ac_base t) (ac_rip t) M dstw srcw raw spw n R)).
      { clear - FR CP2 CPlo CPhi CR CM1_r POST_r. (lazymatch goal with |- ?G => let G' := eval unfold CM3, CM2 in G in change_no_check G' end). rewrite CM1_r. (lazymatch goal with |- ?G => let G' := eval unfold rip_mem, ps_frame in G in change_no_check G' end).
        pose proof (u64_range spw).
        repeat (lazymatch goal with
                | |- context [if Z.ltb ?a ?b then _ else _] => destruct (Z.ltb a b)
                end);
        rewrite !(wbytes_mrestrict Hd) by
          (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
           first [hs_arith_goal; rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); (nodisj; lia)
                 | rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]);
        reflexivity. }
      rewrite CM3_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      + clear RNGd RNGs QCH RGH RD8 RD1 GRAN CH FIN.
        intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. (lazymatch goal with |- ?G => let G' := eval unfold amcpy_post in G in change_no_check G' end). pose proof (u64_range a).
        rewrite wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite LBS; lia | rewrite LBS; lia].
        apply (CM3_agree (ac_base t) (ac_rip t) M dstw srcw raw spw n R HSP'). lia.
      + intros i Hi. apply BY. exact Hi.
      + (lazymatch goal with |- ?G => let G' := eval unfold amcpy_post in G in change_no_check G' end). eapply mem_grows_trans; [apply CM3_grows | apply wbytes_grows]. }
  Qed.

End CONTRACT.
End AsIcptMemcpy.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsIcptMemmove.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsRtAccess.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac nodisjk K := repeat match goal with H : _ \/ _ |- _ => tryif constr_eq H K then fail else clear H end.

Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.


Section CONTRACT.
  Context {fx0 : FPState}.   (* [comment removed for export] *)
  Context {RC : run_ceil}.   (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  (* [comment removed for export] *)
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props IA (AAINVH h) fsbase SEGS.
  (* [comment removed for export] *)
  Hypothesis SEGS_hull : forall a, find_segment SEGS a 1 <> None -> ia_img_lo IA <= a < ia_img_hi IA.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis IMG_HI : ia_img_hi IA <= AS_LO.
  Hypothesis IMG_LO : 0 <= ia_img_lo IA.
  Hypothesis FSB0 : 0 <= fsbase.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable t : ammove_tab.
  Hypothesis TOK : forall fx : FPState, @ammove_tab_ok fx SEGS t.
  Hypothesis T_entry : mm_base t = Z_to_bv 64 (ia_asan_memmove IA).
  (* [comment removed for export] *)
  Definition ammove_cells : list (Z * nat * Z) :=
    [(mm_g_flag t, 8%nat, mm_p_flag t); (mm_p_flag t, 1%nat, 1);
     (mt_g_shoff (rt_m2s (mm_rip t)), 8%nat, mt_p_shoff (rt_m2s (mm_rip t))); (mt_p_shoff (rt_m2s (mm_rip t)), 8%nat, SB);
     (mt_g_midbeg (rt_m2s (mm_rip t)), 8%nat, mt_p_midbeg (rt_m2s (mm_rip t))); (mt_p_midbeg (rt_m2s (mm_rip t)), 8%nat, 0);
     (mt_g_midend (rt_m2s (mm_rip t)), 8%nat, mt_p_midend (rt_m2s (mm_rip t))); (mt_p_midend (rt_m2s (mm_rip t)), 8%nat, 0);
     (mt_g_hiend (rt_m2s (mm_rip t)), 8%nat, mt_p_hiend (rt_m2s (mm_rip t))); (mt_p_hiend (rt_m2s (mm_rip t)), 8%nat, 0x7fffffffffff)].
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN SEGS M (fst (fst c)) (snd (fst c)) (snd c)) ammove_cells.
  (* [comment removed for export] *)
  Hypothesis CELLS_img : Forall (fun c => ia_img_lo IA <= fst (fst c) /\ fst (fst c) + 8 <= ia_img_hi IA) ammove_cells.

  #[local] Abbreviation cfg := (AsIface3.cfg SEGS).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem C_asan_memmove : MEMMOVE_AT SEGS FXOK IA AAINVH (ia_asan_memmove IA).
  Proof using CELLS_img CELLS T_entry TOK t FSB0 IMG_LO IMG_HI SEGS_wx SEGS_hull HP fsbase.
    (lazymatch goal with |- ?G => let G' := eval unfold MEMMOVE_AT in G in change_no_check G' end).
    intros h fx R M mdl Lc FF W B C K ret sp dst src n bs HFX HH AI CP Hdst Hsrc Hn [Hn0 HnN] AIM1 AIM2 AIM3 AIM4
           ACCs ACCd SVs SVd HBS ALIAS DO DSJ SSJ DOK.
    pose proof (HP h) as HPh.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk).
    destruct (aap_lazy _ _ _ _ HPh _ _ _ _ _ _ _ AI) as (AA & Awf & MI & SHCok & BLKok & PRES).
    set (Hd := HL mdl AA).
    pose proof (HL_off_segments SEGS IA (AAINVH h) fsbase HPh SEGS_hull _ _ _ _ _ _ _ AA AI) as HOFF. fold Hd in HOFF.
    pose proof (@ceil_rng RC) as CR.
    assert (NZ : forall z, 0 <= z < 2 ^ 64 -> (ia_img_lo IA <= z < ia_img_hi IA) \/ CEIL <= z -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HL_zone SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI Hz). tauto. }
    unfold AS_HEAPLO, PTRHI, SB, AS_LO, MSTK_M, NMAX in *.
    assert (RNGd : (0x10007fff8000 <= dst /\ dst + n < 2 ^ 47) \/ (0 <= dst /\ dst + n <= 0x7fff7fff)).
    { unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM1, AIM2. lia. }
    assert (RNGs : (0x10007fff8000 <= src /\ src + n < 2 ^ 47) \/ (0 <= src /\ src + n <= 0x7fff7fff)).
    { unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM3, AIM4. lia. }
    assert (Hdn2 : 0 <= dst /\ dst + n < 2 ^ 47) by lia. assert (Hsn2 : 0 <= src /\ src + n < 2 ^ 47) by lia.
    (* [comment removed for export] *)
    assert (NVIS : forall b m, shadow_visible IA Lc FF b m -> forall z, b <= z < b + m -> 0 <= z < 2 ^ 64 -> Hd (Z_to_bv 64 z) = false).
    { intros b m SV z Hz Hz64. destruct (SV z Hz) as [IB | [(f & k & Hf & Hfz) | [ST | IM]]].
      - apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [left; exact IB | exact Hz64].
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [right; exists f, k; split; [exact Hf | lia] | exact Hz64].
      - apply NZ; [lia | right; lia].
      - apply NZ; [lia | left; lia]. }
    assert (NDST : forall z, dst <= z < dst + n -> Hd (Z_to_bv 64 z) = false) by (intros z Hz; apply (NVIS _ _ SVd z Hz); lia).
    assert (NSRC : forall z, src <= z < src + n -> Hd (Z_to_bv 64 z) = false) by (intros z Hz; apply (NVIS _ _ SVs z Hz); lia).
    (* [comment removed for export] *)
    assert (NSH : forall b m, shadow_visible IA Lc FF b m ->
              forall z, b <= z < b + m -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false).
    { intros b m SV z Hz y Hy.
      destruct (SV z Hz) as [(p & pm & Hp & Hpz) | [(f & k & Hf & Hfz) | [ST | IM]]].
      - pose proof (aap_zone _ _ _ _ HPh _ _ _ _ _ _ _ p pm AI Hp) as ((Z1 & Z2 & Z3 & Z4) & Zn & Z16).
        apply (HL_allowed_page mdl AA (sh_lo p) (sh_hi p pm) (sh_lo z) y (BLKok p pm Hp)); [|exact Hy].
        apply sh_lo_in; unfold PTRLO in *; lia.
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_allowed_page mdl AA (sh_lo fsbase) (sh_hi fsbase FAKE_SIZE) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; unfold FAKE_SIZE in *; lia.
      - unfold PTRHI in ST.
        apply (HL_allowed_page mdl AA (sh_lo CEIL) (SB + 2 ^ 44) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + split; [apply sh_lo_mono; lia | apply sh_lo_lt47; lia].
      - apply (HL_allowed_page mdl AA (sh_lo (ia_img_lo IA)) (sh_hi (ia_img_lo IA) (ia_img_hi IA - ia_img_lo IA)) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; lia. }
    pose proof (NSH _ _ SVd) as NSHd. pose proof (NSH _ _ SVs) as NSHs.
    (* [comment removed for export] *)
    set (dstw := getr R 10) in *. set (srcw := getr R 11) in *. set (spw := getr R 2) in *.
    pose proof (u64_range dstw) as Hdr. pose proof (u64_range srcw) as Hsr0. pose proof (u64_range spw) as Hsr. pose proof (u64_range (getr R 12)) as H12r.
    assert (R12 : getr R 12 = Z_to_bv 64 n) by (apply bv_eq; rewrite u_Z2bv by lia; exact Hn).
    assert (RET : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u_Z2bv by lia; exact CPe).
    clear CPe CP16.   (* [comment removed for export] *)
    set (Mr := mrestrict Hd M).
    (* [comment removed for export] *)
    pose proof (CELLS _ _ _ _ _ _ _ _ AI) as CE. pose proof CELLS_img as CI. unfold ammove_cells in CE, CI.
    apply Forall_cons_iff in CE; destruct CE as [C1 CE]. apply Forall_cons_iff in CE; destruct CE as [C2 CE]. apply Forall_cons_iff in CE; destruct CE as [C3 CE]. apply Forall_cons_iff in CE; destruct CE as [C4 CE]. apply Forall_cons_iff in CE; destruct CE as [C5 CE]. apply Forall_cons_iff in CE; destruct CE as [C6 CE]. apply Forall_cons_iff in CE; destruct CE as [C7 CE]. apply Forall_cons_iff in CE; destruct CE as [C8 CE]. apply Forall_cons_iff in CE; destruct CE as [C9 CE]. apply Forall_cons_iff in CE; destruct CE as [C10 CE].
    apply Forall_cons_iff in CI; destruct CI as [D1 CI]. apply Forall_cons_iff in CI; destruct CI as [D2 CI]. apply Forall_cons_iff in CI; destruct CI as [D3 CI]. apply Forall_cons_iff in CI; destruct CI as [D4 CI]. apply Forall_cons_iff in CI; destruct CI as [D5 CI]. apply Forall_cons_iff in CI; destruct CI as [D6 CI]. apply Forall_cons_iff in CI; destruct CI as [D7 CI]. apply Forall_cons_iff in CI; destruct CI as [D8 CI]. apply Forall_cons_iff in CI; destruct CI as [D9 CI]. apply Forall_cons_iff in CI; destruct CI as [D10 CI].
    cbn [fst snd] in *.
    Ltac hoz NZ := apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NZ; lia].
    Ltac konst NZ MM C := apply (cellN_mrestrict SEGS _ MM _ _ _ C); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); hoz NZ].
    assert (K1 : rdn SEGS Mr (Z_to_bv 64 (mm_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mm_p_flag t)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C1).
    assert (K2 : rdn SEGS Mr (Z_to_bv 64 (mm_p_flag t)) 1 = Some [Z_to_bv 8 1]).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C2); [vm_compute; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K4 : rdn SEGS Mr (Z_to_bv 64 (mt_g_shoff (rt_m2s (mm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_shoff (rt_m2s (mm_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C3).
    assert (K5 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midbeg (rt_m2s (mm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midbeg (rt_m2s (mm_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C5).
    assert (K6 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midbeg (rt_m2s (mm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C6).
    assert (K7 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midend (rt_m2s (mm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midend (rt_m2s (mm_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C7).
    assert (K8 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midend (rt_m2s (mm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C8).
    assert (K9 : rdn SEGS Mr (Z_to_bv 64 (mt_g_hiend (rt_m2s (mm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_hiend (rt_m2s (mm_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C9).
    assert (K10 : rdn SEGS Mr (Z_to_bv 64 (mt_p_hiend (rt_m2s (mm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C10).
    assert (K11 : rdn SEGS Mr (Z_to_bv 64 (mt_p_shoff (rt_m2s (mm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C4).
    (* [comment removed for export] *)
    assert (WV : forall (m : mem) (x : word), store_ok SEGS m x 1%nat = true -> wview SEGS m x <> None).
    { intros m x Hx. cbn [store_ok] in Hx. destruct (wview SEGS m x); [discriminate | discriminate Hx]. }
    assert (STK : store_ok SEGS Mr (at_ spw (-2224)) 2224 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ].
      apply store_ok_of_all; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. apply WV. apply CPstk. cbn in Hx. lia. }
    assert (DOKr : store_ok SEGS Mr dstw (Z.to_nat n) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite Z2Nat.id; lia | rewrite Z2Nat.id by lia; apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NDST; lia]].
      apply store_ok_of_all; [rewrite Z2Nat.id; lia|]. intros x Hx. rewrite Z2Nat.id in Hx by lia. apply WV. apply DOK. lia. }
    assert (OFFS : forall b, off_scratch sp b (b + n) -> n = 0 \/ b + n <= U spw - 2224 \/ U spw <= b).
    { intros b BSJ. destruct (Z.eq_dec n 0) as [E0|NE0]; [left; exact E0 | right]. unfold off_scratch, MSTK_M in BSJ.
      pose proof (BSJ b ltac:(lia)) as X1. pose proof (BSJ (b + n - 1) ltac:(lia)) as X2.
      destruct (Z_lt_le_dec b (sp - 2304)) as [L|Ge]; [|lia].
      destruct (Z_lt_le_dec (b + n - 1) (sp - 2304)) as [L2|Ge2]; [lia|].
      exfalso. apply (BSJ (sp - 1)); lia. }
    pose proof (OFFS dst DSJ) as DSTK. pose proof (OFFS src SSJ) as SSTK. clear OFFS.
    (* [comment removed for export] *)
    assert (BS : rdn SEGS M srcw (Z.to_nat n) = Some bs).
    { replace srcw with (Z_to_bv 64 src) by (apply bv_eq; rewrite u_Z2bv by lia; symmetry; exact Hsrc). exact HBS. }
    pose proof (rdn_length _ _ _ _ _ BS) as LBS.
    assert (SR : hid_off Hd (U srcw) n) by (apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NSRC; lia]).
    assert (BSr : rdn SEGS Mr srcw (Z.to_nat n) = Some bs).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact BS | lia | rewrite Z2Nat.id by lia; exact SR]. }
    assert (MV : moveH SEGS Mr dstw srcw n bs).
    { split.
      - lia. - exact LBS. - rewrite LBS. exact BSr. - exact DOKr. - lia. - lia. }
    assert (PRE : ammoveH SEGS t Mr dstw srcw n bs (Z_to_bv 64 ret) spw (Z_to_bv 8 1)).
    { split.
      - lia. - exact MV. - lia. - exact K1. - exact K2. - vm_compute; discriminate.
      - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); (nodisj; lia).
      - exact STK. - rewrite Hsrc; exact SSTK. - rewrite Hdst; exact DSTK. - exact RET. }
    clear SSTK.
    (* [comment removed for export] *)
    set (raw := Z_to_bv 64 ret) in *.
    assert (FR : hid_off Hd (U spw - 2224) 2224) by (hoz NZ).
    assert (DR : hid_off Hd (U dstw) n) by (apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NDST; lia]).
    assert (DM1_r : DM1 Mr raw spw R = mrestrict Hd (DM1 M raw spw R)).
    { clear - FR CP2 CPlo CPhi CR. (lazymatch goal with |- ?G => let G' := eval unfold Mr, DM1, amm_frame in G in change_no_check G' end).
      rewrite !(wbytes_mrestrict Hd) by
        (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
         first [hs_arith_goal; rewrite at_u by (nodisj; lia); (nodisj; lia) | rewrite at_u by (nodisj; lia); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]).
      reflexivity. }
    assert (POST_r : forall X, ammove_post dstw srcw bs (mrestrict Hd X) = mrestrict Hd (ammove_post dstw srcw bs X)).
    { intros X. (lazymatch goal with |- ?G => let G' := eval unfold ammove_post, imemmove_result in G in change_no_check G' end). destruct (Z.eqb (U dstw) (U srcw)); [reflexivity|].
      apply (wbytes_mrestrict_at Hd _ X dstw n); [exact LBS | lia | lia | exact DR]. }
    (* [comment removed for export] *)
    assert (SEGnone : forall a : word, CEIL <= U a -> find_segment SEGS (U a) 1 = None).
    { intros a Ha. destruct (find_segment SEGS (U a) 1) eqn:E; [|reflexivity]. exfalso.
      pose proof (SEGS_hull (U a) ltac:(rewrite E; discriminate)). lia. }
    assert (FIN : forall (M' : mem) (r : bvmap 5 word),
      msteps SEGS (mkst R (mm_base t) Mr (seg_rom SEGS)) (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) ->
      getr r 10 = dstw -> (forall x, In x amset_saved -> getr r x = getr R x) ->
      (forall a : word, M' a <> M a -> dst <= U a < dst + n \/ sp - 2304 <= U a < sp) ->
      (forall i, 0 <= i < n -> M' (Z_to_bv 64 (dst + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
      mem_grows M M' ->
      katD SEGS (cfg fx R (ia_asan_memmove IA) M mdl) (mem_post SEGS FXOK AAINVH h R M mdl Lc FF B C K ret sp dst n (fun i => Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))))).
    { intros M' r RUN A10 SAVED CHG BYTES GR.
      assert (NH' : forall a : word, Hd a = true -> M' a = M a).
      { intros a Ha. destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso.
        pose proof (u64_range a) as Har. destruct (CHG a NE) as [X|X].
        - rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NDST (U a) X) in Ha. discriminate Ha.
        - rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NZ (U a)) in Ha; [discriminate Ha | lia | right; lia]. }
      (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.cfg in G in change_no_check G' end). rewrite <- T_entry.
      apply (katD_msteps_acct SEGS Hd HOFF SEGS_wx AA (mkst R (mm_base t) M (seg_rom SEGS))
               (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) mdl _ (lazy_cover_HL mdl AA) Awf MI HH).
      - rewrite restrict_mkst'. exact RUN.
      - intros mdl' MI' SBM HC. rewrite unrestrict_mkst. (lazymatch goal with |- ?G => let G' := eval cbn [RiscvSemantics.ms_mem mkst] in G in change_no_check G' end).
        rewrite (munrestrict_mrestrict_same Hd M M' NH').
        assert (SCR : scratch_ok SEGS M' sp MSTK_M).
        { intros a Ha. unfold MSTK_M in Ha. split.
          - apply GR. apply (store_ok1_defined SEGS M a); [apply SEGnone; lia | apply CPstk; lia].
          - eapply store_ok_mono; [exact GR | apply CPstk; lia]. }
        apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold mem_post in G in change_no_check G' end). exists fx, r, M', mdl'.
        split; [reflexivity|]. split; [exact HFX|].
        split; [apply regs_kept_of_list; exact SAVED|].
        split; [rewrite A10; exact Hdst|].
        split; [exact BYTES|].
        split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); exact (CHG a Ha)|].
        split; [exact SCR|].
        split; [|exact SBM].
        destruct DO as [WOK OWN].
        apply (aap_frame _ _ _ _ HPh W Lc FF B C K M M' mdl' WOK (PRES mdl' MI' SBM)).
        intros a Ha. destruct (CHG a Ha) as [X|X].
        * split; [apply OWN; exact X|].
          replace a with (Z_to_bv 64 (dst + (U a - dst))) by (apply bv_eq; rewrite u_Z2bv; lia).
          rewrite (BYTES (U a - dst)) by lia. discriminate.
        * split; [right; right; left; lia|]. apply (proj1 (SCR a ltac:((lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); lia))). }
    (* [comment removed for export] *)
    assert (HSP' : (0x10007fff8000 + 2304 <= U spw)%Z /\ (U spw + 16 <= 2 ^ 47)%Z) by lia.
    assert (R1' : getr R 1 = raw) by exact CP1.
    assert (BY : forall X i, 0 <= i < n -> wbytes X dstw bs (Z_to_bv 64 (dst + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
    { intros X i Hi. rewrite (AsRtIMemmove.wbytes_get_g) by (rewrite LBS; lia).
      rewrite LBS, u_Z2bv by lia.
      replace (inrng (U dstw) (Z.of_nat (Z.to_nat n)) (dst + i)) with true by (symmetry; apply inrng_true; lia).
      f_equal. f_equal. lia. }
    assert (RDi : forall i, 0 <= i < n -> AsIface3.rd1 SEGS M (src + i) = Some [nth (Z.to_nat i) bs (Z_to_bv 8 0)]).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.rd1 in G in change_no_check G' end).
      replace (Z_to_bv 64 (src + i)) with (srcw + nat_to_word (Z.to_nat i))%bv
        by (rewrite at_nat; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); apply bv_eq; rewrite !Z_to_bv_unsigned; f_equal; lia).
      apply (rdn_nth SEGS M (Z.to_nat n) srcw bs (Z.to_nat i) BS). lia. }
    assert (BEQ : forall X, (forall x : word, U x < U spw - 2224 \/ U spw <= U x -> X x = M x) ->
                  forall i, 0 <= i < n -> ammove_post dstw srcw bs X (Z_to_bv 64 (dst + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
    { intros X HX i Hi. (lazymatch goal with |- ?G => let G' := eval unfold ammove_post, imemmove_result in G in change_no_check G' end).
      destruct (Z.eqb_spec (U dstw) (U srcw)) as [E|NE].
      - destruct ALIAS as [NEQ | SDEF']; [exfalso; apply NEQ; lia|].
        destruct (M (Z_to_bv 64 (src + i))) as [b|] eqn:Hb; [|exfalso; exact (SDEF' i Hi Hb)].
        pose proof (RDi i Hi) as Ri. unfold AsIface3.rd1 in Ri. rewrite (rdn1_of_mem _ _ _ _ Hb) in Ri.
        injection Ri as Eb.
        replace (dst + i) with (src + i) by lia. rewrite HX; [rewrite Hb; f_equal; exact Eb|]. rewrite u_Z2bv by lia. clear -Hi DSTK Hdst Hsrc E Hn0 Hdn2 Hsn2. lia.
      - apply BY; exact Hi. }
    clear DSTK.
    assert (OUT1 : forall a : word, ~ (dst <= U a < dst + n) -> ~ (sp - 2304 <= U a < sp) ->
                   ammove_post dstw srcw bs (DM1 M raw spw R) a = M a).
    { intros a N1 N2. (lazymatch goal with |- ?G => let G' := eval unfold ammove_post, imemmove_result in G in change_no_check G' end). pose proof (u64_range a).
      destruct (Z.eqb (U dstw) (U srcw)); [apply (DM1_agree dstw M raw spw R HSP'); lia|].
      rewrite wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite LBS; lia | rewrite LBS; lia].
      apply (DM1_agree dstw M raw spw R HSP'). lia. }
    assert (GR1 : mem_grows M (ammove_post dstw srcw bs (DM1 M raw spw R))).
    { (lazymatch goal with |- ?G => let G' := eval unfold ammove_post, imemmove_result in G in change_no_check G' end). destruct (Z.eqb (U dstw) (U srcw)); [apply DM1_grows|].
      eapply mem_grows_trans; [apply DM1_grows | apply wbytes_grows]. }
    pose proof (fun z => aap_shdef _ _ _ _ HPh _ _ _ _ _ _ _ z AI) as SHD.
    assert (SH8 : sh_lo AS_HEAPLO mod 8 = 0 /\ AS_HEAPLO mod 8 = 0 /\ sh_lo AS_HEAPLO = 2201439137792) by (repeat split; reflexivity).
    (* [comment removed for export] *)
    assert (GRAN : forall b g, 0 <= b -> 1 <= n -> Sh b <= g < Sh (b + n - 1) + 1 -> exists z, b <= z < b + n /\ sh_lo z = g).
    { intros b g Hb Hn1 Hg. unfold Sh, sh_lo, SB in *.
      pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
      pose proof (Z.div_mod (b + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)).
      destruct (Z_lt_le_dec g (Sh (b + n - 1))) as [L|Ge]; unfold Sh in *.
      - exists (8 * (g - 2147450880) + 7). split; [lia|].
        replace (8 * (g - 2147450880) + 7) with ((g - 2147450880) * 8 + 7) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small 7 8) by lia. lia.
      - exists (b + n - 1). split; [lia|]. lia. }
    (* [comment removed for export] *)
    assert (RD1 : forall b, (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
                  forall (a : word) bs0, rdn SEGS M a 1%nat = Some bs0 -> (exists z, b <= z < b + n /\ sh_lo z = U a) ->
                  rdn SEGS Mr a 1%nat = Some bs0).
    { intros b NSHb a bs0 Hr (z & Hz & Ez). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). pose proof (u64_range a). rewrite rdn_mrestrict; [exact Hr | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      intros x Hx. cbn in Hx. replace x with a by (apply bv_eq; lia). apply (NSHb z Hz a). rewrite Ez. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    assert (RD8 : forall b, (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
                  ((0x10007fff8000 <= b /\ b + n < 2 ^ 47) \/ (0 <= b /\ b + n <= 0x7fff7fff)) ->
                  forall (w : Z) (z : Z), b <= z < b + n -> w = down8 (sh_lo z) ->
                  exists bs0, rdn SEGS Mr (Z_to_bv 64 w) 8%nat = Some bs0).
    { intros b NSHb RNG w z Hz Ew. pose proof (sh_lo_lt47 z ltac:(lia)) as SZ. pose proof (down8_le (sh_lo z) ltac:(unfold SB in SZ; lia)) as [DL DM].
      assert (LS8 : sh_lo SB = 2415882240 /\ sh_lo SB mod 8 = 0) by (split; reflexivity).
      assert (DEF8 : forall i, w <= i < w + 8 -> M (Z_to_bv 64 i) <> None).
      { destruct RNG as [[RH _] | [_ RL]].
        - assert (LO : sh_lo AS_HEAPLO <= w).
          { subst w. apply down8_ge; [exact (proj1 SH8)|]. apply sh_lo_mono. (lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia. }
          assert (HI : w + 8 <= AS_HEAPLO).
          { subst w. apply down8_lt_top; [exact (proj1 (proj2 SH8))|]. unfold AS_HEAPLO, SB in *. lia. }
          rewrite (proj2 (proj2 SH8)) in LO. unfold AS_HEAPLO in HI.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). right. (lazymatch goal with |- ?G => let G' := eval unfold AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). lia.
        - assert (LO : SB <= w).
          { subst w. apply down8_ge; [reflexivity|]. unfold SB in *. lia. }
          assert (HI : w + 8 <= sh_lo SB).
          { subst w. apply down8_lt_top; [exact (proj2 LS8)|]. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end).
            pose proof (Z.div_le_mono z 2147450879 8 ltac:(lia) ltac:(lia)). change (2147450879 / 8) with 268431359 in *. change (2147450880 / 8) with 268431360 in *. lia. }
          rewrite (proj1 LS8) in HI. unfold SB in LO.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). left. (lazymatch goal with |- ?G => let G' := eval unfold AS_LO, AS_GAPLO in G in change_no_check G' end). lia. }
      unfold SB in SZ.
      destruct (rdn_defined_ex SEGS M (Z_to_bv 64 w) 8) as (bs0 & Hbs & _).
      { intros i Hi. rewrite u_Z2bv in Hi by (nodisj; lia). apply DEF8. cbn in Hi. lia. }
      { rewrite u_Z2bv by (nodisj; lia). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (nodisj; lia). }
      exists bs0. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hbs | rewrite u_Z2bv by (nodisj; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (nodisj; lia) |].
      rewrite u_Z2bv by (nodisj; lia). intros x Hx. cbn in Hx. apply (NSHb z Hz x).
      apply (page_base_word8 w); [rewrite Ew; exact DM | (nodisj; lia) | (nodisj; lia) | rewrite u_Z2bv by (nodisj; lia); (nodisj; lia)]. }
    (* [comment removed for export] *)
    assert (QCH : forall (b : Z) (bw : word), U bw = b -> accessible M b n -> 1 <= n <= 64 ->
              (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
              ((0x10007fff8000 <= b /\ b + n < 2 ^ 47) \/ (0 <= b /\ b + n <= 0x7fff7fff)) ->
              exists w0 w1 s1, qc1H SEGS Mr bw n (mt_g_shoff (rt_m2s (mm_rip t))) (mt_p_shoff (rt_m2s (mm_rip t))) w0 w1 s1).
    { intros b bw Hb ACC Hs NSHb RNG.
      destruct (acc_last SEGS M b n ACC ltac:(lia)) as (s1 & Rs1 & Hs1).
      destruct (RD8 b NSHb RNG (down8 (sh_lo b)) b ltac:(lia) eq_refl) as (w0 & Rw0).
      destruct (RD8 b NSHb RNG (down8 (sh_lo (b + n - 1))) (b + n - 1) ltac:(lia) eq_refl) as (w1 & Rw1).
      exists w0, w1, s1. split; rewrite ?Hb.
      - lia. - lia. - exact K4. - exact K11. - (nodisj; lia).
      - rewrite Sh_is_sh_lo. exact Rw0.
      - rewrite Sh_is_sh_lo. exact Rw1.
      - apply (RD1 b NSHb _ _ Rs1). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (b + n - 1) ltac:(lia)). pose proof (sh_lo_mono b (b + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - exact Hs1.
      - intros a Ha. apply (RD1 b NSHb a _ (acc_zero SEGS M b n ACC ltac:(lia) a Ha)). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo in Ha |- *. lia. }
    (* [comment removed for export] *)
    assert (RGH : forall (b : Z) (bw : word), U bw = b -> accessible M b n -> 65 <= n ->
              (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
              ((0x10007fff8000 <= b /\ b + n < 2 ^ 47) \/ (0 <= b /\ b + n <= 0x7fff7fff)) ->
              exists s0b s1b : byte,
                rdn SEGS Mr (Z_to_bv 64 (Sh (U bw))) 1 = Some [s0b] /\ (U s0b = 0 \/ U bw mod 8 < U s0b < 128)
                /\ rdn SEGS Mr (Z_to_bv 64 (Sh (U bw + n - 1))) 1 = Some [s1b] /\ (U s1b = 0 \/ (U bw + n - 1) mod 8 < U s1b < 128)
                /\ (forall a : word, Sh (up8 (U bw)) <= U a < Sh (down8 (U bw + n)) -> rdn SEGS Mr a 1 = Some [Z_to_bv 8 0])).
    { intros b bw Hb ACC Hbg NSHb RNG. rewrite Hb.
      destruct (acc_first SEGS M b n ACC ltac:(lia)) as (s0b & Rs0 & Hs0).
      destruct (acc_last SEGS M b n ACC ltac:(lia)) as (s1b & Rs1 & Hs1).
      exists s0b, s1b. repeat split.
      - apply (RD1 b NSHb _ _ Rs0). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 b ltac:(lia)). pose proof (sh_lo_mono b (b + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - exact Hs0.
      - apply (RD1 b NSHb _ _ Rs1). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (b + n - 1) ltac:((nodisjk RNG; lia))). pose proof (sh_lo_mono b (b + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - exact Hs1.
      - intros a Ha. apply (RD1 b NSHb a _ (acc_zero_mid SEGS M b n ACC ltac:(lia) a Ha)). apply GRAN; [lia|lia|].
        unfold Sh, up8, down8 in Ha |- *. clear - Ha.
        pose proof (Z.div_mod (b + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + 7) 8 ltac:(lia)).
        pose proof (Z.div_mod (b + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n) 8 ltac:(lia)).
        rewrite !Z.div_mul in Ha by lia.
        pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
        pose proof (Z.div_mod (b + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)). (nodisj; lia). }
    (* [comment removed for export] *)
    destruct (Z.eq_dec n 0) as [N0 | Nn0].
    { (* [comment removed for export] *)
      destruct (asan_memmove_intrin_zero SEGS t (TOK fx) Mr (seg_rom SEGS) dstw srcw raw spw n bs (Z_to_bv 8 1) R PRE N0 R1' eq_refl eq_refl eq_refl R12)
        as (r & RUN & A10 & SAVED).
      rewrite DM1_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. apply OUT1; assumption.
      - apply BEQ. exact (DM1_agree dstw M raw spw R HSP').
      - exact GR1. }
    destruct (Z_le_gt_dec n 64) as [Ns | Nb].
    { (* [comment removed for export] *)
      destruct (QCH src srcw Hsrc ACCs ltac:(lia) NSHs RNGs) as (w0s & w1s & s1s & QS).
      destruct (QCH dst dstw Hdst ACCd ltac:(lia) NSHd RNGd) as (w0d & w1d & s1d & QD).
      destruct (asan_memmove_intrin_small SEGS t (TOK fx) Mr (seg_rom SEGS) dstw srcw raw spw n bs (Z_to_bv 8 1) R w0s w1s s1s w0d w1d s1d
                 PRE ltac:(lia) QS QD R1' eq_refl eq_refl eq_refl R12)
        as (r & RUN & A10 & SAVED).
      rewrite DM1_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. apply OUT1; assumption.
      - apply BEQ. exact (DM1_agree dstw M raw spw R HSP').
      - exact GR1. }
    { (* [comment removed for export] *)
      assert (CH : forall bw : word, (0x10007fff8000 <= U bw \/ U bw <= 0x7fff7fff) -> U bw <= 0x7fffffffffff ->
                 m2sH SEGS (rt_m2s (mm_rip t)) Mr bw (Z_to_bv 64 0)).
      { intros bw H1 H2. split.
        - exact K4. - exact K11. - exact K5. - exact K6. - exact K7. - exact K8. - exact K9. - exact K10.
        - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); lia.
        - exact H1. - exact H2. }
      assert (Hn43 : 65 <= n <= 2 ^ 43) by (unfold NMAX in *; lia).
      assert (RUNx : exists r,
        msteps SEGS (mkst R (mm_base t) Mr (seg_rom SEGS))
                    (mkst r raw (ammove_post dstw srcw bs (DM3 (mm_base t) (mm_rip t) Mr dstw srcw raw spw n R)) (seg_rom SEGS))
        /\ getr r 10 = dstw /\ (forall x, In x amset_saved -> getr r x = getr R x)).
      { pose proof (CH srcw ltac:(lia) ltac:(lia)) as CHs. pose proof (CH dstw ltac:(lia) ltac:(lia)) as CHd.
        assert (Rgs : (0x10007fff8000 <= U srcw /\ U srcw + n + 1 <= 0x800000000000) \/ U srcw + n <= 0x7fff7fff) by lia.
        assert (Rgd : (0x10007fff8000 <= U dstw /\ U dstw + n + 1 <= 0x800000000000) \/ U dstw + n <= 0x7fff7fff) by lia.
        destruct (RGH src srcw Hsrc ACCs ltac:(lia) NSHs RNGs) as (s0s & s1s & Rs0s & Hs0s & Rs1s & Hs1s & Rzs).
        destruct (RGH dst dstw Hdst ACCd ltac:(lia) NSHd RNGd) as (s0d & s1d & Rs0d & Hs0d & Rs1d & Hs1d & Rzd).
        exact (asan_memmove_intrin_big SEGS t (TOK fx) Mr (seg_rom SEGS) dstw srcw raw spw n bs (Z_to_bv 8 1) R s0s s1s s0d s1d (Z_to_bv 64 0)
                 PRE Hn43 CHs CHd Rgs Rgd Rs0s Hs0s Rs1s Hs1s Rzs Rs0d Hs0d Rs1d Hs1d Rzd R1' eq_refl eq_refl eq_refl R12). }
      destruct RUNx as (r & RUN & A10 & SAVED).
      (* [comment removed for export] *)
      assert (DM3_r : DM3 (mm_base t) (mm_rip t) Mr dstw srcw raw spw n R = mrestrict Hd (DM3 (mm_base t) (mm_rip t) M dstw srcw raw spw n R)).
      { clear - FR CP2 CPlo CPhi CR DM1_r POST_r. (lazymatch goal with |- ?G => let G' := eval unfold DM3, DM2 in G in change_no_check G' end). rewrite DM1_r. (lazymatch goal with |- ?G => let G' := eval unfold rip_mem, ps_frame in G in change_no_check G' end).
        pose proof (u64_range spw).
        repeat (lazymatch goal with
                | |- context [if Z.ltb ?a ?b then _ else _] => destruct (Z.ltb a b)
                end);
        rewrite !(wbytes_mrestrict Hd) by
          (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
           first [hs_arith_goal; rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); (nodisj; lia)
                 | rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]);
        reflexivity. }
      rewrite DM3_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      + clear RNGd RNGs QCH RGH RD8 RD1 GRAN CH FIN.
        intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. (lazymatch goal with |- ?G => let G' := eval unfold ammove_post, imemmove_result in G in change_no_check G' end). pose proof (u64_range a).
        destruct (Z.eqb (U dstw) (U srcw)); [apply (DM3_agree (mm_base t) (mm_rip t) M dstw srcw raw spw n R HSP'); lia|].
        rewrite wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite LBS; lia | rewrite LBS; lia].
        apply (DM3_agree (mm_base t) (mm_rip t) M dstw srcw raw spw n R HSP'). lia.
      + apply BEQ. exact (DM3_agree (mm_base t) (mm_rip t) M dstw srcw raw spw n R HSP').
      + (lazymatch goal with |- ?G => let G' := eval unfold ammove_post, imemmove_result in G in change_no_check G' end). destruct (Z.eqb (U dstw) (U srcw)); [apply DM3_grows|].
        eapply mem_grows_trans; [apply DM3_grows | apply wbytes_grows]. }
  Qed.


End CONTRACT.
End AsIcptMemmove.
Module AsIcptMemset.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsRtAccess.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac nodisjk K := repeat match goal with H : _ \/ _ |- _ => tryif constr_eq H K then fail else clear H end.

Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

Section CONTRACT.
  Context {fx0 : FPState}.   (* [comment removed for export] *)
  Context {RC : run_ceil}.   (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  (* [comment removed for export] *)
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props IA (AAINVH h) fsbase SEGS.
  (* [comment removed for export] *)
  Hypothesis SEGS_hull : forall a, find_segment SEGS a 1 <> None -> ia_img_lo IA <= a < ia_img_hi IA.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis IMG_HI : ia_img_hi IA <= AS_LO.
  Hypothesis IMG_LO : 0 <= ia_img_lo IA.
  Hypothesis FSB0 : 0 <= fsbase.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable t : amset_tab.
  Hypothesis TOK : forall fx : FPState, @amset_tab_ok fx SEGS t.
  Hypothesis T_entry : am_base t = Z_to_bv 64 (ia_asan_memset IA).
  (* [comment removed for export] *)
  Definition amset_cells : list (Z * nat * Z) :=
    [(am_g_flag t, 8%nat, am_p_flag t); (am_p_flag t, 1%nat, 1); (am_c_rms t, 8%nat, U (am_mset t));
     (mt_g_shoff (rt_m2s (am_rip t)), 8%nat, mt_p_shoff (rt_m2s (am_rip t))); (mt_p_shoff (rt_m2s (am_rip t)), 8%nat, SB);
     (mt_g_midbeg (rt_m2s (am_rip t)), 8%nat, mt_p_midbeg (rt_m2s (am_rip t))); (mt_p_midbeg (rt_m2s (am_rip t)), 8%nat, 0);
     (mt_g_midend (rt_m2s (am_rip t)), 8%nat, mt_p_midend (rt_m2s (am_rip t))); (mt_p_midend (rt_m2s (am_rip t)), 8%nat, 0);
     (mt_g_hiend (rt_m2s (am_rip t)), 8%nat, mt_p_hiend (rt_m2s (am_rip t))); (mt_p_hiend (rt_m2s (am_rip t)), 8%nat, 0x7fffffffffff)].
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN SEGS M (fst (fst c)) (snd (fst c)) (snd c)) amset_cells.
  (* [comment removed for export] *)
  Hypothesis CELLS_img : Forall (fun c => ia_img_lo IA <= fst (fst c) /\ fst (fst c) + 8 <= ia_img_hi IA) amset_cells.

  #[local] Abbreviation cfg := (AsIface3.cfg SEGS).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem C_asan_memset : MEMSET_AT SEGS FXOK IA AAINVH (ia_asan_memset IA).
  Proof using CELLS_img CELLS T_entry TOK t FSB0 IMG_LO IMG_HI SEGS_wx SEGS_hull HP fsbase.
    (lazymatch goal with |- ?G => let G' := eval unfold MEMSET_AT in G in change_no_check G' end).
    intros h fx R M mdl Lc FF W B C K ret sp dst c n HFX HH AI CP Hdst Hc Hn [Hn0 HnN] AIM1 AIM2 ACC SV DO DSJ DOK.
    pose proof (HP h) as HPh.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk).
    destruct (aap_lazy _ _ _ _ HPh _ _ _ _ _ _ _ AI) as (AA & Awf & MI & SHCok & BLKok & PRES).
    set (Hd := HL mdl AA).
    pose proof (HL_off_segments SEGS IA (AAINVH h) fsbase HPh SEGS_hull _ _ _ _ _ _ _ AA AI) as HOFF. fold Hd in HOFF.
    pose proof (@ceil_rng RC) as CR.
    assert (NZ : forall z, 0 <= z < 2 ^ 64 -> (ia_img_lo IA <= z < ia_img_hi IA) \/ CEIL <= z -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HL_zone SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI Hz). tauto. }
    unfold AS_HEAPLO, PTRHI, SB, AS_LO, MSTK_M, NMAX in *.
    assert (Hdn : dst + n < 2 ^ 47) by (unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM2; lia).
    assert (RNG : (0x10007fff8000 <= dst /\ dst + n < 2 ^ 47) \/ (0 <= dst /\ dst + n <= 0x7fff7fff)).
    { unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM1, AIM2. lia. }
    (* [comment removed for export] *)
    assert (NDST : forall z, dst <= z < dst + n -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. destruct (SV z Hz) as [IB | [(f & k & Hf & Hfz) | [ST | IM]]].
      - apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [left; exact IB | lia].
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [right; exists f, k; split; [exact Hf | lia] | lia].
      - apply NZ; [lia | right; lia].
      - apply NZ; [lia | left; lia]. }
    (* [comment removed for export] *)
    assert (NSH : forall z, dst <= z < dst + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false).
    { intros z Hz y Hy. assert (Hz0 : 0 <= z) by lia.
      destruct (SV z Hz) as [(p & m & Hp & Hpz) | [(f & k & Hf & Hfz) | [ST | IM]]].
      - pose proof (aap_zone _ _ _ _ HPh _ _ _ _ _ _ _ p m AI Hp) as ((Z1 & Z2 & Z3 & Z4) & Zn & Z16).
        apply (HL_allowed_page mdl AA (sh_lo p) (sh_hi p m) (sh_lo z) y (BLKok p m Hp)); [|exact Hy].
        apply sh_lo_in; unfold PTRLO in *; lia.
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & K2 & K3 & K4 & K5).
        apply (HL_allowed_page mdl AA (sh_lo fsbase) (sh_hi fsbase FAKE_SIZE) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; unfold FAKE_SIZE in *; lia.
      - unfold PTRHI in ST.
        apply (HL_allowed_page mdl AA (sh_lo CEIL) (SB + 2 ^ 44) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + split; [apply sh_lo_mono; lia | apply sh_lo_lt47; lia].
      - apply (HL_allowed_page mdl AA (sh_lo (ia_img_lo IA)) (sh_hi (ia_img_lo IA) (ia_img_hi IA - ia_img_lo IA)) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; lia. }
    (* [comment removed for export] *)
    set (dstw := getr R 10) in *. set (cv := getr R 11) in *. set (spw := getr R 2) in *.
    pose proof (u64_range dstw) as Hdr. pose proof (u64_range spw) as Hsr. pose proof (u64_range (getr R 12)) as H12r.
    assert (R12 : getr R 12 = Z_to_bv 64 n) by (apply bv_eq; rewrite u_Z2bv by lia; exact Hn).
    assert (RET : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u_Z2bv by lia; exact CPe).
    set (Mr := mrestrict Hd M).
    (* [comment removed for export] *)
    pose proof (CELLS _ _ _ _ _ _ _ _ AI) as CE. pose proof CELLS_img as CI. unfold amset_cells in CE, CI.
    Ltac fsplit H := apply Forall_cons_iff in H; destruct H as [? H].
    apply Forall_cons_iff in CE; destruct CE as [C1 CE]. apply Forall_cons_iff in CE; destruct CE as [C2 CE]. apply Forall_cons_iff in CE; destruct CE as [C3 CE]. apply Forall_cons_iff in CE; destruct CE as [C4 CE]. apply Forall_cons_iff in CE; destruct CE as [C5 CE]. apply Forall_cons_iff in CE; destruct CE as [C6 CE]. apply Forall_cons_iff in CE; destruct CE as [C7 CE]. apply Forall_cons_iff in CE; destruct CE as [C8 CE]. apply Forall_cons_iff in CE; destruct CE as [C9 CE]. apply Forall_cons_iff in CE; destruct CE as [C10 CE]. apply Forall_cons_iff in CE; destruct CE as [C11 CE].
    apply Forall_cons_iff in CI; destruct CI as [D1 CI]. apply Forall_cons_iff in CI; destruct CI as [D2 CI]. apply Forall_cons_iff in CI; destruct CI as [D3 CI]. apply Forall_cons_iff in CI; destruct CI as [D4 CI]. apply Forall_cons_iff in CI; destruct CI as [D5 CI]. apply Forall_cons_iff in CI; destruct CI as [D6 CI]. apply Forall_cons_iff in CI; destruct CI as [D7 CI]. apply Forall_cons_iff in CI; destruct CI as [D8 CI]. apply Forall_cons_iff in CI; destruct CI as [D9 CI]. apply Forall_cons_iff in CI; destruct CI as [D10 CI]. apply Forall_cons_iff in CI; destruct CI as [D11 CI].
    cbn [fst snd] in *.
    Ltac hoz NZ := apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NZ; lia].
    Ltac konst NZ MM C := apply (cellN_mrestrict SEGS _ MM _ _ _ C); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); hoz NZ].
    assert (K1 : rdn SEGS Mr (Z_to_bv 64 (am_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (am_p_flag t)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C1).
    assert (K2 : rdn SEGS Mr (Z_to_bv 64 (am_p_flag t)) 1 = Some [Z_to_bv 8 1]).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C2); [vm_compute; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K3 : rdn SEGS Mr (Z_to_bv 64 (am_c_rms t)) 8 = Some (word_to_le_bytes 8 (am_mset t))).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C3); [rewrite Z_to_bv_bv_unsigned; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K4 : rdn SEGS Mr (Z_to_bv 64 (mt_g_shoff (rt_m2s (am_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_shoff (rt_m2s (am_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C4).
    assert (K5 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midbeg (rt_m2s (am_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midbeg (rt_m2s (am_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C6).
    assert (K6 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midbeg (rt_m2s (am_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C7).
    assert (K7 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midend (rt_m2s (am_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midend (rt_m2s (am_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C8).
    assert (K8 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midend (rt_m2s (am_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C9).
    assert (K9 : rdn SEGS Mr (Z_to_bv 64 (mt_g_hiend (rt_m2s (am_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_hiend (rt_m2s (am_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C10).
    assert (K10 : rdn SEGS Mr (Z_to_bv 64 (mt_p_hiend (rt_m2s (am_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C11).
    assert (K11 : rdn SEGS Mr (Z_to_bv 64 (mt_p_shoff (rt_m2s (am_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C5).
    (* [comment removed for export] *)
    assert (WV : forall (m : mem) (x : word), store_ok SEGS m x 1%nat = true -> wview SEGS m x <> None).
    { intros m x Hx. cbn [store_ok] in Hx. destruct (wview SEGS m x); [discriminate | discriminate Hx]. }
    assert (STK : store_ok SEGS Mr (at_ spw (-2208)) 2208 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ].
      apply store_ok_of_all; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. apply WV. apply CPstk. cbn in Hx. lia. }
    assert (DOKr : store_ok SEGS Mr dstw (Z.to_nat n) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite Z2Nat.id; lia | rewrite Z2Nat.id by lia; apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NDST; lia]].
      apply store_ok_of_all; [rewrite Z2Nat.id; lia|]. intros x Hx. rewrite Z2Nat.id in Hx by lia. apply WV. apply DOK. lia. }
    assert (DSTK : n = 0 \/ U dstw + n <= U spw - 2208 \/ U spw <= U dstw).
    { destruct (Z.eq_dec n 0) as [E0|NE0]; [left; exact E0 | right]. unfold off_scratch, MSTK_M in DSJ.
      pose proof (DSJ dst ltac:(lia)) as X1. pose proof (DSJ (dst + n - 1) ltac:(lia)) as X2.
      destruct (Z_lt_le_dec dst (sp - 2304)) as [L|Ge]; [|lia].
      destruct (Z_lt_le_dec (dst + n - 1) (sp - 2304)) as [L2|Ge2]; [lia|].
      exfalso. apply (DSJ (sp - 1)); lia. }
    assert (PRE : amsetH SEGS t Mr dstw cv n (Z_to_bv 64 ret) spw (Z_to_bv 8 1)).
    { split.
      - exact Hn0. - lia. - exact K1. - exact K2. - vm_compute; discriminate. - exact K3.
      - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); lia.
      - lia. - exact STK. - exact DOKr. - exact DSTK. - exact RET. }
    (* [comment removed for export] *)
    set (raw := Z_to_bv 64 ret) in *.
    assert (FR : hid_off Hd (U spw - 2208) 2208) by (hoz NZ).
    assert (DR : hid_off Hd (U dstw) n) by (apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NDST; lia]).
    assert (AM1_r : AM1 Mr raw spw R = mrestrict Hd (AM1 M raw spw R)).
    { clear - FR CP2 CPlo CPhi CR. (lazymatch goal with |- ?G => let G' := eval unfold Mr, AM1, ps_frame in G in change_no_check G' end).
      rewrite !(wbytes_mrestrict Hd) by
        (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
         first [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u by lia; eapply hid_off_sub; [exact FR | lia | lia]]).
      reflexivity. }
    assert (POST_r : forall X, amset_post dstw cv n (mrestrict Hd X) = mrestrict Hd (amset_post dstw cv n X)).
    { intros X. (lazymatch goal with |- ?G => let G' := eval unfold amset_post in G in change_no_check G' end). apply (wbytes_mrestrict_at Hd _ X dstw n); [apply repeat_length | lia | lia | exact DR]. }
    (* [comment removed for export] *)
    assert (SEGnone : forall a : word, CEIL <= U a -> find_segment SEGS (U a) 1 = None).
    { intros a Ha. destruct (find_segment SEGS (U a) 1) eqn:E; [|reflexivity]. exfalso.
      pose proof (SEGS_hull (U a) ltac:(rewrite E; discriminate)). lia. }
    assert (FIN : forall (M' : mem) (r : bvmap 5 word),
      msteps SEGS (mkst R (am_base t) Mr (seg_rom SEGS)) (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) ->
      getr r 10 = dstw -> (forall x, In x amset_saved -> getr r x = getr R x) ->
      (forall a : word, M' a <> M a -> dst <= U a < dst + n \/ sp - 2304 <= U a < sp) ->
      (forall i, 0 <= i < n -> M' (Z_to_bv 64 (dst + i)) = Some (Z_to_bv 8 c)) ->
      mem_grows M M' ->
      katD SEGS (cfg fx R (ia_asan_memset IA) M mdl) (mem_post SEGS FXOK AAINVH h R M mdl Lc FF B C K ret sp dst n (fun _ => Some (Z_to_bv 8 c)))).
    { intros M' r RUN A10 SAVED CHG BYTES GR.
      assert (NH' : forall a : word, Hd a = true -> M' a = M a).
      { intros a Ha. destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso.
        pose proof (u64_range a) as Har. destruct (CHG a NE) as [X|X].
        - rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NDST (U a) X) in Ha. discriminate Ha.
        - rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NZ (U a)) in Ha; [discriminate Ha | lia | right; lia]. }
      (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.cfg in G in change_no_check G' end). rewrite <- T_entry.
      apply (katD_msteps_acct SEGS Hd HOFF SEGS_wx AA (mkst R (am_base t) M (seg_rom SEGS))
               (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) mdl _ (lazy_cover_HL mdl AA) Awf MI HH).
      - rewrite restrict_mkst'. exact RUN.
      - intros mdl' MI' SBM HC. rewrite unrestrict_mkst. (lazymatch goal with |- ?G => let G' := eval cbn [RiscvSemantics.ms_mem mkst] in G in change_no_check G' end).
        rewrite (munrestrict_mrestrict_same Hd M M' NH').
        assert (SCR : scratch_ok SEGS M' sp MSTK_M).
        { intros a Ha. unfold MSTK_M in Ha. split.
          - apply GR. apply (store_ok1_defined SEGS M a); [apply SEGnone; lia | apply CPstk; lia].
          - eapply store_ok_mono; [exact GR | apply CPstk; lia]. }
        apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold mem_post in G in change_no_check G' end). exists fx, r, M', mdl'.
        split; [reflexivity|]. split; [exact HFX|].
        split; [apply regs_kept_of_list; exact SAVED|].
        split; [rewrite A10; exact Hdst|].
        split; [exact BYTES|].
        split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); exact (CHG a Ha)|].
        split; [exact SCR|].
        split; [|exact SBM].
        destruct DO as [WOK OWN].
        apply (aap_frame _ _ _ _ HPh W Lc FF B C K M M' mdl' WOK (PRES mdl' MI' SBM)).
        intros a Ha. destruct (CHG a Ha) as [X|X].
        * split; [apply OWN; exact X|]. replace a with (Z_to_bv 64 (dst + (U a - dst))) by (apply bv_eq; rewrite u_Z2bv; lia).
          rewrite BYTES by lia. discriminate.
        * split; [right; right; left; lia|]. apply (proj1 (SCR a ltac:((lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); lia))). }
    (* [comment removed for export] *)
    assert (HSP' : (0x10007fff8000 + 2304 <= U spw)%Z /\ (U spw + 16 <= 2 ^ 47)%Z) by lia.
    assert (R1' : getr R 1 = raw) by exact CP1.
    assert (OUT1 : forall a : word, ~ (dst <= U a < dst + n) -> ~ (sp - 2304 <= U a < sp) ->
                   amset_post dstw cv n (AM1 M raw spw R) a = M a).
    { intros a N1 N2. (lazymatch goal with |- ?G => let G' := eval unfold amset_post in G in change_no_check G' end). pose proof (u64_range a).
      rewrite wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite repeat_length; lia | rewrite repeat_length; lia].
      apply (AM1_out dstw M raw spw R HSP'). lia. }
    assert (GR1 : mem_grows M (amset_post dstw cv n (AM1 M raw spw R))).
    { (lazymatch goal with |- ?G => let G' := eval unfold amset_post in G in change_no_check G' end). eapply mem_grows_trans; [apply AM1_grows | apply wbytes_grows]. }
    assert (BY : forall X i, 0 <= i < n -> amset_post dstw cv n X (Z_to_bv 64 (dst + i)) = Some (Z_to_bv 8 c)).
    { intros X i Hi. (lazymatch goal with |- ?G => let G' := eval unfold amset_post in G in change_no_check G' end). rewrite (AsRtIMemmove.wbytes_get_g) by (rewrite repeat_length; lia).
      rewrite repeat_length, u_Z2bv by lia.
      replace (inrng (U dstw) (Z.of_nat (Z.to_nat n)) (dst + i)) with true by (symmetry; apply inrng_true; lia).
      rewrite nth_repeat_lt by lia. f_equal. (lazymatch goal with |- ?G => let G' := eval unfold cbyte in G in change_no_check G' end). apply bv_eq. rewrite !Z_to_bv_unsigned.
      (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 8) with 256. rewrite <- Hc. rewrite Zmod_mod. reflexivity. }
    pose proof (fun z => aap_shdef _ _ _ _ HPh _ _ _ _ _ _ _ z AI) as SHD.
    assert (SH8 : sh_lo AS_HEAPLO mod 8 = 0 /\ AS_HEAPLO mod 8 = 0 /\ sh_lo AS_HEAPLO = 2201439137792) by (repeat split; reflexivity).
    (* [comment removed for export] *)
    assert (NSHg : forall a : word, (exists z, dst <= z < dst + n /\ sh_lo z = U a) -> Hd a = false).
    { intros a (z & Hz & Ez). apply (NSH z Hz a). rewrite Ez. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    assert (GRAN : forall g, 1 <= n -> Sh dst <= g < Sh (dst + n - 1) + 1 -> exists z, dst <= z < dst + n /\ sh_lo z = g).
    { intros g Hn1 Hg. unfold Sh, sh_lo, SB in *.
      pose proof (Z.div_mod dst 8 ltac:(lia)). pose proof (Z.mod_pos_bound dst 8 ltac:(lia)).
      pose proof (Z.div_mod (dst + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (dst + n - 1) 8 ltac:(lia)).
      destruct (Z_lt_le_dec g (Sh (dst + n - 1))) as [L|Ge]; unfold Sh in *.
      - exists (8 * (g - 2147450880) + 7). split; [(nodisj; lia)|].
        replace (8 * (g - 2147450880) + 7) with ((g - 2147450880) * 8 + 7) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small 7 8) by lia. lia.
      - exists (dst + n - 1). split; [lia|]. lia. }
    (* [comment removed for export] *)
    assert (RD1 : forall (a : word) bs, rdn SEGS M a 1%nat = Some bs -> (exists z, dst <= z < dst + n /\ sh_lo z = U a) ->
                  rdn SEGS Mr a 1%nat = Some bs).
    { intros a bs Hr Hz. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). pose proof (u64_range a). rewrite rdn_mrestrict; [exact Hr | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      intros x Hx. cbn in Hx. replace x with a by (apply bv_eq; lia). apply NSHg. exact Hz. }
    assert (RD8 : forall (w : Z) (z : Z), dst <= z < dst + n -> w = down8 (sh_lo z) ->
                  exists bs, rdn SEGS Mr (Z_to_bv 64 w) 8%nat = Some bs).
    { intros w z Hz Ew. pose proof (sh_lo_lt47 z ltac:(lia)) as SZ. pose proof (down8_le (sh_lo z) ltac:(unfold SB in SZ; lia)) as [DL DM].
      assert (LS8 : sh_lo SB = 2415882240 /\ sh_lo SB mod 8 = 0) by (split; reflexivity).
      assert (DEF8 : forall i, w <= i < w + 8 -> M (Z_to_bv 64 i) <> None).
      { destruct RNG as [[RH _] | [_ RL]].
        - assert (LO : sh_lo AS_HEAPLO <= w).
          { subst w. apply down8_ge; [exact (proj1 SH8)|]. apply sh_lo_mono. (lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia. }
          assert (HI : w + 8 <= AS_HEAPLO).
          { subst w. apply down8_lt_top; [exact (proj1 (proj2 SH8))|]. unfold AS_HEAPLO, SB in *. lia. }
          rewrite (proj2 (proj2 SH8)) in LO. unfold AS_HEAPLO in HI.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). right. (lazymatch goal with |- ?G => let G' := eval unfold AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). (nodisj; lia).
        - assert (LO : SB <= w).
          { subst w. apply down8_ge; [reflexivity|]. unfold SB in *. lia. }
          assert (HI : w + 8 <= sh_lo SB).
          { subst w. apply down8_lt_top; [exact (proj2 LS8)|]. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end).
            pose proof (Z.div_le_mono z 2147450879 8 ltac:(lia) ltac:(lia)). change (2147450879 / 8) with 268431359 in *. change (2147450880 / 8) with 268431360 in *. lia. }
          rewrite (proj1 LS8) in HI. unfold SB in LO.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). left. (lazymatch goal with |- ?G => let G' := eval unfold AS_LO, AS_GAPLO in G in change_no_check G' end). lia. }
      unfold SB in SZ.
      destruct (rdn_defined_ex SEGS M (Z_to_bv 64 w) 8) as (bs & Hbs & _).
      { intros i Hi. rewrite u_Z2bv in Hi by (nodisj; lia). apply DEF8. cbn in Hi. lia. }
      { rewrite u_Z2bv by (nodisj; lia). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (nodisj; lia). }
      exists bs. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hbs | rewrite u_Z2bv by (nodisj; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (nodisj; lia) |].
      rewrite u_Z2bv by (nodisj; lia). intros x Hx. cbn in Hx. apply (NSH z Hz x).
      apply (page_base_word8 w); [rewrite Ew; exact DM | (nodisj; lia) | (nodisj; lia) | rewrite u_Z2bv by (nodisj; lia); (nodisj; lia)]. }
    (* [comment removed for export] *)
    destruct (Z.eq_dec n 0) as [N0 | Nn0].
    { (* [comment removed for export] *)
      destruct (asan_memset_intrin_zero SEGS t (TOK fx) Mr (seg_rom SEGS) dstw cv raw spw n (Z_to_bv 8 1) R PRE N0 R1' eq_refl eq_refl eq_refl R12)
        as (r & RUN & A10 & SAVED).
      rewrite AM1_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. apply OUT1; assumption.
      - intros i Hi. apply BY. exact Hi.
      - exact GR1. }
    destruct (Z_le_gt_dec n 64) as [Ns | Nb].
    { (* [comment removed for export] *)
      destruct (acc_last SEGS M dst n ACC ltac:(lia)) as (s1 & Rs1 & Hs1).
      destruct (RD8 (down8 (sh_lo dst)) dst ltac:(lia) eq_refl) as (w0 & Rw0).
      destruct (RD8 (down8 (sh_lo (dst + n - 1))) (dst + n - 1) ltac:(lia) eq_refl) as (w1 & Rw1).
      assert (QH : qc1H SEGS Mr dstw n (mt_g_shoff (rt_m2s (am_rip t))) (mt_p_shoff (rt_m2s (am_rip t))) w0 w1 s1).
      { split; rewrite ?Hdst.
        - lia. - lia. - exact K4. - exact K11. - (nodisj; lia).
        - rewrite Sh_is_sh_lo. exact Rw0.
        - rewrite Sh_is_sh_lo. exact Rw1.
        - apply (RD1 _ _ Rs1). apply GRAN; [lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (dst + n - 1) ltac:(lia)). pose proof (sh_lo_mono dst (dst + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
        - exact Hs1.
        - intros a Ha. apply (RD1 a _ (acc_zero SEGS M dst n ACC ltac:(lia) a Ha)). apply GRAN; [lia|]. rewrite !Sh_is_sh_lo in Ha |- *. lia. }
      destruct (asan_memset_intrin_small SEGS t (TOK fx) Mr (seg_rom SEGS) dstw cv raw spw n (Z_to_bv 8 1) R w0 w1 s1 PRE ltac:(lia) QH R1' eq_refl eq_refl eq_refl R12)
        as (r & RUN & A10 & SAVED).
      rewrite AM1_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. apply OUT1; assumption.
      - intros i Hi. apply BY. exact Hi.
      - exact GR1. }
    { (* [comment removed for export] *)
      destruct (acc_first SEGS M dst n ACC ltac:(lia)) as (s0b & Rs0 & Hs0).
      destruct (acc_last SEGS M dst n ACC ltac:(lia)) as (s1b & Rs1 & Hs1).
      assert (CH : m2sH SEGS (rt_m2s (am_rip t)) Mr dstw (Z_to_bv 64 0)).
      { split.
        - exact K4. - exact K11. - exact K5. - exact K6. - exact K7. - exact K8. - exact K9. - exact K10.
        - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); (nodisj; lia).
        - (nodisjk RNG; lia). - (nodisjk RNG; lia). }
      assert (Hn43 : 65 <= n <= 2 ^ 43) by (unfold NMAX in *; lia).
      destruct (asan_memset_intrin_big SEGS t (TOK fx) Mr (seg_rom SEGS) dstw cv raw spw n (Z_to_bv 8 1) R s0b s1b (Z_to_bv 64 0)
                 PRE Hn43 CH ltac:(rewrite Hdst; lia)) as (r & RUN & A10 & SAVED).
      - rewrite Hdst. apply (RD1 _ _ Rs0). apply GRAN; [lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 dst ltac:((nodisj; lia))). pose proof (sh_lo_mono dst (dst + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - rewrite Hdst. exact Hs0.
      - rewrite Hdst. apply (RD1 _ _ Rs1). apply GRAN; [lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (dst + n - 1) ltac:((nodisj; lia))). pose proof (sh_lo_mono dst (dst + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - rewrite Hdst. exact Hs1.
      - rewrite Hdst. intros a Ha. apply (RD1 a _ (acc_zero_mid SEGS M dst n ACC ltac:(lia) a Ha)). apply GRAN; [lia|].
        unfold Sh, up8, down8 in Ha |- *. clear - Ha.
        pose proof (Z.div_mod (dst + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (dst + 7) 8 ltac:(lia)).
        pose proof (Z.div_mod (dst + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (dst + n) 8 ltac:(lia)).
        rewrite !Z.div_mul in Ha by lia.
        pose proof (Z.div_mod dst 8 ltac:(lia)). pose proof (Z.mod_pos_bound dst 8 ltac:(lia)).
        pose proof (Z.div_mod (dst + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (dst + n - 1) 8 ltac:(lia)). (nodisj; lia).
      - exact R1'. - reflexivity. - reflexivity. - reflexivity. - exact R12.
      - (* [comment removed for export] *)
        assert (AM2_r : AM2 (am_base t) (am_rip t) Mr dstw cv raw spw n R = mrestrict Hd (AM2 (am_base t) (am_rip t) M dstw cv raw spw n R)).
        { clear - FR CP2 CPlo CPhi CR AM1_r POST_r. (lazymatch goal with |- ?G => let G' := eval unfold AM2 in G in change_no_check G' end). rewrite AM1_r. (lazymatch goal with |- ?G => let G' := eval unfold rip_mem, ps_frame in G in change_no_check G' end).
          pose proof (u64_range spw).
          destruct (Z.ltb _ _);
          rewrite !(wbytes_mrestrict Hd) by
            (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
             first [hs_arith_goal; rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); (nodisj; lia)
                   | rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]);
          reflexivity. }
        rewrite AM2_r, POST_r in RUN.
        apply (FIN _ r RUN A10 SAVED).
        + intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
          exfalso. apply Ha. (lazymatch goal with |- ?G => let G' := eval unfold amset_post in G in change_no_check G' end). pose proof (u64_range a).
          rewrite wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite repeat_length; (nodisj; lia) | rewrite repeat_length; (nodisj; lia)].
          destruct (Z_lt_le_dec (U a) (sp - 2208)).
          * apply (AM2_low (am_base t) (am_rip t) M dstw cv raw spw n R HSP'). (nodisj; lia).
          * (lazymatch goal with |- ?G => let G' := eval unfold AM2 in G in change_no_check G' end). rewrite rip_mem_outside; [| rewrite at_u by (nodisj; lia); (nodisj; lia) | rewrite at_u by (nodisj; lia); (nodisj; lia)].
            apply (AM1_out dstw M raw spw R HSP'). (nodisj; lia).
        + intros i Hi. apply BY. exact Hi.
        + (lazymatch goal with |- ?G => let G' := eval unfold amset_post in G in change_no_check G' end). eapply mem_grows_trans; [apply AM2_grows | apply wbytes_grows]. }
  Qed.

End CONTRACT.
End AsIcptMemset.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsIcptStrlen.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsRtAccess.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.

Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma rd1n_defined_ex_sl {fx : FPState} : forall segs (m : word -> option byte) (a : word) (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> rdn segs m (Z_to_bv 64 (U a + i)) 1%nat <> None) ->
  U a + Z.of_nat n < 2 ^ 64 ->
  exists bs, rdn segs m a n = Some bs /\ length bs = n.
Proof.
  intros segs m a n. revert a. induction n as [|n IH]; intros a Hdef Hnw.
  - exists []. split; reflexivity.
  - pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
    destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:E.
    2:{ exfalso. apply (Hdef 0); [lia|]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). rewrite E. reflexivity. }
    destruct (IH (a + 1)%bv) as [bs [Hr Hl]].
    + intros i Hi. rewrite u_add1 by lia. replace (U a + 1 + i) with (U a + (1 + i)) by lia. apply Hdef. lia.
    + rewrite u_add1 by lia. lia.
    + rewrite Hr. exists (b :: bs). split; [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
Qed.

Section CONTRACT.
  Context {fx0 : FPState}.   (* [comment removed for export] *)
  Context {RC : run_ceil}.   (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  (* [comment removed for export] *)
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props IA (AAINVH h) fsbase SEGS.
  (* [comment removed for export] *)
  Hypothesis SEGS_hull : forall a, find_segment SEGS a 1 <> None -> ia_img_lo IA <= a < ia_img_hi IA.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis IMG_HI : ia_img_hi IA <= AS_LO.
  Hypothesis IMG_LO : 0 <= ia_img_lo IA.
  Hypothesis FSB0 : 0 <= fsbase.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable t : xstrlen_tab.
  Hypothesis TOK : forall fx : FPState, @xstrlen_tab_ok fx SEGS t.
  Hypothesis T_entry : xs_base t = Z_to_bv 64 (ia_strlen_icpt IA).
  (* [comment removed for export] *)
  Definition xstrlen_cells : list (Z * nat * Z) :=
    [(xs_c_rsl t, 8%nat, U (st_base (xs_sl t))); (st_cM (xs_sl t), 8%nat, Mc); (st_cH (xs_sl t), 8%nat, Hc);
     (xs_g_cf t, 8%nat, xs_p_cf t); (xs_p_cf t + 251, 1%nat, 1); (xs_c_inited t, 1%nat, 1);
     (mt_g_shoff (rt_m2s (xs_rip t)), 8%nat, mt_p_shoff (rt_m2s (xs_rip t))); (mt_p_shoff (rt_m2s (xs_rip t)), 8%nat, SB);
     (mt_g_midbeg (rt_m2s (xs_rip t)), 8%nat, mt_p_midbeg (rt_m2s (xs_rip t))); (mt_p_midbeg (rt_m2s (xs_rip t)), 8%nat, 0);
     (mt_g_midend (rt_m2s (xs_rip t)), 8%nat, mt_p_midend (rt_m2s (xs_rip t))); (mt_p_midend (rt_m2s (xs_rip t)), 8%nat, 0);
     (mt_g_hiend (rt_m2s (xs_rip t)), 8%nat, mt_p_hiend (rt_m2s (xs_rip t))); (mt_p_hiend (rt_m2s (xs_rip t)), 8%nat, 0x7fffffffffff)].
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN SEGS M (fst (fst c)) (snd (fst c)) (snd c)) xstrlen_cells.
  (* [comment removed for export] *)
  Hypothesis CELLS_img : Forall (fun c => ia_img_lo IA <= fst (fst c) /\ fst (fst c) + 8 <= ia_img_hi IA) xstrlen_cells.
  Hypothesis PCF_img : 0 <= xs_p_cf t /\ xs_p_cf t + 8 <= AS_LO.   (* [comment removed for export] *)

  #[local] Abbreviation cfg := (AsIface3.cfg SEGS).

  Theorem C_strlen_icpt : STRLEN_AT SEGS FXOK IA AAINVH (ia_strlen_icpt IA).
  Proof using PCF_img CELLS_img CELLS T_entry TOK t FSB0 IMG_LO IMG_HI SEGS_wx SEGS_hull HP fsbase.
    (lazymatch goal with |- ?G => let G' := eval unfold STRLEN_AT in G in change_no_check G' end).
    intros h fx R M mdl Lc FF B C K ret sp s len HFX HH AI CP Hs Hlen0 HlenN NZB ZB HULL AIM1 AIM2 ACC SV SSJ.
    pose proof (HP h) as HPh.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk).
    destruct (aap_lazy _ _ _ _ HPh _ _ _ _ _ _ _ AI) as (AA & Awf & MI & SHCok & BLKok & PRES).
    set (Hd := HL mdl AA).
    pose proof (HL_off_segments SEGS IA (AAINVH h) fsbase HPh SEGS_hull _ _ _ _ _ _ _ AA AI) as HOFF. fold Hd in HOFF.
    pose proof (@ceil_rng RC) as CR.
    assert (NZ : forall z, 0 <= z < 2 ^ 64 -> (ia_img_lo IA <= z < ia_img_hi IA) \/ CEIL <= z -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HL_zone SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI Hz). tauto. }
    unfold AS_HEAPLO, PTRHI, SB, AS_LO, MSTK_M, NMAX in *.
    assert (RNG : (0x10007fff8000 <= s /\ s + len + 1 < 2 ^ 47) \/ (0 <= s /\ s + len + 1 <= 0x7fff7fff)).
    { unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM1, AIM2. lia. }
    assert (Hsn2 : 0 <= s /\ s + len + 1 < 2 ^ 47) by lia.
    (* [comment removed for export] *)
    set (E := (s + len + 8) - (s + len) mod 8).
    pose proof (Z.mod_pos_bound (s + len) 8 ltac:(lia)) as Hm8. pose proof (Z.div_mod (s + len) 8 ltac:(lia)) as Hdm8.
    assert (HE : s + len + 1 <= E <= s + len + 8 /\ E = (s + len) / 8 * 8 + 8 /\ E <= 2 ^ 47) by (subst E; lia).
    (* [comment removed for export] *)
    assert (NVIS : forall z, s <= z < s + (len + 1) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. destruct (SV z Hz) as [IB | [(f & k & Hf & Hfz) | [ST | IM]]].
      - apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [left; exact IB | lia].
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [right; exists f, k; split; [exact Hf | (nodisj; lia)] | (nodisj; lia)].
      - apply NZ; [lia | right; lia].
      - apply NZ; [lia | left; lia]. }
    (* [comment removed for export] *)
    assert (NWIN : forall z, s <= z < E -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. destruct (Z_lt_le_dec z (s + len + 1)) as [L1|G1]; [apply NVIS; lia|].
      (lazymatch goal with |- ?G => let G' := eval unfold Hd in G in change_no_check G' end). rewrite (HL_page mdl AA (Z_to_bv 64 z) (Z_to_bv 64 (s + len))); [apply NVIS; lia|].
      apply (page_base_word8 ((s + len) / 8 * 8)); [apply Z.mod_mul; lia | lia | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]]. }
    (* [comment removed for export] *)
    assert (NSH : forall z, s <= z < s + (len + 1) -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false).
    { intros z Hz y Hy.
      destruct (SV z Hz) as [(p & pm & Hp & Hpz) | [(f & k & Hf & Hfz) | [ST | IM]]].
      - pose proof (aap_zone _ _ _ _ HPh _ _ _ _ _ _ _ p pm AI Hp) as ((Z1 & Z2 & Z3 & Z4) & Zn & Z16).
        apply (HL_allowed_page mdl AA (sh_lo p) (sh_hi p pm) (sh_lo z) y (BLKok p pm Hp)); [|exact Hy].
        apply sh_lo_in; unfold PTRLO in *; lia.
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_allowed_page mdl AA (sh_lo fsbase) (sh_hi fsbase FAKE_SIZE) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; unfold FAKE_SIZE in *; lia.
      - unfold PTRHI in ST.
        apply (HL_allowed_page mdl AA (sh_lo CEIL) (SB + 2 ^ 44) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + split; [apply sh_lo_mono; lia | apply sh_lo_lt47; lia].
      - apply (HL_allowed_page mdl AA (sh_lo (ia_img_lo IA)) (sh_hi (ia_img_lo IA) (ia_img_hi IA - ia_img_lo IA)) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; lia. }
    (* [comment removed for export] *)
    set (sw := getr R 10) in *. set (spw := getr R 2) in *.
    pose proof (u64_range sw) as Hswr. pose proof (u64_range spw) as Hsr.
    assert (RET : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u_Z2bv by lia; exact CPe).
    clear CPe CP16.
    set (Mr := mrestrict Hd M).
    (* [comment removed for export] *)
    pose proof (CELLS _ _ _ _ _ _ _ _ AI) as CE. pose proof CELLS_img as CI. unfold xstrlen_cells in CE, CI.
    apply Forall_cons_iff in CE; destruct CE as [C1 CE]. apply Forall_cons_iff in CE; destruct CE as [C2 CE]. apply Forall_cons_iff in CE; destruct CE as [C3 CE]. apply Forall_cons_iff in CE; destruct CE as [C4 CE]. apply Forall_cons_iff in CE; destruct CE as [C5 CE]. apply Forall_cons_iff in CE; destruct CE as [C6 CE]. apply Forall_cons_iff in CE; destruct CE as [C7 CE]. apply Forall_cons_iff in CE; destruct CE as [C8 CE]. apply Forall_cons_iff in CE; destruct CE as [C9 CE]. apply Forall_cons_iff in CE; destruct CE as [C10 CE]. apply Forall_cons_iff in CE; destruct CE as [C11 CE]. apply Forall_cons_iff in CE; destruct CE as [C12 CE]. apply Forall_cons_iff in CE; destruct CE as [C13 CE]. apply Forall_cons_iff in CE; destruct CE as [C14 CE].
    apply Forall_cons_iff in CI; destruct CI as [D1 CI]. apply Forall_cons_iff in CI; destruct CI as [D2 CI]. apply Forall_cons_iff in CI; destruct CI as [D3 CI]. apply Forall_cons_iff in CI; destruct CI as [D4 CI]. apply Forall_cons_iff in CI; destruct CI as [D5 CI]. apply Forall_cons_iff in CI; destruct CI as [D6 CI]. apply Forall_cons_iff in CI; destruct CI as [D7 CI]. apply Forall_cons_iff in CI; destruct CI as [D8 CI]. apply Forall_cons_iff in CI; destruct CI as [D9 CI]. apply Forall_cons_iff in CI; destruct CI as [D10 CI]. apply Forall_cons_iff in CI; destruct CI as [D11 CI]. apply Forall_cons_iff in CI; destruct CI as [D12 CI]. apply Forall_cons_iff in CI; destruct CI as [D13 CI]. apply Forall_cons_iff in CI; destruct CI as [D14 CI].
    cbn [fst snd] in *.
    Ltac hoz NZ := apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NZ; lia].
    Ltac konst NZ MM C := apply (cellN_mrestrict SEGS _ MM _ _ _ C); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); hoz NZ].
    assert (K1 : rdn SEGS Mr (Z_to_bv 64 (xs_c_rsl t)) 8 = Some (word_to_le_bytes 8 (st_base (xs_sl t)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C1); [rewrite Z_to_bv_bv_unsigned; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K2 : rdn SEGS Mr (Z_to_bv 64 (st_cM (xs_sl t))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 Mc))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C2).
    assert (K3 : rdn SEGS Mr (Z_to_bv 64 (st_cH (xs_sl t))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 Hc))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C3).
    assert (K4 : rdn SEGS Mr (Z_to_bv 64 (xs_g_cf t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (xs_p_cf t)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C4).
    assert (K5 : rdn SEGS Mr (Z_to_bv 64 (xs_p_cf t + 251)) 1 = Some [Z_to_bv 8 1]).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C5); [vm_compute; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K6 : rdn SEGS Mr (Z_to_bv 64 (xs_c_inited t)) 1 = Some [Z_to_bv 8 1]).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C6); [vm_compute; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K7 : rdn SEGS Mr (Z_to_bv 64 (mt_g_shoff (rt_m2s (xs_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_shoff (rt_m2s (xs_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C7).
    assert (K8 : rdn SEGS Mr (Z_to_bv 64 (mt_p_shoff (rt_m2s (xs_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C8).
    assert (K9 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midbeg (rt_m2s (xs_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midbeg (rt_m2s (xs_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C9).
    assert (K10 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midbeg (rt_m2s (xs_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C10).
    assert (K11 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midend (rt_m2s (xs_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midend (rt_m2s (xs_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C11).
    assert (K12 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midend (rt_m2s (xs_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C12).
    assert (K13 : rdn SEGS Mr (Z_to_bv 64 (mt_g_hiend (rt_m2s (xs_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_hiend (rt_m2s (xs_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C13).
    assert (K14 : rdn SEGS Mr (Z_to_bv 64 (mt_p_hiend (rt_m2s (xs_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C14).
    (* [comment removed for export] *)
    assert (WV : forall (m : mem) (x : word), store_ok SEGS m x 1%nat = true -> wview SEGS m x <> None).
    { intros m x Hx. cbn [store_ok] in Hx. destruct (wview SEGS m x); [discriminate | discriminate Hx]. }
    assert (STK : store_ok SEGS Mr (at_ spw (-2240)) 2240 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ].
      apply store_ok_of_all; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. apply WV. apply CPstk. cbn in Hx. lia. }
    (* [comment removed for export] *)
    assert (SSTK : s + len + 1 <= U spw - 2304 \/ U spw <= s).
    { unfold off_scratch, MSTK_M in SSJ.
      pose proof (SSJ s ltac:(lia)) as X1. pose proof (SSJ (s + len) ltac:(lia)) as X2.
      destruct (Z_lt_le_dec s (sp - 2304)) as [L|Ge]; [|lia].
      destruct (Z_lt_le_dec (s + len) (sp - 2304)) as [L2|Ge2]; [lia|].
      exfalso. apply (SSJ (sp - 2304)); lia. }
    clear SSJ.
    destruct (rd1n_defined_ex_sl SEGS M sw (Z.to_nat (E - s))) as (buf & BUF & LBUF).
    { intros i Hi. rewrite Hs. apply HULL. lia. }
    { lia. }
    assert (WR : hid_off Hd (U sw) (E - s)) by (apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NWIN; lia]).
    assert (BUFr : rdn SEGS Mr sw (Z.to_nat (E - s)) = Some buf).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact BUF | lia | rewrite Z2Nat.id by lia; exact WR]. }
    assert (BYTE : forall j, 0 <= j <= len -> rdn SEGS M (Z_to_bv 64 (s + j)) 1 = Some [nth (Z.to_nat j) buf (Z_to_bv 8 0)]).
    { intros j Hj. replace (Z_to_bv 64 (s + j)) with (sw + nat_to_word (Z.to_nat j))%bv
        by (rewrite at_nat; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); apply bv_eq; rewrite !Z_to_bv_unsigned; f_equal; lia).
      apply (rdn_nth SEGS M (Z.to_nat (E - s)) sw buf (Z.to_nat j) BUF). lia. }
    assert (STRH : strlH SEGS Mr sw buf len).
    { split.
      - rewrite LBUF. exact BUFr.
      - rewrite Hs, LBUF. lia.
      - rewrite LBUF. lia.
      - exact Hlen0.
      - pose proof (BYTE len ltac:(lia)) as X. unfold AsIface3.rd1 in ZB. rewrite ZB in X. injection X as X. rewrite <- X. reflexivity.
      - intros j Hj. destruct (NZB (Z.of_nat j) ltac:(lia)) as (b & Rb & NZb).
        pose proof (BYTE (Z.of_nat j) ltac:(lia)) as X. unfold AsIface3.rd1 in Rb. rewrite Rb in X. injection X as X. rewrite Nat2Z.id in X. rewrite <- X.
        intros E0. apply NZb. apply bv_eq. rewrite E0. reflexivity. }
    assert (PRE : xstrlenH SEGS t Mr sw len buf (Z_to_bv 64 ret) spw (Z_to_bv 8 1)).
    { split.
      - lia.
      - exact STRH.
      - lia.
      - exact K1. - exact K2. - exact K3. - exact K4. - exact K5. - vm_compute; discriminate. - exact K6.
      - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); (nodisj; lia).
      - exact STK.
      - lia.
      - exact RET. }
    clear SSTK.
    (* [comment removed for export] *)
    set (raw := Z_to_bv 64 ret) in *.
    assert (FR : hid_off Hd (U spw - 2240) 2240) by (hoz NZ).
    assert (XS1_r : XS1 Mr raw spw R = mrestrict Hd (XS1 M raw spw R)).
    { clear - FR CP2 CPlo CPhi CR. (lazymatch goal with |- ?G => let G' := eval unfold Mr, XS1, xsl_frame in G in change_no_check G' end).
      rewrite !(wbytes_mrestrict Hd) by
        (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
         first [hs_arith_goal; rewrite at_u by (nodisj; lia); (nodisj; lia) | rewrite at_u by (nodisj; lia); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]).
      reflexivity. }
    assert (XS2_r : XS2 (xs_base t) Mr raw spw R = mrestrict Hd (XS2 (xs_base t) M raw spw R)).
    { clear - FR CP2 CPlo CPhi CR XS1_r. (lazymatch goal with |- ?G => let G' := eval unfold XS2, tai_mem in G in change_no_check G' end). rewrite XS1_r.
      rewrite !(wbytes_mrestrict Hd) by
        (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
         first [hs_arith_goal; rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); (nodisj; lia)
               | rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]).
      reflexivity. }
    (* [comment removed for export] *)
    assert (SEGnone : forall a : word, CEIL <= U a -> find_segment SEGS (U a) 1 = None).
    { intros a Ha. destruct (find_segment SEGS (U a) 1) eqn:FSE; [|reflexivity]. exfalso.
      pose proof (SEGS_hull (U a) ltac:(rewrite FSE; discriminate)). lia. }
    assert (WINS0 : as_wins_ok IA []).
    { intros a (lo & hi & Hin & _). destruct Hin. }
    assert (FIN : forall (M' : mem) (r : bvmap 5 word),
      msteps SEGS (mkst R (xs_base t) Mr (seg_rom SEGS)) (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) ->
      getr r 10 = Z_to_bv 64 len -> (forall x, In x amset_saved -> getr r x = getr R x) ->
      (forall a : word, M' a <> M a -> sp - 2304 <= U a < sp) ->
      mem_grows M M' ->
      katD SEGS (cfg fx R (ia_strlen_icpt IA) M mdl)
           (fun c' => exists fx' R' M' mdl',
              c' = cfg fx' R' ret M' mdl' /\ FXOK fx' /\ regs_kept R R' /\ U (getr R' 10) = len
              /\ (forall a : word, M' a <> M a -> sp - MSTK_M <= U a < sp)
              /\ scratch_ok SEGS M' sp MSTK_M
              /\ AAINVH h Lc FF B C K M' mdl' /\ same_but_materialized mdl mdl')).
    { intros M' r RUN A10 SAVED CHG GR.
      assert (NH' : forall a : word, Hd a = true -> M' a = M a).
      { intros a Ha. destruct (decide (M' a = M a)) as [E'|NE]; [exact E'|]. exfalso.
        pose proof (u64_range a) as Har. pose proof (CHG a NE) as X.
        rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NZ (U a)) in Ha; [discriminate Ha | lia | right; lia]. }
      (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.cfg in G in change_no_check G' end). rewrite <- T_entry.
      apply (katD_msteps_acct SEGS Hd HOFF SEGS_wx AA (mkst R (xs_base t) M (seg_rom SEGS))
               (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) mdl _ (lazy_cover_HL mdl AA) Awf MI HH).
      - rewrite restrict_mkst'. exact RUN.
      - intros mdl' MI' SBM HC. rewrite unrestrict_mkst. (lazymatch goal with |- ?G => let G' := eval cbn [RiscvSemantics.ms_mem mkst] in G in change_no_check G' end).
        rewrite (munrestrict_mrestrict_same Hd M M' NH').
        assert (SCR : scratch_ok SEGS M' sp MSTK_M).
        { intros a Ha. unfold MSTK_M in Ha. split.
          - apply GR. apply (store_ok1_defined SEGS M a); [apply SEGnone; lia | apply CPstk; lia].
          - eapply store_ok_mono; [exact GR | apply CPstk; lia]. }
        apply katD_refl. exists fx, r, M', mdl'.
        split; [reflexivity|]. split; [exact HFX|].
        split; [apply regs_kept_of_list; exact SAVED|].
        split; [rewrite A10; apply u_Z2bv; lia|].
        split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); exact (CHG a Ha)|].
        split; [exact SCR|].
        split; [|exact SBM].
        apply (aap_frame _ _ _ _ HPh [] Lc FF B C K M M' mdl' WINS0 (PRES mdl' MI' SBM)).
        intros a Ha. pose proof (CHG a Ha) as X.
        split; [right; right; left; lia|]. apply (proj1 (SCR a ltac:((lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); lia))). }
    assert (R1' : getr R 1 = raw) by exact CP1.
    (* [comment removed for export] *)
    assert (GRAN : forall g, Sh s <= g < Sh (s + (len + 1) - 1) + 1 -> exists z, s <= z < s + (len + 1) /\ sh_lo z = g).
    { intros g Hg. unfold Sh, sh_lo, SB in *.
      pose proof (Z.div_mod s 8 ltac:(lia)). pose proof (Z.mod_pos_bound s 8 ltac:(lia)).
      pose proof (Z.div_mod (s + (len + 1) - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + (len + 1) - 1) 8 ltac:(lia)).
      destruct (Z_lt_le_dec g (Sh (s + (len + 1) - 1))) as [L|Ge]; unfold Sh in *.
      - exists (8 * (g - 2147450880) + 7). split; [lia|].
        replace (8 * (g - 2147450880) + 7) with ((g - 2147450880) * 8 + 7) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small 7 8) by lia. lia.
      - exists (s + (len + 1) - 1). split; [lia|]. lia. }
    assert (RD1 : forall (a : word) bs0, rdn SEGS M a 1%nat = Some bs0 -> (exists z, s <= z < s + (len + 1) /\ sh_lo z = U a) ->
                  rdn SEGS Mr a 1%nat = Some bs0).
    { intros a bs0 Hr (z & Hz & Ez). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). pose proof (u64_range a). rewrite rdn_mrestrict; [exact Hr | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      intros x Hx. cbn in Hx. replace x with a by (apply bv_eq; lia). apply (NSH z Hz a). rewrite Ez. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    pose proof (fun z => aap_shdef _ _ _ _ HPh _ _ _ _ _ _ _ z AI) as SHD.
    assert (RD8 : forall (w : Z) (z : Z), s <= z < s + (len + 1) -> w = down8 (sh_lo z) ->
                  exists bs0, rdn SEGS Mr (Z_to_bv 64 w) 8%nat = Some bs0).
    { intros w z Hz Ew. pose proof (sh_lo_lt47 z ltac:(lia)) as SZ. pose proof (down8_le (sh_lo z) ltac:(unfold SB in SZ; lia)) as [DL DM].
      assert (SH8 : sh_lo AS_HEAPLO mod 8 = 0 /\ AS_HEAPLO mod 8 = 0 /\ sh_lo AS_HEAPLO = 2201439137792) by (repeat split; reflexivity).
      assert (LS8 : sh_lo SB = 2415882240 /\ sh_lo SB mod 8 = 0) by (split; reflexivity).
      assert (DEF8 : forall i, w <= i < w + 8 -> M (Z_to_bv 64 i) <> None).
      { destruct RNG as [[RH _] | [_ RL]].
        - assert (LO : sh_lo AS_HEAPLO <= w).
          { subst w. apply down8_ge; [exact (proj1 SH8)|]. apply sh_lo_mono. (lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia. }
          assert (HI : w + 8 <= AS_HEAPLO).
          { subst w. apply down8_lt_top; [exact (proj1 (proj2 SH8))|]. unfold AS_HEAPLO, SB in *. lia. }
          rewrite (proj2 (proj2 SH8)) in LO. unfold AS_HEAPLO in HI.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). right. (lazymatch goal with |- ?G => let G' := eval unfold AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). (nodisj; lia).
        - assert (LO : SB <= w).
          { subst w. apply down8_ge; [reflexivity|]. unfold SB in *. lia. }
          assert (HI : w + 8 <= sh_lo SB).
          { subst w. apply down8_lt_top; [exact (proj2 LS8)|]. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end).
            pose proof (Z.div_le_mono z 2147450879 8 ltac:(lia) ltac:(lia)). change (2147450879 / 8) with 268431359 in *. change (2147450880 / 8) with 268431360 in *. lia. }
          rewrite (proj1 LS8) in HI. unfold SB in LO.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). left. (lazymatch goal with |- ?G => let G' := eval unfold AS_LO, AS_GAPLO in G in change_no_check G' end). (nodisj; lia). }
      unfold SB in SZ.
      destruct (rdn_defined_ex SEGS M (Z_to_bv 64 w) 8) as (bs0 & Hbs & _).
      { intros i Hi. rewrite u_Z2bv in Hi by (nodisj; lia). apply DEF8. cbn in Hi. lia. }
      { rewrite u_Z2bv by (nodisj; lia). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
      exists bs0. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hbs | rewrite u_Z2bv by (nodisj; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (nodisj; lia) |].
      rewrite u_Z2bv by (nodisj; lia). intros x Hx. cbn in Hx. apply (NSH z Hz x).
      apply (page_base_word8 w); [rewrite Ew; exact DM | (nodisj; lia) | (nodisj; lia) | rewrite u_Z2bv by (nodisj; lia); (nodisj; lia)]. }
    (* [comment removed for export] *)
    assert (OUT2 : forall a : word, XS2 (xs_base t) M raw spw R a <> M a -> sp - 2304 <= U a < sp).
    { intros a Ha. pose proof (u64_range a). destruct (decide (sp - 2304 <= U a < sp)) as [Y|N]; [exact Y|]. exfalso. apply Ha.
      apply (XS2_agree (xs_base t) M raw spw R ltac:(lia)). lia. }
    (* [comment removed for export] *)
    destruct (Z_le_gt_dec len 63) as [Ls | Lb].
    { (* [comment removed for export] *)
      destruct (acc_last SEGS M s (len + 1) ACC ltac:(lia)) as (s1 & Rs1 & Hs1).
      destruct (RD8 (down8 (sh_lo s)) s ltac:(lia) eq_refl) as (w0 & Rw0).
      destruct (RD8 (down8 (sh_lo (s + (len + 1) - 1))) (s + (len + 1) - 1) ltac:(lia) eq_refl) as (w1 & Rw1).
      assert (QH : qc1H SEGS Mr sw (len + 1) (mt_g_shoff (rt_m2s (xs_rip t))) (mt_p_shoff (rt_m2s (xs_rip t))) w0 w1 s1).
      { split; rewrite ?Hs.
        - lia. - lia. - exact K7. - exact K8. - lia.
        - rewrite Sh_is_sh_lo. exact Rw0.
        - rewrite Sh_is_sh_lo. exact Rw1.
        - apply (RD1 _ _ Rs1). apply GRAN. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (s + (len + 1) - 1) ltac:(lia)). pose proof (sh_lo_mono s (s + (len + 1) - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
        - exact Hs1.
        - intros a Ha. apply (RD1 a _ (acc_zero SEGS M s (len + 1) ACC ltac:(lia) a Ha)). apply GRAN. rewrite !Sh_is_sh_lo in Ha |- *. lia. }
      destruct (asan_strlen_icpt_small SEGS t (TOK fx) Mr (seg_rom SEGS) sw raw spw len buf (Z_to_bv 8 1) R w0 w1 s1
                 PRE ltac:(lia) QH R1' eq_refl eq_refl) as (r & RUN & A10 & SAVED).
      rewrite XS2_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - exact OUT2.
      - apply XS2_grows. }
    { (* [comment removed for export] *)
      assert (CH : m2sH SEGS (rt_m2s (xs_rip t)) Mr sw (Z_to_bv 64 0)).
      { split.
        - exact K7. - exact K8. - exact K9. - exact K10. - exact K11. - exact K12. - exact K13. - exact K14.
        - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); lia.
        - lia. - lia. }
      destruct (acc_first SEGS M s (len + 1) ACC ltac:(lia)) as (s0b & Rs0 & Hs0).
      destruct (acc_last SEGS M s (len + 1) ACC ltac:(lia)) as (s1b & Rs1 & Hs1).
      assert (RUNx : exists r,
        msteps SEGS (mkst R (xs_base t) Mr (seg_rom SEGS))
                    (mkst r raw (XS3 (xs_base t) (xs_rip t) (xs_p_cf t) Mr sw raw spw len R) (seg_rom SEGS))
        /\ getr r 10 = Z_to_bv 64 len /\ (forall x, In x amset_saved -> getr r x = getr R x)).
      { apply (asan_strlen_icpt_big SEGS t (TOK fx) Mr (seg_rom SEGS) sw raw spw len buf (Z_to_bv 8 1) R s0b s1b (Z_to_bv 64 0)
                 PRE ltac:(lia) ltac:(lia) CH).
        - rewrite Hs. lia.
        - rewrite Hs. apply (RD1 _ _ Rs0). apply GRAN. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 s ltac:(lia)). pose proof (sh_lo_mono s (s + (len + 1) - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
        - rewrite Hs. exact Hs0.
        - rewrite Hs. apply (RD1 _ _ Rs1). apply GRAN. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (s + (len + 1) - 1) ltac:(lia)). pose proof (sh_lo_mono s (s + (len + 1) - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
        - rewrite Hs. exact Hs1.
        - rewrite Hs. intros a Ha. apply (RD1 a _ (acc_zero_mid SEGS M s (len + 1) ACC ltac:(lia) a Ha)). apply GRAN.
          unfold Sh, up8, down8 in Ha |- *. clear - Ha.
          pose proof (Z.div_mod (s + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + 7) 8 ltac:(lia)).
          pose proof (Z.div_mod (s + (len + 1)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + (len + 1)) 8 ltac:(lia)).
          rewrite !Z.div_mul in Ha by lia.
          pose proof (Z.div_mod s 8 ltac:(lia)). pose proof (Z.mod_pos_bound s 8 ltac:(lia)).
          pose proof (Z.div_mod (s + (len + 1) - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + (len + 1) - 1) 8 ltac:(lia)). (nodisj; lia).
        - exact R1'. - reflexivity. - reflexivity. }
      destruct RUNx as (r & RUN & A10 & SAVED).
      assert (XS3_r : XS3 (xs_base t) (xs_rip t) (xs_p_cf t) Mr sw raw spw len R
                      = mrestrict Hd (XS3 (xs_base t) (xs_rip t) (xs_p_cf t) M sw raw spw len R)).
      { clear - FR CP2 CPlo CPhi CR XS1_r XS2_r. (lazymatch goal with |- ?G => let G' := eval unfold XS3 in G in change_no_check G' end). rewrite XS2_r. (lazymatch goal with |- ?G => let G' := eval unfold rip_mem, ps_frame in G in change_no_check G' end).
        pose proof (u64_range spw).
        repeat (lazymatch goal with
                | |- context [if Z.ltb ?a ?b then _ else _] => destruct (Z.ltb a b)
                end);
        rewrite !(wbytes_mrestrict Hd) by
          (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
           first [hs_arith_goal; rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); (nodisj; lia)
                 | rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]);
        reflexivity. }
      rewrite XS3_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      + clear GRAN RD1 RD8 CH FIN.
        intros a Ha. pose proof (u64_range a). destruct (decide (sp - 2304 <= U a < sp)) as [Y|N]; [exact Y|]. exfalso. apply Ha.
        apply (XS3_agree (xs_base t) (xs_rip t) (xs_p_cf t) M sw raw spw len R ltac:((nodisj; lia))). lia.
      + apply XS3_grows. }
  Qed.

End CONTRACT.
End AsIcptStrlen.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtXMemcpy.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Definition xmcpy_words : list (option (bv 32)) :=
  [
   Some W_6d960; Some W_6d964; Some W_6d968; Some W_6d96c; Some W_6d970; Some W_6d974; Some W_6d978; Some W_6d97c;
   Some W_6d980; Some W_6d984; Some W_6d988; Some W_6d98c; Some W_6d990; None; None; Some W_6d99c; Some W_6d9a0;
   Some W_6d9a4; Some W_6d9a8; Some W_6d9ac; Some W_6d9b0; Some W_6d9b4; Some W_6d9b8; Some W_6d9bc; Some W_6d9c0;
   Some W_6d9c4; Some W_6d9c8; Some W_6d9cc; Some W_6d9d0; None; None; Some W_6d9dc; Some W_6d9e0; Some W_6d9e4;
   Some W_6d9e8; Some W_6d9ec; Some W_6d9f0; Some W_6d9f4; Some W_6d9f8; Some W_6d9fc; Some W_6da00; Some W_6da04;
   Some W_6da08; Some W_6da0c; Some W_6da10; Some W_6da14; Some W_6da18; None; None; Some W_6da24; Some W_6da28;
   Some W_6da2c; Some W_6da30; Some W_6da34; Some W_6da38; Some W_6da3c; Some W_6da40; Some W_6da44; Some W_6da48;
   Some W_6da4c; Some W_6da50; None; None; Some W_6da5c; Some W_6da60; Some W_6da64; Some W_6da68; Some W_6da6c;
   Some W_6da70; Some W_6da74; Some W_6da78; Some W_6da7c; Some W_6da80; Some W_6da84; Some W_6da88; Some W_6da8c;
   Some W_6da90; Some W_6da94; Some W_6da98; Some W_6da9c; Some W_6daa0; Some W_6daa4; Some W_6daa8; Some W_6daac;
   Some W_6dab0; Some W_6dab4; Some W_6dab8; Some W_6dabc; Some W_6dac0; Some W_6dac4; Some W_6dac8; Some W_6dacc;
   Some W_6dad0; Some W_6dad4; Some W_6dad8; Some W_6dadc; Some W_6dae0; Some W_6dae4; Some W_6dae8; Some W_6daec;
   Some W_6daf0; Some W_6daf4; Some W_6daf8; Some W_6dafc; Some W_6db00; Some W_6db04; Some W_6db08; Some W_6db0c;
   Some W_6db10; Some W_6db14; Some W_6db18; Some W_6db1c; None; None; Some W_6db28; Some W_6db2c; Some W_6db30;
   Some W_6db34; Some W_6db38; Some W_6db3c; Some W_6db40; Some W_6db44; Some W_6db48; Some W_6db4c; Some W_6db50;
   Some W_6db54; Some W_6db58; Some W_6db5c; Some W_6db60; Some W_6db64; Some W_6db68; Some W_6db6c; Some W_6db70;
   Some W_6db74; Some W_6db78; Some W_6db7c; Some W_6db80; Some W_6db84; Some W_6db88; Some W_6db8c; Some W_6db90;
   Some W_6db94; Some W_6db98; Some W_6db9c; Some W_6dba0; Some W_6dba4; Some W_6dba8; None; None; Some W_6dbb4;
   Some W_6dbb8; Some W_6dbbc; Some W_6dbc0; Some W_6dbc4; Some W_6dbc8; Some W_6dbcc; Some W_6dbd0; Some W_6dbd4;
   None; Some W_6dbdc; Some W_6dbe0; Some W_6dbe4; Some W_6dbe8; Some W_6dbec; Some W_6dbf0; Some W_6dbf4;
   Some W_6dbf8; Some W_6dbfc; None; Some W_6dc04; Some W_6dc08; Some W_6dc0c; Some W_6dc10; Some W_6dc14;
   Some W_6dc18; Some W_6dc1c; Some W_6dc20; Some W_6dc24; Some W_6dc28; Some W_6dc2c; Some W_6dc30; Some W_6dc34;
   Some W_6dc38; Some W_6dc3c; Some W_6dc40; Some W_6dc44; Some W_6dc48; Some W_6dc4c; Some W_6dc50; Some W_6dc54;
   Some W_6dc58; Some W_6dc5c; Some W_6dc60; Some W_6dc64; None; None; Some W_6dc70; Some W_6dc74; Some W_6dc78;
   Some W_6dc7c; Some W_6dc80; Some W_6dc84; Some W_6dc88; Some W_6dc8c; Some W_6dc90; Some W_6dc94; Some W_6dc98;
   Some W_6dc9c; Some W_6dca0; Some W_6dca4; Some W_6dca8; Some W_6dcac; Some W_6dcb0; Some W_6dcb4; Some W_6dcb8;
   Some W_6dcbc; Some W_6dcc0; Some W_6dcc4; Some W_6dcc8; Some W_6dccc; Some W_6dcd0; Some W_6dcd4; Some W_6dcd8;
   Some W_6dcdc; Some W_6dce0; Some W_6dce4; Some W_6dce8; Some W_6dcec; Some W_6dcf0; Some W_6dcf4; Some W_6dcf8;
   Some W_6dcfc; Some W_6dd00; Some W_6dd04; Some W_6dd08; Some W_6dd0c; Some W_6dd10; Some W_6dd14; Some W_6dd18;
   Some W_6dd1c; Some W_6dd20; Some W_6dd24; None; Some W_6dd2c; Some W_6dd30; Some W_6dd34; Some W_6dd38;
   Some W_6dd3c; Some W_6dd40; Some W_6dd44; Some W_6dd48; Some W_6dd4c; Some W_6dd50; Some W_6dd54; Some W_6dd58;
   Some W_6dd5c; Some W_6dd60; Some W_6dd64; Some W_6dd68; Some W_6dd6c; Some W_6dd70; None; None; Some W_6dd7c;
   Some W_6dd80; Some W_6dd84; Some W_6dd88; Some W_6dd8c; Some W_6dd90; Some W_6dd94; Some W_6dd98; Some W_6dd9c;
   Some W_6dda0; Some W_6dda4; Some W_6dda8; Some W_6ddac; Some W_6ddb0; Some W_6ddb4; Some W_6ddb8; Some W_6ddbc;
   Some W_6ddc0; Some W_6ddc4; Some W_6ddc8; Some W_6ddcc; Some W_6ddd0; Some W_6ddd4; Some W_6ddd8; Some W_6dddc;
   Some W_6dde0; Some W_6dde4; Some W_6dde8; Some W_6ddec; Some W_6ddf0; Some W_6ddf4; Some W_6ddf8; Some W_6ddfc;
   Some W_6de00; Some W_6de04; Some W_6de08; Some W_6de0c; Some W_6de10; Some W_6de14; Some W_6de18; Some W_6de1c;
   Some W_6de20; None; Some W_6de28; Some W_6de2c; Some W_6de30; Some W_6de34; Some W_6de38; Some W_6de3c;
   Some W_6de40; Some W_6de44; Some W_6de48; Some W_6de4c; Some W_6de50; Some W_6de54; Some W_6de58; Some W_6de5c;
   Some W_6de60; Some W_6de64; Some W_6de68; Some W_6de6c; None; None; Some W_6de78; Some W_6de7c; Some W_6de80;
   Some W_6de84; Some W_6de88; Some W_6de8c; Some W_6de90; Some W_6de94; Some W_6de98; Some W_6de9c
  ]%list.


(* [comment removed for export] *)
Record xmcpy_tab : Type := XMCT {
  xc_base : word;          (* [comment removed for export] *)
  xc_rip : rip_tab;        (* [comment removed for export] *)
  xc_mcp : word;           (* [comment removed for export] *)
  xc_g_flag : Z; xc_p_flag : Z;   (* [comment removed for export] *)
  xc_c_rmc : Z }.          (* [comment removed for export] *)

Record xmcpy_tab_ok (segs : list Segment) (t : xmcpy_tab) : Prop := XMCTOK {
  xcto_code : code_ato segs (xc_base t) 0 xmcpy_words;
  xcto_rip : rip_tab_ok segs (xc_rip t);
  xcto_rip_base : rt_base (xc_rip t) = at_ (xc_base t) 9776;
  xcto_mcp : code_at segs (xc_mcp t) 0 mmemcpy_words;
  xcto_qcf1 : code_ato segs (at_ (xc_base t) 116) 0 (qc2f_words 11 19);
  xcto_qcs1 : code_ato segs (at_ (xc_base t) 868) 0 (qc2s_words 19);
  xcto_qcf2 : code_ato segs (at_ (xc_base t) 188) 0 (qc2f_words 10 20);
  xcto_qcs2 : code_ato segs (at_ (xc_base t) 1124) 0 (qc2s_words 20);
  xcto_g52 : gload segs (xc_base t) 52 13 (xc_g_flag t);
  xcto_g116 : gload segs (at_ (xc_base t) 116) 0 13 (mt_g_shoff (rt_m2s (xc_rip t)));
  xcto_g188 : gload segs (at_ (xc_base t) 188) 0 13 (mt_g_shoff (rt_m2s (xc_rip t)));
  xcto_g244 : gload segs (xc_base t) 244 13 (xc_c_rmc t);
  xcto_b168 : gbnez segs (at_ (xc_base t) 168) 15 (at_ (xc_base t) 868);
  xcto_b916 : gbeqz segs (at_ (xc_base t) 916) 13 (at_ (xc_base t) 172);
  xcto_b240 : gbnez segs (at_ (xc_base t) 240) 15 (at_ (xc_base t) 1124);
  xcto_b1172 : gbeqz segs (at_ (xc_base t) 1172) 13 (at_ (xc_base t) 244);
  xcto_base : (U (xc_base t) mod 2 = 0)%Z /\ (U (xc_base t) + 20000 < 2 ^ 64)%Z;
  xcto_mcp_ok : ret_ok (xc_mcp t) }.

(* [comment removed for export] *)
Definition xmc_frame (mem : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (word_to_le_bytes 8 ra))
    (at_ sp (-16)) (word_to_le_bytes 8 s0))
    (at_ sp (-24)) (word_to_le_bytes 8 s1))
    (at_ sp (-32)) (word_to_le_bytes 8 s2))
    (at_ sp (-40)) (word_to_le_bytes 8 s3))
    (at_ sp (-48)) (word_to_le_bytes 8 s4))
    (at_ sp (-56)) (word_to_le_bytes 8 s5))
    (at_ sp (-64)) (word_to_le_bytes 8 s6))
    (at_ sp (-72)) (word_to_le_bytes 8 s7))
    (at_ sp (-80)) (word_to_le_bytes 8 s8).

Section XMCPY.
  Variable segs : list Segment.
  Variable base : word.
  Variable rt : rip_tab.
  Variable mcp : word.
  Variables g_flag p_flag c_rmc : Z.
  #[local] Abbreviation g_shoff := (mt_g_shoff (rt_m2s rt)).
  #[local] Abbreviation p_shoff := (mt_p_shoff (rt_m2s rt)).
  Hypothesis HCODE : code_ato segs base 0 xmcpy_words.
  Hypothesis RTOK : rip_tab_ok segs rt.
  Hypothesis RTB : rt_base rt = at_ base 9776.
  Hypothesis MCP : code_at segs mcp 0 mmemcpy_words.
  Hypothesis QCF1 : code_ato segs (at_ base 116) 0 (qc2f_words 11 19).
  Hypothesis QCS1 : code_ato segs (at_ base 868) 0 (qc2s_words 19).
  Hypothesis QCF2 : code_ato segs (at_ base 188) 0 (qc2f_words 10 20).
  Hypothesis QCS2 : code_ato segs (at_ base 1124) 0 (qc2s_words 20).
  Hypothesis G52 : gload segs base 52 13 g_flag.
  Hypothesis G116 : gload segs (at_ base 116) 0 13 g_shoff.
  Hypothesis G188 : gload segs (at_ base 188) 0 13 g_shoff.
  Hypothesis G244 : gload segs base 244 13 c_rmc.
  Hypothesis B168 : gbnez segs (at_ base 168) 15 (at_ base 868).
  Hypothesis B916 : gbeqz segs (at_ base 916) 13 (at_ base 172).
  Hypothesis B240 : gbnez segs (at_ base 240) 15 (at_ base 1124).
  Hypothesis B1172 : gbeqz segs (at_ base 1172) 13 (at_ base 244).
  Hypothesis Hbase : (U base mod 2 = 0)%Z /\ (U base + 20000 < 2 ^ 64)%Z.
  Hypothesis Hmcp : ret_ok mcp.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_6d960.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_6d964.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_6d968.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_6d96c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_6d970.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_6d974.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_6d978.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_6d97c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_6d980.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_6d984.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_6d988.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 10 _ HCODE eq_refl). Qed.
  Lemma Fo44 : fetch_word segs (at_ base 44) = Some W_6d98c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 11 _ HCODE eq_refl). Qed.
  Lemma Fo48 : fetch_word segs (at_ base 48) = Some W_6d990.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 12 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo60 : fetch_word segs (at_ base 60) = Some W_6d99c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 15 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_6d9a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_6d9a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_6d9a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_6d9ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_6d9b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo84 : fetch_word segs (at_ base 84) = Some W_6d9b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 21 _ HCODE eq_refl). Qed.
  Lemma Fo88 : fetch_word segs (at_ base 88) = Some W_6d9b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 22 _ HCODE eq_refl). Qed.
  Lemma Fo92 : fetch_word segs (at_ base 92) = Some W_6d9bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 23 _ HCODE eq_refl). Qed.
  Lemma Fo96 : fetch_word segs (at_ base 96) = Some W_6d9c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 24 _ HCODE eq_refl). Qed.
  Lemma Fo100 : fetch_word segs (at_ base 100) = Some W_6d9c4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 25 _ HCODE eq_refl). Qed.
  Lemma Fo104 : fetch_word segs (at_ base 104) = Some W_6d9c8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 26 _ HCODE eq_refl). Qed.
  Lemma Fo108 : fetch_word segs (at_ base 108) = Some W_6d9cc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 27 _ HCODE eq_refl). Qed.
  Lemma Fo112 : fetch_word segs (at_ base 112) = Some W_6d9d0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 28 _ HCODE eq_refl). Qed.












  Lemma Fo172 : fetch_word segs (at_ base 172) = Some W_6da0c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 43 _ HCODE eq_refl). Qed.
  Lemma Fo176 : fetch_word segs (at_ base 176) = Some W_6da10.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 44 _ HCODE eq_refl). Qed.
  Lemma Fo180 : fetch_word segs (at_ base 180) = Some W_6da14.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 45 _ HCODE eq_refl). Qed.
  Lemma Fo184 : fetch_word segs (at_ base 184) = Some W_6da18.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 46 _ HCODE eq_refl). Qed.












  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo252 : fetch_word segs (at_ base 252) = Some W_6da5c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 63 _ HCODE eq_refl). Qed.
  Lemma Fo256 : fetch_word segs (at_ base 256) = Some W_6da60.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 64 _ HCODE eq_refl). Qed.
  Lemma Fo260 : fetch_word segs (at_ base 260) = Some W_6da64.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 65 _ HCODE eq_refl). Qed.
  Lemma Fo264 : fetch_word segs (at_ base 264) = Some W_6da68.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 66 _ HCODE eq_refl). Qed.
  Lemma Fo268 : fetch_word segs (at_ base 268) = Some W_6da6c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 67 _ HCODE eq_refl). Qed.
  Lemma Fo272 : fetch_word segs (at_ base 272) = Some W_6da70.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 68 _ HCODE eq_refl). Qed.
  Lemma Fo276 : fetch_word segs (at_ base 276) = Some W_6da74.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 69 _ HCODE eq_refl). Qed.
  Lemma Fo280 : fetch_word segs (at_ base 280) = Some W_6da78.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 70 _ HCODE eq_refl). Qed.
  Lemma Fo284 : fetch_word segs (at_ base 284) = Some W_6da7c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 71 _ HCODE eq_refl). Qed.
  Lemma Fo288 : fetch_word segs (at_ base 288) = Some W_6da80.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 72 _ HCODE eq_refl). Qed.
  Lemma Fo292 : fetch_word segs (at_ base 292) = Some W_6da84.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 73 _ HCODE eq_refl). Qed.
  Lemma Fo296 : fetch_word segs (at_ base 296) = Some W_6da88.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 74 _ HCODE eq_refl). Qed.
  Lemma Fo300 : fetch_word segs (at_ base 300) = Some W_6da8c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 75 _ HCODE eq_refl). Qed.
  Lemma Fo304 : fetch_word segs (at_ base 304) = Some W_6da90.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 76 _ HCODE eq_refl). Qed.





















































  Lemma Fo528 : fetch_word segs (at_ base 528) = Some W_6db70.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 132 _ HCODE eq_refl). Qed.
  Lemma Fo532 : fetch_word segs (at_ base 532) = Some W_6db74.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 133 _ HCODE eq_refl). Qed.











































































  Lemma Fo860 : fetch_word segs (at_ base 860) = Some W_6dcbc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 215 _ HCODE eq_refl). Qed.
  Lemma Fo864 : fetch_word segs (at_ base 864) = Some W_6dcc0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 216 _ HCODE eq_refl). Qed.













  Lemma Fo920 : fetch_word segs (at_ base 920) = Some W_6dcf8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 230 _ HCODE eq_refl). Qed.
  Lemma Fo924 : fetch_word segs (at_ base 924) = Some W_6dcfc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 231 _ HCODE eq_refl). Qed.
  Lemma Fo928 : fetch_word segs (at_ base 928) = Some W_6dd00.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 232 _ HCODE eq_refl). Qed.
  Lemma Fo932 : fetch_word segs (at_ base 932) = Some W_6dd04.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 233 _ HCODE eq_refl). Qed.
  Lemma Fo936 : fetch_word segs (at_ base 936) = Some W_6dd08.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 234 _ HCODE eq_refl). Qed.
  Lemma Fo940 : fetch_word segs (at_ base 940) = Some W_6dd0c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 235 _ HCODE eq_refl). Qed.
  Lemma Fo944 : fetch_word segs (at_ base 944) = Some W_6dd10.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 236 _ HCODE eq_refl). Qed.
  Lemma Fo948 : fetch_word segs (at_ base 948) = Some W_6dd14.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 237 _ HCODE eq_refl). Qed.
  Lemma Fo952 : fetch_word segs (at_ base 952) = Some W_6dd18.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 238 _ HCODE eq_refl). Qed.
  Lemma Fo956 : fetch_word segs (at_ base 956) = Some W_6dd1c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 239 _ HCODE eq_refl). Qed.
  Lemma Fo960 : fetch_word segs (at_ base 960) = Some W_6dd20.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 240 _ HCODE eq_refl). Qed.


















































  Lemma Fo1176 : fetch_word segs (at_ base 1176) = Some W_6ddf8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 294 _ HCODE eq_refl). Qed.
  Lemma Fo1180 : fetch_word segs (at_ base 1180) = Some W_6ddfc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 295 _ HCODE eq_refl). Qed.
  Lemma Fo1184 : fetch_word segs (at_ base 1184) = Some W_6de00.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 296 _ HCODE eq_refl). Qed.
  Lemma Fo1188 : fetch_word segs (at_ base 1188) = Some W_6de04.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 297 _ HCODE eq_refl). Qed.
  Lemma Fo1192 : fetch_word segs (at_ base 1192) = Some W_6de08.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 298 _ HCODE eq_refl). Qed.
  Lemma Fo1196 : fetch_word segs (at_ base 1196) = Some W_6de0c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 299 _ HCODE eq_refl). Qed.
  Lemma Fo1200 : fetch_word segs (at_ base 1200) = Some W_6de10.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 300 _ HCODE eq_refl). Qed.
  Lemma Fo1204 : fetch_word segs (at_ base 1204) = Some W_6de14.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 301 _ HCODE eq_refl). Qed.
  Lemma Fo1208 : fetch_word segs (at_ base 1208) = Some W_6de18.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 302 _ HCODE eq_refl). Qed.
  Lemma Fo1212 : fetch_word segs (at_ base 1212) = Some W_6de1c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmcpy_words 303 _ HCODE eq_refl). Qed.






























  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables dst src ra sp : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable fl : byte.
  Variable regs : bvmap 5 word.
  Hypothesis Hsp : (0x10007fff8000 + 2304 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  (* [comment removed for export] *)
  Definition XC1 : word -> option byte :=
    xmc_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
              (getr regs 22) (getr regs 23) (getr regs 24).
  (* [comment removed for export] *)
  Definition XC2 : word -> option byte :=
    rip_mem rt XC1 (at_ sp (-2160)) (at_ base 944) sp (Z_to_bv 64 n) (getr regs 18) (Z_to_bv 64 (U src + n))
            (Z_to_bv 64 (U dst + n)) (at_ sp (-2152)) src (Z_to_bv 64 n).
  Definition XC3 : word -> option byte :=
    rip_mem rt XC2 (at_ sp (-2160)) (at_ base 1196) sp dst (Z_to_bv 64 n) (Z_to_bv 64 (U src + n))
            (Z_to_bv 64 (U dst + n)) (at_ sp (-2152)) dst (Z_to_bv 64 n).
  Definition xmcpy_post (M : word -> option byte) : word -> option byte := wbytes M dst bs.

  Lemma XC1_out : forall x : word, (U x < U sp - 80 \/ U sp <= U x)%Z -> XC1 x = mem x.
  Proof using Hsp base.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold XC1, xmc_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma XC1_low : forall x : word, (U x < U sp - 2240)%Z -> XC1 x = mem x.
  Proof using Hsp base. intros x Hx. apply XC1_out. lia. Qed.
  Lemma XC1_agree : forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> XC1 x = mem x.
  Proof using Hsp base. intros x Hx. apply XC1_out. lia. Qed.
  Lemma XC1_grows : mem_grows mem XC1.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold XC1, xmc_frame in G in change_no_check G' end).
    repeat (lazymatch goal with
            | |- mem_grows ?a ?a => apply mem_grows_refl
            | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
            end).
  Qed.
  Lemma XC2_agree : forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> XC2 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold XC2 in G in change_no_check G' end). rewrite rip_mem_outside; [apply XC1_agree; exact Hx | rewrite at_u; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  Qed.

  Lemma XC3_agree : forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> XC3 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold XC3 in G in change_no_check G' end). rewrite rip_mem_outside; [apply XC2_agree; exact Hx | rewrite at_u; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  Qed.

  Lemma rip_mem_grows' : forall t M (sp' raX s0 s1 s2 s3 s4 s5 b z : word), mem_grows M (rip_mem t M sp' raX s0 s1 s2 s3 s4 s5 b z).
  Proof using.
    intros. (lazymatch goal with |- ?G => let G' := eval unfold rip_mem, ps_frame in G in change_no_check G' end).
    destruct (Z.ltb _ _);
      repeat (lazymatch goal with
              | |- mem_grows ?a ?a => apply mem_grows_refl
              | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
              end).
  Qed.
  Lemma XC2_grows : mem_grows mem XC2.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold XC2 in G in change_no_check G' end). eapply mem_grows_trans; [apply XC1_grows | apply rip_mem_grows']. Qed.
  Lemma XC3_grows : mem_grows mem XC3.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold XC3 in G in change_no_check G' end). eapply mem_grows_trans; [apply XC2_grows | apply rip_mem_grows']. Qed.

  Lemma rd_o : forall (M : word -> option byte) (B : Z) (a : word) k bs0,
    (forall x : word, (U x < B)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= B)%Z -> (B <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M B a k bs0 HM Ha HB Hr. rewrite <- Hr. apply rdn_ext; [lia|].
    intros x Hx. apply HM. lia.
  Qed.
  Lemma rd_outF : forall (M : word -> option byte) (a : word) k bs0,
    (forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= U sp - 2240 \/ U sp <= U a)%Z -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M a k bs0 HM Ha Hnw Hr. rewrite <- Hr. apply rdn_ext; [exact Hnw|].
    intros x Hx. apply HM. lia.
  Qed.
  Lemma rd_outZ : forall (M : word -> option byte) (c : Z) k bs0,
    (forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> M x = mem x) ->
    (0 <= c)%Z -> (c + Z.of_nat k <= U sp - 2240)%Z ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs0 -> rdn segs M (Z_to_bv 64 c) k = Some bs0.
  Proof using Hsp base.
    intros M c k bs0 HM Hc Hk Hr. pose proof (u64_range sp). apply (rd_outF M); try assumption; wd_ulia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MC : mcH segs mem dst src n bs.
  Hypothesis Hends : (U src + n <= 2 ^ 47)%Z /\ (U dst + n <= 2 ^ 47)%Z.
  Hypothesis Rgf : rdn segs mem (Z_to_bv 64 g_flag) 8 = Some (LE8 (Z_to_bv 64 p_flag)).
  Hypothesis Rfl : rdn segs mem (Z_to_bv 64 p_flag) 1 = Some [fl].
  Hypothesis Hfl : U fl <> 0%Z.
  Hypothesis Rrmc : rdn segs mem (Z_to_bv 64 c_rmc) 8 = Some (LE8 mcp).
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 2240)%Z (g_flag :: p_flag :: c_rmc :: m2s_cells (rt_m2s rt)).
  Hypothesis Hstk : store_ok segs mem (at_ sp (-2240)) 2240 = true.
  Hypothesis Hsrc_stk : (n = 0 \/ U src + n <= U sp - 2240 \/ U sp <= U src)%Z.
  Hypothesis Hdst_stk : (n = 0 \/ U dst + n <= U sp - 2240 \/ U sp <= U dst)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis R1 : getr regs 1 = ra.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R10 : getr regs 10 = dst.
  Hypothesis R11 : getr regs 11 = src.
  Hypothesis R12 : getr regs 12 = Z_to_bv 64 n.

  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC; unfold m2s_cells in HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ sp (-2240)) _ 2240);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac addr_n := gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; rewrite ?at_addi; zlit_at;
                 try (progress ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end)); unorm).
  Ltac rd_close LOW Hr :=
    apply (rd_o _ _ _ _ _ LOW);
    [ rewrite ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ]
    | lia
    | first [ exact Hr | rewrite <- Hr; f_equal; apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ] ] ].
  Ltac cldb F D bb LOW Hr :=
    chain_step; [reflexivity
      | eapply step_lbu with (b := bb);
        [exact F | reflexivity | exact D | addr_n; rd_close LOW Hr]
      | step_simpl]; vn.
  Ltac gl G LOW Hr :=
    eapply msteps_trans; [ eapply G; apply (rd_o _ _ _ _ _ LOW); [(lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia | lia | exact Hr] | ]; zlit_at.

  (* [comment removed for export] *)
  #[local] Abbreviation CLX := (fun r : reg => In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cblkA :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 104) XC1 rom)
      /\ getr r 1 = ra /\ getr r 2 = at_ sp (-2160) /\ getr r 8 = sp /\ getr r 10 = dst /\ getr r 11 = src
      /\ getr r 12 = Z_to_bv 64 n /\ getr r 19 = Z_to_bv 64 (U src + n) /\ getr r 20 = Z_to_bv 64 (U dst + n) /\ getr r 21 = at_ sp (-2152)
      /\ (forall i : reg, In i [9; 18; 22; 23; 24; 25; 26; 27; 3; 4]%list -> getr r i = getr regs i)
      /\ regs_agree CLX regs r.
  Proof using R12 R11 R10 R2 R1 Hdst_stk Hsrc_stk Hstk Hcells Hfl Rfl Rgf Hends MC Hsp fl bs G52 HCODE c_rmc p_flag g_flag rt.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs. pose proof (u8_range fl) as Hflr.
    destruct MC as [Mn Mlen Msrc Mdst Mdisj Mnws Mnwd]. cells_split.
    Ltac pro G52 XC1_low Rgf Rfl :=
      an Fo0 D_6d960;                                    (* [comment removed for export] *)
      fsd Fo4 D_6d964 (at_ sp (-8));                     (* [comment removed for export] *)
      fsd Fo8 D_6d968 (at_ sp (-16));                    (* [comment removed for export] *)
      fsd Fo12 D_6d96c (at_ sp (-24));
      fsd Fo16 D_6d970 (at_ sp (-32));
      fsd Fo20 D_6d974 (at_ sp (-40));
      fsd Fo24 D_6d978 (at_ sp (-48));
      fsd Fo28 D_6d97c (at_ sp (-56));
      fsd Fo32 D_6d980 (at_ sp (-64));
      fsd Fo36 D_6d984 (at_ sp (-72));
      fsd Fo40 D_6d988 (at_ sp (-80));
      change (wbytes _ _ _) with XC1;
      an Fo44 D_6d98c;                                   (* [comment removed for export] *)
      an Fo48 D_6d990;                                   (* [comment removed for export] *)
      gl G52 XC1_low Rgf;                                (* [comment removed for export] *)
      cldb Fo60 D_6d99c fl XC1_low Rfl;                  (* [comment removed for export] *)
      ab_ft Fo64 D_6d9a0 ltac:(condz);                 (* [comment removed for export] *)
      an Fo68 D_6d9a4; an Fo72 D_6d9a8;                  (* [comment removed for export] *)
      av Fo76 D_6d9ac (Z_to_bv 64 (U src + n)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      av Fo80 D_6d9b0 (Z_to_bv 64 (U dst + n)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
    Ltac tailA :=
      av Fo96 D_6d9c0 (Z_to_bv 64 (2 ^ 64 - 1 - U src)) ltac:(apply v_not_word);         (* [comment removed for export] *)
      ab_ft Fo100 D_6d9c4 ltac:(condz);                (* [comment removed for export] *)
      wd_refl.
    Ltac fin := post; rewrite ?at_0; try reflexivity;
      [ intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi | ra_solve ].
    destruct (decide (dst = src)) as [EQ | NEQ].
    - (* [comment removed for export] *)
      wd_eexists. split.
      + pro G52 XC1_low Rgf Rfl.
        ab_tk Fo84 D_6d9b4 ltac:(rewrite EQ; apply c_eq_refl).     (* [comment removed for export] *)
        tailA.
      + fin.
    - assert (NE' : U dst <> U src) by (intros E; apply NEQ; apply bv_eq; exact E).
      destruct (Z_le_gt_dec (U dst + n) (U src)) as [LE | GT].
      + wd_eexists. split.
        * pro G52 XC1_low Rgf Rfl.
          ab_ft Fo84 D_6d9b4 ltac:(condz).                (* [comment removed for export] *)
          ab_tk Fo88 D_6d9b8 ltac:(condz).                (* [comment removed for export] *)
          tailA.
        * fin.
      + wd_eexists. split.
        * pro G52 XC1_low Rgf Rfl.
          ab_ft Fo84 D_6d9b4 ltac:(condz).                (* [comment removed for export] *)
          ab_ft Fo88 D_6d9b8 ltac:(condz).                (* [comment removed for export] *)
          ab_ft Fo92 D_6d9bc ltac:(condz).                (* [comment removed for export] *)
          tailA.
        * fin.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cblkSs : forall M r0, (1 <= n <= 64)%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 104) M rom) (mkst r (at_ base 116) M rom)
      /\ getr r 22 = Z_to_bv 64 (2 ^ 64 + n - 65) /\ regs_agree (fun x => In x [13; 22]%list) r0 r.
  Proof using HCODE.
    intros M r0 Hs R12'. wd_eexists. split.
    - av Fo104 D_6d9c8 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm (2 ^ 64 + n - 65) (-1)); f_equal; lia).
      an Fo108 D_6d9cc.
      ab_ft Fo112 D_6d9d0 ltac:(condz).
      wd_refl.
    - post. ra_solve.
  Qed.
  Lemma cblkSz : forall M r0, n = 0%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 104) M rom) (mkst r (at_ base 172) M rom)
      /\ getr r 22 = Z_to_bv 64 (2 ^ 64 + n - 65) /\ regs_agree (fun x => In x [13; 22]%list) r0 r.
  Proof using HCODE.
    intros M r0 Hz R12'. wd_eexists. split.
    - av Fo104 D_6d9c8 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm (2 ^ 64 + n - 65) (-1)); f_equal; lia).
      an Fo108 D_6d9cc.
      ab_tk Fo112 D_6d9d0 ltac:(condz).
      ab_ft Fo860 D_6dcbc ltac:(condz).
      an Fo864 D_6dcc0.
      wd_refl.
    - post. ra_solve.
  Qed.
  Lemma cblkSb : forall M r0, (65 <= n)%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 104) M rom) (mkst r (at_ base 920) M rom)
      /\ getr r 22 = Z_to_bv 64 (n - 65) /\ regs_agree (fun x => In x [13; 22]%list) r0 r.
  Proof using Hdst_stk Hends Hsp sp src dst HCODE.
    intros M r0 Hb R12'. pose proof (u64_range dst) as Hd. wd_eexists. split.
    - av Fo104 D_6d9c8 (Z_to_bv 64 (n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).
      an Fo108 D_6d9cc.
      ab_tk Fo112 D_6d9d0 ltac:(condz).
      ab_tk Fo860 D_6dcbc ltac:(condz).
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cblkDs : forall M r0, (1 <= n <= 64)%Z -> getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n -> getr r0 22 = Z_to_bv 64 (2 ^ 64 + n - 65) ->
    exists r, msteps segs (mkst r0 (at_ base 172) M rom) (mkst r (at_ base 188) M rom)
      /\ regs_agree (fun x => In x [13]%list) r0 r.
  Proof using Hends src HCODE.
    intros M r0 Hs R10' R12' R22'. pose proof (u64_range dst) as Hd. wd_eexists. split.
    - av Fo172 D_6da0c (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).
      ab_ft Fo176 D_6da10 ltac:(condz).
      an Fo180 D_6da14.
      ab_ft Fo184 D_6da18 ltac:(condz).
      wd_refl.
    - ra_solve.
  Qed.
  Lemma cblkDz : forall M r0, n = 0%Z -> getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n -> getr r0 22 = Z_to_bv 64 (2 ^ 64 + n - 65) ->
    exists r, msteps segs (mkst r0 (at_ base 172) M rom) (mkst r (at_ base 244) M rom)
      /\ regs_agree (fun x => In x [13]%list) r0 r.
  Proof using Hends src HCODE.
    intros M r0 Hz R10' R12' R22'. pose proof (u64_range dst) as Hd. wd_eexists. split.
    - av Fo172 D_6da0c (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).
      ab_ft Fo176 D_6da10 ltac:(condz).
      an Fo180 D_6da14.
      ab_tk Fo184 D_6da18 ltac:(condz).
      ab_ft Fo528 D_6db70 ltac:(condz).
      an Fo532 D_6db74.
      wd_refl.
    - ra_solve.
  Qed.
  Lemma cblkDb : forall M r0, (65 <= n)%Z -> getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n -> getr r0 22 = Z_to_bv 64 (n - 65) ->
    exists r, msteps segs (mkst r0 (at_ base 172) M rom) (mkst r (at_ base 1176) M rom)
      /\ regs_agree (fun x => In x [13]%list) r0 r.
  Proof using Hdst_stk Hends Hsp sp src HCODE.
    intros M r0 Hb R10' R12' R22'. pose proof (u64_range dst) as Hd. wd_eexists. split.
    - av Fo172 D_6da0c (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).
      ab_ft Fo176 D_6da10 ltac:(condz).
      an Fo180 D_6da14.
      ab_tk Fo184 D_6da18 ltac:(condz).
      ab_tk Fo528 D_6db70 ltac:(condz).
      wd_refl.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma qc1H_XC1 : forall (b : word) w0 w1 s1,
    (U b + n <= 2 ^ 47)%Z ->
    qc1H segs mem b n g_shoff p_shoff w0 w1 s1 -> qc1H segs XC1 b n g_shoff p_shoff w0 w1 s1.
  Proof using Hcells Hsp c_rmc p_flag g_flag base.
    intros b w0 w1 s1 Hb [Q1 Q2 Q3 Q4 [Q5 Q6] Q7 Q8 Q9 Q10 Q11].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range b) as Hbr. cells_split.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos a 8).
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U b) ltac:(lia)) as S0. pose proof (HSh (U b + n - 1)%Z ltac:(lia)) as S1.
    assert (D0 : (Sh (U b) - 7 <= down8 (Sh (U b)) <= Sh (U b))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U b)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U b)) 8 ltac:(lia)); lia).
    assert (D1 : (Sh (U b + n - 1) - 7 <= down8 (Sh (U b + n - 1)) <= Sh (U b + n - 1))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U b + n - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U b + n - 1)) 8 ltac:(lia)); lia).
    Ltac ro Hr := apply (rd_o _ _ _ _ _ XC1_low); [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | lia | exact Hr].
    split; try assumption.
    - ro Q3. - ro Q4. - split; assumption. - ro Q7. - ro Q8. - ro Q9.
    - intros a Ha. pose proof (u64_range a). apply (rd_o _ _ _ _ _ XC1_low); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia | exact (Q11 a Ha)].
  Qed.

  Lemma cblkQ1 : forall r0 w0 w1 s1,
    qc1H segs mem src n g_shoff p_shoff w0 w1 s1 ->
    getr r0 11 = src -> getr r0 19 = Z_to_bv 64 (U src + n) ->
    exists r, msteps segs (mkst r0 (at_ base 116) XC1 rom) (mkst r (at_ base 172) XC1 rom)
      /\ regs_agree (fun x => In x qc2_clob \/ x = 19) r0 r.
  Proof using Hcells Hends Hsp dst B916 B168 G116 QCS1 QCF1 c_rmc p_flag g_flag.
    intros r0 w0 w1 s1 QH R11' R19'. pose proof (u64_range base).
    destruct (qc2_pass segs (at_ base 116) (at_ base 868) (at_ base 172) 11 19 g_shoff p_shoff QCF1 QCS1 G116
             ltac:(rewrite at_at; exact B168) ltac:(rewrite at_at; exact B916) ltac:(rewrite at_at; reflexivity)
             (or_intror eq_refl) (or_introl eq_refl)
             r0 XC1 rom src n w0 w1 s1 (qc1H_XC1 _ _ _ _ (proj1 Hends) QH) R11' R19') as (r & RUN & _ & AG).
    exists r. split; [|exact AG]. rewrite at_at, Z.add_0_r in RUN. exact RUN.
  Qed.

  Lemma cblkQ2 : forall r0 w0 w1 s1,
    qc1H segs mem dst n g_shoff p_shoff w0 w1 s1 ->
    getr r0 10 = dst -> getr r0 20 = Z_to_bv 64 (U dst + n) ->
    exists r, msteps segs (mkst r0 (at_ base 188) XC1 rom) (mkst r (at_ base 244) XC1 rom)
      /\ regs_agree (fun x => In x qc2_clob \/ x = 20) r0 r.
  Proof using Hcells Hends Hsp src B1172 B240 G188 QCS2 QCF2 c_rmc p_flag g_flag.
    intros r0 w0 w1 s1 QH R10' R20'. pose proof (u64_range base).
    destruct (qc2_pass segs (at_ base 188) (at_ base 1124) (at_ base 244) 10 20 g_shoff p_shoff QCF2 QCS2 G188
             ltac:(rewrite at_at; exact B240) ltac:(rewrite at_at; exact B1172) ltac:(rewrite at_at; reflexivity)
             (or_introl eq_refl) (or_intror (or_introl eq_refl))
             r0 XC1 rom dst n w0 w1 s1 (qc1H_XC1 _ _ _ _ (proj2 Hends) QH) R10' R20') as (r & RUN & _ & AG).
    exists r. split; [|exact AG]. rewrite at_at, Z.add_0_r in RUN. exact RUN.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ripH_on : forall (M : word -> option byte) (b raX : word) (s0 s1 : byte) (midend : word),
    (forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> M x = mem x) -> mem_grows mem M ->
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem b midend ->
    ((0x10007fff8000 <= U b /\ U b + n + 1 <= 0x800000000000) \/ U b + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U b))) 1 = Some [s0] -> (U s0 = 0 \/ U b mod 8 < U s0 < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U b + n - 1))) 1 = Some [s1] -> (U s1 = 0 \/ (U b + n - 1) mod 8 < U s1 < 128)%Z ->
    (forall a : word, (Sh (up8 (U b)) <= U a < Sh (down8 (U b + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok raX ->
    ripH segs rt M b (Z_to_bv 64 n) raX (at_ sp (-2160)) s0 s1 midend.
  Proof using Hstk Hcells Hsp c_rmc p_flag g_flag base.
    intros M b raX s0 s1 midend HM HG Hn65 CH Hrng R0 H0 R1' H1' RZ HR.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range b) as Hb.
    destruct CH as [C1 C2 C3 C4 C5 C6 C7 C8 CC Clo Chi]. cells_split.
    assert (SH : forall x, (0 <= x < 0x800000000000)%Z -> (0x7fff8000 <= Sh x < 0x10007fff8000)%Z).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos x 8). pose proof (Z.div_lt_upper_bound x 8 0x100000000000 ltac:(lia) ltac:(lia)). lia. }
    pose proof (SH (U b) ltac:(lia)) as S0'.
    pose proof (SH (U b + n - 1)%Z ltac:(lia)) as S1'.
    assert (UP : (U b <= up8 (U b) <= U b + 7)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end); pose proof (Z.div_mod (U b + 7) 8); pose proof (Z.mod_pos_bound (U b + 7) 8); lia).
    assert (DN : (U b + n - 7 <= down8 (U b + n) <= U b + n)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (U b + n) 8); pose proof (Z.mod_pos_bound (U b + n) 8); lia).
    pose proof (SH (up8 (U b)) ltac:(lia)) as S2. pose proof (SH (down8 (U b + n)) ltac:(lia)) as S3.
    assert (Un : U (Z_to_bv 64 n) = n) by (apply u_Z2bv; lia).
    Ltac rdo HMx Hr := apply (rd_outZ _ _ _ _ HMx); [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr].
    split.
    - split; [rdo HM C1 | rdo HM C2 | rdo HM C3 | rdo HM C4 | rdo HM C5 | rdo HM C6 | rdo HM C7 | rdo HM C8 | exact CC | lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat constructor; rewrite ?at_u; lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rdo HM R0.
    - exact H0.
    - rewrite Un. rdo HM R1'.
    - rewrite Un. exact H1'.
    - rewrite Un. intros a Ha. pose proof (u64_range a). pose proof (RZ a Ha) as Ra.
      rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ra |- *. rdo HM Ra.
    - rewrite at_u by lia. lia.
    - rewrite at_at. replace (-2160 + -80)%Z with (-2240)%Z by lia. eapply store_ok_mono; [exact HG|].
      eapply (store_ok_sub segs mem (at_ sp (-2240)) _ 2240); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - exact HR.
  Qed.

  Lemma cblkR1 : forall r0 (s0b s1b : byte) (midend : word),
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem src midend ->
    ((0x10007fff8000 <= U src /\ U src + n + 1 <= 0x800000000000) \/ U src + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0b] -> (U s0b = 0 \/ U src mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U src + n - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr r0 2 = at_ sp (-2160) -> getr r0 8 = sp -> getr r0 10 = dst -> getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    getr r0 18 = getr regs 18 -> getr r0 19 = Z_to_bv 64 (U src + n) -> getr r0 20 = Z_to_bv 64 (U dst + n) -> getr r0 21 = at_ sp (-2152) ->
    exists r, msteps segs (mkst r0 (at_ base 920) XC1 rom) (mkst r (at_ base 172) XC2 rom)
      /\ getr r 2 = at_ sp (-2160) /\ getr r 8 = sp /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 n
      /\ getr r 19 = Z_to_bv 64 (U src + n) /\ getr r 20 = Z_to_bv 64 (U dst + n) /\ getr r 21 = at_ sp (-2152)
      /\ regs_agree (fun x => In x ([1; 9; 18; 23; 24]%list ++ rip_clob)) r0 r.
  Proof using Hstk Hcells Hsp Hbase RTB RTOK HCODE c_rmc p_flag g_flag.
    intros r0 s0b s1b midend Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz R2' R8' R10' R11' R12' R18' R19' R20' R21'.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    assert (RA : ret_ok (at_ base 944)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    set (r1 := regupd (regupd (regupd (regupd (regupd (regupd r0 23 dst) 10 src) 24 src) 11 (Z_to_bv 64 n)) 9 (Z_to_bv 64 n)) 1 (at_ base 944)).
    destruct (region_clear segs rt RTOK XC1 rom src (Z_to_bv 64 n) (at_ base 944) (at_ sp (-2160)) s0b s1b midend r1
                (ripH_on XC1 src (at_ base 944) s0b s1b midend XC1_agree XC1_grows Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz RA))
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; reflexivity | subst r1; gres; exact R2' | subst r1; gres; reflexivity | subst r1; gres; reflexivity |].
    wd_eexists. split.
    - an Fo920 D_6dcf8.                                  (* [comment removed for export] *)
      an Fo924 D_6dcfc.                                  (* [comment removed for export] *)
      an Fo928 D_6dd00.                                  (* [comment removed for export] *)
      an Fo932 D_6dd04.                                  (* [comment removed for export] *)
      an Fo936 D_6dd08.                                  (* [comment removed for export] *)
      an Fo940 D_6dd0c.                                  (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- RTB.
      eapply msteps_trans; [exact RUN2|].
      replace (rip_mem rt XC1 (at_ sp (-2160)) (at_ base 944) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) src (Z_to_bv 64 n))
         with XC2.
      2:{ (lazymatch goal with |- ?G => let G' := eval unfold XC2 in G in change_no_check G' end). subst r1. gres. rewrite R8', R18', R19', R20', R21'. reflexivity. }
      assert (A24 : getr r2 24 = src) by (rewrite (AG2 24) by notin; subst r1; gres; reflexivity).
      assert (A9 : getr r2 9 = Z_to_bv 64 n) by (rewrite (AG2 9) by notin; subst r1; gres; reflexivity).
      assert (A23 : getr r2 23 = dst) by (rewrite (AG2 23) by notin; subst r1; gres; reflexivity).
      an Fo944 D_6dd10.                                  (* [comment removed for export] *)
      an Fo948 D_6dd14.                                  (* [comment removed for export] *)
      an Fo952 D_6dd18.                                  (* [comment removed for export] *)
      an Fo956 D_6dd1c.                                  (* [comment removed for export] *)
      ab_tk Fo960 D_6dd20 ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - assert (A2 : getr r2 2 = at_ sp (-2160)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
      assert (A8 : getr r2 8 = sp) by (rewrite (AG2 8) by notin; subst r1; gres; exact R8').
      assert (A19 : getr r2 19 = Z_to_bv 64 (U src + n)) by (rewrite (AG2 19) by notin; subst r1; gres; exact R19').
      assert (A20 : getr r2 20 = Z_to_bv 64 (U dst + n)) by (rewrite (AG2 20) by notin; subst r1; gres; exact R20').
      assert (A21 : getr r2 21 = at_ sp (-2152)) by (rewrite (AG2 21) by notin; subst r1; gres; exact R21').
      post; try assumption.
      intros x Hx. gres.
      assert (X : x <> 10 /\ x <> 18 /\ x <> 12 /\ x <> 11) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct X as (X1 & X2 & X3 & X4). rewrite !getr_other by assumption.
      rewrite (AG2 x) by (intros Hc; apply Hx; apply in_or_app; right; exact Hc).
      subst r1. assert (Y : x <> 1 /\ x <> 9 /\ x <> 11 /\ x <> 24 /\ x <> 10 /\ x <> 23) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct Y as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). rewrite !getr_other by assumption. reflexivity.
  Qed.

  Lemma cblkR2 : forall r0 (s0b s1b : byte) (midend : word),
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0b] -> (U s0b = 0 \/ U dst mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U dst + n - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr r0 2 = at_ sp (-2160) -> getr r0 8 = sp -> getr r0 10 = dst -> getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    getr r0 19 = Z_to_bv 64 (U src + n) -> getr r0 20 = Z_to_bv 64 (U dst + n) -> getr r0 21 = at_ sp (-2152) ->
    exists r, msteps segs (mkst r0 (at_ base 1176) XC2 rom) (mkst r (at_ base 244) XC3 rom)
      /\ getr r 2 = at_ sp (-2160) /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 n
      /\ regs_agree (fun x => In x ([1; 9; 18; 19; 22]%list ++ rip_clob)) r0 r.
  Proof using Hstk Hcells Hsp Hbase RTB RTOK HCODE c_rmc p_flag g_flag.
    intros r0 s0b s1b midend Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz R2' R8' R10' R11' R12' R19' R20' R21'.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    assert (RA : ret_ok (at_ base 1196)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    set (r1 := regupd (regupd (regupd (regupd (regupd r0 9 dst) 22 src) 11 (Z_to_bv 64 n)) 18 (Z_to_bv 64 n)) 1 (at_ base 1196)).
    destruct (region_clear segs rt RTOK XC2 rom dst (Z_to_bv 64 n) (at_ base 1196) (at_ sp (-2160)) s0b s1b midend r1
                (ripH_on XC2 dst (at_ base 1196) s0b s1b midend XC2_agree XC2_grows Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz RA))
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; reflexivity | subst r1; gres; exact R2' | subst r1; gres; exact R10' | subst r1; gres; reflexivity |].
    wd_eexists. split.
    - an Fo1176 D_6ddf8.                                 (* [comment removed for export] *)
      an Fo1180 D_6ddfc.                                 (* [comment removed for export] *)
      an Fo1184 D_6de00.                                 (* [comment removed for export] *)
      an Fo1188 D_6de04.                                 (* [comment removed for export] *)
      an Fo1192 D_6de08.                                 (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- RTB.
      eapply msteps_trans; [exact RUN2|].
      replace (rip_mem rt XC2 (at_ sp (-2160)) (at_ base 1196) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) dst (Z_to_bv 64 n))
         with XC3.
      2:{ (lazymatch goal with |- ?G => let G' := eval unfold XC3 in G in change_no_check G' end). subst r1. gres. rewrite R8', R19', R20', R21'. reflexivity. }
      assert (A22 : getr r2 22 = src) by (rewrite (AG2 22) by notin; subst r1; gres; reflexivity).
      assert (A18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (AG2 18) by notin; subst r1; gres; reflexivity).
      assert (A9 : getr r2 9 = dst) by (rewrite (AG2 9) by notin; subst r1; gres; reflexivity).
      an Fo1196 D_6de0c.                                 (* [comment removed for export] *)
      an Fo1200 D_6de10.                                 (* [comment removed for export] *)
      an Fo1204 D_6de14.                                 (* [comment removed for export] *)
      an Fo1208 D_6de18.                                 (* [comment removed for export] *)
      ab_tk Fo1212 D_6de1c ltac:(condz).               (* [comment removed for export] *)
      wd_refl.
    - assert (A2 : getr r2 2 = at_ sp (-2160)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
      post; try assumption.
      intros x Hx. gres.
      assert (X : x <> 10 /\ x <> 19 /\ x <> 12 /\ x <> 11) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct X as (X1 & X2 & X3 & X4). rewrite !getr_other by assumption.
      rewrite (AG2 x) by (intros Hc; apply Hx; apply in_or_app; right; exact Hc).
      subst r1. assert (Y : x <> 1 /\ x <> 18 /\ x <> 11 /\ x <> 22 /\ x <> 9) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct Y as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition xmc_slots : list (Z * word) :=
    [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20);
     (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24)]%Z.

  Lemma slots_XC1 : forall (k : Z) (v : word), In (k, v) xmc_slots -> rdn segs XC1 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp base.
    intros k v Hin. pose proof (u64_range sp). unfold xmc_slots in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval unfold XC1, xmc_frame in G in change_no_check G' end); rd8_chain|]). destruct Hin.
  Qed.
  Lemma slots_XC3 : forall (k : Z) (v : word), In (k, v) xmc_slots -> rdn segs XC3 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp).
    assert (Hk : (-80 <= k /\ k + 8 <= 0)%Z).
    { unfold xmc_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    rewrite <- (slots_XC1 k v Hin). apply rdn_ext; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    intros x Hx. rewrite at_u in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold XC3, XC2 in G in change_no_check G' end).
    rewrite !rip_mem_outside; first [reflexivity | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u; lia].
  Qed.
  Lemma slots_post : forall (M : word -> option byte) (k : Z) (v : word),
    (forall k' v', In (k', v') xmc_slots -> rdn segs M (at_ sp k') 8 = Some (word_to_le_bytes 8 v')) ->
    In (k, v) xmc_slots -> rdn segs (xmcpy_post M) (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hdst_stk Hsrc_stk Hends MC Hsp n src mem base.
    intros M k v HM Hin. pose proof (u64_range sp). pose proof (u64_range dst).
    destruct MC as [Mn Mlen Msrc Mdst Mdisj Mnws Mnwd].
    assert (Hk : (-80 <= k /\ k + 8 <= 0)%Z).
    { unfold xmc_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    (lazymatch goal with |- ?G => let G' := eval unfold xmcpy_post in G in change_no_check G' end). destruct (Z.eq_dec n 0) as [E0 | NZ0].
    { assert (bs = []%list) as -> by (destruct bs; [reflexivity | rewrite E0 in Mlen; cbn in Mlen; lia]). (lazymatch goal with |- ?G => let G' := eval cbn [wbytes] in G in change_no_check G' end). exact (HM k v Hin). }
    rewrite rdn_wbytes_out; [exact (HM k v Hin) | rewrite Mlen, at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Mlen; lia].
  Qed.

  Lemma cblkC : forall (M : word -> option byte) r0,
    (forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> M x = mem x) -> mem_grows mem M ->
    (forall k v, In (k, v) xmc_slots -> rdn segs M (at_ sp k) 8 = Some (word_to_le_bytes 8 v)) ->
    getr r0 2 = at_ sp (-2160) -> getr r0 10 = dst -> getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 244) M rom) (mkst r ra (xmcpy_post M) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R2 Hret Hdst_stk Hsrc_stk Hcells Rrmc Hends MC Hsp Hmcp Hbase G244 MCP HCODE c_rmc p_flag g_flag mcp rt.
    intros M r0 HMA HG SL R2' R10' R11' R12' AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs. cells_split.
    assert (HM : forall x : word, (U x < U sp - 2240)%Z -> M x = mem x) by (intros x Hx; apply HMA; lia).
    assert (RA : ret_ok (at_ base 256)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    assert (MCM : mcH segs M dst src n bs).
    { destruct MC as [Mn Mlen Msrc Mdst Mdisj Mnws Mnwd]. split; try assumption.
      - rewrite <- Msrc. apply rdn_ext; [rewrite Mlen; lia|]. intros x Hx. apply HMA. rewrite Mlen in Hx. lia.
      - eapply store_ok_mono; [exact HG | exact Mdst]. }
    set (r1 := regupd (regupd r0 13 mcp) 1 (at_ base 256)).
    destruct (mmemcpy_run segs mcp MCP M dst src n bs rom MCM r1 (at_ base 256) RA)
      as (r2 & RUN2 & KP); [subst r1; gres; reflexivity | subst r1; gres; exact R10' | subst r1; gres; exact R11' | subst r1; gres; exact R12' |].
    assert (A2 : getr r2 2 = at_ sp (-2160)) by (rewrite (KP 2) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); subst r1; gres; exact R2').
    assert (A10 : getr r2 10 = dst) by (rewrite (KP 10) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); subst r1; gres; exact R10').
    pose proof (fun k v H => slots_post M k v SL H) as SLP. unfold xmc_slots in SLP.
    Ltac fldM F D vv SLP :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply SLP; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    wd_eexists. split; [|split].
    - gl G244 HM Rrmc.                                   (* [comment removed for export] *)
      aret Fo252 D_6da5c mcp.                            (* [comment removed for export] *)
      rewrite at_addi; zlit_at. change (regupd _ 1 _) with r1. rewrite <- (at_0 mcp).
      eapply msteps_trans; [exact RUN2|].
      an Fo256 D_6da60.                                  (* [comment removed for export] *)
      fldM Fo260 D_6da64 ra SLP.
      fldM Fo264 D_6da68 (getr regs 8) SLP.
      fldM Fo268 D_6da6c (getr regs 9) SLP.
      fldM Fo272 D_6da70 (getr regs 18) SLP.
      fldM Fo276 D_6da74 (getr regs 19) SLP.
      fldM Fo280 D_6da78 (getr regs 20) SLP.
      fldM Fo284 D_6da7c (getr regs 21) SLP.
      fldM Fo288 D_6da80 (getr regs 22) SLP.
      fldM Fo292 D_6da84 (getr regs 23) SLP.
      fldM Fo296 D_6da88 (getr regs 24) SLP.
      an Fo300 D_6da8c.                                  (* [comment removed for export] *)
      aret Fo304 D_6da90 ra.                             (* [comment removed for export] *)
      wd_refl.
    - gres. exact A10.
    - intros x Hx. unfold amset_saved in Hx. cbn [In] in Hx. gres.
      repeat (destruct Hx as [<-|Hx];
        [ gres; rwH; rewrite ?at_addi, ?at_0; first
            [ reflexivity
            | f_equal; lia
            | rewrite (KP _) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); subst r1; gres; rewrite ?(AG0 _) by notin; first [reflexivity | assumption | rwH; rewrite ?at_addi; f_equal; lia] ]
        |]).
      destruct Hx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac regx AG x := rewrite (AG x) by notin.
  Ltac notin2 := let Hc := fresh "Hin" in intros Hc; cbn [In app qc2_clob rip_clob] in Hc;
    decompose [or] Hc; first [discriminate | contradiction].
  Ltac regxi AG x := rewrite (AG x) by notin2.
  Ltac in_lit := (lazymatch goal with |- ?G => let G' := eval cbn [In app amset_saved] in G in change_no_check G' end); repeat (first [left; reflexivity | right]).
  Ltac from_or Hc := cbn [In app qc2_clob rip_clob] in Hc; decompose [or] Hc; first [contradiction | subst; in_lit; fail].

  Theorem xmcpy_zero : n = 0%Z ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (xmcpy_post XC1) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hsrc_stk Hstk Hcells Rrmc Hfl Rfl Rgf Hends MC Hsp fl src Hmcp Hbase G244 G52 MCP HCODE c_rmc p_flag g_flag mcp rt.
    intros Hz.
    destruct cblkA as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A19 & A20 & A21 & AK & AG1).
    destruct (cblkSz XC1 r1 Hz A12) as (r2 & RUN2 & B22 & AG2).
    destruct (cblkDz XC1 r2 Hz) as (r3 & RUN3 & AG3); [regx AG2 (10:reg); exact A10 | regx AG2 (12:reg); exact A12 | exact B22 |].
    destruct (cblkC XC1 r3 XC1_agree XC1_grows slots_XC1) as (r4 & RUN4 & C10 & CK);
      [ regx AG3 (2:reg); regx AG2 (2:reg); exact A2 | regx AG3 (10:reg); regx AG2 (10:reg); exact A10
      | regx AG3 (11:reg); regx AG2 (11:reg); exact A11 | regx AG3 (12:reg); regx AG2 (12:reg); exact A12
      | intros x Hx; rewrite (AG3 x); [rewrite (AG2 x); [exact (AG1 x Hx) | intros Hc; apply Hx; from_or Hc] | intros Hc; apply Hx; from_or Hc] |].
    exists r4. split; [|split; [exact C10 | exact CK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
  Qed.

  Theorem xmcpy_small : forall w0s w1s s1s w0d w1d s1d, (1 <= n <= 64)%Z ->
    qc1H segs mem src n g_shoff p_shoff w0s w1s s1s ->
    qc1H segs mem dst n g_shoff p_shoff w0d w1d s1d ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (xmcpy_post XC1) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hsrc_stk Hstk Hcells Rrmc Hfl Rfl Rgf Hends MC Hsp fl Hmcp Hbase B1172 B240 B916 B168 G244 G188 G116 G52 QCS2 QCF2 QCS1 QCF1 MCP HCODE c_rmc p_flag g_flag mcp.
    intros w0s w1s s1s w0d w1d s1d Hs QS QD.
    destruct cblkA as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A19 & A20 & A21 & AK & AG1).
    destruct (cblkSs XC1 r1 Hs A12) as (r2 & RUN2 & B22 & AG2).
    destruct (cblkQ1 r2 w0s w1s s1s QS) as (r3 & RUN3 & AG3); [regx AG2 (11:reg); exact A11 | regx AG2 (19:reg); exact A19 |].
    assert (C10 : getr r3 10 = dst) by (regxi AG3 (10:reg); regx AG2 (10:reg); exact A10).
    assert (C12 : getr r3 12 = Z_to_bv 64 n) by (regxi AG3 (12:reg); regx AG2 (12:reg); exact A12).
    assert (C22 : getr r3 22 = Z_to_bv 64 (2 ^ 64 + n - 65)) by (regxi AG3 (22:reg); exact B22).
    destruct (cblkDs XC1 r3 Hs C10 C12 C22) as (r4 & RUN4 & AG4).
    destruct (cblkQ2 r4 w0d w1d s1d QD) as (r5 & RUN5 & AG5);
      [regx AG4 (10:reg); exact C10 | regx AG4 (20:reg); regxi AG3 (20:reg); regx AG2 (20:reg); exact A20 |].
    destruct (cblkC XC1 r5 XC1_agree XC1_grows slots_XC1) as (r6 & RUN6 & D10 & DK).
    { regxi AG5 (2:reg). regx AG4 (2:reg). regxi AG3 (2:reg). regx AG2 (2:reg). exact A2. }
    { regxi AG5 (10:reg). regx AG4 (10:reg). exact C10. }
    { regxi AG5 (11:reg). regx AG4 (11:reg). regxi AG3 (11:reg). regx AG2 (11:reg). exact A11. }
    { regxi AG5 (12:reg). regx AG4 (12:reg). exact C12. }
    { intros x Hx.
      rewrite (AG5 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG4 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG3 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG2 x) by (intros Hc; apply Hx; from_or Hc). exact (AG1 x Hx). }
    exists r6. split; [|split; [exact D10 | exact DK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
    eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN6.
  Qed.

  Theorem xmcpy_big : forall (s0s s1s s0d s1d : byte) (midend : word), (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem src midend -> m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U src /\ U src + n + 1 <= 0x800000000000) \/ U src + n <= 0x7fff7fff)%Z ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0s] -> (U s0s = 0 \/ U src mod 8 < U s0s < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1s] -> (U s1s = 0 \/ (U src + n - 1) mod 8 < U s1s < 128)%Z ->
    (forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0d] -> (U s0d = 0 \/ U dst mod 8 < U s0d < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1d] -> (U s1d = 0 \/ (U dst + n - 1) mod 8 < U s1d < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (xmcpy_post XC3) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hsrc_stk Hstk Hcells Rrmc Hfl Rfl Rgf Hends MC Hsp fl Hmcp Hbase G244 G52 MCP RTB RTOK HCODE c_rmc p_flag g_flag mcp.
    intros s0s s1s s0d s1d midend Hb CHs CHd Rgs Rgd Rs0s Hs0s Rs1s Hs1s Rzs Rs0d Hs0d Rs1d Hs1d Rzd.
    destruct cblkA as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A19 & A20 & A21 & AK & AG1).
    destruct (cblkSb XC1 r1 ltac:(lia) A12) as (r2 & RUN2 & B22 & AG2).
    destruct (cblkR1 r2 s0s s1s midend Hb CHs Rgs Rs0s Hs0s Rs1s Hs1s Rzs) as (r3 & RUN3 & C2 & C8 & C10 & C11 & C12 & C19 & C20 & C21 & AG3);
      [ regx AG2 (2:reg); exact A2 | regx AG2 (8:reg); exact A8 | regx AG2 (10:reg); exact A10 | regx AG2 (11:reg); exact A11
      | regx AG2 (12:reg); exact A12 | regx AG2 (18:reg); apply AK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | regx AG2 (19:reg); exact A19 | regx AG2 (20:reg); exact A20
      | regx AG2 (21:reg); exact A21 |].
    assert (C22 : getr r3 22 = Z_to_bv 64 (n - 65)) by (regxi AG3 (22:reg); exact B22).
    destruct (cblkDb XC2 r3 ltac:(lia) C10 C12 C22) as (r4 & RUN4 & AG4).
    destruct (cblkR2 r4 s0d s1d midend Hb CHd Rgd Rs0d Hs0d Rs1d Hs1d Rzd) as (r5 & RUN5 & D2 & D10 & D11 & D12 & AG5);
      [ regx AG4 (2:reg); exact C2 | regx AG4 (8:reg); exact C8 | regx AG4 (10:reg); exact C10 | regx AG4 (11:reg); exact C11
      | regx AG4 (12:reg); exact C12 | regx AG4 (19:reg); exact C19 | regx AG4 (20:reg); exact C20 | regx AG4 (21:reg); exact C21 |].
    destruct (cblkC XC3 r5 XC3_agree XC3_grows slots_XC3 D2 D10 D11 D12) as (r6 & RUN6 & E10 & EK).
    { intros x Hx.
      rewrite (AG5 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG4 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG3 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG2 x) by (intros Hc; apply Hx; from_or Hc). exact (AG1 x Hx). }
    exists r6. split; [|split; [exact E10 | exact EK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
    eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN6.
  Qed.

End XMCPY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record xmcpyH (segs : list Segment) (t : xmcpy_tab) (mem : word -> option byte)
       (dst src : word) (n : Z) (bs : list byte) (ra sp : word) (fl : byte) : Prop := XMCPYH {
  xch_sp : (0x10007fff8000 + 2304 <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 <= 2 ^ 47)%Z;
  xch_mc : mcH segs mem dst src n bs;
  xch_ends : (bv_unsigned src + n <= 2 ^ 47)%Z /\ (bv_unsigned dst + n <= 2 ^ 47)%Z;
  xch_gf : rdn segs mem (Z_to_bv 64 (xc_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (xc_p_flag t)));
  xch_fl : rdn segs mem (Z_to_bv 64 (xc_p_flag t)) 1 = Some [fl];
  xch_flnz : bv_unsigned fl <> 0%Z;
  xch_rmc : rdn segs mem (Z_to_bv 64 (xc_c_rmc t)) 8 = Some (word_to_le_bytes 8 (xc_mcp t));
  xch_cells : Forall (fun c => 0 <= c /\ c + 8 <= bv_unsigned sp - 2240)%Z
                (xc_g_flag t :: xc_p_flag t :: xc_c_rmc t :: m2s_cells (rt_m2s (xc_rip t)));
  xch_stk : store_ok segs mem (at_ sp (-2240)) 2240 = true;
  xch_src_stk : (n = 0 \/ bv_unsigned src + n <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= bv_unsigned src)%Z;
  xch_dst_stk : (n = 0 \/ bv_unsigned dst + n <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= bv_unsigned dst)%Z;
  xch_ret : ret_ok ra }.

Section PKG.
  Variable segs : list Segment.
  Variable t : xmcpy_tab.
  Hypothesis TOK : xmcpy_tab_ok segs t.
  #[local] Abbreviation U := bv_unsigned.

  Ltac pkg_finish P9 P8 :=
    lazymatch goal with
    | |- store_ok _ _ (at_ _ _) _ = true => exact P9
    | |- Forall _ _ => exact P8
    | _ => first [eassumption | reflexivity]
    end.

  Theorem asan_memcpy_icpt_zero : forall mem rom (dst src ra sp : word) (n : Z) (bs : list byte) (fl : byte) regs,
    xmcpyH segs t mem dst src n bs ra sp fl -> n = 0%Z ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (xc_base t) mem rom) (mkst r ra (xmcpy_post dst bs (XC1 mem ra sp regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst src ra sp n bs fl regs [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12] Hz R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18].
    replace (mkst regs (xc_base t) mem rom) with (mkst regs (at_ (xc_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply xmcpy_zero. all: pkg_finish P9 P8.
  Qed.

  Theorem asan_memcpy_icpt_small : forall mem rom (dst src ra sp : word) (n : Z) (bs : list byte) (fl : byte) regs w0s w1s s1s w0d w1d s1d,
    xmcpyH segs t mem dst src n bs ra sp fl -> (1 <= n <= 64)%Z ->
    qc1H segs mem src n (mt_g_shoff (rt_m2s (xc_rip t))) (mt_p_shoff (rt_m2s (xc_rip t))) w0s w1s s1s ->
    qc1H segs mem dst n (mt_g_shoff (rt_m2s (xc_rip t))) (mt_p_shoff (rt_m2s (xc_rip t))) w0d w1d s1d ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (xc_base t) mem rom) (mkst r ra (xmcpy_post dst bs (XC1 mem ra sp regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst src ra sp n bs fl regs w0s w1s s1s w0d w1d s1d [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12] Hs QS QD R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18].
    replace (mkst regs (xc_base t) mem rom) with (mkst regs (at_ (xc_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply xmcpy_small. all: pkg_finish P9 P8.
  Qed.

  Theorem asan_memcpy_icpt_big : forall mem rom (dst src ra sp : word) (n : Z) (bs : list byte) (fl : byte) regs
      (s0s s1s s0d s1d : byte) (midend : word),
    xmcpyH segs t mem dst src n bs ra sp fl -> (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s (xc_rip t)) mem src midend -> m2sH segs (rt_m2s (xc_rip t)) mem dst midend ->
    ((0x10007fff8000 <= U src /\ U src + n + 1 <= 0x800000000000) \/ U src + n <= 0x7fff7fff)%Z ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0s] -> (U s0s = 0 \/ U src mod 8 < U s0s < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1s] -> (U s1s = 0 \/ (U src + n - 1) mod 8 < U s1s < 128)%Z ->
    (forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0d] -> (U s0d = 0 \/ U dst mod 8 < U s0d < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1d] -> (U s1d = 0 \/ (U dst + n - 1) mod 8 < U s1d < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (xc_base t) mem rom)
                  (mkst r ra (xmcpy_post dst bs (XC3 (xc_base t) (xc_rip t) mem dst src ra sp n regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst src ra sp n bs fl regs s0s s1s s0d s1d midend [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12]
           Hb CHs CHd Rgs Rgd Rs0s Hs0s Rs1s Hs1s Rzs Rs0d Hs0d Rs1d Hs1d Rzd R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18].
    replace (mkst regs (xc_base t) mem rom) with (mkst regs (at_ (xc_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply xmcpy_big. all: pkg_finish P9 P8.
  Qed.
End PKG.
End FPGen1.
End AsRtXMemcpy.
Module AsIcptXMemcpy.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsRtAccess.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset AsRtXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.

Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.


Section CONTRACT.
  Context {fx0 : FPState}.   (* [comment removed for export] *)
  Context {RC : run_ceil}.   (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  (* [comment removed for export] *)
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props IA (AAINVH h) fsbase SEGS.
  (* [comment removed for export] *)
  Hypothesis SEGS_hull : forall a, find_segment SEGS a 1 <> None -> ia_img_lo IA <= a < ia_img_hi IA.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis IMG_HI : ia_img_hi IA <= AS_LO.
  Hypothesis IMG_LO : 0 <= ia_img_lo IA.
  Hypothesis FSB0 : 0 <= fsbase.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable t : xmcpy_tab.
  Hypothesis TOK : forall fx : FPState, @xmcpy_tab_ok fx SEGS t.
  Hypothesis T_entry : xc_base t = Z_to_bv 64 (ia_memcpy_icpt IA).
  (* [comment removed for export] *)
  Definition xmcpy_cells : list (Z * nat * Z) :=
    [(xc_g_flag t, 8%nat, xc_p_flag t); (xc_p_flag t, 1%nat, 1); (xc_c_rmc t, 8%nat, U (xc_mcp t));
     (mt_g_shoff (rt_m2s (xc_rip t)), 8%nat, mt_p_shoff (rt_m2s (xc_rip t))); (mt_p_shoff (rt_m2s (xc_rip t)), 8%nat, SB);
     (mt_g_midbeg (rt_m2s (xc_rip t)), 8%nat, mt_p_midbeg (rt_m2s (xc_rip t))); (mt_p_midbeg (rt_m2s (xc_rip t)), 8%nat, 0);
     (mt_g_midend (rt_m2s (xc_rip t)), 8%nat, mt_p_midend (rt_m2s (xc_rip t))); (mt_p_midend (rt_m2s (xc_rip t)), 8%nat, 0);
     (mt_g_hiend (rt_m2s (xc_rip t)), 8%nat, mt_p_hiend (rt_m2s (xc_rip t))); (mt_p_hiend (rt_m2s (xc_rip t)), 8%nat, 0x7fffffffffff)].
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN SEGS M (fst (fst c)) (snd (fst c)) (snd c)) xmcpy_cells.
  (* [comment removed for export] *)
  Hypothesis CELLS_img : Forall (fun c => ia_img_lo IA <= fst (fst c) /\ fst (fst c) + 8 <= ia_img_hi IA) xmcpy_cells.

  #[local] Abbreviation cfg := (AsIface3.cfg SEGS).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem C_memcpy_icpt : MEMCPY_AT SEGS FXOK IA AAINVH (ia_memcpy_icpt IA).
  Proof using CELLS_img CELLS T_entry TOK t FSB0 IMG_LO IMG_HI SEGS_wx SEGS_hull HP fsbase.
    (lazymatch goal with |- ?G => let G' := eval unfold MEMCPY_AT in G in change_no_check G' end).
    intros h fx R M mdl Lc FF W B C K ret sp dst src n bs HFX HH AI CP Hdst Hsrc Hn [Hn0 HnN] OV AIM1 AIM2 AIM3 AIM4
           ACCs ACCd SVs SVd HBS DO DSJ SSJ DOK.
    pose proof (HP h) as HPh.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk).
    destruct (aap_lazy _ _ _ _ HPh _ _ _ _ _ _ _ AI) as (AA & Awf & MI & SHCok & BLKok & PRES).
    set (Hd := HL mdl AA).
    pose proof (HL_off_segments SEGS IA (AAINVH h) fsbase HPh SEGS_hull _ _ _ _ _ _ _ AA AI) as HOFF. fold Hd in HOFF.
    pose proof (@ceil_rng RC) as CR.
    assert (NZ : forall z, 0 <= z < 2 ^ 64 -> (ia_img_lo IA <= z < ia_img_hi IA) \/ CEIL <= z -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HL_zone SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI Hz). tauto. }
    unfold AS_HEAPLO, PTRHI, SB, AS_LO, MSTK_M, NMAX in *.
    assert (RNGd : (0x10007fff8000 <= dst /\ dst + n < 2 ^ 47) \/ (0 <= dst /\ dst + n <= 0x7fff7fff)).
    { unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM1, AIM2. lia. }
    assert (RNGs : (0x10007fff8000 <= src /\ src + n < 2 ^ 47) \/ (0 <= src /\ src + n <= 0x7fff7fff)).
    { unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM3, AIM4. lia. }
    assert (Hdn2 : 0 <= dst /\ dst + n < 2 ^ 47) by lia. assert (Hsn2 : 0 <= src /\ src + n < 2 ^ 47) by lia.
    (* [comment removed for export] *)
    assert (NVIS : forall b m, shadow_visible IA Lc FF b m -> forall z, b <= z < b + m -> 0 <= z < 2 ^ 64 -> Hd (Z_to_bv 64 z) = false).
    { intros b m SV z Hz Hz64. destruct (SV z Hz) as [IB | [(f & k & Hf & Hfz) | [ST | IM]]].
      - apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [left; exact IB | exact Hz64].
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [right; exists f, k; split; [exact Hf | lia] | exact Hz64].
      - apply NZ; [lia | right; lia].
      - apply NZ; [lia | left; lia]. }
    assert (NDST : forall z, dst <= z < dst + n -> Hd (Z_to_bv 64 z) = false) by (intros z Hz; apply (NVIS _ _ SVd z Hz); lia).
    assert (NSRC : forall z, src <= z < src + n -> Hd (Z_to_bv 64 z) = false) by (intros z Hz; apply (NVIS _ _ SVs z Hz); lia).
    (* [comment removed for export] *)
    assert (NSH : forall b m, shadow_visible IA Lc FF b m ->
              forall z, b <= z < b + m -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false).
    { intros b m SV z Hz y Hy.
      destruct (SV z Hz) as [(p & pm & Hp & Hpz) | [(f & k & Hf & Hfz) | [ST | IM]]].
      - pose proof (aap_zone _ _ _ _ HPh _ _ _ _ _ _ _ p pm AI Hp) as ((Z1 & Z2 & Z3 & Z4) & Zn & Z16).
        apply (HL_allowed_page mdl AA (sh_lo p) (sh_hi p pm) (sh_lo z) y (BLKok p pm Hp)); [|exact Hy].
        apply sh_lo_in; unfold PTRLO in *; lia.
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_allowed_page mdl AA (sh_lo fsbase) (sh_hi fsbase FAKE_SIZE) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; unfold FAKE_SIZE in *; lia.
      - unfold PTRHI in ST.
        apply (HL_allowed_page mdl AA (sh_lo CEIL) (SB + 2 ^ 44) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + split; [apply sh_lo_mono; lia | apply sh_lo_lt47; lia].
      - apply (HL_allowed_page mdl AA (sh_lo (ia_img_lo IA)) (sh_hi (ia_img_lo IA) (ia_img_hi IA - ia_img_lo IA)) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; lia. }
    pose proof (NSH _ _ SVd) as NSHd. pose proof (NSH _ _ SVs) as NSHs.
    (* [comment removed for export] *)
    set (dstw := getr R 10) in *. set (srcw := getr R 11) in *. set (spw := getr R 2) in *.
    pose proof (u64_range dstw) as Hdr. pose proof (u64_range srcw) as Hsr0. pose proof (u64_range spw) as Hsr. pose proof (u64_range (getr R 12)) as H12r.
    assert (R12 : getr R 12 = Z_to_bv 64 n) by (apply bv_eq; rewrite u_Z2bv by lia; exact Hn).
    assert (RET : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u_Z2bv by lia; exact CPe).
    clear CPe CP16.   (* [comment removed for export] *)
    set (Mr := mrestrict Hd M).
    (* [comment removed for export] *)
    pose proof (CELLS _ _ _ _ _ _ _ _ AI) as CE. pose proof CELLS_img as CI. unfold xmcpy_cells in CE, CI.
    apply Forall_cons_iff in CE; destruct CE as [C1 CE]. apply Forall_cons_iff in CE; destruct CE as [C2 CE]. apply Forall_cons_iff in CE; destruct CE as [C3 CE]. apply Forall_cons_iff in CE; destruct CE as [C4 CE]. apply Forall_cons_iff in CE; destruct CE as [C5 CE]. apply Forall_cons_iff in CE; destruct CE as [C6 CE]. apply Forall_cons_iff in CE; destruct CE as [C7 CE]. apply Forall_cons_iff in CE; destruct CE as [C8 CE]. apply Forall_cons_iff in CE; destruct CE as [C9 CE]. apply Forall_cons_iff in CE; destruct CE as [C10 CE]. apply Forall_cons_iff in CE; destruct CE as [C11 CE].
    apply Forall_cons_iff in CI; destruct CI as [D1 CI]. apply Forall_cons_iff in CI; destruct CI as [D2 CI]. apply Forall_cons_iff in CI; destruct CI as [D3 CI]. apply Forall_cons_iff in CI; destruct CI as [D4 CI]. apply Forall_cons_iff in CI; destruct CI as [D5 CI]. apply Forall_cons_iff in CI; destruct CI as [D6 CI]. apply Forall_cons_iff in CI; destruct CI as [D7 CI]. apply Forall_cons_iff in CI; destruct CI as [D8 CI]. apply Forall_cons_iff in CI; destruct CI as [D9 CI]. apply Forall_cons_iff in CI; destruct CI as [D10 CI]. apply Forall_cons_iff in CI; destruct CI as [D11 CI].
    cbn [fst snd] in *.
    Ltac hoz NZ := apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NZ; lia].
    Ltac konst NZ MM C := apply (cellN_mrestrict SEGS _ MM _ _ _ C); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); hoz NZ].
    assert (K1 : rdn SEGS Mr (Z_to_bv 64 (xc_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (xc_p_flag t)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C1).
    assert (K2 : rdn SEGS Mr (Z_to_bv 64 (xc_p_flag t)) 1 = Some [Z_to_bv 8 1]).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C2); [vm_compute; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K3 : rdn SEGS Mr (Z_to_bv 64 (xc_c_rmc t)) 8 = Some (word_to_le_bytes 8 (xc_mcp t))).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C3); [rewrite Z_to_bv_bv_unsigned; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K4 : rdn SEGS Mr (Z_to_bv 64 (mt_g_shoff (rt_m2s (xc_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_shoff (rt_m2s (xc_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C4).
    assert (K5 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midbeg (rt_m2s (xc_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midbeg (rt_m2s (xc_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C6).
    assert (K6 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midbeg (rt_m2s (xc_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C7).
    assert (K7 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midend (rt_m2s (xc_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midend (rt_m2s (xc_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C8).
    assert (K8 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midend (rt_m2s (xc_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C9).
    assert (K9 : rdn SEGS Mr (Z_to_bv 64 (mt_g_hiend (rt_m2s (xc_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_hiend (rt_m2s (xc_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C10).
    assert (K10 : rdn SEGS Mr (Z_to_bv 64 (mt_p_hiend (rt_m2s (xc_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C11).
    assert (K11 : rdn SEGS Mr (Z_to_bv 64 (mt_p_shoff (rt_m2s (xc_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C5).
    (* [comment removed for export] *)
    assert (WV : forall (m : mem) (x : word), store_ok SEGS m x 1%nat = true -> wview SEGS m x <> None).
    { intros m x Hx. cbn [store_ok] in Hx. destruct (wview SEGS m x); [discriminate | discriminate Hx]. }
    assert (STK : store_ok SEGS Mr (at_ spw (-2240)) 2240 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ].
      apply store_ok_of_all; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. apply WV. apply CPstk. cbn in Hx. lia. }
    assert (DOKr : store_ok SEGS Mr dstw (Z.to_nat n) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite Z2Nat.id; lia | rewrite Z2Nat.id by lia; apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NDST; lia]].
      apply store_ok_of_all; [rewrite Z2Nat.id; lia|]. intros x Hx. rewrite Z2Nat.id in Hx by lia. apply WV. apply DOK. lia. }
    assert (OFFS : forall b, off_scratch sp b (b + n) -> n = 0 \/ b + n <= U spw - 2240 \/ U spw <= b).
    { intros b BSJ. destruct (Z.eq_dec n 0) as [E0|NE0]; [left; exact E0 | right]. unfold off_scratch, MSTK_M in BSJ.
      pose proof (BSJ b ltac:(lia)) as X1. pose proof (BSJ (b + n - 1) ltac:(lia)) as X2.
      destruct (Z_lt_le_dec b (sp - 2304)) as [L|Ge]; [|lia].
      destruct (Z_lt_le_dec (b + n - 1) (sp - 2304)) as [L2|Ge2]; [lia|].
      exfalso. apply (BSJ (sp - 1)); lia. }
    pose proof (OFFS dst DSJ) as DSTK. pose proof (OFFS src SSJ) as SSTK. clear OFFS.
    (* [comment removed for export] *)
    assert (BS : rdn SEGS M srcw (Z.to_nat n) = Some bs).
    { replace srcw with (Z_to_bv 64 src) by (apply bv_eq; rewrite u_Z2bv by lia; symmetry; exact Hsrc). exact HBS. }
    pose proof (rdn_length _ _ _ _ _ BS) as LBS.
    assert (SR : hid_off Hd (U srcw) n) by (apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NSRC; lia]).
    assert (BSr : rdn SEGS Mr srcw (Z.to_nat n) = Some bs).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact BS | lia | rewrite Z2Nat.id by lia; exact SR]. }
    assert (MC : mcH SEGS Mr dstw srcw n bs).
    { split.
      - lia. - exact LBS. - rewrite LBS. exact BSr. - rewrite LBS. exact DOKr.
      - destruct OV as [O0 | O1]; [|lia]. destruct (Z_le_gt_dec (U dstw) (U srcw)); lia.
      - lia. - lia. }
    clear OV.
    assert (PRE : xmcpyH SEGS t Mr dstw srcw n bs (Z_to_bv 64 ret) spw (Z_to_bv 8 1)).
    { split.
      - lia. - exact MC. - lia. - exact K1. - exact K2. - vm_compute; discriminate. - exact K3.
      - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); (nodisj; lia).
      - exact STK. - rewrite Hsrc; exact SSTK. - rewrite Hdst; exact DSTK. - exact RET. }
    clear DSTK SSTK.
    (* [comment removed for export] *)
    set (raw := Z_to_bv 64 ret) in *.
    assert (FR : hid_off Hd (U spw - 2240) 2240) by (hoz NZ).
    assert (DR : hid_off Hd (U dstw) n) by (apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NDST; lia]).
    assert (CM1_r : XC1 Mr raw spw R = mrestrict Hd (XC1 M raw spw R)).
    { clear - FR CP2 CPlo CPhi CR. (lazymatch goal with |- ?G => let G' := eval unfold Mr, XC1, xmc_frame in G in change_no_check G' end).
      rewrite !(wbytes_mrestrict Hd) by
        (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
         first [hs_arith_goal; rewrite at_u by (nodisj; lia); (nodisj; lia) | rewrite at_u by (nodisj; lia); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]).
      reflexivity. }
    assert (POST_r : forall X, xmcpy_post dstw bs (mrestrict Hd X) = mrestrict Hd (xmcpy_post dstw bs X)).
    { intros X. (lazymatch goal with |- ?G => let G' := eval unfold xmcpy_post in G in change_no_check G' end). apply (wbytes_mrestrict_at Hd _ X dstw n); [exact LBS | lia | lia | exact DR]. }
    (* [comment removed for export] *)
    assert (SEGnone : forall a : word, CEIL <= U a -> find_segment SEGS (U a) 1 = None).
    { intros a Ha. destruct (find_segment SEGS (U a) 1) eqn:E; [|reflexivity]. exfalso.
      pose proof (SEGS_hull (U a) ltac:(rewrite E; discriminate)). lia. }
    assert (FIN : forall (M' : mem) (r : bvmap 5 word),
      msteps SEGS (mkst R (xc_base t) Mr (seg_rom SEGS)) (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) ->
      getr r 10 = dstw -> (forall x, In x amset_saved -> getr r x = getr R x) ->
      (forall a : word, M' a <> M a -> dst <= U a < dst + n \/ sp - 2304 <= U a < sp) ->
      (forall i, 0 <= i < n -> M' (Z_to_bv 64 (dst + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
      mem_grows M M' ->
      katD SEGS (cfg fx R (ia_memcpy_icpt IA) M mdl) (mem_post SEGS FXOK AAINVH h R M mdl Lc FF B C K ret sp dst n (fun i => Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))))).
    { intros M' r RUN A10 SAVED CHG BYTES GR.
      assert (NH' : forall a : word, Hd a = true -> M' a = M a).
      { intros a Ha. destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso.
        pose proof (u64_range a) as Har. destruct (CHG a NE) as [X|X].
        - rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NDST (U a) X) in Ha. discriminate Ha.
        - rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NZ (U a)) in Ha; [discriminate Ha | lia | right; lia]. }
      (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.cfg in G in change_no_check G' end). rewrite <- T_entry.
      apply (katD_msteps_acct SEGS Hd HOFF SEGS_wx AA (mkst R (xc_base t) M (seg_rom SEGS))
               (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) mdl _ (lazy_cover_HL mdl AA) Awf MI HH).
      - rewrite restrict_mkst'. exact RUN.
      - intros mdl' MI' SBM HC. rewrite unrestrict_mkst. (lazymatch goal with |- ?G => let G' := eval cbn [RiscvSemantics.ms_mem mkst] in G in change_no_check G' end).
        rewrite (munrestrict_mrestrict_same Hd M M' NH').
        assert (SCR : scratch_ok SEGS M' sp MSTK_M).
        { intros a Ha. unfold MSTK_M in Ha. split.
          - apply GR. apply (store_ok1_defined SEGS M a); [apply SEGnone; lia | apply CPstk; lia].
          - eapply store_ok_mono; [exact GR | apply CPstk; lia]. }
        apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold mem_post in G in change_no_check G' end). exists fx, r, M', mdl'.
        split; [reflexivity|]. split; [exact HFX|].
        split; [apply regs_kept_of_list; exact SAVED|].
        split; [rewrite A10; exact Hdst|].
        split; [exact BYTES|].
        split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); exact (CHG a Ha)|].
        split; [exact SCR|].
        split; [|exact SBM].
        destruct DO as [WOK OWN].
        apply (aap_frame _ _ _ _ HPh W Lc FF B C K M M' mdl' WOK (PRES mdl' MI' SBM)).
        intros a Ha. destruct (CHG a Ha) as [X|X].
        * split; [apply OWN; exact X|].
          replace a with (Z_to_bv 64 (dst + (U a - dst))) by (apply bv_eq; rewrite u_Z2bv; lia).
          rewrite (BYTES (U a - dst)) by lia. discriminate.
        * split; [right; right; left; lia|]. apply (proj1 (SCR a ltac:((lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); lia))). }
    (* [comment removed for export] *)
    assert (HSP' : (0x10007fff8000 + 2304 <= U spw)%Z /\ (U spw + 16 <= 2 ^ 47)%Z) by lia.
    assert (R1' : getr R 1 = raw) by exact CP1.
    assert (BY : forall X i, 0 <= i < n -> xmcpy_post dstw bs X (Z_to_bv 64 (dst + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
    { intros X i Hi. (lazymatch goal with |- ?G => let G' := eval unfold xmcpy_post in G in change_no_check G' end). rewrite (AsRtIMemmove.wbytes_get_g) by (rewrite LBS; lia).
      rewrite LBS, u_Z2bv by lia.
      replace (inrng (U dstw) (Z.of_nat (Z.to_nat n)) (dst + i)) with true by (symmetry; apply inrng_true; lia).
      f_equal. f_equal. lia. }
    assert (RDi : forall i, 0 <= i < n -> AsIface3.rd1 SEGS M (src + i) = Some [nth (Z.to_nat i) bs (Z_to_bv 8 0)]).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.rd1 in G in change_no_check G' end).
      replace (Z_to_bv 64 (src + i)) with (srcw + nat_to_word (Z.to_nat i))%bv
        by (rewrite at_nat; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); apply bv_eq; rewrite !Z_to_bv_unsigned; f_equal; lia).
      apply (rdn_nth SEGS M (Z.to_nat n) srcw bs (Z.to_nat i) BS). lia. }
    assert (OUT1 : forall a : word, ~ (dst <= U a < dst + n) -> ~ (sp - 2304 <= U a < sp) ->
                   xmcpy_post dstw bs (XC1 M raw spw R) a = M a).
    { intros a N1 N2. (lazymatch goal with |- ?G => let G' := eval unfold xmcpy_post in G in change_no_check G' end). pose proof (u64_range a).
      rewrite wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite LBS; lia | rewrite LBS; lia].
      apply (XC1_agree dstw M raw spw R HSP'). lia. }
    assert (GR1 : mem_grows M (xmcpy_post dstw bs (XC1 M raw spw R))).
    { (lazymatch goal with |- ?G => let G' := eval unfold xmcpy_post in G in change_no_check G' end). eapply mem_grows_trans; [apply XC1_grows | apply wbytes_grows]. }
    pose proof (fun z => aap_shdef _ _ _ _ HPh _ _ _ _ _ _ _ z AI) as SHD.
    assert (SH8 : sh_lo AS_HEAPLO mod 8 = 0 /\ AS_HEAPLO mod 8 = 0 /\ sh_lo AS_HEAPLO = 2201439137792) by (repeat split; reflexivity).
    (* [comment removed for export] *)
    assert (GRAN : forall b g, 0 <= b -> 1 <= n -> Sh b <= g < Sh (b + n - 1) + 1 -> exists z, b <= z < b + n /\ sh_lo z = g).
    { intros b g Hb Hn1 Hg. unfold Sh, sh_lo, SB in *.
      pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
      pose proof (Z.div_mod (b + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)).
      destruct (Z_lt_le_dec g (Sh (b + n - 1))) as [L|Ge]; unfold Sh in *.
      - exists (8 * (g - 2147450880) + 7). split; [(nodisj; lia)|].
        replace (8 * (g - 2147450880) + 7) with ((g - 2147450880) * 8 + 7) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small 7 8) by lia. lia.
      - exists (b + n - 1). split; [lia|]. lia. }
    (* [comment removed for export] *)
    assert (RD1 : forall b, (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
                  forall (a : word) bs0, rdn SEGS M a 1%nat = Some bs0 -> (exists z, b <= z < b + n /\ sh_lo z = U a) ->
                  rdn SEGS Mr a 1%nat = Some bs0).
    { intros b NSHb a bs0 Hr (z & Hz & Ez). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). pose proof (u64_range a). rewrite rdn_mrestrict; [exact Hr | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      intros x Hx. cbn in Hx. replace x with a by (apply bv_eq; lia). apply (NSHb z Hz a). rewrite Ez. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    assert (RD8 : forall b, (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
                  ((0x10007fff8000 <= b /\ b + n < 2 ^ 47) \/ (0 <= b /\ b + n <= 0x7fff7fff)) ->
                  forall (w : Z) (z : Z), b <= z < b + n -> w = down8 (sh_lo z) ->
                  exists bs0, rdn SEGS Mr (Z_to_bv 64 w) 8%nat = Some bs0).
    { intros b NSHb RNG w z Hz Ew. pose proof (sh_lo_lt47 z ltac:(lia)) as SZ. pose proof (down8_le (sh_lo z) ltac:(unfold SB in SZ; lia)) as [DL DM].
      assert (LS8 : sh_lo SB = 2415882240 /\ sh_lo SB mod 8 = 0) by (split; reflexivity).
      assert (DEF8 : forall i, w <= i < w + 8 -> M (Z_to_bv 64 i) <> None).
      { destruct RNG as [[RH _] | [_ RL]].
        - assert (LO : sh_lo AS_HEAPLO <= w).
          { subst w. apply down8_ge; [exact (proj1 SH8)|]. apply sh_lo_mono. (lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia. }
          assert (HI : w + 8 <= AS_HEAPLO).
          { subst w. apply down8_lt_top; [exact (proj1 (proj2 SH8))|]. unfold AS_HEAPLO, SB in *. lia. }
          rewrite (proj2 (proj2 SH8)) in LO. unfold AS_HEAPLO in HI.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). right. (lazymatch goal with |- ?G => let G' := eval unfold AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). lia.
        - assert (LO : SB <= w).
          { subst w. apply down8_ge; [reflexivity|]. unfold SB in *. lia. }
          assert (HI : w + 8 <= sh_lo SB).
          { subst w. apply down8_lt_top; [exact (proj2 LS8)|]. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end).
            pose proof (Z.div_le_mono z 2147450879 8 ltac:((nodisj; lia)) ltac:((nodisj; lia))). change (2147450879 / 8) with 268431359 in *. change (2147450880 / 8) with 268431360 in *. lia. }
          rewrite (proj1 LS8) in HI. unfold SB in LO.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). left. (lazymatch goal with |- ?G => let G' := eval unfold AS_LO, AS_GAPLO in G in change_no_check G' end). (nodisj; lia). }
      unfold SB in SZ.
      destruct (rdn_defined_ex SEGS M (Z_to_bv 64 w) 8) as (bs0 & Hbs & _).
      { intros i Hi. rewrite u_Z2bv in Hi by (nodisj; lia). apply DEF8. cbn in Hi. lia. }
      { rewrite u_Z2bv by (nodisj; lia). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
      exists bs0. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hbs | rewrite u_Z2bv by (nodisj; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (nodisj; lia) |].
      rewrite u_Z2bv by lia. intros x Hx. cbn in Hx. apply (NSHb z Hz x).
      apply (page_base_word8 w); [rewrite Ew; exact DM | (nodisj; lia) | (nodisj; lia) | rewrite u_Z2bv by (nodisj; lia); (nodisj; lia)]. }
    (* [comment removed for export] *)
    assert (QCH : forall (b : Z) (bw : word), U bw = b -> accessible M b n -> 1 <= n <= 64 ->
              (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
              ((0x10007fff8000 <= b /\ b + n < 2 ^ 47) \/ (0 <= b /\ b + n <= 0x7fff7fff)) ->
              exists w0 w1 s1, qc1H SEGS Mr bw n (mt_g_shoff (rt_m2s (xc_rip t))) (mt_p_shoff (rt_m2s (xc_rip t))) w0 w1 s1).
    { intros b bw Hb ACC Hs NSHb RNG.
      destruct (acc_last SEGS M b n ACC ltac:(lia)) as (s1 & Rs1 & Hs1).
      destruct (RD8 b NSHb RNG (down8 (sh_lo b)) b ltac:(lia) eq_refl) as (w0 & Rw0).
      destruct (RD8 b NSHb RNG (down8 (sh_lo (b + n - 1))) (b + n - 1) ltac:(lia) eq_refl) as (w1 & Rw1).
      exists w0, w1, s1. split; rewrite ?Hb.
      - lia. - lia. - exact K4. - exact K11. - lia.
      - rewrite Sh_is_sh_lo. exact Rw0.
      - rewrite Sh_is_sh_lo. exact Rw1.
      - apply (RD1 b NSHb _ _ Rs1). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (b + n - 1) ltac:(lia)). pose proof (sh_lo_mono b (b + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - exact Hs1.
      - intros a Ha. apply (RD1 b NSHb a _ (acc_zero SEGS M b n ACC ltac:(lia) a Ha)). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo in Ha |- *. lia. }
    (* [comment removed for export] *)
    assert (RGH : forall (b : Z) (bw : word), U bw = b -> accessible M b n -> 65 <= n ->
              (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
              ((0x10007fff8000 <= b /\ b + n < 2 ^ 47) \/ (0 <= b /\ b + n <= 0x7fff7fff)) ->
              exists s0b s1b : byte,
                rdn SEGS Mr (Z_to_bv 64 (Sh (U bw))) 1 = Some [s0b] /\ (U s0b = 0 \/ U bw mod 8 < U s0b < 128)
                /\ rdn SEGS Mr (Z_to_bv 64 (Sh (U bw + n - 1))) 1 = Some [s1b] /\ (U s1b = 0 \/ (U bw + n - 1) mod 8 < U s1b < 128)
                /\ (forall a : word, Sh (up8 (U bw)) <= U a < Sh (down8 (U bw + n)) -> rdn SEGS Mr a 1 = Some [Z_to_bv 8 0])).
    { intros b bw Hb ACC Hbg NSHb RNG. rewrite Hb.
      destruct (acc_first SEGS M b n ACC ltac:(lia)) as (s0b & Rs0 & Hs0).
      destruct (acc_last SEGS M b n ACC ltac:(lia)) as (s1b & Rs1 & Hs1).
      exists s0b, s1b. repeat split.
      - apply (RD1 b NSHb _ _ Rs0). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 b ltac:(lia)). pose proof (sh_lo_mono b (b + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - exact Hs0.
      - apply (RD1 b NSHb _ _ Rs1). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (b + n - 1) ltac:(lia)). pose proof (sh_lo_mono b (b + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - exact Hs1.
      - intros a Ha. apply (RD1 b NSHb a _ (acc_zero_mid SEGS M b n ACC ltac:(lia) a Ha)). apply GRAN; [lia|lia|].
        unfold Sh, up8, down8 in Ha |- *. clear - Ha.
        pose proof (Z.div_mod (b + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + 7) 8 ltac:(lia)).
        pose proof (Z.div_mod (b + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n) 8 ltac:(lia)).
        rewrite !Z.div_mul in Ha by lia.
        pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
        pose proof (Z.div_mod (b + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)). (nodisj; lia). }
    (* [comment removed for export] *)
    destruct (Z.eq_dec n 0) as [N0 | Nn0].
    { (* [comment removed for export] *)
      destruct (asan_memcpy_icpt_zero SEGS t (TOK fx) Mr (seg_rom SEGS) dstw srcw raw spw n bs (Z_to_bv 8 1) R PRE N0 R1' eq_refl eq_refl eq_refl R12)
        as (r & RUN & A10 & SAVED).
      rewrite CM1_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. apply OUT1; assumption.
      - intros i Hi. apply BY. exact Hi.
      - exact GR1. }
    destruct (Z_le_gt_dec n 64) as [Ns | Nb].
    { (* [comment removed for export] *)
      destruct (QCH src srcw Hsrc ACCs ltac:(lia) NSHs RNGs) as (w0s & w1s & s1s & QS).
      destruct (QCH dst dstw Hdst ACCd ltac:(lia) NSHd RNGd) as (w0d & w1d & s1d & QD).
      destruct (asan_memcpy_icpt_small SEGS t (TOK fx) Mr (seg_rom SEGS) dstw srcw raw spw n bs (Z_to_bv 8 1) R w0s w1s s1s w0d w1d s1d
                 PRE ltac:(lia) QS QD R1' eq_refl eq_refl eq_refl R12)
        as (r & RUN & A10 & SAVED).
      rewrite CM1_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. apply OUT1; assumption.
      - intros i Hi. apply BY. exact Hi.
      - exact GR1. }
    { (* [comment removed for export] *)
      assert (CH : forall bw : word, (0x10007fff8000 <= U bw \/ U bw <= 0x7fff7fff) -> U bw <= 0x7fffffffffff ->
                 m2sH SEGS (rt_m2s (xc_rip t)) Mr bw (Z_to_bv 64 0)).
      { intros bw H1 H2. split.
        - exact K4. - exact K11. - exact K5. - exact K6. - exact K7. - exact K8. - exact K9. - exact K10.
        - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); lia.
        - exact H1. - exact H2. }
      assert (Hn43 : 65 <= n <= 2 ^ 43) by (unfold NMAX in *; lia).
      assert (RUNx : exists r,
        msteps SEGS (mkst R (xc_base t) Mr (seg_rom SEGS))
                    (mkst r raw (xmcpy_post dstw bs (XC3 (xc_base t) (xc_rip t) Mr dstw srcw raw spw n R)) (seg_rom SEGS))
        /\ getr r 10 = dstw /\ (forall x, In x amset_saved -> getr r x = getr R x)).
      { pose proof (CH srcw ltac:(lia) ltac:(lia)) as CHs. pose proof (CH dstw ltac:(lia) ltac:(lia)) as CHd.
        assert (Rgs : (0x10007fff8000 <= U srcw /\ U srcw + n + 1 <= 0x800000000000) \/ U srcw + n <= 0x7fff7fff) by lia.
        assert (Rgd : (0x10007fff8000 <= U dstw /\ U dstw + n + 1 <= 0x800000000000) \/ U dstw + n <= 0x7fff7fff) by lia.
        destruct (RGH src srcw Hsrc ACCs ltac:(lia) NSHs RNGs) as (s0s & s1s & Rs0s & Hs0s & Rs1s & Hs1s & Rzs).
        destruct (RGH dst dstw Hdst ACCd ltac:(lia) NSHd RNGd) as (s0d & s1d & Rs0d & Hs0d & Rs1d & Hs1d & Rzd).
        exact (asan_memcpy_icpt_big SEGS t (TOK fx) Mr (seg_rom SEGS) dstw srcw raw spw n bs (Z_to_bv 8 1) R s0s s1s s0d s1d (Z_to_bv 64 0)
                 PRE Hn43 CHs CHd Rgs Rgd Rs0s Hs0s Rs1s Hs1s Rzs Rs0d Hs0d Rs1d Hs1d Rzd R1' eq_refl eq_refl eq_refl R12). }
      destruct RUNx as (r & RUN & A10 & SAVED).
      (* [comment removed for export] *)
      assert (CM3_r : XC3 (xc_base t) (xc_rip t) Mr dstw srcw raw spw n R = mrestrict Hd (XC3 (xc_base t) (xc_rip t) M dstw srcw raw spw n R)).
      { clear - FR CP2 CPlo CPhi CR CM1_r POST_r. (lazymatch goal with |- ?G => let G' := eval unfold XC3, XC2 in G in change_no_check G' end). rewrite CM1_r. (lazymatch goal with |- ?G => let G' := eval unfold rip_mem, ps_frame in G in change_no_check G' end).
        pose proof (u64_range spw).
        repeat (lazymatch goal with
                | |- context [if Z.ltb ?a ?b then _ else _] => destruct (Z.ltb a b)
                end);
        rewrite !(wbytes_mrestrict Hd) by
          (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
           first [hs_arith_goal; rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); (nodisj; lia)
                 | rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]);
        reflexivity. }
      rewrite CM3_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      + clear RNGd RNGs QCH RGH RD8 RD1 GRAN CH FIN.
        intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. (lazymatch goal with |- ?G => let G' := eval unfold xmcpy_post in G in change_no_check G' end). pose proof (u64_range a).
        rewrite wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite LBS; lia | rewrite LBS; lia].
        apply (XC3_agree (xc_base t) (xc_rip t) M dstw srcw raw spw n R HSP'). lia.
      + intros i Hi. apply BY. exact Hi.
      + (lazymatch goal with |- ?G => let G' := eval unfold xmcpy_post in G in change_no_check G' end). eapply mem_grows_trans; [apply XC3_grows | apply wbytes_grows]. }
  Qed.

End CONTRACT.
End AsIcptXMemcpy.
Module AsRtXMemmove.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Definition xmmove_words : list (option (bv 32)) :=
  [
   Some W_6d4a0; Some W_6d4a4; Some W_6d4a8; Some W_6d4ac; Some W_6d4b0; Some W_6d4b4; Some W_6d4b8; Some W_6d4bc;
   Some W_6d4c0; Some W_6d4c4; Some W_6d4c8; Some W_6d4cc; None; None; Some W_6d4d8; Some W_6d4dc;
   Some W_6d4e0; Some W_6d4e4; Some W_6d4e8; Some W_6d4ec; Some W_6d4f0; Some W_6d4f4; Some W_6d4f8; None;
   None; Some W_6d504; Some W_6d508; Some W_6d50c; Some W_6d510; Some W_6d514; Some W_6d518; Some W_6d51c;
   Some W_6d520; Some W_6d524; Some W_6d528; Some W_6d52c; Some W_6d530; Some W_6d534; Some W_6d538; Some W_6d53c;
   Some W_6d540; Some W_6d544; None; None; Some W_6d550; Some W_6d554; Some W_6d558; Some W_6d55c;
   Some W_6d560; Some W_6d564; Some W_6d568; Some W_6d56c; Some W_6d570; Some W_6d574; Some W_6d578; Some W_6d57c;
   Some W_6d580; Some W_6d584; Some W_6d588; Some W_6d58c; Some W_6d590; Some W_6d594; Some W_6d598; Some W_6d59c;
   Some W_6d5a0; Some W_6d5a4; Some W_6d5a8; Some W_6d5ac; Some W_6d5b0; Some W_6d5b4; Some W_6d5b8; Some W_6d5bc;
   Some W_6d5c0; Some W_6d5c4; Some W_6d5c8; Some W_6d5cc; Some W_6d5d0; Some W_6d5d4; Some W_6d5d8; Some W_6d5dc;
   Some W_6d5e0; Some W_6d5e4; Some W_6d5e8; None; None; Some W_6d5f4; Some W_6d5f8; Some W_6d5fc;
   Some W_6d600; Some W_6d604; Some W_6d608; Some W_6d60c; Some W_6d610; Some W_6d614; Some W_6d618; Some W_6d61c;
   Some W_6d620; Some W_6d624; Some W_6d628; Some W_6d62c; Some W_6d630; Some W_6d634; Some W_6d638; Some W_6d63c;
   Some W_6d640; Some W_6d644; Some W_6d648; Some W_6d64c; Some W_6d650; Some W_6d654; Some W_6d658; Some W_6d65c;
   Some W_6d660; Some W_6d664; Some W_6d668; Some W_6d66c; Some W_6d670; Some W_6d674; Some W_6d678; None;
   None; Some W_6d684; Some W_6d688; Some W_6d68c; Some W_6d690; Some W_6d694; Some W_6d698; Some W_6d69c;
   Some W_6d6a0; Some W_6d6a4; Some W_6d6a8; Some W_6d6ac; Some W_6d6b0; Some W_6d6b4; Some W_6d6b8; Some W_6d6bc;
   Some W_6d6c0; Some W_6d6c4; Some W_6d6c8; Some W_6d6cc; Some W_6d6d0; Some W_6d6d4; Some W_6d6d8; Some W_6d6dc;
   Some W_6d6e0; Some W_6d6e4; Some W_6d6e8; Some W_6d6ec; Some W_6d6f0; Some W_6d6f4; Some W_6d6f8; Some W_6d6fc;
   Some W_6d700; Some W_6d704; Some W_6d708; Some W_6d70c; Some W_6d710; Some W_6d714; Some W_6d718; Some W_6d71c;
   Some W_6d720; Some W_6d724; Some W_6d728; Some W_6d72c; Some W_6d730; Some W_6d734; None; Some W_6d73c;
   Some W_6d740; Some W_6d744; Some W_6d748; Some W_6d74c; Some W_6d750; Some W_6d754; Some W_6d758; Some W_6d75c;
   Some W_6d760; Some W_6d764; Some W_6d768; Some W_6d76c; Some W_6d770; Some W_6d774; Some W_6d778; Some W_6d77c;
   Some W_6d780; None; None; Some W_6d78c; Some W_6d790; Some W_6d794; Some W_6d798; Some W_6d79c;
   Some W_6d7a0; Some W_6d7a4; Some W_6d7a8; Some W_6d7ac; Some W_6d7b0; Some W_6d7b4; Some W_6d7b8; Some W_6d7bc;
   Some W_6d7c0; Some W_6d7c4; Some W_6d7c8; Some W_6d7cc; Some W_6d7d0; Some W_6d7d4; Some W_6d7d8; Some W_6d7dc;
   Some W_6d7e0; Some W_6d7e4; Some W_6d7e8; Some W_6d7ec; Some W_6d7f0; Some W_6d7f4; Some W_6d7f8; Some W_6d7fc;
   Some W_6d800; Some W_6d804; Some W_6d808; Some W_6d80c; Some W_6d810; Some W_6d814; Some W_6d818; Some W_6d81c;
   Some W_6d820; Some W_6d824; Some W_6d828; Some W_6d82c; Some W_6d830; None; Some W_6d838; Some W_6d83c;
   Some W_6d840; Some W_6d844; Some W_6d848; Some W_6d84c; Some W_6d850; Some W_6d854; Some W_6d858; Some W_6d85c;
   Some W_6d860; Some W_6d864; Some W_6d868; Some W_6d86c; Some W_6d870; Some W_6d874; Some W_6d878; Some W_6d87c;
   None; None; Some W_6d888; Some W_6d88c; Some W_6d890; Some W_6d894; Some W_6d898; Some W_6d89c;
   Some W_6d8a0; Some W_6d8a4; Some W_6d8a8; Some W_6d8ac; Some W_6d8b0; Some W_6d8b4; Some W_6d8b8; Some W_6d8bc;
   Some W_6d8c0; Some W_6d8c4; Some W_6d8c8; Some W_6d8cc; Some W_6d8d0; Some W_6d8d4; None; None;
   Some W_6d8e0; Some W_6d8e4; Some W_6d8e8; Some W_6d8ec; Some W_6d8f0; Some W_6d8f4; Some W_6d8f8; Some W_6d8fc;
   Some W_6d900; Some W_6d904; Some W_6d908; Some W_6d90c; Some W_6d910; Some W_6d914; Some W_6d918; Some W_6d91c;
   None; None; Some W_6d928; Some W_6d92c; Some W_6d930; Some W_6d934; Some W_6d938; Some W_6d93c;
   Some W_6d940; Some W_6d944; Some W_6d948; Some W_6d94c; Some W_6d950; Some W_6d954; Some W_6d958; Some W_6d95c
  ]%list.


(* [comment removed for export] *)
Record xmmove_tab : Type := XMMT {
  ym_base : word;          (* [comment removed for export] *)
  ym_rip : rip_tab;        (* [comment removed for export] *)
  ym_imm : word;           (* [comment removed for export] *)
  ym_g_flag : Z; ym_p_flag : Z }.   (* [comment removed for export] *)

Record xmmove_tab_ok (segs : list Segment) (t : xmmove_tab) : Prop := XMMTOK {
  yto_code : code_ato segs (ym_base t) 0 xmmove_words;
  yto_rip : rip_tab_ok segs (ym_rip t);
  yto_rip_base : rt_base (ym_rip t) = at_ (ym_base t) 10992;
  yto_imm : code_at segs (ym_imm t) 0 imemmove_words;
  yto_imm_base : ym_imm t = at_ (ym_base t) 76344;
  yto_qcf1 : code_ato segs (at_ (ym_base t) 92) 0 (qc1f_words 11);
  yto_qcs1 : code_ato segs (at_ (ym_base t) 564) 0 qc1s_words;
  yto_qcf2 : code_ato segs (at_ (ym_base t) 168) 0 (qc1f_words 10);
  yto_qcs2 : code_ato segs (at_ (ym_base t) 820) 0 qc1s_words;
  yto_g48 : gload segs (ym_base t) 48 13 (ym_g_flag t);
  yto_g92 : gload segs (at_ (ym_base t) 92) 0 13 (mt_g_shoff (rt_m2s (ym_rip t)));
  yto_g168 : gload segs (at_ (ym_base t) 168) 0 13 (mt_g_shoff (rt_m2s (ym_rip t)));
  yto_b148 : gbnez segs (at_ (ym_base t) 148) 16 (at_ (ym_base t) 564);
  yto_b612 : gbeqz segs (at_ (ym_base t) 612) 13 (at_ (ym_base t) 152);
  yto_b224 : gbnez segs (at_ (ym_base t) 224) 16 (at_ (ym_base t) 820);
  yto_b868 : gbeqz segs (at_ (ym_base t) 868) 13 (at_ (ym_base t) 228);
  yto_base : (U (ym_base t) mod 2 = 0)%Z /\ (U (ym_base t) + 100000 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Definition xmm_frame (mem : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (word_to_le_bytes 8 ra))
    (at_ sp (-16)) (word_to_le_bytes 8 s0))
    (at_ sp (-24)) (word_to_le_bytes 8 s1))
    (at_ sp (-32)) (word_to_le_bytes 8 s2))
    (at_ sp (-40)) (word_to_le_bytes 8 s3))
    (at_ sp (-48)) (word_to_le_bytes 8 s4))
    (at_ sp (-56)) (word_to_le_bytes 8 s5))
    (at_ sp (-64)) (word_to_le_bytes 8 s6))
    (at_ sp (-72)) (word_to_le_bytes 8 s7).

Section XMMOVE.
  Variable segs : list Segment.
  Variable base : word.
  Variable rt : rip_tab.
  Variable imm : word.
  Variables g_flag p_flag : Z.
  #[local] Abbreviation g_shoff := (mt_g_shoff (rt_m2s rt)).
  #[local] Abbreviation p_shoff := (mt_p_shoff (rt_m2s rt)).
  Hypothesis HCODE : code_ato segs base 0 xmmove_words.
  Hypothesis RTOK : rip_tab_ok segs rt.
  Hypothesis RTB : rt_base rt = at_ base 10992.
  Hypothesis IMC : code_at segs imm 0 imemmove_words.
  Hypothesis IMB : imm = at_ base 76344.
  Hypothesis QCF1 : code_ato segs (at_ base 92) 0 (qc1f_words 11).
  Hypothesis QCS1 : code_ato segs (at_ base 564) 0 qc1s_words.
  Hypothesis QCF2 : code_ato segs (at_ base 168) 0 (qc1f_words 10).
  Hypothesis QCS2 : code_ato segs (at_ base 820) 0 qc1s_words.
  Hypothesis G48 : gload segs base 48 13 g_flag.
  Hypothesis G92 : gload segs (at_ base 92) 0 13 g_shoff.
  Hypothesis G168 : gload segs (at_ base 168) 0 13 g_shoff.
  Hypothesis B148 : gbnez segs (at_ base 148) 16 (at_ base 564).
  Hypothesis B612 : gbeqz segs (at_ base 612) 13 (at_ base 152).
  Hypothesis B224 : gbnez segs (at_ base 224) 16 (at_ base 820).
  Hypothesis B868 : gbeqz segs (at_ base 868) 13 (at_ base 228).
  Hypothesis Hbase : (U base mod 2 = 0)%Z /\ (U base + 100000 < 2 ^ 64)%Z.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_6d4a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_6d4a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_6d4a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_6d4ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_6d4b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_6d4b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_6d4b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_6d4bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_6d4c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_6d4c4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_6d4c8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 10 _ HCODE eq_refl). Qed.
  Lemma Fo44 : fetch_word segs (at_ base 44) = Some W_6d4cc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 11 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_6d4d8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 14 _ HCODE eq_refl). Qed.
  Lemma Fo60 : fetch_word segs (at_ base 60) = Some W_6d4dc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 15 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_6d4e0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_6d4e4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_6d4e8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_6d4ec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_6d4f0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo84 : fetch_word segs (at_ base 84) = Some W_6d4f4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 21 _ HCODE eq_refl). Qed.
  Lemma Fo88 : fetch_word segs (at_ base 88) = Some W_6d4f8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 22 _ HCODE eq_refl). Qed.













  Lemma Fo152 : fetch_word segs (at_ base 152) = Some W_6d538.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 38 _ HCODE eq_refl). Qed.
  Lemma Fo156 : fetch_word segs (at_ base 156) = Some W_6d53c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 39 _ HCODE eq_refl). Qed.
  Lemma Fo160 : fetch_word segs (at_ base 160) = Some W_6d540.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 40 _ HCODE eq_refl). Qed.
  Lemma Fo164 : fetch_word segs (at_ base 164) = Some W_6d544.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 41 _ HCODE eq_refl). Qed.













  Lemma Fo228 : fetch_word segs (at_ base 228) = Some W_6d584.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 57 _ HCODE eq_refl). Qed.
  Lemma Fo232 : fetch_word segs (at_ base 232) = Some W_6d588.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 58 _ HCODE eq_refl). Qed.
  Lemma Fo236 : fetch_word segs (at_ base 236) = Some W_6d58c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 59 _ HCODE eq_refl). Qed.
  Lemma Fo240 : fetch_word segs (at_ base 240) = Some W_6d590.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 60 _ HCODE eq_refl). Qed.
  Lemma Fo244 : fetch_word segs (at_ base 244) = Some W_6d594.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 61 _ HCODE eq_refl). Qed.
  Lemma Fo248 : fetch_word segs (at_ base 248) = Some W_6d598.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 62 _ HCODE eq_refl). Qed.
  Lemma Fo252 : fetch_word segs (at_ base 252) = Some W_6d59c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 63 _ HCODE eq_refl). Qed.
  Lemma Fo256 : fetch_word segs (at_ base 256) = Some W_6d5a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 64 _ HCODE eq_refl). Qed.
  Lemma Fo260 : fetch_word segs (at_ base 260) = Some W_6d5a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 65 _ HCODE eq_refl). Qed.
  Lemma Fo264 : fetch_word segs (at_ base 264) = Some W_6d5a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 66 _ HCODE eq_refl). Qed.
  Lemma Fo268 : fetch_word segs (at_ base 268) = Some W_6d5ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 67 _ HCODE eq_refl). Qed.
  Lemma Fo272 : fetch_word segs (at_ base 272) = Some W_6d5b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 68 _ HCODE eq_refl). Qed.
  Lemma Fo276 : fetch_word segs (at_ base 276) = Some W_6d5b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 69 _ HCODE eq_refl). Qed.
































  Lemma Fo416 : fetch_word segs (at_ base 416) = Some W_6d640.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 104 _ HCODE eq_refl). Qed.
  Lemma Fo420 : fetch_word segs (at_ base 420) = Some W_6d644.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 105 _ HCODE eq_refl). Qed.































  Lemma Fo556 : fetch_word segs (at_ base 556) = Some W_6d6cc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 139 _ HCODE eq_refl). Qed.
  Lemma Fo560 : fetch_word segs (at_ base 560) = Some W_6d6d0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 140 _ HCODE eq_refl). Qed.













  Lemma Fo616 : fetch_word segs (at_ base 616) = Some W_6d708.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 154 _ HCODE eq_refl). Qed.
  Lemma Fo620 : fetch_word segs (at_ base 620) = Some W_6d70c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 155 _ HCODE eq_refl). Qed.
  Lemma Fo624 : fetch_word segs (at_ base 624) = Some W_6d710.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 156 _ HCODE eq_refl). Qed.
  Lemma Fo628 : fetch_word segs (at_ base 628) = Some W_6d714.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 157 _ HCODE eq_refl). Qed.
  Lemma Fo632 : fetch_word segs (at_ base 632) = Some W_6d718.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 158 _ HCODE eq_refl). Qed.
  Lemma Fo636 : fetch_word segs (at_ base 636) = Some W_6d71c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 159 _ HCODE eq_refl). Qed.
  Lemma Fo640 : fetch_word segs (at_ base 640) = Some W_6d720.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 160 _ HCODE eq_refl). Qed.
  Lemma Fo644 : fetch_word segs (at_ base 644) = Some W_6d724.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 161 _ HCODE eq_refl). Qed.
  Lemma Fo648 : fetch_word segs (at_ base 648) = Some W_6d728.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 162 _ HCODE eq_refl). Qed.
  Lemma Fo652 : fetch_word segs (at_ base 652) = Some W_6d72c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 163 _ HCODE eq_refl). Qed.
  Lemma Fo656 : fetch_word segs (at_ base 656) = Some W_6d730.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 164 _ HCODE eq_refl). Qed.


















































  Lemma Fo872 : fetch_word segs (at_ base 872) = Some W_6d808.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 218 _ HCODE eq_refl). Qed.
  Lemma Fo876 : fetch_word segs (at_ base 876) = Some W_6d80c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 219 _ HCODE eq_refl). Qed.
  Lemma Fo880 : fetch_word segs (at_ base 880) = Some W_6d810.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 220 _ HCODE eq_refl). Qed.
  Lemma Fo884 : fetch_word segs (at_ base 884) = Some W_6d814.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 221 _ HCODE eq_refl). Qed.
  Lemma Fo888 : fetch_word segs (at_ base 888) = Some W_6d818.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 222 _ HCODE eq_refl). Qed.
  Lemma Fo892 : fetch_word segs (at_ base 892) = Some W_6d81c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 223 _ HCODE eq_refl). Qed.
  Lemma Fo896 : fetch_word segs (at_ base 896) = Some W_6d820.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 224 _ HCODE eq_refl). Qed.
  Lemma Fo900 : fetch_word segs (at_ base 900) = Some W_6d824.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 225 _ HCODE eq_refl). Qed.
  Lemma Fo904 : fetch_word segs (at_ base 904) = Some W_6d828.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 226 _ HCODE eq_refl). Qed.
  Lemma Fo908 : fetch_word segs (at_ base 908) = Some W_6d82c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmmove_words 227 _ HCODE eq_refl). Qed.






































































  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables dst src ra sp : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable fl : byte.
  Variable regs : bvmap 5 word.
  Hypothesis Hsp : (0x10007fff8000 + 2304 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  (* [comment removed for export] *)
  Definition XD1 : word -> option byte :=
    xmm_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23).
  (* [comment removed for export] *)
  Definition XD2 : word -> option byte :=
    rip_mem rt XD1 (at_ sp (-2144)) (at_ base 640) sp (Z_to_bv 64 n) (getr regs 18) (getr regs 19) (Z_to_bv 64 (n - 65))
            (at_ sp (-2144)) src (Z_to_bv 64 n).
  Definition XD3 : word -> option byte :=
    rip_mem rt XD2 (at_ sp (-2144)) (at_ base 892) sp dst (Z_to_bv 64 n) (getr regs 19) (Z_to_bv 64 (n - 65))
            (at_ sp (-2144)) dst (Z_to_bv 64 n).
  (* [comment removed for export] *)
  Definition xmmove_post (M : word -> option byte) : word -> option byte := imemmove_result M dst src bs.

  Lemma XD1_out : forall x : word, (U x < U sp - 72 \/ U sp <= U x)%Z -> XD1 x = mem x.
  Proof using Hsp base.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold XD1, xmm_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma XD1_low : forall x : word, (U x < U sp - 2224)%Z -> XD1 x = mem x.
  Proof using Hsp base. intros x Hx. apply XD1_out. lia. Qed.
  Lemma XD1_agree : forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> XD1 x = mem x.
  Proof using Hsp base. intros x Hx. apply XD1_out. lia. Qed.
  Lemma XD1_grows : mem_grows mem XD1.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold XD1, xmm_frame in G in change_no_check G' end).
    repeat (lazymatch goal with
            | |- mem_grows ?a ?a => apply mem_grows_refl
            | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
            end).
  Qed.
  Lemma rip_mem_grows' : forall t M (sp' raX s0 s1 s2 s3 s4 s5 b z : word), mem_grows M (rip_mem t M sp' raX s0 s1 s2 s3 s4 s5 b z).
  Proof using.
    intros. (lazymatch goal with |- ?G => let G' := eval unfold rip_mem, ps_frame in G in change_no_check G' end).
    destruct (Z.ltb _ _);
      repeat (lazymatch goal with
              | |- mem_grows ?a ?a => apply mem_grows_refl
              | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
              end).
  Qed.
  Lemma XD2_agree : forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> XD2 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold XD2 in G in change_no_check G' end). rewrite rip_mem_outside; [apply XD1_agree; exact Hx | rewrite at_u; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  Qed.

  Lemma XD2_grows : mem_grows mem XD2.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold XD2 in G in change_no_check G' end). eapply mem_grows_trans; [apply XD1_grows | apply rip_mem_grows']. Qed.
  Lemma XD3_agree : forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> XD3 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold XD3 in G in change_no_check G' end). rewrite rip_mem_outside; [apply XD2_agree; exact Hx | rewrite at_u; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  Qed.

  Lemma XD3_grows : mem_grows mem XD3.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold XD3 in G in change_no_check G' end). eapply mem_grows_trans; [apply XD2_grows | apply rip_mem_grows']. Qed.

  Lemma rd_o : forall (M : word -> option byte) (B : Z) (a : word) k bs0,
    (forall x : word, (U x < B)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= B)%Z -> (B <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M B a k bs0 HM Ha HB Hr. rewrite <- Hr. apply rdn_ext; [lia|].
    intros x Hx. apply HM. lia.
  Qed.
  Lemma rd_outF : forall (M : word -> option byte) (a : word) k bs0,
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= U sp - 2224 \/ U sp <= U a)%Z -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M a k bs0 HM Ha Hnw Hr. rewrite <- Hr. apply rdn_ext; [exact Hnw|].
    intros x Hx. apply HM. lia.
  Qed.
  Lemma rd_outZ : forall (M : word -> option byte) (c : Z) k bs0,
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) ->
    (0 <= c)%Z -> (c + Z.of_nat k <= U sp - 2224)%Z ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs0 -> rdn segs M (Z_to_bv 64 c) k = Some bs0.
  Proof using Hsp base.
    intros M c k bs0 HM Hc Hk Hr. pose proof (u64_range sp). apply (rd_outF M); try assumption; wd_ulia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MV : moveH segs mem dst src n bs.
  Hypothesis Hends : (U src + n <= 2 ^ 47)%Z /\ (U dst + n <= 2 ^ 47)%Z.
  Hypothesis Rgf : rdn segs mem (Z_to_bv 64 g_flag) 8 = Some (LE8 (Z_to_bv 64 p_flag)).
  Hypothesis Rfl : rdn segs mem (Z_to_bv 64 p_flag) 1 = Some [fl].
  Hypothesis Hfl : U fl <> 0%Z.
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 2224)%Z (g_flag :: p_flag :: m2s_cells (rt_m2s rt)).
  Hypothesis Hstk : store_ok segs mem (at_ sp (-2224)) 2224 = true.
  Hypothesis Hsrc_stk : (n = 0 \/ U src + n <= U sp - 2224 \/ U sp <= U src)%Z.
  Hypothesis Hdst_stk : (n = 0 \/ U dst + n <= U sp - 2224 \/ U sp <= U dst)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis R1 : getr regs 1 = ra.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R10 : getr regs 10 = dst.
  Hypothesis R11 : getr regs 11 = src.
  Hypothesis R12 : getr regs 12 = Z_to_bv 64 n.

  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC; unfold m2s_cells in HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ sp (-2224)) _ 2224);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac addr_n := gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; rewrite ?at_addi; zlit_at;
                 try (progress ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end)); unorm).
  Ltac rd_close LOW Hr :=
    apply (rd_o _ _ _ _ _ LOW);
    [ rewrite ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ]
    | lia
    | first [ exact Hr | rewrite <- Hr; f_equal; apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ] ] ].
  Ltac cldb F D bb LOW Hr :=
    chain_step; [reflexivity
      | eapply step_lbu with (b := bb);
        [exact F | reflexivity | exact D | addr_n; rd_close LOW Hr]
      | step_simpl]; vn.
  Ltac gl G LOW Hr :=
    eapply msteps_trans; [ eapply G; apply (rd_o _ _ _ _ _ LOW); [(lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia | lia | exact Hr] | ]; zlit_at.

  (* [comment removed for export] *)
  #[local] Abbreviation CLX := (fun r : reg => In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dblkA :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 80) XD1 rom)
      /\ getr r 1 = ra /\ getr r 2 = at_ sp (-2144) /\ getr r 8 = sp /\ getr r 10 = dst /\ getr r 11 = src
      /\ getr r 12 = Z_to_bv 64 n /\ getr r 21 = at_ sp (-2144)
      /\ (forall i : reg, In i [9; 18; 19; 20; 22; 23; 24; 25; 26; 27; 3; 4]%list -> getr r i = getr regs i)
      /\ regs_agree CLX regs r.
  Proof using R12 R11 R10 R2 R1 Hstk Hcells Hfl Rfl Rgf Hends MV Hsp fl bs G48 HCODE p_flag g_flag rt.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs. pose proof (u8_range fl) as Hflr.
    destruct MV as [Mn Mlen Msrc Mdst Mnws Mnwd]. cells_split.
    wd_eexists. split.
    - an Fo0 D_6d4a0.                                    (* [comment removed for export] *)
      fsd Fo4 D_6d4a4 (at_ sp (-8));                     (* [comment removed for export] *)
      fsd Fo8 D_6d4a8 (at_ sp (-16));                    (* [comment removed for export] *)
      fsd Fo12 D_6d4ac (at_ sp (-24));
      fsd Fo16 D_6d4b0 (at_ sp (-32));
      fsd Fo20 D_6d4b4 (at_ sp (-40));
      fsd Fo24 D_6d4b8 (at_ sp (-48));
      fsd Fo28 D_6d4bc (at_ sp (-56));
      fsd Fo32 D_6d4c0 (at_ sp (-64));
      fsd Fo36 D_6d4c4 (at_ sp (-72));
      change (wbytes _ _ _) with XD1.
      an Fo40 D_6d4c8.                                   (* [comment removed for export] *)
      an Fo44 D_6d4cc.                                   (* [comment removed for export] *)
      gl G48 XD1_low Rgf.                                (* [comment removed for export] *)
      cldb Fo56 D_6d4d8 fl XD1_low Rfl.                  (* [comment removed for export] *)
      ab_ft Fo60 D_6d4dc ltac:(condz).                 (* [comment removed for export] *)
      av Fo64 D_6d4e0 (Z_to_bv 64 (2 ^ 64 - 1 - U src)) ltac:(apply v_not_word).         (* [comment removed for export] *)
      an Fo68 D_6d4e4; an Fo72 D_6d4e8.                  (* [comment removed for export] *)
      ab_ft Fo76 D_6d4ec ltac:(condz);                 (* [comment removed for export] *)
      wd_refl.
    - post; rewrite ?at_0; try reflexivity;
      [ intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi | ra_solve ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dblkSs : forall M r0, (1 <= n <= 64)%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 80) M rom) (mkst r (at_ base 92) M rom)
      /\ getr r 20 = Z_to_bv 64 (2 ^ 64 + n - 65) /\ regs_agree (fun x => In x [13; 20]%list) r0 r.
  Proof using HCODE.
    intros M r0 Hs R12'. wd_eexists. split.
    - av Fo80 D_6d4f0 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm (2 ^ 64 + n - 65) (-1)); f_equal; lia).
      an Fo84 D_6d4f4.
      ab_ft Fo88 D_6d4f8 ltac:(condz).
      wd_refl.
    - post. ra_solve.
  Qed.
  Lemma dblkSz : forall M r0, n = 0%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 80) M rom) (mkst r (at_ base 152) M rom)
      /\ getr r 20 = Z_to_bv 64 (2 ^ 64 + n - 65) /\ regs_agree (fun x => In x [13; 20]%list) r0 r.
  Proof using HCODE.
    intros M r0 Hz R12'. wd_eexists. split.
    - av Fo80 D_6d4f0 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm (2 ^ 64 + n - 65) (-1)); f_equal; lia).
      an Fo84 D_6d4f4.
      ab_tk Fo88 D_6d4f8 ltac:(condz).
      ab_ft Fo416 D_6d640 ltac:(condz).
      an Fo420 D_6d644.
      wd_refl.
    - post. ra_solve.
  Qed.
  Lemma dblkSb : forall M r0, (65 <= n)%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 80) M rom) (mkst r (at_ base 616) M rom)
      /\ getr r 20 = Z_to_bv 64 (n - 65) /\ regs_agree (fun x => In x [13; 20]%list) r0 r.
  Proof using MV bs src dst mem HCODE.
    intros M r0 Hb R12'. pose proof (u64_range dst) as Hd. destruct MV as [Mn Mlen Msrc Mdst Mnws Mnwd]. wd_eexists. split.
    - av Fo80 D_6d4f0 (Z_to_bv 64 (n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).
      an Fo84 D_6d4f4.
      ab_tk Fo88 D_6d4f8 ltac:(condz).
      ab_tk Fo416 D_6d640 ltac:(condz).
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dblkDs : forall M r0, (1 <= n <= 64)%Z -> getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n -> getr r0 20 = Z_to_bv 64 (2 ^ 64 + n - 65) ->
    exists r, msteps segs (mkst r0 (at_ base 152) M rom) (mkst r (at_ base 168) M rom)
      /\ regs_agree (fun x => In x [13]%list) r0 r.
  Proof using Hends src HCODE.
    intros M r0 Hs R10' R12' R20'. pose proof (u64_range dst) as Hd. wd_eexists. split.
    - av Fo152 D_6d538 (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).
      ab_ft Fo156 D_6d53c ltac:(condz).
      an Fo160 D_6d540.
      ab_ft Fo164 D_6d544 ltac:(condz).
      wd_refl.
    - ra_solve.
  Qed.
  Lemma dblkDz : forall M r0, n = 0%Z -> getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n -> getr r0 20 = Z_to_bv 64 (2 ^ 64 + n - 65) ->
    exists r, msteps segs (mkst r0 (at_ base 152) M rom) (mkst r (at_ base 228) M rom)
      /\ regs_agree (fun x => In x [13]%list) r0 r.
  Proof using Hends src HCODE.
    intros M r0 Hz R10' R12' R20'. pose proof (u64_range dst) as Hd. wd_eexists. split.
    - av Fo152 D_6d538 (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).
      ab_ft Fo156 D_6d53c ltac:(condz).
      an Fo160 D_6d540.
      ab_tk Fo164 D_6d544 ltac:(condz).
      ab_ft Fo556 D_6d6cc ltac:(condz).
      an Fo560 D_6d6d0.
      wd_refl.
    - ra_solve.
  Qed.
  Lemma dblkDb : forall M r0, (65 <= n)%Z -> getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n -> getr r0 20 = Z_to_bv 64 (n - 65) ->
    exists r, msteps segs (mkst r0 (at_ base 152) M rom) (mkst r (at_ base 872) M rom)
      /\ regs_agree (fun x => In x [13]%list) r0 r.
  Proof using Hends MV bs src mem HCODE.
    intros M r0 Hb R10' R12' R20'. pose proof (u64_range dst) as Hd. destruct MV as [Mn Mlen Msrc Mdst Mnws Mnwd]. wd_eexists. split.
    - av Fo152 D_6d538 (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).
      ab_ft Fo156 D_6d53c ltac:(condz).
      an Fo160 D_6d540.
      ab_tk Fo164 D_6d544 ltac:(condz).
      ab_tk Fo556 D_6d6cc ltac:(condz).
      wd_refl.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma qc1H_XD1 : forall (b : word) w0 w1 s1,
    (U b + n <= 2 ^ 47)%Z ->
    qc1H segs mem b n g_shoff p_shoff w0 w1 s1 -> qc1H segs XD1 b n g_shoff p_shoff w0 w1 s1.
  Proof using Hcells Hsp p_flag g_flag base.
    intros b w0 w1 s1 Hb [Q1 Q2 Q3 Q4 [Q5 Q6] Q7 Q8 Q9 Q10 Q11].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range b) as Hbr. cells_split.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos a 8).
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U b) ltac:(lia)) as S0. pose proof (HSh (U b + n - 1)%Z ltac:(lia)) as S1.
    assert (D0 : (Sh (U b) - 7 <= down8 (Sh (U b)) <= Sh (U b))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U b)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U b)) 8 ltac:(lia)); lia).
    assert (D1 : (Sh (U b + n - 1) - 7 <= down8 (Sh (U b + n - 1)) <= Sh (U b + n - 1))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U b + n - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U b + n - 1)) 8 ltac:(lia)); lia).
    Ltac ro Hr := apply (rd_o _ _ _ _ _ XD1_low); [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | lia | exact Hr].
    split; try assumption.
    - ro Q3. - ro Q4. - split; assumption. - ro Q7. - ro Q8. - ro Q9.
    - intros a Ha. pose proof (u64_range a). apply (rd_o _ _ _ _ _ XD1_low); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia | exact (Q11 a Ha)].
  Qed.

  Lemma dblkQ1 : forall r0 w0 w1 s1,
    qc1H segs mem src n g_shoff p_shoff w0 w1 s1 ->
    getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 92) XD1 rom) (mkst r (at_ base 152) XD1 rom)
      /\ regs_agree (fun x => In x qc1_clob) r0 r.
  Proof using Hcells Hends Hsp dst B612 B148 G92 QCS1 QCF1 p_flag g_flag.
    intros r0 w0 w1 s1 QH R11' R12'. pose proof (u64_range base).
    pose proof (qc1_pass segs (at_ base 92) (at_ base 564) (at_ base 152) 11 g_shoff p_shoff QCF1 QCS1 G92
             ltac:(rewrite at_at; exact B148) ltac:(rewrite at_at; exact B612) ltac:(rewrite at_at; reflexivity)
             (or_intror eq_refl)
             r0 XD1 rom src n w0 w1 s1 (qc1H_XD1 _ _ _ _ (proj1 Hends) QH) R11' R12') as X.
    rewrite at_at, Z.add_0_r in X. exact X.
  Qed.

  Lemma dblkQ2 : forall r0 w0 w1 s1,
    qc1H segs mem dst n g_shoff p_shoff w0 w1 s1 ->
    getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 168) XD1 rom) (mkst r (at_ base 228) XD1 rom)
      /\ regs_agree (fun x => In x qc1_clob) r0 r.
  Proof using Hcells Hends Hsp src B868 B224 G168 QCS2 QCF2 p_flag g_flag.
    intros r0 w0 w1 s1 QH R10' R12'. pose proof (u64_range base).
    pose proof (qc1_pass segs (at_ base 168) (at_ base 820) (at_ base 228) 10 g_shoff p_shoff QCF2 QCS2 G168
             ltac:(rewrite at_at; exact B224) ltac:(rewrite at_at; exact B868) ltac:(rewrite at_at; reflexivity)
             (or_introl eq_refl)
             r0 XD1 rom dst n w0 w1 s1 (qc1H_XD1 _ _ _ _ (proj2 Hends) QH) R10' R12') as X.
    rewrite at_at, Z.add_0_r in X. exact X.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ripH_on : forall (M : word -> option byte) (b raX : word) (s0 s1 : byte) (midend : word),
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) -> mem_grows mem M ->
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem b midend ->
    ((0x10007fff8000 <= U b /\ U b + n + 1 <= 0x800000000000) \/ U b + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U b))) 1 = Some [s0] -> (U s0 = 0 \/ U b mod 8 < U s0 < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U b + n - 1))) 1 = Some [s1] -> (U s1 = 0 \/ (U b + n - 1) mod 8 < U s1 < 128)%Z ->
    (forall a : word, (Sh (up8 (U b)) <= U a < Sh (down8 (U b + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok raX ->
    ripH segs rt M b (Z_to_bv 64 n) raX (at_ sp (-2144)) s0 s1 midend.
  Proof using Hstk Hcells Hsp p_flag g_flag base.
    intros M b raX s0 s1 midend HM HG Hn65 CH Hrng R0 H0 R1' H1' RZ HR.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range b) as Hb.
    destruct CH as [C1 C2 C3 C4 C5 C6 C7 C8 CC Clo Chi]. cells_split.
    assert (SH : forall x, (0 <= x < 0x800000000000)%Z -> (0x7fff8000 <= Sh x < 0x10007fff8000)%Z).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos x 8). pose proof (Z.div_lt_upper_bound x 8 0x100000000000 ltac:(lia) ltac:(lia)). lia. }
    pose proof (SH (U b) ltac:(lia)) as S0'.
    pose proof (SH (U b + n - 1)%Z ltac:(lia)) as S1'.
    assert (UP : (U b <= up8 (U b) <= U b + 7)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end); pose proof (Z.div_mod (U b + 7) 8); pose proof (Z.mod_pos_bound (U b + 7) 8); lia).
    assert (DN : (U b + n - 7 <= down8 (U b + n) <= U b + n)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (U b + n) 8); pose proof (Z.mod_pos_bound (U b + n) 8); lia).
    pose proof (SH (up8 (U b)) ltac:(lia)) as S2. pose proof (SH (down8 (U b + n)) ltac:(lia)) as S3.
    assert (Un : U (Z_to_bv 64 n) = n) by (apply u_Z2bv; lia).
    Ltac rdo HMx Hr := apply (rd_outZ _ _ _ _ HMx); [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr].
    split.
    - split; [rdo HM C1 | rdo HM C2 | rdo HM C3 | rdo HM C4 | rdo HM C5 | rdo HM C6 | rdo HM C7 | rdo HM C8 | exact CC | lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat constructor; rewrite ?at_u; lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rdo HM R0.
    - exact H0.
    - rewrite Un. rdo HM R1'.
    - rewrite Un. exact H1'.
    - rewrite Un. intros a Ha. pose proof (u64_range a). pose proof (RZ a Ha) as Ra.
      rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ra |- *. rdo HM Ra.
    - rewrite at_u by lia. lia.
    - rewrite at_at. replace (-2144 + -80)%Z with (-2224)%Z by lia. eapply store_ok_mono; [exact HG|].
      eapply (store_ok_sub segs mem (at_ sp (-2224)) _ 2224); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - exact HR.
  Qed.

  Lemma dblkR1 : forall r0 (s0b s1b : byte) (midend : word),
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem src midend ->
    ((0x10007fff8000 <= U src /\ U src + n + 1 <= 0x800000000000) \/ U src + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0b] -> (U s0b = 0 \/ U src mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U src + n - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 8 = sp -> getr r0 10 = dst -> getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    getr r0 18 = getr regs 18 -> getr r0 19 = getr regs 19 -> getr r0 20 = Z_to_bv 64 (n - 65) -> getr r0 21 = at_ sp (-2144) ->
    exists r, msteps segs (mkst r0 (at_ base 616) XD1 rom) (mkst r (at_ base 152) XD2 rom)
      /\ getr r 2 = at_ sp (-2144) /\ getr r 8 = sp /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 n
      /\ getr r 19 = getr regs 19 /\ getr r 20 = Z_to_bv 64 (n - 65) /\ getr r 21 = at_ sp (-2144)
      /\ regs_agree (fun x => In x ([1; 9; 18; 22; 23]%list ++ rip_clob)) r0 r.
  Proof using Hstk Hcells Hsp Hbase RTB RTOK HCODE p_flag g_flag.
    intros r0 s0b s1b midend Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz R2' R8' R10' R11' R12' R18' R19' R20' R21'.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    assert (RA : ret_ok (at_ base 640)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    set (r1 := regupd (regupd (regupd (regupd (regupd (regupd r0 22 dst) 10 src) 23 src) 11 (Z_to_bv 64 n)) 9 (Z_to_bv 64 n)) 1 (at_ base 640)).
    destruct (region_clear segs rt RTOK XD1 rom src (Z_to_bv 64 n) (at_ base 640) (at_ sp (-2144)) s0b s1b midend r1
                (ripH_on XD1 src (at_ base 640) s0b s1b midend XD1_agree XD1_grows Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz RA))
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; reflexivity | subst r1; gres; exact R2' | subst r1; gres; reflexivity | subst r1; gres; reflexivity |].
    wd_eexists. split.
    - an Fo616 D_6d708.                                  (* [comment removed for export] *)
      an Fo620 D_6d70c.                                  (* [comment removed for export] *)
      an Fo624 D_6d710.                                  (* [comment removed for export] *)
      an Fo628 D_6d714.                                  (* [comment removed for export] *)
      an Fo632 D_6d718.                                  (* [comment removed for export] *)
      an Fo636 D_6d71c.                                  (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- RTB.
      eapply msteps_trans; [exact RUN2|].
      replace (rip_mem rt XD1 (at_ sp (-2144)) (at_ base 640) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) src (Z_to_bv 64 n))
         with XD2.
      2:{ (lazymatch goal with |- ?G => let G' := eval unfold XD2 in G in change_no_check G' end). subst r1. gres. rewrite R8', R18', R19', R20', R21'. reflexivity. }
      assert (A23 : getr r2 23 = src) by (rewrite (AG2 23) by notin; subst r1; gres; reflexivity).
      assert (A9 : getr r2 9 = Z_to_bv 64 n) by (rewrite (AG2 9) by notin; subst r1; gres; reflexivity).
      assert (A22 : getr r2 22 = dst) by (rewrite (AG2 22) by notin; subst r1; gres; reflexivity).
      an Fo640 D_6d720.                                  (* [comment removed for export] *)
      an Fo644 D_6d724.                                  (* [comment removed for export] *)
      an Fo648 D_6d728.                                  (* [comment removed for export] *)
      an Fo652 D_6d72c.                                  (* [comment removed for export] *)
      ab_tk Fo656 D_6d730 ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
      assert (A8 : getr r2 8 = sp) by (rewrite (AG2 8) by notin; subst r1; gres; exact R8').
      assert (A19 : getr r2 19 = getr regs 19) by (rewrite (AG2 19) by notin; subst r1; gres; exact R19').
      assert (A20 : getr r2 20 = Z_to_bv 64 (n - 65)) by (rewrite (AG2 20) by notin; subst r1; gres; exact R20').
      assert (A21 : getr r2 21 = at_ sp (-2144)) by (rewrite (AG2 21) by notin; subst r1; gres; exact R21').
      post; try assumption.
      intros x Hx. gres.
      assert (X : x <> 10 /\ x <> 18 /\ x <> 12 /\ x <> 11) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct X as (X1 & X2 & X3 & X4). rewrite !getr_other by assumption.
      rewrite (AG2 x) by (intros Hc; apply Hx; apply in_or_app; right; exact Hc).
      subst r1. assert (Y : x <> 1 /\ x <> 9 /\ x <> 11 /\ x <> 23 /\ x <> 10 /\ x <> 22) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct Y as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). rewrite !getr_other by assumption. reflexivity.
  Qed.

  Lemma dblkR2 : forall r0 (s0b s1b : byte) (midend : word),
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0b] -> (U s0b = 0 \/ U dst mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U dst + n - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 8 = sp -> getr r0 10 = dst -> getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    getr r0 19 = getr regs 19 -> getr r0 20 = Z_to_bv 64 (n - 65) -> getr r0 21 = at_ sp (-2144) ->
    exists r, msteps segs (mkst r0 (at_ base 872) XD2 rom) (mkst r (at_ base 228) XD3 rom)
      /\ getr r 2 = at_ sp (-2144) /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 n
      /\ regs_agree (fun x => In x ([1; 9; 18; 19; 22]%list ++ rip_clob)) r0 r.
  Proof using Hstk Hcells Hsp Hbase RTB RTOK HCODE p_flag g_flag.
    intros r0 s0b s1b midend Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz R2' R8' R10' R11' R12' R19' R20' R21'.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    assert (RA : ret_ok (at_ base 892)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    set (r1 := regupd (regupd (regupd (regupd (regupd r0 9 dst) 22 src) 11 (Z_to_bv 64 n)) 18 (Z_to_bv 64 n)) 1 (at_ base 892)).
    destruct (region_clear segs rt RTOK XD2 rom dst (Z_to_bv 64 n) (at_ base 892) (at_ sp (-2144)) s0b s1b midend r1
                (ripH_on XD2 dst (at_ base 892) s0b s1b midend XD2_agree XD2_grows Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz RA))
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; reflexivity | subst r1; gres; exact R2' | subst r1; gres; exact R10' | subst r1; gres; reflexivity |].
    wd_eexists. split.
    - an Fo872 D_6d808.                                  (* [comment removed for export] *)
      an Fo876 D_6d80c.                                  (* [comment removed for export] *)
      an Fo880 D_6d810.                                  (* [comment removed for export] *)
      an Fo884 D_6d814.                                  (* [comment removed for export] *)
      an Fo888 D_6d818.                                  (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- RTB.
      eapply msteps_trans; [exact RUN2|].
      replace (rip_mem rt XD2 (at_ sp (-2144)) (at_ base 892) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) dst (Z_to_bv 64 n))
         with XD3.
      2:{ (lazymatch goal with |- ?G => let G' := eval unfold XD3 in G in change_no_check G' end). subst r1. gres. rewrite R8', R19', R20', R21'. reflexivity. }
      assert (A22 : getr r2 22 = src) by (rewrite (AG2 22) by notin; subst r1; gres; reflexivity).
      assert (A18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (AG2 18) by notin; subst r1; gres; reflexivity).
      assert (A9 : getr r2 9 = dst) by (rewrite (AG2 9) by notin; subst r1; gres; reflexivity).
      an Fo892 D_6d81c.                                  (* [comment removed for export] *)
      an Fo896 D_6d820.                                  (* [comment removed for export] *)
      an Fo900 D_6d824.                                  (* [comment removed for export] *)
      an Fo904 D_6d828.                                  (* [comment removed for export] *)
      ab_tk Fo908 D_6d82c ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
      post; try assumption.
      intros x Hx. gres.
      assert (X : x <> 10 /\ x <> 19 /\ x <> 12 /\ x <> 11) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct X as (X1 & X2 & X3 & X4). rewrite !getr_other by assumption.
      rewrite (AG2 x) by (intros Hc; apply Hx; apply in_or_app; right; exact Hc).
      subst r1. assert (Y : x <> 1 /\ x <> 18 /\ x <> 11 /\ x <> 22 /\ x <> 9) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct Y as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition xmm_slots : list (Z * word) :=
    [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20);
     (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23)]%Z.

  Lemma slots_XD1 : forall (k : Z) (v : word), In (k, v) xmm_slots -> rdn segs XD1 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp base.
    intros k v Hin. pose proof (u64_range sp). unfold xmm_slots in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval unfold XD1, xmm_frame in G in change_no_check G' end); rd8_chain|]). destruct Hin.
  Qed.
  Lemma slots_XD3 : forall (k : Z) (v : word), In (k, v) xmm_slots -> rdn segs XD3 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp).
    assert (Hk : (-72 <= k /\ k + 8 <= 0)%Z).
    { unfold xmm_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    rewrite <- (slots_XD1 k v Hin). apply rdn_ext; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    intros x Hx. rewrite at_u in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold XD3, XD2 in G in change_no_check G' end).
    rewrite !rip_mem_outside; first [reflexivity | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u; lia].
  Qed.
  Lemma slots_post : forall (M : word -> option byte) (k : Z) (v : word),
    (forall k' v', In (k', v') xmm_slots -> rdn segs M (at_ sp k') 8 = Some (word_to_le_bytes 8 v')) ->
    In (k, v) xmm_slots -> rdn segs (xmmove_post M) (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hdst_stk Hends MV Hsp n mem base.
    intros M k v HM Hin. pose proof (u64_range sp). pose proof (u64_range dst).
    destruct MV as [Mn Mlen Msrc Mdst Mnws Mnwd].
    assert (Hk : (-72 <= k /\ k + 8 <= 0)%Z).
    { unfold xmm_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    (lazymatch goal with |- ?G => let G' := eval unfold xmmove_post, imemmove_result in G in change_no_check G' end). destruct (Z.eqb (U dst) (U src)); [exact (HM k v Hin)|].
    destruct (Z.eq_dec n 0) as [E0 | NZ0].
    { assert (bs = []%list) as -> by (destruct bs; [reflexivity | rewrite E0 in Mlen; cbn in Mlen; lia]). (lazymatch goal with |- ?G => let G' := eval cbn [wbytes] in G in change_no_check G' end). exact (HM k v Hin). }
    rewrite rdn_wbytes_out; [exact (HM k v Hin) | rewrite Mlen, at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Mlen; lia].
  Qed.

  Lemma dblkC : forall (M : word -> option byte) r0,
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) -> mem_grows mem M ->
    (forall k v, In (k, v) xmm_slots -> rdn segs M (at_ sp k) 8 = Some (word_to_le_bytes 8 v)) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 10 = dst -> getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 228) M rom) (mkst r ra (xmmove_post M) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R2 Hret Hdst_stk Hsrc_stk Hcells Hends MV Hsp Hbase IMB IMC HCODE p_flag g_flag imm rt.
    intros M r0 HMA HG SL R2' R10' R11' R12' AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs. cells_split.
    assert (HM : forall x : word, (U x < U sp - 2224)%Z -> M x = mem x) by (intros x Hx; apply HMA; lia).
    assert (RA : ret_ok (at_ base 232)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    assert (MVM : moveH segs M dst src n bs).
    { destruct MV as [Mn Mlen Msrc Mdst Mnws Mnwd]. split; try assumption.
      - rewrite <- Msrc. apply rdn_ext; [rewrite Mlen; lia|]. intros x Hx. apply HMA. rewrite Mlen in Hx. lia.
      - eapply store_ok_mono; [exact HG | exact Mdst]. }
    set (r1 := regupd r0 1 (at_ base 232)).
    destruct (imemmove_summary segs imm M dst src n bs rom r1 (at_ base 232) IMC MVM RA)
      as (r2 & RUN2 & KP); [subst r1; gres; reflexivity | subst r1; gres; exact R10' | subst r1; gres; exact R11' | subst r1; gres; exact R12' |].
    assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (KP 2) by notin; subst r1; gres; exact R2').
    assert (A10 : getr r2 10 = dst) by (rewrite (KP 10) by notin; subst r1; gres; exact R10').
    pose proof (fun k v H => slots_post M k v SL H) as SLP. unfold xmm_slots in SLP.
    Ltac fldM F D vv SLP :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply SLP; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    wd_eexists. split; [|split].
    - an Fo228 D_6d584.                                  (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- IMB, <- (at_0 imm).
      eapply msteps_trans; [exact RUN2|].
      an Fo232 D_6d588.                                  (* [comment removed for export] *)
      fldM Fo236 D_6d58c ra SLP.
      fldM Fo240 D_6d590 (getr regs 8) SLP.
      fldM Fo244 D_6d594 (getr regs 9) SLP.
      fldM Fo248 D_6d598 (getr regs 18) SLP.
      fldM Fo252 D_6d59c (getr regs 19) SLP.
      fldM Fo256 D_6d5a0 (getr regs 20) SLP.
      fldM Fo260 D_6d5a4 (getr regs 21) SLP.
      fldM Fo264 D_6d5a8 (getr regs 22) SLP.
      fldM Fo268 D_6d5ac (getr regs 23) SLP.
      an Fo272 D_6d5b0.                                  (* [comment removed for export] *)
      aret Fo276 D_6d5b4 ra.                             (* [comment removed for export] *)
      wd_refl.
    - gres. exact A10.
    - intros x Hx. unfold amset_saved in Hx. cbn [In] in Hx. gres.
      repeat (destruct Hx as [<-|Hx];
        [ gres; rwH; rewrite ?at_addi, ?at_0; first
            [ reflexivity
            | f_equal; lia
            | rewrite (KP _) by notin; subst r1; gres; rewrite ?(AG0 _) by notin; first [reflexivity | assumption | rwH; rewrite ?at_addi; f_equal; lia] ]
        |]).
      destruct Hx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac regx AG x := rewrite (AG x) by notin.
  Ltac notin2 := let Hc := fresh "Hin" in intros Hc; cbn [In app qc1_clob rip_clob] in Hc;
    decompose [or] Hc; first [discriminate | contradiction].
  Ltac regxi AG x := rewrite (AG x) by notin2.
  Ltac in_lit := (lazymatch goal with |- ?G => let G' := eval cbn [In app amset_saved] in G in change_no_check G' end); repeat (first [left; reflexivity | right]).
  Ltac from_or Hc := cbn [In app qc1_clob rip_clob] in Hc; decompose [or] Hc; first [contradiction | subst; in_lit; fail].

  Theorem xmmove_zero : n = 0%Z ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (xmmove_post XD1) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hsrc_stk Hstk Hcells Hfl Rfl Rgf Hends MV Hsp fl Hbase G48 IMB IMC HCODE p_flag g_flag imm rt.
    intros Hz.
    destruct dblkA as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A21 & AK & AG1).
    destruct (dblkSz XD1 r1 Hz A12) as (r2 & RUN2 & B20 & AG2).
    destruct (dblkDz XD1 r2 Hz) as (r3 & RUN3 & AG3); [regx AG2 (10:reg); exact A10 | regx AG2 (12:reg); exact A12 | exact B20 |].
    destruct (dblkC XD1 r3 XD1_agree XD1_grows slots_XD1) as (r4 & RUN4 & C10 & CK);
      [ regx AG3 (2:reg); regx AG2 (2:reg); exact A2 | regx AG3 (10:reg); regx AG2 (10:reg); exact A10
      | regx AG3 (11:reg); regx AG2 (11:reg); exact A11 | regx AG3 (12:reg); regx AG2 (12:reg); exact A12
      | intros x Hx; rewrite (AG3 x); [rewrite (AG2 x); [exact (AG1 x Hx) | intros Hc; apply Hx; from_or Hc] | intros Hc; apply Hx; from_or Hc] |].
    exists r4. split; [|split; [exact C10 | exact CK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
  Qed.

  Theorem xmmove_small : forall w0s w1s s1s w0d w1d s1d, (1 <= n <= 64)%Z ->
    qc1H segs mem src n g_shoff p_shoff w0s w1s s1s ->
    qc1H segs mem dst n g_shoff p_shoff w0d w1d s1d ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (xmmove_post XD1) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hsrc_stk Hstk Hcells Hfl Rfl Rgf Hends MV Hsp fl Hbase B868 B224 B612 B148 G168 G92 G48 QCS2 QCF2 QCS1 QCF1 IMB IMC HCODE p_flag g_flag imm.
    intros w0s w1s s1s w0d w1d s1d Hs QS QD.
    destruct dblkA as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A21 & AK & AG1).
    destruct (dblkSs XD1 r1 Hs A12) as (r2 & RUN2 & B20 & AG2).
    destruct (dblkQ1 r2 w0s w1s s1s QS) as (r3 & RUN3 & AG3); [regx AG2 (11:reg); exact A11 | regx AG2 (12:reg); exact A12 |].
    assert (C10 : getr r3 10 = dst) by (regxi AG3 (10:reg); regx AG2 (10:reg); exact A10).
    assert (C12 : getr r3 12 = Z_to_bv 64 n) by (regxi AG3 (12:reg); regx AG2 (12:reg); exact A12).
    assert (C20 : getr r3 20 = Z_to_bv 64 (2 ^ 64 + n - 65)) by (regxi AG3 (20:reg); exact B20).
    destruct (dblkDs XD1 r3 Hs C10 C12 C20) as (r4 & RUN4 & AG4).
    destruct (dblkQ2 r4 w0d w1d s1d QD) as (r5 & RUN5 & AG5);
      [regx AG4 (10:reg); exact C10 | regx AG4 (12:reg); exact C12 |].
    destruct (dblkC XD1 r5 XD1_agree XD1_grows slots_XD1) as (r6 & RUN6 & D10 & DK).
    { regxi AG5 (2:reg). regx AG4 (2:reg). regxi AG3 (2:reg). regx AG2 (2:reg). exact A2. }
    { regxi AG5 (10:reg). regx AG4 (10:reg). exact C10. }
    { regxi AG5 (11:reg). regx AG4 (11:reg). regxi AG3 (11:reg). regx AG2 (11:reg). exact A11. }
    { regxi AG5 (12:reg). regx AG4 (12:reg). exact C12. }
    { intros x Hx.
      rewrite (AG5 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG4 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG3 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG2 x) by (intros Hc; apply Hx; from_or Hc). exact (AG1 x Hx). }
    exists r6. split; [|split; [exact D10 | exact DK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
    eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN6.
  Qed.

  Theorem xmmove_big : forall (s0s s1s s0d s1d : byte) (midend : word), (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem src midend -> m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U src /\ U src + n + 1 <= 0x800000000000) \/ U src + n <= 0x7fff7fff)%Z ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0s] -> (U s0s = 0 \/ U src mod 8 < U s0s < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1s] -> (U s1s = 0 \/ (U src + n - 1) mod 8 < U s1s < 128)%Z ->
    (forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0d] -> (U s0d = 0 \/ U dst mod 8 < U s0d < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1d] -> (U s1d = 0 \/ (U dst + n - 1) mod 8 < U s1d < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (xmmove_post XD3) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hsrc_stk Hstk Hcells Hfl Rfl Rgf Hends MV Hsp fl Hbase G48 IMB IMC RTB RTOK HCODE p_flag g_flag imm.
    intros s0s s1s s0d s1d midend Hb CHs CHd Rgs Rgd Rs0s Hs0s Rs1s Hs1s Rzs Rs0d Hs0d Rs1d Hs1d Rzd.
    destruct dblkA as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A21 & AK & AG1).
    destruct (dblkSb XD1 r1 ltac:(lia) A12) as (r2 & RUN2 & B20 & AG2).
    destruct (dblkR1 r2 s0s s1s midend Hb CHs Rgs Rs0s Hs0s Rs1s Hs1s Rzs) as (r3 & RUN3 & C2 & C8 & C10 & C11 & C12 & C19 & C20 & C21 & AG3);
      [ regx AG2 (2:reg); exact A2 | regx AG2 (8:reg); exact A8 | regx AG2 (10:reg); exact A10 | regx AG2 (11:reg); exact A11
      | regx AG2 (12:reg); exact A12 | regx AG2 (18:reg); apply AK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | regx AG2 (19:reg); apply AK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | exact B20 | regx AG2 (21:reg); exact A21 |].
    destruct (dblkDb XD2 r3 ltac:(lia) C10 C12 C20) as (r4 & RUN4 & AG4).
    destruct (dblkR2 r4 s0d s1d midend Hb CHd Rgd Rs0d Hs0d Rs1d Hs1d Rzd) as (r5 & RUN5 & D2 & D10 & D11 & D12 & AG5);
      [ regx AG4 (2:reg); exact C2 | regx AG4 (8:reg); exact C8 | regx AG4 (10:reg); exact C10 | regx AG4 (11:reg); exact C11
      | regx AG4 (12:reg); exact C12 | regx AG4 (19:reg); exact C19 | regx AG4 (20:reg); exact C20 | regx AG4 (21:reg); exact C21 |].
    destruct (dblkC XD3 r5 XD3_agree XD3_grows slots_XD3 D2 D10 D11 D12) as (r6 & RUN6 & E10 & EK).
    { intros x Hx.
      rewrite (AG5 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG4 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG3 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG2 x) by (intros Hc; apply Hx; from_or Hc). exact (AG1 x Hx). }
    exists r6. split; [|split; [exact E10 | exact EK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
    eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN6.
  Qed.

End XMMOVE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record xmmoveH (segs : list Segment) (t : xmmove_tab) (mem : word -> option byte)
       (dst src : word) (n : Z) (bs : list byte) (ra sp : word) (fl : byte) : Prop := XMMOVEH {
  ymh_sp : (0x10007fff8000 + 2304 <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 <= 2 ^ 47)%Z;
  ymh_mv : moveH segs mem dst src n bs;
  ymh_ends : (bv_unsigned src + n <= 2 ^ 47)%Z /\ (bv_unsigned dst + n <= 2 ^ 47)%Z;
  ymh_gf : rdn segs mem (Z_to_bv 64 (ym_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (ym_p_flag t)));
  ymh_fl : rdn segs mem (Z_to_bv 64 (ym_p_flag t)) 1 = Some [fl];
  ymh_flnz : bv_unsigned fl <> 0%Z;
  ymh_cells : Forall (fun c => 0 <= c /\ c + 8 <= bv_unsigned sp - 2224)%Z
                (ym_g_flag t :: ym_p_flag t :: m2s_cells (rt_m2s (ym_rip t)));
  ymh_stk : store_ok segs mem (at_ sp (-2224)) 2224 = true;
  ymh_src_stk : (n = 0 \/ bv_unsigned src + n <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= bv_unsigned src)%Z;
  ymh_dst_stk : (n = 0 \/ bv_unsigned dst + n <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= bv_unsigned dst)%Z;
  ymh_ret : ret_ok ra }.

Section PKG.
  Variable segs : list Segment.
  Variable t : xmmove_tab.
  Hypothesis TOK : xmmove_tab_ok segs t.
  #[local] Abbreviation U := bv_unsigned.

  Ltac pkg_finish P8 P7 :=
    lazymatch goal with
    | |- store_ok _ _ (at_ _ _) _ = true => exact P8
    | |- Forall _ _ => exact P7
    | _ => first [eassumption | reflexivity]
    end.

  Theorem asan_memmove_icpt_zero : forall mem rom (dst src ra sp : word) (n : Z) (bs : list byte) (fl : byte) regs,
    xmmoveH segs t mem dst src n bs ra sp fl -> n = 0%Z ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (ym_base t) mem rom) (mkst r ra (xmmove_post dst src bs (XD1 mem ra sp regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst src ra sp n bs fl regs [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11] Hz R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17].
    replace (mkst regs (ym_base t) mem rom) with (mkst regs (at_ (ym_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply xmmove_zero. all: pkg_finish P8 P7.
  Qed.

  Theorem asan_memmove_icpt_small : forall mem rom (dst src ra sp : word) (n : Z) (bs : list byte) (fl : byte) regs w0s w1s s1s w0d w1d s1d,
    xmmoveH segs t mem dst src n bs ra sp fl -> (1 <= n <= 64)%Z ->
    qc1H segs mem src n (mt_g_shoff (rt_m2s (ym_rip t))) (mt_p_shoff (rt_m2s (ym_rip t))) w0s w1s s1s ->
    qc1H segs mem dst n (mt_g_shoff (rt_m2s (ym_rip t))) (mt_p_shoff (rt_m2s (ym_rip t))) w0d w1d s1d ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (ym_base t) mem rom) (mkst r ra (xmmove_post dst src bs (XD1 mem ra sp regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst src ra sp n bs fl regs w0s w1s s1s w0d w1d s1d [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11] Hs QS QD R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17].
    replace (mkst regs (ym_base t) mem rom) with (mkst regs (at_ (ym_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply xmmove_small. all: pkg_finish P8 P7.
  Qed.

  Theorem asan_memmove_icpt_big : forall mem rom (dst src ra sp : word) (n : Z) (bs : list byte) (fl : byte) regs
      (s0s s1s s0d s1d : byte) (midend : word),
    xmmoveH segs t mem dst src n bs ra sp fl -> (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s (ym_rip t)) mem src midend -> m2sH segs (rt_m2s (ym_rip t)) mem dst midend ->
    ((0x10007fff8000 <= U src /\ U src + n + 1 <= 0x800000000000) \/ U src + n <= 0x7fff7fff)%Z ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0s] -> (U s0s = 0 \/ U src mod 8 < U s0s < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1s] -> (U s1s = 0 \/ (U src + n - 1) mod 8 < U s1s < 128)%Z ->
    (forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0d] -> (U s0d = 0 \/ U dst mod 8 < U s0d < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1d] -> (U s1d = 0 \/ (U dst + n - 1) mod 8 < U s1d < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (ym_base t) mem rom)
                  (mkst r ra (xmmove_post dst src bs (XD3 (ym_base t) (ym_rip t) mem dst src ra sp n regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst src ra sp n bs fl regs s0s s1s s0d s1d midend [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11]
           Hb CHs CHd Rgs Rgd Rs0s Hs0s Rs1s Hs1s Rzs Rs0d Hs0d Rs1d Hs1d Rzd R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17].
    replace (mkst regs (ym_base t) mem rom) with (mkst regs (at_ (ym_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply xmmove_big. all: pkg_finish P8 P7.
  Qed.
End PKG.
End FPGen1.
End AsRtXMemmove.
Module AsIcptXMemmove.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsRtAccess.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove AsRtXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift AsIcptMemmove.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.

Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.


Section CONTRACT.
  Context {fx0 : FPState}.   (* [comment removed for export] *)
  Context {RC : run_ceil}.   (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  (* [comment removed for export] *)
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props IA (AAINVH h) fsbase SEGS.
  (* [comment removed for export] *)
  Hypothesis SEGS_hull : forall a, find_segment SEGS a 1 <> None -> ia_img_lo IA <= a < ia_img_hi IA.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis IMG_HI : ia_img_hi IA <= AS_LO.
  Hypothesis IMG_LO : 0 <= ia_img_lo IA.
  Hypothesis FSB0 : 0 <= fsbase.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable t : xmmove_tab.
  Hypothesis TOK : forall fx : FPState, @xmmove_tab_ok fx SEGS t.
  Hypothesis T_entry : ym_base t = Z_to_bv 64 (ia_memmove_icpt IA).
  (* [comment removed for export] *)
  Definition xmmove_cells : list (Z * nat * Z) :=
    [(ym_g_flag t, 8%nat, ym_p_flag t); (ym_p_flag t, 1%nat, 1);
     (mt_g_shoff (rt_m2s (ym_rip t)), 8%nat, mt_p_shoff (rt_m2s (ym_rip t))); (mt_p_shoff (rt_m2s (ym_rip t)), 8%nat, SB);
     (mt_g_midbeg (rt_m2s (ym_rip t)), 8%nat, mt_p_midbeg (rt_m2s (ym_rip t))); (mt_p_midbeg (rt_m2s (ym_rip t)), 8%nat, 0);
     (mt_g_midend (rt_m2s (ym_rip t)), 8%nat, mt_p_midend (rt_m2s (ym_rip t))); (mt_p_midend (rt_m2s (ym_rip t)), 8%nat, 0);
     (mt_g_hiend (rt_m2s (ym_rip t)), 8%nat, mt_p_hiend (rt_m2s (ym_rip t))); (mt_p_hiend (rt_m2s (ym_rip t)), 8%nat, 0x7fffffffffff)].
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN SEGS M (fst (fst c)) (snd (fst c)) (snd c)) xmmove_cells.
  (* [comment removed for export] *)
  Hypothesis CELLS_img : Forall (fun c => ia_img_lo IA <= fst (fst c) /\ fst (fst c) + 8 <= ia_img_hi IA) xmmove_cells.

  #[local] Abbreviation cfg := (AsIface3.cfg SEGS).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem C_memmove_icpt : MEMMOVE_AT SEGS FXOK IA AAINVH (ia_memmove_icpt IA).
  Proof using CELLS_img CELLS T_entry TOK t FSB0 IMG_LO IMG_HI SEGS_wx SEGS_hull HP fsbase.
    (lazymatch goal with |- ?G => let G' := eval unfold MEMMOVE_AT in G in change_no_check G' end).
    intros h fx R M mdl Lc FF W B C K ret sp dst src n bs HFX HH AI CP Hdst Hsrc Hn [Hn0 HnN] AIM1 AIM2 AIM3 AIM4
           ACCs ACCd SVs SVd HBS ALIAS DO DSJ SSJ DOK.
    pose proof (HP h) as HPh.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk).
    destruct (aap_lazy _ _ _ _ HPh _ _ _ _ _ _ _ AI) as (AA & Awf & MI & SHCok & BLKok & PRES).
    set (Hd := HL mdl AA).
    pose proof (HL_off_segments SEGS IA (AAINVH h) fsbase HPh SEGS_hull _ _ _ _ _ _ _ AA AI) as HOFF. fold Hd in HOFF.
    pose proof (@ceil_rng RC) as CR.
    assert (NZ : forall z, 0 <= z < 2 ^ 64 -> (ia_img_lo IA <= z < ia_img_hi IA) \/ CEIL <= z -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HL_zone SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI Hz). tauto. }
    unfold AS_HEAPLO, PTRHI, SB, AS_LO, MSTK_M, NMAX in *.
    assert (RNGd : (0x10007fff8000 <= dst /\ dst + n < 2 ^ 47) \/ (0 <= dst /\ dst + n <= 0x7fff7fff)).
    { unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM1, AIM2. lia. }
    assert (RNGs : (0x10007fff8000 <= src /\ src + n < 2 ^ 47) \/ (0 <= src /\ src + n <= 0x7fff7fff)).
    { unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM3, AIM4. lia. }
    assert (Hdn2 : 0 <= dst /\ dst + n < 2 ^ 47) by lia. assert (Hsn2 : 0 <= src /\ src + n < 2 ^ 47) by lia.
    (* [comment removed for export] *)
    assert (NVIS : forall b m, shadow_visible IA Lc FF b m -> forall z, b <= z < b + m -> 0 <= z < 2 ^ 64 -> Hd (Z_to_bv 64 z) = false).
    { intros b m SV z Hz Hz64. destruct (SV z Hz) as [IB | [(f & k & Hf & Hfz) | [ST | IM]]].
      - apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [left; exact IB | exact Hz64].
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [right; exists f, k; split; [exact Hf | lia] | exact Hz64].
      - apply NZ; [lia | right; lia].
      - apply NZ; [lia | left; lia]. }
    assert (NDST : forall z, dst <= z < dst + n -> Hd (Z_to_bv 64 z) = false) by (intros z Hz; apply (NVIS _ _ SVd z Hz); lia).
    assert (NSRC : forall z, src <= z < src + n -> Hd (Z_to_bv 64 z) = false) by (intros z Hz; apply (NVIS _ _ SVs z Hz); lia).
    (* [comment removed for export] *)
    assert (NSH : forall b m, shadow_visible IA Lc FF b m ->
              forall z, b <= z < b + m -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false).
    { intros b m SV z Hz y Hy.
      destruct (SV z Hz) as [(p & pm & Hp & Hpz) | [(f & k & Hf & Hfz) | [ST | IM]]].
      - pose proof (aap_zone _ _ _ _ HPh _ _ _ _ _ _ _ p pm AI Hp) as ((Z1 & Z2 & Z3 & Z4) & Zn & Z16).
        apply (HL_allowed_page mdl AA (sh_lo p) (sh_hi p pm) (sh_lo z) y (BLKok p pm Hp)); [|exact Hy].
        apply sh_lo_in; unfold PTRLO in *; lia.
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_allowed_page mdl AA (sh_lo fsbase) (sh_hi fsbase FAKE_SIZE) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; unfold FAKE_SIZE in *; lia.
      - unfold PTRHI in ST.
        apply (HL_allowed_page mdl AA (sh_lo CEIL) (SB + 2 ^ 44) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + split; [apply sh_lo_mono; lia | apply sh_lo_lt47; lia].
      - apply (HL_allowed_page mdl AA (sh_lo (ia_img_lo IA)) (sh_hi (ia_img_lo IA) (ia_img_hi IA - ia_img_lo IA)) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; lia. }
    pose proof (NSH _ _ SVd) as NSHd. pose proof (NSH _ _ SVs) as NSHs.
    (* [comment removed for export] *)
    set (dstw := getr R 10) in *. set (srcw := getr R 11) in *. set (spw := getr R 2) in *.
    pose proof (u64_range dstw) as Hdr. pose proof (u64_range srcw) as Hsr0. pose proof (u64_range spw) as Hsr. pose proof (u64_range (getr R 12)) as H12r.
    assert (R12 : getr R 12 = Z_to_bv 64 n) by (apply bv_eq; rewrite u_Z2bv by lia; exact Hn).
    assert (RET : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u_Z2bv by lia; exact CPe).
    clear CPe CP16.   (* [comment removed for export] *)
    set (Mr := mrestrict Hd M).
    (* [comment removed for export] *)
    pose proof (CELLS _ _ _ _ _ _ _ _ AI) as CE. pose proof CELLS_img as CI. unfold xmmove_cells in CE, CI.
    apply Forall_cons_iff in CE; destruct CE as [C1 CE]. apply Forall_cons_iff in CE; destruct CE as [C2 CE]. apply Forall_cons_iff in CE; destruct CE as [C3 CE]. apply Forall_cons_iff in CE; destruct CE as [C4 CE]. apply Forall_cons_iff in CE; destruct CE as [C5 CE]. apply Forall_cons_iff in CE; destruct CE as [C6 CE]. apply Forall_cons_iff in CE; destruct CE as [C7 CE]. apply Forall_cons_iff in CE; destruct CE as [C8 CE]. apply Forall_cons_iff in CE; destruct CE as [C9 CE]. apply Forall_cons_iff in CE; destruct CE as [C10 CE].
    apply Forall_cons_iff in CI; destruct CI as [D1 CI]. apply Forall_cons_iff in CI; destruct CI as [D2 CI]. apply Forall_cons_iff in CI; destruct CI as [D3 CI]. apply Forall_cons_iff in CI; destruct CI as [D4 CI]. apply Forall_cons_iff in CI; destruct CI as [D5 CI]. apply Forall_cons_iff in CI; destruct CI as [D6 CI]. apply Forall_cons_iff in CI; destruct CI as [D7 CI]. apply Forall_cons_iff in CI; destruct CI as [D8 CI]. apply Forall_cons_iff in CI; destruct CI as [D9 CI]. apply Forall_cons_iff in CI; destruct CI as [D10 CI].
    cbn [fst snd] in *.
    Ltac hoz NZ := apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NZ; lia].
    Ltac konst NZ MM C := apply (cellN_mrestrict SEGS _ MM _ _ _ C); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); hoz NZ].
    assert (K1 : rdn SEGS Mr (Z_to_bv 64 (ym_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (ym_p_flag t)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C1).
    assert (K2 : rdn SEGS Mr (Z_to_bv 64 (ym_p_flag t)) 1 = Some [Z_to_bv 8 1]).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C2); [vm_compute; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K4 : rdn SEGS Mr (Z_to_bv 64 (mt_g_shoff (rt_m2s (ym_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_shoff (rt_m2s (ym_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C3).
    assert (K5 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midbeg (rt_m2s (ym_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midbeg (rt_m2s (ym_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C5).
    assert (K6 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midbeg (rt_m2s (ym_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C6).
    assert (K7 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midend (rt_m2s (ym_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midend (rt_m2s (ym_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C7).
    assert (K8 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midend (rt_m2s (ym_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C8).
    assert (K9 : rdn SEGS Mr (Z_to_bv 64 (mt_g_hiend (rt_m2s (ym_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_hiend (rt_m2s (ym_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C9).
    assert (K10 : rdn SEGS Mr (Z_to_bv 64 (mt_p_hiend (rt_m2s (ym_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C10).
    assert (K11 : rdn SEGS Mr (Z_to_bv 64 (mt_p_shoff (rt_m2s (ym_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C4).
    (* [comment removed for export] *)
    assert (WV : forall (m : mem) (x : word), store_ok SEGS m x 1%nat = true -> wview SEGS m x <> None).
    { intros m x Hx. cbn [store_ok] in Hx. destruct (wview SEGS m x); [discriminate | discriminate Hx]. }
    assert (STK : store_ok SEGS Mr (at_ spw (-2224)) 2224 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ].
      apply store_ok_of_all; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. apply WV. apply CPstk. cbn in Hx. lia. }
    assert (DOKr : store_ok SEGS Mr dstw (Z.to_nat n) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite Z2Nat.id; lia | rewrite Z2Nat.id by lia; apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NDST; lia]].
      apply store_ok_of_all; [rewrite Z2Nat.id; lia|]. intros x Hx. rewrite Z2Nat.id in Hx by lia. apply WV. apply DOK. lia. }
    assert (OFFS : forall b, off_scratch sp b (b + n) -> n = 0 \/ b + n <= U spw - 2224 \/ U spw <= b).
    { intros b BSJ. destruct (Z.eq_dec n 0) as [E0|NE0]; [left; exact E0 | right]. unfold off_scratch, MSTK_M in BSJ.
      pose proof (BSJ b ltac:(lia)) as X1. pose proof (BSJ (b + n - 1) ltac:(lia)) as X2.
      destruct (Z_lt_le_dec b (sp - 2304)) as [L|Ge]; [|lia].
      destruct (Z_lt_le_dec (b + n - 1) (sp - 2304)) as [L2|Ge2]; [lia|].
      exfalso. apply (BSJ (sp - 1)); lia. }
    pose proof (OFFS dst DSJ) as DSTK. pose proof (OFFS src SSJ) as SSTK. clear OFFS.
    (* [comment removed for export] *)
    assert (BS : rdn SEGS M srcw (Z.to_nat n) = Some bs).
    { replace srcw with (Z_to_bv 64 src) by (apply bv_eq; rewrite u_Z2bv by lia; symmetry; exact Hsrc). exact HBS. }
    pose proof (rdn_length _ _ _ _ _ BS) as LBS.
    assert (SR : hid_off Hd (U srcw) n) by (apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NSRC; lia]).
    assert (BSr : rdn SEGS Mr srcw (Z.to_nat n) = Some bs).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact BS | lia | rewrite Z2Nat.id by lia; exact SR]. }
    assert (MV : moveH SEGS Mr dstw srcw n bs).
    { split.
      - lia. - exact LBS. - rewrite LBS. exact BSr. - exact DOKr. - lia. - lia. }
    assert (PRE : xmmoveH SEGS t Mr dstw srcw n bs (Z_to_bv 64 ret) spw (Z_to_bv 8 1)).
    { split.
      - lia. - exact MV. - lia. - exact K1. - exact K2. - vm_compute; discriminate.
      - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); (nodisj; lia).
      - exact STK. - rewrite Hsrc; exact SSTK. - rewrite Hdst; exact DSTK. - exact RET. }
    clear SSTK.
    (* [comment removed for export] *)
    set (raw := Z_to_bv 64 ret) in *.
    assert (FR : hid_off Hd (U spw - 2224) 2224) by (hoz NZ).
    assert (DR : hid_off Hd (U dstw) n) by (apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NDST; lia]).
    assert (DM1_r : XD1 Mr raw spw R = mrestrict Hd (XD1 M raw spw R)).
    { clear - FR CP2 CPlo CPhi CR. (lazymatch goal with |- ?G => let G' := eval unfold Mr, XD1, xmm_frame in G in change_no_check G' end).
      rewrite !(wbytes_mrestrict Hd) by
        (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
         first [hs_arith_goal; rewrite at_u by (nodisj; lia); (nodisj; lia) | rewrite at_u by (nodisj; lia); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]).
      reflexivity. }
    assert (POST_r : forall X, xmmove_post dstw srcw bs (mrestrict Hd X) = mrestrict Hd (xmmove_post dstw srcw bs X)).
    { intros X. (lazymatch goal with |- ?G => let G' := eval unfold xmmove_post, imemmove_result in G in change_no_check G' end). destruct (Z.eqb (U dstw) (U srcw)); [reflexivity|].
      apply (wbytes_mrestrict_at Hd _ X dstw n); [exact LBS | lia | lia | exact DR]. }
    (* [comment removed for export] *)
    assert (SEGnone : forall a : word, CEIL <= U a -> find_segment SEGS (U a) 1 = None).
    { intros a Ha. destruct (find_segment SEGS (U a) 1) eqn:E; [|reflexivity]. exfalso.
      pose proof (SEGS_hull (U a) ltac:(rewrite E; discriminate)). lia. }
    assert (FIN : forall (M' : mem) (r : bvmap 5 word),
      msteps SEGS (mkst R (ym_base t) Mr (seg_rom SEGS)) (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) ->
      getr r 10 = dstw -> (forall x, In x amset_saved -> getr r x = getr R x) ->
      (forall a : word, M' a <> M a -> dst <= U a < dst + n \/ sp - 2304 <= U a < sp) ->
      (forall i, 0 <= i < n -> M' (Z_to_bv 64 (dst + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
      mem_grows M M' ->
      katD SEGS (cfg fx R (ia_memmove_icpt IA) M mdl) (mem_post SEGS FXOK AAINVH h R M mdl Lc FF B C K ret sp dst n (fun i => Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))))).
    { intros M' r RUN A10 SAVED CHG BYTES GR.
      assert (NH' : forall a : word, Hd a = true -> M' a = M a).
      { intros a Ha. destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso.
        pose proof (u64_range a) as Har. destruct (CHG a NE) as [X|X].
        - rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NDST (U a) X) in Ha. discriminate Ha.
        - rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NZ (U a)) in Ha; [discriminate Ha | lia | right; lia]. }
      (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.cfg in G in change_no_check G' end). rewrite <- T_entry.
      apply (katD_msteps_acct SEGS Hd HOFF SEGS_wx AA (mkst R (ym_base t) M (seg_rom SEGS))
               (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) mdl _ (lazy_cover_HL mdl AA) Awf MI HH).
      - rewrite restrict_mkst'. exact RUN.
      - intros mdl' MI' SBM HC. rewrite unrestrict_mkst. (lazymatch goal with |- ?G => let G' := eval cbn [RiscvSemantics.ms_mem mkst] in G in change_no_check G' end).
        rewrite (munrestrict_mrestrict_same Hd M M' NH').
        assert (SCR : scratch_ok SEGS M' sp MSTK_M).
        { intros a Ha. unfold MSTK_M in Ha. split.
          - apply GR. apply (store_ok1_defined SEGS M a); [apply SEGnone; lia | apply CPstk; lia].
          - eapply store_ok_mono; [exact GR | apply CPstk; lia]. }
        apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold mem_post in G in change_no_check G' end). exists fx, r, M', mdl'.
        split; [reflexivity|]. split; [exact HFX|].
        split; [apply regs_kept_of_list; exact SAVED|].
        split; [rewrite A10; exact Hdst|].
        split; [exact BYTES|].
        split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); exact (CHG a Ha)|].
        split; [exact SCR|].
        split; [|exact SBM].
        destruct DO as [WOK OWN].
        apply (aap_frame _ _ _ _ HPh W Lc FF B C K M M' mdl' WOK (PRES mdl' MI' SBM)).
        intros a Ha. destruct (CHG a Ha) as [X|X].
        * split; [apply OWN; exact X|].
          replace a with (Z_to_bv 64 (dst + (U a - dst))) by (apply bv_eq; rewrite u_Z2bv; lia).
          rewrite (BYTES (U a - dst)) by lia. discriminate.
        * split; [right; right; left; lia|]. apply (proj1 (SCR a ltac:((lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); lia))). }
    (* [comment removed for export] *)
    assert (HSP' : (0x10007fff8000 + 2304 <= U spw)%Z /\ (U spw + 16 <= 2 ^ 47)%Z) by lia.
    assert (R1' : getr R 1 = raw) by exact CP1.
    assert (BY : forall X i, 0 <= i < n -> wbytes X dstw bs (Z_to_bv 64 (dst + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
    { intros X i Hi. rewrite (AsRtIMemmove.wbytes_get_g) by (rewrite LBS; lia).
      rewrite LBS, u_Z2bv by lia.
      replace (inrng (U dstw) (Z.of_nat (Z.to_nat n)) (dst + i)) with true by (symmetry; apply inrng_true; lia).
      f_equal. f_equal. (nodisj; lia). }
    assert (RDi : forall i, 0 <= i < n -> AsIface3.rd1 SEGS M (src + i) = Some [nth (Z.to_nat i) bs (Z_to_bv 8 0)]).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.rd1 in G in change_no_check G' end).
      replace (Z_to_bv 64 (src + i)) with (srcw + nat_to_word (Z.to_nat i))%bv
        by (rewrite at_nat; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); apply bv_eq; rewrite !Z_to_bv_unsigned; f_equal; lia).
      apply (rdn_nth SEGS M (Z.to_nat n) srcw bs (Z.to_nat i) BS). lia. }
    assert (BEQ : forall X, (forall x : word, U x < U spw - 2224 \/ U spw <= U x -> X x = M x) ->
                  forall i, 0 <= i < n -> xmmove_post dstw srcw bs X (Z_to_bv 64 (dst + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
    { intros X HX i Hi. (lazymatch goal with |- ?G => let G' := eval unfold xmmove_post, imemmove_result in G in change_no_check G' end).
      destruct (Z.eqb_spec (U dstw) (U srcw)) as [E|NE].
      - destruct ALIAS as [NEQ | SDEF']; [exfalso; apply NEQ; lia|].
        destruct (M (Z_to_bv 64 (src + i))) as [b|] eqn:Hb; [|exfalso; exact (SDEF' i Hi Hb)].
        pose proof (RDi i Hi) as Ri. unfold AsIface3.rd1 in Ri. rewrite (rdn1_of_mem _ _ _ _ Hb) in Ri.
        injection Ri as Eb.
        replace (dst + i) with (src + i) by lia. rewrite HX; [rewrite Hb; f_equal; exact Eb|]. rewrite u_Z2bv by lia. clear -Hi DSTK Hdst Hsrc E Hn0 Hdn2 Hsn2. lia.
      - apply BY; exact Hi. }
    clear DSTK.
    assert (OUT1 : forall a : word, ~ (dst <= U a < dst + n) -> ~ (sp - 2304 <= U a < sp) ->
                   xmmove_post dstw srcw bs (XD1 M raw spw R) a = M a).
    { intros a N1 N2. (lazymatch goal with |- ?G => let G' := eval unfold xmmove_post, imemmove_result in G in change_no_check G' end). pose proof (u64_range a).
      destruct (Z.eqb (U dstw) (U srcw)); [apply (XD1_agree dstw M raw spw R HSP'); lia|].
      rewrite wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite LBS; lia | rewrite LBS; lia].
      apply (XD1_agree dstw M raw spw R HSP'). lia. }
    assert (GR1 : mem_grows M (xmmove_post dstw srcw bs (XD1 M raw spw R))).
    { (lazymatch goal with |- ?G => let G' := eval unfold xmmove_post, imemmove_result in G in change_no_check G' end). destruct (Z.eqb (U dstw) (U srcw)); [apply XD1_grows|].
      eapply mem_grows_trans; [apply XD1_grows | apply wbytes_grows]. }
    pose proof (fun z => aap_shdef _ _ _ _ HPh _ _ _ _ _ _ _ z AI) as SHD.
    assert (SH8 : sh_lo AS_HEAPLO mod 8 = 0 /\ AS_HEAPLO mod 8 = 0 /\ sh_lo AS_HEAPLO = 2201439137792) by (repeat split; reflexivity).
    (* [comment removed for export] *)
    assert (GRAN : forall b g, 0 <= b -> 1 <= n -> Sh b <= g < Sh (b + n - 1) + 1 -> exists z, b <= z < b + n /\ sh_lo z = g).
    { intros b g Hb Hn1 Hg. unfold Sh, sh_lo, SB in *.
      pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
      pose proof (Z.div_mod (b + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)).
      destruct (Z_lt_le_dec g (Sh (b + n - 1))) as [L|Ge]; unfold Sh in *.
      - exists (8 * (g - 2147450880) + 7). split; [lia|].
        replace (8 * (g - 2147450880) + 7) with ((g - 2147450880) * 8 + 7) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small 7 8) by lia. lia.
      - exists (b + n - 1). split; [lia|]. lia. }
    (* [comment removed for export] *)
    assert (RD1 : forall b, (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
                  forall (a : word) bs0, rdn SEGS M a 1%nat = Some bs0 -> (exists z, b <= z < b + n /\ sh_lo z = U a) ->
                  rdn SEGS Mr a 1%nat = Some bs0).
    { intros b NSHb a bs0 Hr (z & Hz & Ez). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). pose proof (u64_range a). rewrite rdn_mrestrict; [exact Hr | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      intros x Hx. cbn in Hx. replace x with a by (apply bv_eq; lia). apply (NSHb z Hz a). rewrite Ez. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    assert (RD8 : forall b, (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
                  ((0x10007fff8000 <= b /\ b + n < 2 ^ 47) \/ (0 <= b /\ b + n <= 0x7fff7fff)) ->
                  forall (w : Z) (z : Z), b <= z < b + n -> w = down8 (sh_lo z) ->
                  exists bs0, rdn SEGS Mr (Z_to_bv 64 w) 8%nat = Some bs0).
    { intros b NSHb RNG w z Hz Ew. pose proof (sh_lo_lt47 z ltac:(lia)) as SZ. pose proof (down8_le (sh_lo z) ltac:(unfold SB in SZ; lia)) as [DL DM].
      assert (LS8 : sh_lo SB = 2415882240 /\ sh_lo SB mod 8 = 0) by (split; reflexivity).
      assert (DEF8 : forall i, w <= i < w + 8 -> M (Z_to_bv 64 i) <> None).
      { destruct RNG as [[RH _] | [_ RL]].
        - assert (LO : sh_lo AS_HEAPLO <= w).
          { subst w. apply down8_ge; [exact (proj1 SH8)|]. apply sh_lo_mono. (lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia. }
          assert (HI : w + 8 <= AS_HEAPLO).
          { subst w. apply down8_lt_top; [exact (proj1 (proj2 SH8))|]. unfold AS_HEAPLO, SB in *. lia. }
          rewrite (proj2 (proj2 SH8)) in LO. unfold AS_HEAPLO in HI.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). right. (lazymatch goal with |- ?G => let G' := eval unfold AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). lia.
        - assert (LO : SB <= w).
          { subst w. apply down8_ge; [reflexivity|]. unfold SB in *. lia. }
          assert (HI : w + 8 <= sh_lo SB).
          { subst w. apply down8_lt_top; [exact (proj2 LS8)|]. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end).
            pose proof (Z.div_le_mono z 2147450879 8 ltac:(lia) ltac:(lia)). change (2147450879 / 8) with 268431359 in *. change (2147450880 / 8) with 268431360 in *. lia. }
          rewrite (proj1 LS8) in HI. unfold SB in LO.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). left. (lazymatch goal with |- ?G => let G' := eval unfold AS_LO, AS_GAPLO in G in change_no_check G' end). (nodisj; lia). }
      unfold SB in SZ.
      destruct (rdn_defined_ex SEGS M (Z_to_bv 64 w) 8) as (bs0 & Hbs & _).
      { intros i Hi. rewrite u_Z2bv in Hi by lia. apply DEF8. cbn in Hi. lia. }
      { rewrite u_Z2bv by (nodisj; lia). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (nodisj; lia). }
      exists bs0. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hbs | rewrite u_Z2bv by (nodisj; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (nodisj; lia) |].
      rewrite u_Z2bv by (nodisj; lia). intros x Hx. cbn in Hx. apply (NSHb z Hz x).
      apply (page_base_word8 w); [rewrite Ew; exact DM | (nodisj; lia) | (nodisj; lia) | rewrite u_Z2bv by (nodisj; lia); (nodisj; lia)]. }
    (* [comment removed for export] *)
    assert (QCH : forall (b : Z) (bw : word), U bw = b -> accessible M b n -> 1 <= n <= 64 ->
              (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
              ((0x10007fff8000 <= b /\ b + n < 2 ^ 47) \/ (0 <= b /\ b + n <= 0x7fff7fff)) ->
              exists w0 w1 s1, qc1H SEGS Mr bw n (mt_g_shoff (rt_m2s (ym_rip t))) (mt_p_shoff (rt_m2s (ym_rip t))) w0 w1 s1).
    { intros b bw Hb ACC Hs NSHb RNG.
      destruct (acc_last SEGS M b n ACC ltac:(lia)) as (s1 & Rs1 & Hs1).
      destruct (RD8 b NSHb RNG (down8 (sh_lo b)) b ltac:(lia) eq_refl) as (w0 & Rw0).
      destruct (RD8 b NSHb RNG (down8 (sh_lo (b + n - 1))) (b + n - 1) ltac:(lia) eq_refl) as (w1 & Rw1).
      exists w0, w1, s1. split; rewrite ?Hb.
      - lia. - lia. - exact K4. - exact K11. - (nodisj; lia).
      - rewrite Sh_is_sh_lo. exact Rw0.
      - rewrite Sh_is_sh_lo. exact Rw1.
      - apply (RD1 b NSHb _ _ Rs1). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (b + n - 1) ltac:(lia)). pose proof (sh_lo_mono b (b + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - exact Hs1.
      - intros a Ha. apply (RD1 b NSHb a _ (acc_zero SEGS M b n ACC ltac:(lia) a Ha)). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo in Ha |- *. lia. }
    (* [comment removed for export] *)
    assert (RGH : forall (b : Z) (bw : word), U bw = b -> accessible M b n -> 65 <= n ->
              (forall z, b <= z < b + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false) ->
              ((0x10007fff8000 <= b /\ b + n < 2 ^ 47) \/ (0 <= b /\ b + n <= 0x7fff7fff)) ->
              exists s0b s1b : byte,
                rdn SEGS Mr (Z_to_bv 64 (Sh (U bw))) 1 = Some [s0b] /\ (U s0b = 0 \/ U bw mod 8 < U s0b < 128)
                /\ rdn SEGS Mr (Z_to_bv 64 (Sh (U bw + n - 1))) 1 = Some [s1b] /\ (U s1b = 0 \/ (U bw + n - 1) mod 8 < U s1b < 128)
                /\ (forall a : word, Sh (up8 (U bw)) <= U a < Sh (down8 (U bw + n)) -> rdn SEGS Mr a 1 = Some [Z_to_bv 8 0])).
    { intros b bw Hb ACC Hbg NSHb RNG. rewrite Hb.
      destruct (acc_first SEGS M b n ACC ltac:(lia)) as (s0b & Rs0 & Hs0).
      destruct (acc_last SEGS M b n ACC ltac:(lia)) as (s1b & Rs1 & Hs1).
      exists s0b, s1b. repeat split.
      - apply (RD1 b NSHb _ _ Rs0). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 b ltac:(lia)). pose proof (sh_lo_mono b (b + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - exact Hs0.
      - apply (RD1 b NSHb _ _ Rs1). apply GRAN; [lia|lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (b + n - 1) ltac:(lia)). pose proof (sh_lo_mono b (b + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - exact Hs1.
      - intros a Ha. apply (RD1 b NSHb a _ (acc_zero_mid SEGS M b n ACC ltac:(lia) a Ha)). apply GRAN; [lia|lia|].
        unfold Sh, up8, down8 in Ha |- *. clear - Ha.
        pose proof (Z.div_mod (b + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + 7) 8 ltac:(lia)).
        pose proof (Z.div_mod (b + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n) 8 ltac:(lia)).
        rewrite !Z.div_mul in Ha by lia.
        pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
        pose proof (Z.div_mod (b + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)). (nodisj; lia). }
    (* [comment removed for export] *)
    destruct (Z.eq_dec n 0) as [N0 | Nn0].
    { (* [comment removed for export] *)
      destruct (asan_memmove_icpt_zero SEGS t (TOK fx) Mr (seg_rom SEGS) dstw srcw raw spw n bs (Z_to_bv 8 1) R PRE N0 R1' eq_refl eq_refl eq_refl R12)
        as (r & RUN & A10 & SAVED).
      rewrite DM1_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. apply OUT1; assumption.
      - apply BEQ. exact (XD1_agree dstw M raw spw R HSP').
      - exact GR1. }
    destruct (Z_le_gt_dec n 64) as [Ns | Nb].
    { (* [comment removed for export] *)
      destruct (QCH src srcw Hsrc ACCs ltac:(lia) NSHs RNGs) as (w0s & w1s & s1s & QS).
      destruct (QCH dst dstw Hdst ACCd ltac:(lia) NSHd RNGd) as (w0d & w1d & s1d & QD).
      destruct (asan_memmove_icpt_small SEGS t (TOK fx) Mr (seg_rom SEGS) dstw srcw raw spw n bs (Z_to_bv 8 1) R w0s w1s s1s w0d w1d s1d
                 PRE ltac:(lia) QS QD R1' eq_refl eq_refl eq_refl R12)
        as (r & RUN & A10 & SAVED).
      rewrite DM1_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. apply OUT1; assumption.
      - apply BEQ. exact (XD1_agree dstw M raw spw R HSP').
      - exact GR1. }
    { (* [comment removed for export] *)
      assert (CH : forall bw : word, (0x10007fff8000 <= U bw \/ U bw <= 0x7fff7fff) -> U bw <= 0x7fffffffffff ->
                 m2sH SEGS (rt_m2s (ym_rip t)) Mr bw (Z_to_bv 64 0)).
      { intros bw H1 H2. split.
        - exact K4. - exact K11. - exact K5. - exact K6. - exact K7. - exact K8. - exact K9. - exact K10.
        - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); lia.
        - exact H1. - exact H2. }
      assert (Hn43 : 65 <= n <= 2 ^ 43) by (unfold NMAX in *; lia).
      assert (RUNx : exists r,
        msteps SEGS (mkst R (ym_base t) Mr (seg_rom SEGS))
                    (mkst r raw (xmmove_post dstw srcw bs (XD3 (ym_base t) (ym_rip t) Mr dstw srcw raw spw n R)) (seg_rom SEGS))
        /\ getr r 10 = dstw /\ (forall x, In x amset_saved -> getr r x = getr R x)).
      { pose proof (CH srcw ltac:(lia) ltac:(lia)) as CHs. pose proof (CH dstw ltac:(lia) ltac:(lia)) as CHd.
        assert (Rgs : (0x10007fff8000 <= U srcw /\ U srcw + n + 1 <= 0x800000000000) \/ U srcw + n <= 0x7fff7fff) by lia.
        assert (Rgd : (0x10007fff8000 <= U dstw /\ U dstw + n + 1 <= 0x800000000000) \/ U dstw + n <= 0x7fff7fff) by lia.
        destruct (RGH src srcw Hsrc ACCs ltac:(lia) NSHs RNGs) as (s0s & s1s & Rs0s & Hs0s & Rs1s & Hs1s & Rzs).
        destruct (RGH dst dstw Hdst ACCd ltac:(lia) NSHd RNGd) as (s0d & s1d & Rs0d & Hs0d & Rs1d & Hs1d & Rzd).
        exact (asan_memmove_icpt_big SEGS t (TOK fx) Mr (seg_rom SEGS) dstw srcw raw spw n bs (Z_to_bv 8 1) R s0s s1s s0d s1d (Z_to_bv 64 0)
                 PRE Hn43 CHs CHd Rgs Rgd Rs0s Hs0s Rs1s Hs1s Rzs Rs0d Hs0d Rs1d Hs1d Rzd R1' eq_refl eq_refl eq_refl R12). }
      destruct RUNx as (r & RUN & A10 & SAVED).
      (* [comment removed for export] *)
      assert (DM3_r : XD3 (ym_base t) (ym_rip t) Mr dstw srcw raw spw n R = mrestrict Hd (XD3 (ym_base t) (ym_rip t) M dstw srcw raw spw n R)).
      { clear - FR CP2 CPlo CPhi CR DM1_r POST_r. (lazymatch goal with |- ?G => let G' := eval unfold XD3, XD2 in G in change_no_check G' end). rewrite DM1_r. (lazymatch goal with |- ?G => let G' := eval unfold rip_mem, ps_frame in G in change_no_check G' end).
        pose proof (u64_range spw).
        repeat (lazymatch goal with
                | |- context [if Z.ltb ?a ?b then _ else _] => destruct (Z.ltb a b)
                end);
        rewrite !(wbytes_mrestrict Hd) by
          (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
           first [hs_arith_goal; rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); (nodisj; lia)
                 | rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]);
        reflexivity. }
      rewrite DM3_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      + clear RNGd RNGs QCH RGH RD8 RD1 GRAN CH FIN.
        intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. (lazymatch goal with |- ?G => let G' := eval unfold xmmove_post, imemmove_result in G in change_no_check G' end). pose proof (u64_range a).
        destruct (Z.eqb (U dstw) (U srcw)); [apply (XD3_agree (ym_base t) (ym_rip t) M dstw srcw raw spw n R HSP'); lia|].
        rewrite wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite LBS; lia | rewrite LBS; lia].
        apply (XD3_agree (ym_base t) (ym_rip t) M dstw srcw raw spw n R HSP'). lia.
      + apply BEQ. exact (XD3_agree (ym_base t) (ym_rip t) M dstw srcw raw spw n R HSP').
      + (lazymatch goal with |- ?G => let G' := eval unfold xmmove_post, imemmove_result in G in change_no_check G' end). destruct (Z.eqb (U dstw) (U srcw)); [apply XD3_grows|].
        eapply mem_grows_trans; [apply XD3_grows | apply wbytes_grows]. }
  Qed.


End CONTRACT.
End AsIcptXMemmove.
Module AsRtXMemset.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Definition xmset_words : list (option (bv 32)) :=
  [
   Some W_6d1b0; Some W_6d1b4; Some W_6d1b8; Some W_6d1bc; Some W_6d1c0; Some W_6d1c4; Some W_6d1c8; Some W_6d1cc;
   Some W_6d1d0; Some W_6d1d4; Some W_6d1d8; None; None; Some W_6d1e4; Some W_6d1e8; Some W_6d1ec;
   Some W_6d1f0; Some W_6d1f4; Some W_6d1f8; Some W_6d1fc; Some W_6d200; Some W_6d204; None; None;
   Some W_6d210; Some W_6d214; Some W_6d218; Some W_6d21c; Some W_6d220; Some W_6d224; Some W_6d228; Some W_6d22c;
   Some W_6d230; Some W_6d234; Some W_6d238; Some W_6d23c; Some W_6d240; None; None; Some W_6d24c;
   Some W_6d250; Some W_6d254; Some W_6d258; Some W_6d25c; Some W_6d260; Some W_6d264; Some W_6d268; Some W_6d26c;
   Some W_6d270; Some W_6d274; Some W_6d278; Some W_6d27c; Some W_6d280; Some W_6d284; Some W_6d288; Some W_6d28c;
   Some W_6d290; Some W_6d294; Some W_6d298; Some W_6d29c; Some W_6d2a0; Some W_6d2a4; Some W_6d2a8; Some W_6d2ac;
   Some W_6d2b0; Some W_6d2b4; Some W_6d2b8; Some W_6d2bc; Some W_6d2c0; Some W_6d2c4; Some W_6d2c8; Some W_6d2cc;
   Some W_6d2d0; Some W_6d2d4; Some W_6d2d8; Some W_6d2dc; Some W_6d2e0; Some W_6d2e4; Some W_6d2e8; Some W_6d2ec;
   Some W_6d2f0; Some W_6d2f4; Some W_6d2f8; Some W_6d2fc; None; None; Some W_6d308; Some W_6d30c;
   Some W_6d310; Some W_6d314; Some W_6d318; Some W_6d31c; Some W_6d320; Some W_6d324; Some W_6d328; Some W_6d32c;
   Some W_6d330; Some W_6d334; Some W_6d338; Some W_6d33c; Some W_6d340; Some W_6d344; Some W_6d348; Some W_6d34c;
   Some W_6d350; Some W_6d354; Some W_6d358; Some W_6d35c; Some W_6d360; Some W_6d364; Some W_6d368; Some W_6d36c;
   Some W_6d370; Some W_6d374; Some W_6d378; Some W_6d37c; Some W_6d380; Some W_6d384; Some W_6d388; Some W_6d38c;
   Some W_6d390; Some W_6d394; Some W_6d398; Some W_6d39c; Some W_6d3a0; Some W_6d3a4; Some W_6d3a8; Some W_6d3ac;
   Some W_6d3b0; Some W_6d3b4; None; None; Some W_6d3c0; Some W_6d3c4; Some W_6d3c8; Some W_6d3cc;
   Some W_6d3d0; Some W_6d3d4; Some W_6d3d8; Some W_6d3dc; Some W_6d3e0; Some W_6d3e4; Some W_6d3e8; Some W_6d3ec;
   Some W_6d3f0; Some W_6d3f4; Some W_6d3f8; Some W_6d3fc; Some W_6d400; Some W_6d404; None; None;
   Some W_6d410; Some W_6d414; Some W_6d418; Some W_6d41c; Some W_6d420; Some W_6d424; Some W_6d428; Some W_6d42c;
   Some W_6d430; Some W_6d434; Some W_6d438; Some W_6d43c; Some W_6d440; Some W_6d444; Some W_6d448; Some W_6d44c;
   Some W_6d450; Some W_6d454; Some W_6d458; Some W_6d45c; None; None; Some W_6d468; Some W_6d46c;
   Some W_6d470; Some W_6d474; Some W_6d478; Some W_6d47c; Some W_6d480; Some W_6d484; Some W_6d488; Some W_6d48c;
   Some W_6d490; Some W_6d494; Some W_6d498; Some W_6d49c
  ]%list.


(* [comment removed for export] *)
Record xmset_tab : Type := XMST {
  xm_base : word;          (* [comment removed for export] *)
  xm_rip : rip_tab;        (* [comment removed for export] *)
  xm_mset : word;          (* [comment removed for export] *)
  xm_g_flag : Z; xm_p_flag : Z;   (* [comment removed for export] *)
  xm_c_rms : Z }.          (* [comment removed for export] *)

Record xmset_tab_ok (segs : list Segment) (t : xmset_tab) : Prop := XMSTOK {
  xto_code : code_ato segs (xm_base t) 0 xmset_words;
  xto_rip : rip_tab_ok segs (xm_rip t);
  xto_rip_base : rt_base (xm_rip t) = at_ (xm_base t) 11744;
  xto_mset : code_at segs (xm_mset t) 0 mmemset_words;
  xto_qcf : code_ato segs (at_ (xm_base t) 88) 0 (qc1f_words 10);
  xto_qcs : code_ato segs (at_ (xm_base t) 428) 0 qc1s_words;
  xto_g44 : gload segs (xm_base t) 44 13 (xm_g_flag t);
  xto_g88 : gload segs (at_ (xm_base t) 88) 0 13 (mt_g_shoff (rt_m2s (xm_rip t)));
  xto_g148 : gload segs (xm_base t) 148 13 (xm_c_rms t);
  xto_b144 : gbnez segs (at_ (xm_base t) 144) 16 (at_ (xm_base t) 428);
  xto_b476 : gbeqz segs (at_ (xm_base t) 476) 13 (at_ (xm_base t) 148);
  xto_base : (U (xm_base t) mod 2 = 0)%Z /\ (U (xm_base t) + 20000 < 2 ^ 64)%Z;
  xto_mset_ok : ret_ok (xm_mset t) }.

(* [comment removed for export] *)
Definition xms_frame (mem : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 s6 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (word_to_le_bytes 8 ra))
    (at_ sp (-16)) (word_to_le_bytes 8 s0))
    (at_ sp (-24)) (word_to_le_bytes 8 s1))
    (at_ sp (-32)) (word_to_le_bytes 8 s2))
    (at_ sp (-40)) (word_to_le_bytes 8 s3))
    (at_ sp (-48)) (word_to_le_bytes 8 s4))
    (at_ sp (-56)) (word_to_le_bytes 8 s5))
    (at_ sp (-64)) (word_to_le_bytes 8 s6).

Section XMSET.
  Variable segs : list Segment.
  Variable base : word.
  Variable rt : rip_tab.
  Variable mset : word.
  Variables g_flag p_flag c_rms : Z.
  #[local] Abbreviation g_shoff := (mt_g_shoff (rt_m2s rt)).
  #[local] Abbreviation p_shoff := (mt_p_shoff (rt_m2s rt)).
  Hypothesis HCODE : code_ato segs base 0 xmset_words.
  Hypothesis RTOK : rip_tab_ok segs rt.
  Hypothesis RTB : rt_base rt = at_ base 11744.
  Hypothesis MSC : code_at segs mset 0 mmemset_words.
  Hypothesis QCF : code_ato segs (at_ base 88) 0 (qc1f_words 10).
  Hypothesis QCS : code_ato segs (at_ base 428) 0 qc1s_words.
  Hypothesis G44 : gload segs base 44 13 g_flag.
  Hypothesis G88 : gload segs (at_ base 88) 0 13 g_shoff.
  Hypothesis G148 : gload segs base 148 13 c_rms.
  Hypothesis B144 : gbnez segs (at_ base 144) 16 (at_ base 428).
  Hypothesis B476 : gbeqz segs (at_ base 476) 13 (at_ base 148).
  Hypothesis Hbase : (U base mod 2 = 0)%Z /\ (U base + 20000 < 2 ^ 64)%Z.
  Hypothesis Hmset : ret_ok mset.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_6d1b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_6d1b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_6d1b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_6d1bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_6d1c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_6d1c4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_6d1c8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_6d1cc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_6d1d0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_6d1d4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_6d1d8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 10 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_6d1e4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_6d1e8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 14 _ HCODE eq_refl). Qed.
  Lemma Fo60 : fetch_word segs (at_ base 60) = Some W_6d1ec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 15 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_6d1f0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_6d1f4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_6d1f8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_6d1fc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_6d200.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo84 : fetch_word segs (at_ base 84) = Some W_6d204.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 21 _ HCODE eq_refl). Qed.













  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo156 : fetch_word segs (at_ base 156) = Some W_6d24c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 39 _ HCODE eq_refl). Qed.
  Lemma Fo160 : fetch_word segs (at_ base 160) = Some W_6d250.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 40 _ HCODE eq_refl). Qed.
  Lemma Fo164 : fetch_word segs (at_ base 164) = Some W_6d254.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 41 _ HCODE eq_refl). Qed.
  Lemma Fo168 : fetch_word segs (at_ base 168) = Some W_6d258.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 42 _ HCODE eq_refl). Qed.
  Lemma Fo172 : fetch_word segs (at_ base 172) = Some W_6d25c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 43 _ HCODE eq_refl). Qed.
  Lemma Fo176 : fetch_word segs (at_ base 176) = Some W_6d260.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 44 _ HCODE eq_refl). Qed.
  Lemma Fo180 : fetch_word segs (at_ base 180) = Some W_6d264.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 45 _ HCODE eq_refl). Qed.
  Lemma Fo184 : fetch_word segs (at_ base 184) = Some W_6d268.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 46 _ HCODE eq_refl). Qed.
  Lemma Fo188 : fetch_word segs (at_ base 188) = Some W_6d26c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 47 _ HCODE eq_refl). Qed.
  Lemma Fo192 : fetch_word segs (at_ base 192) = Some W_6d270.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 48 _ HCODE eq_refl). Qed.
  Lemma Fo196 : fetch_word segs (at_ base 196) = Some W_6d274.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 49 _ HCODE eq_refl). Qed.
  Lemma Fo200 : fetch_word segs (at_ base 200) = Some W_6d278.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 50 _ HCODE eq_refl). Qed.




















































  Lemma Fo420 : fetch_word segs (at_ base 420) = Some W_6d354.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 105 _ HCODE eq_refl). Qed.
  Lemma Fo424 : fetch_word segs (at_ base 424) = Some W_6d358.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 106 _ HCODE eq_refl). Qed.













  Lemma Fo480 : fetch_word segs (at_ base 480) = Some W_6d390.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 120 _ HCODE eq_refl). Qed.
  Lemma Fo484 : fetch_word segs (at_ base 484) = Some W_6d394.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 121 _ HCODE eq_refl). Qed.
  Lemma Fo488 : fetch_word segs (at_ base 488) = Some W_6d398.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 122 _ HCODE eq_refl). Qed.
  Lemma Fo492 : fetch_word segs (at_ base 492) = Some W_6d39c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 123 _ HCODE eq_refl). Qed.
  Lemma Fo496 : fetch_word segs (at_ base 496) = Some W_6d3a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 124 _ HCODE eq_refl). Qed.
  Lemma Fo500 : fetch_word segs (at_ base 500) = Some W_6d3a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 125 _ HCODE eq_refl). Qed.
  Lemma Fo504 : fetch_word segs (at_ base 504) = Some W_6d3a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 126 _ HCODE eq_refl). Qed.
  Lemma Fo508 : fetch_word segs (at_ base 508) = Some W_6d3ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 127 _ HCODE eq_refl). Qed.
  Lemma Fo512 : fetch_word segs (at_ base 512) = Some W_6d3b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 128 _ HCODE eq_refl). Qed.
  Lemma Fo516 : fetch_word segs (at_ base 516) = Some W_6d3b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xmset_words 129 _ HCODE eq_refl). Qed.





















































  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables dst cv ra sp : word.
  Variable n : Z.
  Variable fl : byte.
  Variable regs : bvmap 5 word.
  Hypothesis Hsp : (0x10007fff8000 + 2304 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  (* [comment removed for export] *)
  Definition XM1 : word -> option byte :=
    xms_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22).
  (* [comment removed for export] *)
  Definition XM2 : word -> option byte :=
    rip_mem rt XM1 (at_ sp (-2144)) (at_ base 500) sp dst (Z_to_bv 64 n) (getr regs 19) (getr regs 20) (at_ sp (-2136)) dst (Z_to_bv 64 n).
  (* [comment removed for export] *)
  Definition xmset_post (M : word -> option byte) : word -> option byte := wbytes M dst (repeat (cbyte cv) (Z.to_nat n)).

  Lemma XM1_out : forall x : word, (U x < U sp - 64 \/ U sp <= U x)%Z -> XM1 x = mem x.
  Proof using Hsp base.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold XM1, xms_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma XM1_low : forall x : word, (U x < U sp - 2224)%Z -> XM1 x = mem x.
  Proof using Hsp base. intros x Hx. apply XM1_out. lia. Qed.
  Lemma XM1_grows : mem_grows mem XM1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold XM1, xms_frame in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma XM2_low : forall x : word, (U x < U sp - 2224)%Z -> XM2 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold XM2 in G in change_no_check G' end). rewrite rip_mem_outside; [apply XM1_low; exact Hx | rewrite at_u; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  Qed.
  Lemma XM2_grows : mem_grows mem XM2.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold XM2, rip_mem, ps_frame in G in change_no_check G' end). eapply mem_grows_trans; [apply XM1_grows|].
    destruct (Z.ltb _ _);
      repeat (lazymatch goal with
              | |- mem_grows ?a ?a => apply mem_grows_refl
              | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
              end).
  Qed.

  Lemma rd_o : forall (M : word -> option byte) (B : Z) (a : word) k bs0,
    (forall x : word, (U x < B)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= B)%Z -> (B <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M B a k bs0 HM Ha HB Hr. rewrite <- Hr. apply rdn_ext; [lia|].
    intros x Hx. apply HM. lia.
  Qed.

  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hend : (U dst + n <= 2 ^ 47)%Z.
  Hypothesis Rgf : rdn segs mem (Z_to_bv 64 g_flag) 8 = Some (LE8 (Z_to_bv 64 p_flag)).
  Hypothesis Rfl : rdn segs mem (Z_to_bv 64 p_flag) 1 = Some [fl].
  Hypothesis Hfl : U fl <> 0%Z.
  Hypothesis Rrms : rdn segs mem (Z_to_bv 64 c_rms) 8 = Some (LE8 mset).
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 2224)%Z (g_flag :: p_flag :: c_rms :: m2s_cells (rt_m2s rt)).
  Hypothesis Hstk : store_ok segs mem (at_ sp (-2224)) 2224 = true.
  Hypothesis Hdok : store_ok segs mem dst (Z.to_nat n) = true.
  Hypothesis Hdst_stk : (n = 0 \/ U dst + n <= U sp - 2224 \/ U sp <= U dst)%Z.   (* [comment removed for export] *)
  Hypothesis Hret : ret_ok ra.
  Hypothesis R1 : getr regs 1 = ra.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R10 : getr regs 10 = dst.
  Hypothesis R11 : getr regs 11 = cv.
  Hypothesis R12 : getr regs 12 = Z_to_bv 64 n.

  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC; unfold m2s_cells in HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ sp (-2224)) _ 2224);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac addr_n := gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; rewrite ?at_addi; zlit_at;
                 try (progress ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end)); unorm).
  Ltac rd_close LOW Hr :=
    apply (rd_o _ _ _ _ _ LOW);
    [ rewrite ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ]
    | lia
    | first [ exact Hr | rewrite <- Hr; f_equal; apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ] ] ].
  Ltac cldb F D bb LOW Hr :=
    chain_step; [reflexivity
      | eapply step_lbu with (b := bb);
        [exact F | reflexivity | exact D | addr_n; rd_close LOW Hr]
      | step_simpl]; vn.
  Ltac gl G LOW Hr :=
    eapply msteps_trans; [ eapply G; apply (rd_o _ _ _ _ _ LOW); [(lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia | lia | exact Hr] | ]; zlit_at.

  #[local] Abbreviation CLX := (fun r : reg => In r [2; 8; 21; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31; 1; 9; 18; 19; 22]%list).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkA0 :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 76) XM1 rom)
      /\ getr r 1 = ra /\ getr r 2 = at_ sp (-2144) /\ getr r 8 = sp /\ getr r 10 = dst /\ getr r 11 = cv
      /\ getr r 12 = Z_to_bv 64 n /\ getr r 21 = at_ sp (-2136)
      /\ (forall i : reg, In i [9; 18; 19; 20; 22; 23; 24; 25; 26; 27; 3; 4]%list -> getr r i = getr regs i)
      /\ regs_agree CLX regs r.
  Proof using R12 R11 R10 R2 R1 Hstk Hcells Hfl Rfl Rgf Hend Hn Hsp fl G44 HCODE c_rms p_flag g_flag rt.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range dst) as Hd. pose proof (u8_range fl) as Hflr.
    cells_split.
    wd_eexists. split.
    - an Fo0 D_6d1b0.                                    (* [comment removed for export] *)
      fsd Fo4 D_6d1b4 (at_ sp (-8)).                     (* [comment removed for export] *)
      fsd Fo8 D_6d1b8 (at_ sp (-16)).                    (* [comment removed for export] *)
      fsd Fo12 D_6d1bc (at_ sp (-24)).                   (* [comment removed for export] *)
      fsd Fo16 D_6d1c0 (at_ sp (-32)).                   (* [comment removed for export] *)
      fsd Fo20 D_6d1c4 (at_ sp (-40)).                   (* [comment removed for export] *)
      fsd Fo24 D_6d1c8 (at_ sp (-48)).                   (* [comment removed for export] *)
      fsd Fo28 D_6d1cc (at_ sp (-56)).                   (* [comment removed for export] *)
      fsd Fo32 D_6d1d0 (at_ sp (-64)).                   (* [comment removed for export] *)
      change (wbytes _ _ _) with XM1.
      an Fo36 D_6d1d4.                                   (* [comment removed for export] *)
      an Fo40 D_6d1d8.                                   (* [comment removed for export] *)
      gl G44 XM1_low Rgf.                                (* [comment removed for export] *)
      cldb Fo52 D_6d1e4 fl XM1_low Rfl.                  (* [comment removed for export] *)
      ab_ft Fo56 D_6d1e8 ltac:(condz).                 (* [comment removed for export] *)
      av Fo60 D_6d1ec (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).   (* [comment removed for export] *)
      an Fo64 D_6d1f0. an Fo68 D_6d1f4.                  (* [comment removed for export] *)
      ab_ft Fo72 D_6d1f8 ltac:(condz).                 (* [comment removed for export] *)
      wd_refl.
    - post; rewrite ?at_0; try reflexivity.
      + intros i Hi. cbn [In] in Hi. repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]). destruct Hi.
      + ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma blkA1s : forall r0, (1 <= n <= 64)%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 76) XM1 rom) (mkst r (at_ base 88) XM1 rom)
      /\ regs_agree (fun x => In x [13; 14]%list) r0 r.
  Proof using Hn HCODE.
    intros r0 Hs R12'. wd_eexists. split.
    - av Fo76 D_6d1fc (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm (2 ^ 64 + n - 65) (-1)); f_equal; lia).  (* [comment removed for export] *)
      an Fo80 D_6d200.                                   (* [comment removed for export] *)
      ab_ft Fo84 D_6d204 ltac:(condz).                 (* [comment removed for export] *)
      wd_refl.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma blkA1z : forall r0, n = 0%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 76) XM1 rom) (mkst r (at_ base 148) XM1 rom)
      /\ regs_agree (fun x => In x [13; 14]%list) r0 r.
  Proof using Hn HCODE.
    intros r0 Hz R12'. wd_eexists. split.
    - av Fo76 D_6d1fc (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm (2 ^ 64 + n - 65) (-1)); f_equal; lia).  (* [comment removed for export] *)
      an Fo80 D_6d200.                                   (* [comment removed for export] *)
      ab_tk Fo84 D_6d204 ltac:(condz).                 (* [comment removed for export] *)
      ab_ft Fo420 D_6d354 ltac:(condz).                (* [comment removed for export] *)
      an Fo424 D_6d358.                                  (* [comment removed for export] *)
      wd_refl.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma blkA1b : forall r0, (65 <= n)%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 76) XM1 rom) (mkst r (at_ base 480) XM1 rom)
      /\ regs_agree (fun x => In x [13; 14]%list) r0 r.
  Proof using Hend Hn Hsp dst HCODE.
    intros r0 Hb R12'. pose proof (u64_range dst) as Hd.
    wd_eexists. split.
    - av Fo76 D_6d1fc (Z_to_bv 64 (n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).  (* [comment removed for export] *)
      an Fo80 D_6d200.                                   (* [comment removed for export] *)
      ab_tk Fo84 D_6d204 ltac:(condz).                 (* [comment removed for export] *)
      ab_tk Fo420 D_6d354 ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma qc1H_XM1 : forall w0 w1 s1,
    qc1H segs mem dst n g_shoff p_shoff w0 w1 s1 -> qc1H segs XM1 dst n g_shoff p_shoff w0 w1 s1.
  Proof using Hcells Hend Hsp c_rms p_flag g_flag base.
    intros w0 w1 s1 [Q1 Q2 Q3 Q4 [Q5 Q6] Q7 Q8 Q9 Q10 Q11].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range dst) as Hd. cells_split.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos a 8).
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U dst) ltac:(lia)) as S0. pose proof (HSh (U dst + n - 1)%Z ltac:(lia)) as S1.
    assert (D0 : (Sh (U dst) - 7 <= down8 (Sh (U dst)) <= Sh (U dst))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U dst)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U dst)) 8 ltac:(lia)); lia).
    assert (D1 : (Sh (U dst + n - 1) - 7 <= down8 (Sh (U dst + n - 1)) <= Sh (U dst + n - 1))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U dst + n - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U dst + n - 1)) 8 ltac:(lia)); lia).
    Ltac ro Hr := apply (rd_o _ _ _ _ _ XM1_low); [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | lia | exact Hr].
    split; try assumption.
    - ro Q3. - ro Q4. - split; assumption. - ro Q7. - ro Q8. - ro Q9.
    - intros a Ha. pose proof (u64_range a). apply (rd_o _ _ _ _ _ XM1_low); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia | exact (Q11 a Ha)].
  Qed.

  Lemma blkQ : forall r0 w0 w1 s1,
    qc1H segs mem dst n g_shoff p_shoff w0 w1 s1 ->
    getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 88) XM1 rom) (mkst r (at_ base 148) XM1 rom)
      /\ regs_agree (fun x => In x qc1_clob) r0 r.
  Proof using Hcells Hend Hsp B476 B144 G88 QCS QCF c_rms p_flag g_flag.
    intros r0 w0 w1 s1 QH R10' R12'. pose proof (u64_range base).
    pose proof (qc1_pass segs (at_ base 88) (at_ base 428) (at_ base 148) 10 g_shoff p_shoff QCF QCS G88
             ltac:(rewrite at_at; exact B144) ltac:(rewrite at_at; exact B476) ltac:(rewrite at_at; reflexivity)
             (or_introl eq_refl)
             r0 XM1 rom dst n w0 w1 s1 (qc1H_XM1 _ _ _ QH) R10' R12') as X.
    rewrite at_at, Z.add_0_r in X. exact X.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rd_outF : forall (M : word -> option byte) (a : word) k bs0,
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= U sp - 2224 \/ U sp <= U a)%Z -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M a k bs0 HM Ha Hnw Hr. rewrite <- Hr. apply rdn_ext; [exact Hnw|].
    intros x Hx. apply HM. lia.
  Qed.
  Lemma rd_outZ : forall (M : word -> option byte) (c : Z) k bs0,
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) ->
    (0 <= c)%Z -> (c + Z.of_nat k <= U sp - 2224)%Z ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs0 -> rdn segs M (Z_to_bv 64 c) k = Some bs0.
  Proof using Hsp base.
    intros M c k bs0 HM Hc Hk Hr. pose proof (u64_range sp). apply (rd_outF M); try assumption; wd_ulia.
  Qed.
  Lemma XM1_agree : forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> XM1 x = mem x.
  Proof using Hsp base. intros x Hx. apply XM1_out. lia. Qed.

  (* [comment removed for export] *)
  Lemma ripH_on : forall (M : word -> option byte) (raX : word) (s0 s1 : byte) (midend : word),
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) -> mem_grows mem M ->
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0] -> (U s0 = 0 \/ U dst mod 8 < U s0 < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1] -> (U s1 = 0 \/ (U dst + n - 1) mod 8 < U s1 < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok raX ->
    ripH segs rt M dst (Z_to_bv 64 n) raX (at_ sp (-2144)) s0 s1 midend.
  Proof using Hdst_stk Hstk Hcells Hend Hn Hsp c_rms p_flag g_flag base.
    intros M raX s0 s1 midend HM HG Hn65 CH Hhi R0 H0 R1' H1' RZ HR.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range dst) as Hb.
    destruct CH as [C1 C2 C3 C4 C5 C6 C7 C8 CC Clo Chi]. cells_split.
    assert (SH : forall x, (0 <= x < 0x800000000000)%Z -> (0x7fff8000 <= Sh x < 0x10007fff8000)%Z).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos x 8). pose proof (Z.div_lt_upper_bound x 8 0x100000000000 ltac:(lia) ltac:(lia)). lia. }
    pose proof (SH (U dst) ltac:(lia)) as S0.
    pose proof (SH (U dst + n - 1)%Z ltac:(lia)) as S1.
    assert (UP : (U dst <= up8 (U dst) <= U dst + 7)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end); pose proof (Z.div_mod (U dst + 7) 8); pose proof (Z.mod_pos_bound (U dst + 7) 8); lia).
    assert (DN : (U dst + n - 7 <= down8 (U dst + n) <= U dst + n)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (U dst + n) 8); pose proof (Z.mod_pos_bound (U dst + n) 8); lia).
    pose proof (SH (up8 (U dst)) ltac:(lia)) as S2. pose proof (SH (down8 (U dst + n)) ltac:(lia)) as S3.
    assert (Un : U (Z_to_bv 64 n) = n) by (apply u_Z2bv; lia).
    Ltac rdo HMx Hr := apply (rd_outZ _ _ _ _ HMx); [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr].
    split.
    - split; [rdo HM C1 | rdo HM C2 | rdo HM C3 | rdo HM C4 | rdo HM C5 | rdo HM C6 | rdo HM C7 | rdo HM C8 | exact CC | lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat constructor; rewrite ?at_u; lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rdo HM R0.
    - exact H0.
    - rewrite Un. rdo HM R1'.
    - rewrite Un. exact H1'.
    - rewrite Un. intros a Ha. pose proof (u64_range a). pose proof (RZ a Ha) as Ra.
      rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ra |- *. rdo HM Ra.
    - rewrite at_u by lia. lia.
    - rewrite at_at. replace (-2144 + -80)%Z with (-2224)%Z by lia. eapply store_ok_mono; [exact HG|].
      eapply (store_ok_sub segs mem (at_ sp (-2224)) _ 2224); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - exact HR.
  Qed.

  Lemma blkR : forall r0 (s0b s1b : byte) (midend : word),
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0b] -> (U s0b = 0 \/ U dst mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U dst + n - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 8 = sp -> getr r0 10 = dst -> getr r0 11 = cv -> getr r0 12 = Z_to_bv 64 n ->
    getr r0 19 = getr regs 19 -> getr r0 20 = getr regs 20 -> getr r0 21 = at_ sp (-2136) ->
    exists r, msteps segs (mkst r0 (at_ base 480) XM1 rom) (mkst r (at_ base 148) XM2 rom)
      /\ getr r 2 = at_ sp (-2144) /\ getr r 8 = sp /\ getr r 10 = dst /\ getr r 11 = cv /\ getr r 12 = Z_to_bv 64 n
      /\ regs_agree (fun x => In x ([1; 9; 18; 19; 22]%list ++ rip_clob)) r0 r.
  Proof using Hdst_stk Hstk Hcells Hend Hn Hsp Hbase RTB RTOK HCODE c_rms p_flag g_flag.
    intros r0 s0b s1b midend Hn65 CH Hhi Rs0 Hs0 Rs1 Hs1 Rz R2' R8' R10' R11' R12' R19' R20' R21'.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    assert (RA : ret_ok (at_ base 500)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    (* [comment removed for export] *)
    set (r1 := regupd (regupd (regupd (regupd (regupd r0 9 dst) 22 cv) 11 (Z_to_bv 64 n)) 18 (Z_to_bv 64 n)) 1 (at_ base 500)).
    destruct (region_clear segs rt RTOK XM1 rom dst (Z_to_bv 64 n) (at_ base 500) (at_ sp (-2144)) s0b s1b midend r1
                (ripH_on XM1 (at_ base 500) s0b s1b midend XM1_agree XM1_grows Hn65 CH Hhi Rs0 Hs0 Rs1 Hs1 Rz RA))
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; reflexivity | subst r1; gres; exact R2' | subst r1; gres; exact R10' | subst r1; gres; reflexivity |].
    wd_eexists. split.
    - an Fo480 D_6d390.                                  (* [comment removed for export] *)
      an Fo484 D_6d394.                                  (* [comment removed for export] *)
      an Fo488 D_6d398.                                  (* [comment removed for export] *)
      an Fo492 D_6d39c.                                  (* [comment removed for export] *)
      an Fo496 D_6d3a0.                                  (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- RTB.
      eapply msteps_trans; [exact RUN2|].
      replace (rip_mem rt XM1 (at_ sp (-2144)) (at_ base 500) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) dst (Z_to_bv 64 n))
         with XM2.
      2:{ (lazymatch goal with |- ?G => let G' := eval unfold XM2 in G in change_no_check G' end). subst r1. gres. rewrite R8', R19', R20', R21'. reflexivity. }
      assert (A9 : getr r2 9 = dst) by (rewrite (AG2 9) by notin; subst r1; gres; reflexivity).
      assert (A22 : getr r2 22 = cv) by (rewrite (AG2 22) by notin; subst r1; gres; reflexivity).
      assert (A18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (AG2 18) by notin; subst r1; gres; reflexivity).
      an Fo500 D_6d3a4.                                  (* [comment removed for export] *)
      an Fo504 D_6d3a8.                                  (* [comment removed for export] *)
      an Fo508 D_6d3ac.                                  (* [comment removed for export] *)
      an Fo512 D_6d3b0.                                  (* [comment removed for export] *)
      ab_tk Fo516 D_6d3b4 ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
      assert (A8 : getr r2 8 = sp) by (rewrite (AG2 8) by notin; subst r1; gres; exact R8').
      post; try assumption.
      intros x Hx. gres.
      assert (X : x <> 10 /\ x <> 19 /\ x <> 12 /\ x <> 11) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct X as (X1 & X2 & X3 & X4). rewrite !getr_other by assumption.
      rewrite (AG2 x) by (intros Hc; apply Hx; apply in_or_app; right; exact Hc).
      subst r1. assert (Y : x <> 1 /\ x <> 18 /\ x <> 11 /\ x <> 22 /\ x <> 9) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct Y as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition xm_slots : list (Z * word) :=
    [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22)]%Z.

  Lemma slots_XM1 : forall (k : Z) (v : word), In (k, v) xm_slots -> rdn segs XM1 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp base.
    intros k v Hin. pose proof (u64_range sp). unfold xm_slots in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval unfold XM1, xms_frame in G in change_no_check G' end); rd8_chain|]). destruct Hin.
  Qed.

  Lemma slots_XM2 : forall (k : Z) (v : word), In (k, v) xm_slots -> rdn segs XM2 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp).
    assert (Hk : (-64 <= k /\ k + 8 <= 0)%Z).
    { unfold xm_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    rewrite <- (slots_XM1 k v Hin). apply rdn_ext; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    intros x Hx. rewrite at_u in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold XM2 in G in change_no_check G' end). apply rip_mem_outside; rewrite at_u; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma slots_post : forall (M : word -> option byte) (k : Z) (v : word),
    (forall k' v', In (k', v') xm_slots -> rdn segs M (at_ sp k') 8 = Some (word_to_le_bytes 8 v')) ->
    In (k, v) xm_slots -> rdn segs (xmset_post M) (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hdst_stk Hend Hn Hsp base.
    intros M k v HM Hin. pose proof (u64_range sp). pose proof (u64_range dst).
    assert (Hk : (-64 <= k /\ k + 8 <= 0)%Z).
    { unfold xm_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    (lazymatch goal with |- ?G => let G' := eval unfold xmset_post in G in change_no_check G' end). destruct (Z.eq_dec n 0) as [E0 | NZ0].
    { rewrite E0. (lazymatch goal with |- ?G => let G' := eval cbn [Z.to_nat repeat wbytes] in G in change_no_check G' end). exact (HM k v Hin). }
    rewrite rdn_wbytes_out; [exact (HM k v Hin) | rewrite repeat_length, at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite repeat_length; lia].
  Qed.

  Lemma blkC : forall (M : word -> option byte) r0,
    (forall x : word, (U x < U sp - 2224)%Z -> M x = mem x) -> mem_grows mem M ->
    (forall k v, In (k, v) xm_slots -> rdn segs M (at_ sp k) 8 = Some (word_to_le_bytes 8 v)) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 10 = dst -> getr r0 11 = cv -> getr r0 12 = Z_to_bv 64 n ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 148) M rom) (mkst r ra (xmset_post M) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R2 Hret Hdst_stk Hdok Hcells Rrms Hend Hn Hsp Hmset Hbase G148 MSC HCODE c_rms p_flag g_flag mset rt.
    intros M r0 HM HG SL R2' R10' R11' R12' AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. pose proof (u64_range dst) as Hd. cells_split.
    assert (RA : ret_ok (at_ base 160)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    assert (OKM : store_ok segs M dst (Z.to_nat n) = true) by (eapply store_ok_mono; [exact HG | exact Hdok]).
    (* [comment removed for export] *)
    set (r1 := regupd (regupd r0 13 mset) 1 (at_ base 160)).
    destruct (memset_summary segs mset MSC M dst cv (at_ base 160) n rom Hn ltac:(lia) OKM RA r1)
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; exact R10' | subst r1; gres; exact R11' | subst r1; gres; exact R12' | subst r1; gres; reflexivity |].
    assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
    pose proof (fun k v H => slots_post M k v SL H) as SLP. unfold xm_slots in SLP.
    Ltac fldM F D vv SLP :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply SLP; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    wd_eexists. split; [|split].
    - gl G148 HM Rrms.                                   (* [comment removed for export] *)
      aret Fo156 D_6d24c mset.                           (* [comment removed for export] *)
      rewrite at_addi; zlit_at. change (regupd _ 1 _) with r1. rewrite <- (at_0 mset).
      eapply msteps_trans; [exact RUN2|].
      an Fo160 D_6d250.                                  (* [comment removed for export] *)
      fldM Fo164 D_6d254 ra SLP.                         (* [comment removed for export] *)
      fldM Fo168 D_6d258 (getr regs 8) SLP.              (* [comment removed for export] *)
      fldM Fo172 D_6d25c (getr regs 9) SLP.
      fldM Fo176 D_6d260 (getr regs 18) SLP.
      fldM Fo180 D_6d264 (getr regs 19) SLP.
      fldM Fo184 D_6d268 (getr regs 20) SLP.
      fldM Fo188 D_6d26c (getr regs 21) SLP.
      fldM Fo192 D_6d270 (getr regs 22) SLP.
      an Fo196 D_6d274.                                  (* [comment removed for export] *)
      aret Fo200 D_6d278 ra.                             (* [comment removed for export] *)
      wd_refl.
    - gres. exact A10.
    - intros x Hx. unfold amset_saved in Hx. cbn [In] in Hx. gres.
      repeat (destruct Hx as [<-|Hx];
        [ gres; rwH; rewrite ?at_addi, ?at_0; first
            [ reflexivity
            | f_equal; lia
            | rewrite (AG2 _) by notin; subst r1; gres; rewrite ?(AG0 _) by notin; first [reflexivity | assumption | rwH; rewrite ?at_addi; f_equal; lia] ]
        |]).
      destruct Hx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac regx AG x := rewrite (AG x) by notin.

  (* [comment removed for export] *)
  Theorem xmset_zero : n = 0%Z ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (xmset_post XM1) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hdok Hstk Hcells Rrms Hfl Rfl Rgf Hend Hn Hsp fl Hmset Hbase G148 G44 MSC HCODE c_rms p_flag g_flag mset rt.
    intros Hz.
    destruct blkA0 as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A21 & AK & AG1).
    destruct (blkA1z r1 Hz A12) as (r2 & RUN2 & AG2).
    destruct (blkC XM1 r2 XM1_low XM1_grows slots_XM1) as (r3 & RUN3 & B10 & BK);
      [regx AG2 (2 : reg); exact A2 | regx AG2 (10 : reg); exact A10 | regx AG2 (11 : reg); exact A11 | regx AG2 (12 : reg); exact A12
      | intros x Hx; rewrite (AG2 x); [exact (AG1 x Hx) | intros Hc; apply Hx; clear - Hc; cbn in Hc |- *; tauto] |].
    exists r3. split; [|split; [exact B10 | exact BK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
  Qed.

  (* [comment removed for export] *)
  Theorem xmset_small : forall w0 w1 s1, (1 <= n <= 64)%Z ->
    qc1H segs mem dst n g_shoff p_shoff w0 w1 s1 ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (xmset_post XM1) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hdok Hstk Hcells Rrms Hfl Rfl Rgf Hend Hn Hsp fl Hmset Hbase B476 B144 G148 G88 G44 QCS QCF MSC HCODE c_rms p_flag g_flag mset.
    intros w0 w1 s1 Hs QH.
    destruct blkA0 as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A21 & AK & AG1).
    destruct (blkA1s r1 Hs A12) as (r2 & RUN2 & AG2).
    destruct (blkQ r2 w0 w1 s1 QH) as (r3 & RUN3 & AG3); [regx AG2 (10 : reg); exact A10 | regx AG2 (12 : reg); exact A12 |].
    destruct (blkC XM1 r3 XM1_low XM1_grows slots_XM1) as (r4 & RUN4 & B10 & BK);
      [ regx AG3 (2 : reg); regx AG2 (2 : reg); exact A2 | regx AG3 (10 : reg); regx AG2 (10 : reg); exact A10
      | regx AG3 (11 : reg); regx AG2 (11 : reg); exact A11 | regx AG3 (12 : reg); regx AG2 (12 : reg); exact A12
      | intros x Hx; rewrite (AG3 x); [rewrite (AG2 x); [exact (AG1 x Hx) | intros Hc; apply Hx; clear - Hc; cbn in Hc |- *; tauto]
                               | intros Hc; apply Hx; clear - Hc; cbn in Hc |- *; tauto] |].
    exists r4. split; [|split; [exact B10 | exact BK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
  Qed.

  (* [comment removed for export] *)
  Theorem xmset_big : forall (s0b s1b : byte) (midend : word), (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0b] -> (U s0b = 0 \/ U dst mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U dst + n - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (xmset_post XM2) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hdok Hstk Hcells Rrms Hfl Rfl Rgf Hend Hn Hsp fl Hmset Hbase G148 G44 MSC RTB RTOK HCODE c_rms p_flag g_flag mset.
    intros s0b s1b midend Hb CH Hhi Rs0 Hs0 Rs1 Hs1 Rz.
    destruct blkA0 as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A21 & AK & AG1).
    destruct (blkA1b r1 ltac:(lia) A12) as (r2 & RUN2 & AG2).
    destruct (blkR r2 s0b s1b midend Hb CH Hhi Rs0 Hs0 Rs1 Hs1 Rz) as (r3 & RUN3 & B2 & B8 & B10 & B11 & B12 & AG3);
      [ regx AG2 (2 : reg); exact A2 | regx AG2 (8 : reg); exact A8 | regx AG2 (10 : reg); exact A10 | regx AG2 (11 : reg); exact A11 | regx AG2 (12 : reg); exact A12
      | regx AG2 (19 : reg); apply AK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | regx AG2 (20 : reg); apply AK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | regx AG2 (21 : reg); exact A21 |].
    destruct (blkC XM2 r3 XM2_low XM2_grows slots_XM2 B2 B10 B11 B12) as (r4 & RUN4 & C10 & CK).
    { intros x Hx. rewrite (AG3 x). 1: rewrite (AG2 x); [exact (AG1 x Hx) | intros Hc; apply Hx; clear - Hc; cbn in Hc |- *; tauto].
      intros Hc. apply Hx. clear - Hc. apply in_app_or in Hc. cbn in Hc |- *. tauto. }
    exists r4. split; [|split; [exact C10 | exact CK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
  Qed.

End XMSET.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record xmsetH (segs : list Segment) (t : xmset_tab) (mem : word -> option byte)
       (dst cv : word) (n : Z) (ra sp : word) (fl : byte) : Prop := XMSETH {
  xmh_n : (0 <= n)%Z;
  xmh_end : (bv_unsigned dst + n <= 2 ^ 47)%Z;
  xmh_gf : rdn segs mem (Z_to_bv 64 (xm_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (xm_p_flag t)));
  xmh_fl : rdn segs mem (Z_to_bv 64 (xm_p_flag t)) 1 = Some [fl];
  xmh_flnz : bv_unsigned fl <> 0%Z;
  xmh_rms : rdn segs mem (Z_to_bv 64 (xm_c_rms t)) 8 = Some (word_to_le_bytes 8 (xm_mset t));
  xmh_cells : Forall (fun c => 0 <= c /\ c + 8 <= bv_unsigned sp - 2224)%Z
                (xm_g_flag t :: xm_p_flag t :: xm_c_rms t :: m2s_cells (rt_m2s (xm_rip t)));
  xmh_sp : (0x10007fff8000 + 2304 <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 <= 2 ^ 47)%Z;
  xmh_stk : store_ok segs mem (at_ sp (-2224)) 2224 = true;
  xmh_dok : store_ok segs mem dst (Z.to_nat n) = true;
  xmh_dst_stk : (n = 0 \/ bv_unsigned dst + n <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= bv_unsigned dst)%Z;
  xmh_ret : ret_ok ra }.

Section PKG.
  Variable segs : list Segment.
  Variable t : xmset_tab.
  Hypothesis TOK : xmset_tab_ok segs t.
  #[local] Abbreviation PM1 mem ra sp regs := (XM1 mem ra sp regs).
  #[local] Abbreviation PM2 mem dst ra sp n regs := (XM2 (xm_base t) (xm_rip t) mem dst ra sp n regs).

  Theorem asan_memset_icpt_zero : forall mem rom (dst cv ra sp : word) (n : Z) (fl : byte) regs,
    xmsetH segs t mem dst cv n ra sp fl -> n = 0%Z ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (xm_base t) mem rom) (mkst r ra (xmset_post dst cv n (XM1 mem ra sp regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst cv ra sp n fl regs [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12] Hz R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13].
    replace (mkst regs (xm_base t) mem rom) with (mkst regs (at_ (xm_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply xmset_zero.
    all: lazymatch goal with
         | |- store_ok _ _ (at_ _ _) _ = true => exact P9
         | |- store_ok _ _ _ _ = true => exact P10
         | |- Forall _ _ => exact P7
         | _ => first [eassumption | reflexivity]
         end.
  Qed.

  Theorem asan_memset_icpt_small : forall mem rom (dst cv ra sp : word) (n : Z) (fl : byte) regs w0 w1 s1,
    xmsetH segs t mem dst cv n ra sp fl -> (1 <= n <= 64)%Z ->
    qc1H segs mem dst n (mt_g_shoff (rt_m2s (xm_rip t))) (mt_p_shoff (rt_m2s (xm_rip t))) w0 w1 s1 ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (xm_base t) mem rom) (mkst r ra (xmset_post dst cv n (XM1 mem ra sp regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst cv ra sp n fl regs w0 w1 s1 [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12] Hs QH R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13].
    replace (mkst regs (xm_base t) mem rom) with (mkst regs (at_ (xm_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply xmset_small.
    all: lazymatch goal with
         | |- store_ok _ _ (at_ _ _) _ = true => exact P9
         | |- store_ok _ _ _ _ = true => exact P10
         | |- Forall _ _ => exact P7
         | _ => first [eassumption | reflexivity]
         end.
  Qed.

  Theorem asan_memset_icpt_big : forall mem rom (dst cv ra sp : word) (n : Z) (fl : byte) regs (s0b s1b : byte) (midend : word),
    xmsetH segs t mem dst cv n ra sp fl -> (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s (xm_rip t)) mem dst midend ->
    ((0x10007fff8000 <= bv_unsigned dst /\ bv_unsigned dst + n + 1 <= 0x800000000000) \/ bv_unsigned dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (bv_unsigned dst))) 1 = Some [s0b] -> (bv_unsigned s0b = 0 \/ bv_unsigned dst mod 8 < bv_unsigned s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (bv_unsigned dst + n - 1))) 1 = Some [s1b] ->
    (bv_unsigned s1b = 0 \/ (bv_unsigned dst + n - 1) mod 8 < bv_unsigned s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (bv_unsigned dst)) <= bv_unsigned a < Sh (down8 (bv_unsigned dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (xm_base t) mem rom)
                  (mkst r ra (xmset_post dst cv n (XM2 (xm_base t) (xm_rip t) mem dst ra sp n regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst cv ra sp n fl regs s0b s1b midend [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12] Hb CH Hhi Rs0 Hs0 Rs1 Hs1 Rz R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13].
    replace (mkst regs (xm_base t) mem rom) with (mkst regs (at_ (xm_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply xmset_big.
    all: lazymatch goal with
         | |- store_ok _ _ (at_ _ _) _ = true => exact P9
         | |- store_ok _ _ _ _ = true => exact P10
         | |- Forall _ _ => exact P7
         | _ => first [eassumption | reflexivity]
         end.
  Qed.
End PKG.
End FPGen1.
End AsRtXMemset.
Module AsIcptXMemset.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsRtAccess.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset AsRtXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.

Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

Section CONTRACT.
  Context {fx0 : FPState}.   (* [comment removed for export] *)
  Context {RC : run_ceil}.   (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  (* [comment removed for export] *)
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props IA (AAINVH h) fsbase SEGS.
  (* [comment removed for export] *)
  Hypothesis SEGS_hull : forall a, find_segment SEGS a 1 <> None -> ia_img_lo IA <= a < ia_img_hi IA.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis IMG_HI : ia_img_hi IA <= AS_LO.
  Hypothesis IMG_LO : 0 <= ia_img_lo IA.
  Hypothesis FSB0 : 0 <= fsbase.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable t : xmset_tab.
  Hypothesis TOK : forall fx : FPState, @xmset_tab_ok fx SEGS t.
  Hypothesis T_entry : xm_base t = Z_to_bv 64 (ia_memset_icpt IA).
  (* [comment removed for export] *)
  Definition xmset_cells : list (Z * nat * Z) :=
    [(xm_g_flag t, 8%nat, xm_p_flag t); (xm_p_flag t, 1%nat, 1); (xm_c_rms t, 8%nat, U (xm_mset t));
     (mt_g_shoff (rt_m2s (xm_rip t)), 8%nat, mt_p_shoff (rt_m2s (xm_rip t))); (mt_p_shoff (rt_m2s (xm_rip t)), 8%nat, SB);
     (mt_g_midbeg (rt_m2s (xm_rip t)), 8%nat, mt_p_midbeg (rt_m2s (xm_rip t))); (mt_p_midbeg (rt_m2s (xm_rip t)), 8%nat, 0);
     (mt_g_midend (rt_m2s (xm_rip t)), 8%nat, mt_p_midend (rt_m2s (xm_rip t))); (mt_p_midend (rt_m2s (xm_rip t)), 8%nat, 0);
     (mt_g_hiend (rt_m2s (xm_rip t)), 8%nat, mt_p_hiend (rt_m2s (xm_rip t))); (mt_p_hiend (rt_m2s (xm_rip t)), 8%nat, 0x7fffffffffff)].
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN SEGS M (fst (fst c)) (snd (fst c)) (snd c)) xmset_cells.
  (* [comment removed for export] *)
  Hypothesis CELLS_img : Forall (fun c => ia_img_lo IA <= fst (fst c) /\ fst (fst c) + 8 <= ia_img_hi IA) xmset_cells.

  #[local] Abbreviation cfg := (AsIface3.cfg SEGS).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem C_memset_icpt : MEMSET_AT SEGS FXOK IA AAINVH (ia_memset_icpt IA).
  Proof using CELLS_img CELLS T_entry TOK t FSB0 IMG_LO IMG_HI SEGS_wx SEGS_hull HP fsbase.
    (lazymatch goal with |- ?G => let G' := eval unfold MEMSET_AT in G in change_no_check G' end).
    intros h fx R M mdl Lc FF W B C K ret sp dst c n HFX HH AI CP Hdst Hc Hn [Hn0 HnN] AIM1 AIM2 ACC SV DO DSJ DOK.
    pose proof (HP h) as HPh.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk).
    destruct (aap_lazy _ _ _ _ HPh _ _ _ _ _ _ _ AI) as (AA & Awf & MI & SHCok & BLKok & PRES).
    set (Hd := HL mdl AA).
    pose proof (HL_off_segments SEGS IA (AAINVH h) fsbase HPh SEGS_hull _ _ _ _ _ _ _ AA AI) as HOFF. fold Hd in HOFF.
    pose proof (@ceil_rng RC) as CR.
    assert (NZ : forall z, 0 <= z < 2 ^ 64 -> (ia_img_lo IA <= z < ia_img_hi IA) \/ CEIL <= z -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HL_zone SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI Hz). tauto. }
    unfold AS_HEAPLO, PTRHI, SB, AS_LO, MSTK_M, NMAX in *.
    assert (Hdn : dst + n < 2 ^ 47) by (unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM2; lia).
    assert (RNG : (0x10007fff8000 <= dst /\ dst + n < 2 ^ 47) \/ (0 <= dst /\ dst + n <= 0x7fff7fff)).
    { unfold addr_is_mem, AS_HEAPLO, PTRHI, SB in AIM1, AIM2. lia. }
    (* [comment removed for export] *)
    assert (NDST : forall z, dst <= z < dst + n -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. destruct (SV z Hz) as [IB | [(f & k & Hf & Hfz) | [ST | IM]]].
      - apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [left; exact IB | lia].
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_block SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI); [right; exists f, k; split; [exact Hf | lia] | lia].
      - apply NZ; [lia | right; lia].
      - apply NZ; [lia | left; lia]. }
    (* [comment removed for export] *)
    assert (NSH : forall z, dst <= z < dst + n -> forall y : word, page_base y = page_base (Z_to_bv 64 (sh_lo z)) -> Hd y = false).
    { intros z Hz y Hy. assert (Hz0 : 0 <= z) by lia.
      destruct (SV z Hz) as [(p & m & Hp & Hpz) | [(f & k & Hf & Hfz) | [ST | IM]]].
      - pose proof (aap_zone _ _ _ _ HPh _ _ _ _ _ _ _ p m AI Hp) as ((Z1 & Z2 & Z3 & Z4) & Zn & Z16).
        apply (HL_allowed_page mdl AA (sh_lo p) (sh_hi p m) (sh_lo z) y (BLKok p m Hp)); [|exact Hy].
        apply sh_lo_in; unfold PTRLO in *; lia.
      - pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI Hf) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
        apply (HL_allowed_page mdl AA (sh_lo fsbase) (sh_hi fsbase FAKE_SIZE) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; unfold FAKE_SIZE in *; lia.
      - unfold PTRHI in ST.
        apply (HL_allowed_page mdl AA (sh_lo CEIL) (SB + 2 ^ 44) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + split; [apply sh_lo_mono; lia | apply sh_lo_lt47; lia].
      - apply (HL_allowed_page mdl AA (sh_lo (ia_img_lo IA)) (sh_hi (ia_img_lo IA) (ia_img_hi IA - ia_img_lo IA)) (sh_lo z) y); [| |exact Hy].
        + apply SHCok. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). first [ solve [repeat (first [left; reflexivity | right])] | tauto ].
        + apply sh_lo_in; lia. }
    (* [comment removed for export] *)
    set (dstw := getr R 10) in *. set (cv := getr R 11) in *. set (spw := getr R 2) in *.
    pose proof (u64_range dstw) as Hdr. pose proof (u64_range spw) as Hsr. pose proof (u64_range (getr R 12)) as H12r.
    assert (R12 : getr R 12 = Z_to_bv 64 n) by (apply bv_eq; rewrite u_Z2bv by lia; exact Hn).
    assert (RET : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u_Z2bv by lia; exact CPe).
    set (Mr := mrestrict Hd M).
    (* [comment removed for export] *)
    pose proof (CELLS _ _ _ _ _ _ _ _ AI) as CE. pose proof CELLS_img as CI. unfold xmset_cells in CE, CI.
    Ltac fsplit H := apply Forall_cons_iff in H; destruct H as [? H].
    apply Forall_cons_iff in CE; destruct CE as [C1 CE]. apply Forall_cons_iff in CE; destruct CE as [C2 CE]. apply Forall_cons_iff in CE; destruct CE as [C3 CE]. apply Forall_cons_iff in CE; destruct CE as [C4 CE]. apply Forall_cons_iff in CE; destruct CE as [C5 CE]. apply Forall_cons_iff in CE; destruct CE as [C6 CE]. apply Forall_cons_iff in CE; destruct CE as [C7 CE]. apply Forall_cons_iff in CE; destruct CE as [C8 CE]. apply Forall_cons_iff in CE; destruct CE as [C9 CE]. apply Forall_cons_iff in CE; destruct CE as [C10 CE]. apply Forall_cons_iff in CE; destruct CE as [C11 CE].
    apply Forall_cons_iff in CI; destruct CI as [D1 CI]. apply Forall_cons_iff in CI; destruct CI as [D2 CI]. apply Forall_cons_iff in CI; destruct CI as [D3 CI]. apply Forall_cons_iff in CI; destruct CI as [D4 CI]. apply Forall_cons_iff in CI; destruct CI as [D5 CI]. apply Forall_cons_iff in CI; destruct CI as [D6 CI]. apply Forall_cons_iff in CI; destruct CI as [D7 CI]. apply Forall_cons_iff in CI; destruct CI as [D8 CI]. apply Forall_cons_iff in CI; destruct CI as [D9 CI]. apply Forall_cons_iff in CI; destruct CI as [D10 CI]. apply Forall_cons_iff in CI; destruct CI as [D11 CI].
    cbn [fst snd] in *.
    Ltac hoz NZ := apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NZ; lia].
    Ltac konst NZ MM C := apply (cellN_mrestrict SEGS _ MM _ _ _ C); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); hoz NZ].
    assert (K1 : rdn SEGS Mr (Z_to_bv 64 (xm_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (xm_p_flag t)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C1).
    assert (K2 : rdn SEGS Mr (Z_to_bv 64 (xm_p_flag t)) 1 = Some [Z_to_bv 8 1]).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C2); [vm_compute; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K3 : rdn SEGS Mr (Z_to_bv 64 (xm_c_rms t)) 8 = Some (word_to_le_bytes 8 (xm_mset t))).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (cellN_mrestrict SEGS Hd M _ _ _ C3); [rewrite Z_to_bv_bv_unsigned; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]. }
    assert (K4 : rdn SEGS Mr (Z_to_bv 64 (mt_g_shoff (rt_m2s (xm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_shoff (rt_m2s (xm_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C4).
    assert (K5 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midbeg (rt_m2s (xm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midbeg (rt_m2s (xm_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C6).
    assert (K6 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midbeg (rt_m2s (xm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C7).
    assert (K7 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midend (rt_m2s (xm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midend (rt_m2s (xm_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C8).
    assert (K8 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midend (rt_m2s (xm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C9).
    assert (K9 : rdn SEGS Mr (Z_to_bv 64 (mt_g_hiend (rt_m2s (xm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_hiend (rt_m2s (xm_rip t)))))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C10).
    assert (K10 : rdn SEGS Mr (Z_to_bv 64 (mt_p_hiend (rt_m2s (xm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C11).
    assert (K11 : rdn SEGS Mr (Z_to_bv 64 (mt_p_shoff (rt_m2s (xm_rip t)))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C5).
    (* [comment removed for export] *)
    assert (WV : forall (m : mem) (x : word), store_ok SEGS m x 1%nat = true -> wview SEGS m x <> None).
    { intros m x Hx. cbn [store_ok] in Hx. destruct (wview SEGS m x); [discriminate | discriminate Hx]. }
    assert (STK : store_ok SEGS Mr (at_ spw (-2224)) 2224 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ].
      apply store_ok_of_all; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. apply WV. apply CPstk. cbn in Hx. lia. }
    assert (DOKr : store_ok SEGS Mr dstw (Z.to_nat n) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite Z2Nat.id; lia | rewrite Z2Nat.id by lia; apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NDST; lia]].
      apply store_ok_of_all; [rewrite Z2Nat.id; lia|]. intros x Hx. rewrite Z2Nat.id in Hx by lia. apply WV. apply DOK. lia. }
    assert (DSTK : n = 0 \/ U dstw + n <= U spw - 2224 \/ U spw <= U dstw).
    { destruct (Z.eq_dec n 0) as [E0|NE0]; [left; exact E0 | right]. unfold off_scratch, MSTK_M in DSJ.
      pose proof (DSJ dst ltac:(lia)) as X1. pose proof (DSJ (dst + n - 1) ltac:(lia)) as X2.
      destruct (Z_lt_le_dec dst (sp - 2304)) as [L|Ge]; [|lia].
      destruct (Z_lt_le_dec (dst + n - 1) (sp - 2304)) as [L2|Ge2]; [lia|].
      exfalso. apply (DSJ (sp - 1)); lia. }
    assert (PRE : xmsetH SEGS t Mr dstw cv n (Z_to_bv 64 ret) spw (Z_to_bv 8 1)).
    { split.
      - exact Hn0. - lia. - exact K1. - exact K2. - vm_compute; discriminate. - exact K3.
      - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); lia.
      - lia. - exact STK. - exact DOKr. - exact DSTK. - exact RET. }
    (* [comment removed for export] *)
    set (raw := Z_to_bv 64 ret) in *.
    assert (FR : hid_off Hd (U spw - 2224) 2224) by (hoz NZ).
    assert (DR : hid_off Hd (U dstw) n) by (apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NDST; lia]).
    assert (AM1_r : XM1 Mr raw spw R = mrestrict Hd (XM1 M raw spw R)).
    { clear - FR CP2 CPlo CPhi CR. (lazymatch goal with |- ?G => let G' := eval unfold Mr, XM1, xms_frame in G in change_no_check G' end).
      rewrite !(wbytes_mrestrict Hd) by
        (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
         first [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u by lia; eapply hid_off_sub; [exact FR | lia | lia]]).
      reflexivity. }
    assert (POST_r : forall X, xmset_post dstw cv n (mrestrict Hd X) = mrestrict Hd (xmset_post dstw cv n X)).
    { intros X. (lazymatch goal with |- ?G => let G' := eval unfold xmset_post in G in change_no_check G' end). apply (wbytes_mrestrict_at Hd _ X dstw n); [apply repeat_length | lia | lia | exact DR]. }
    (* [comment removed for export] *)
    assert (SEGnone : forall a : word, CEIL <= U a -> find_segment SEGS (U a) 1 = None).
    { intros a Ha. destruct (find_segment SEGS (U a) 1) eqn:E; [|reflexivity]. exfalso.
      pose proof (SEGS_hull (U a) ltac:(rewrite E; discriminate)). lia. }
    assert (FIN : forall (M' : mem) (r : bvmap 5 word),
      msteps SEGS (mkst R (xm_base t) Mr (seg_rom SEGS)) (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) ->
      getr r 10 = dstw -> (forall x, In x amset_saved -> getr r x = getr R x) ->
      (forall a : word, M' a <> M a -> dst <= U a < dst + n \/ sp - 2304 <= U a < sp) ->
      (forall i, 0 <= i < n -> M' (Z_to_bv 64 (dst + i)) = Some (Z_to_bv 8 c)) ->
      mem_grows M M' ->
      katD SEGS (cfg fx R (ia_memset_icpt IA) M mdl) (mem_post SEGS FXOK AAINVH h R M mdl Lc FF B C K ret sp dst n (fun _ => Some (Z_to_bv 8 c)))).
    { intros M' r RUN A10 SAVED CHG BYTES GR.
      assert (NH' : forall a : word, Hd a = true -> M' a = M a).
      { intros a Ha. destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso.
        pose proof (u64_range a) as Har. destruct (CHG a NE) as [X|X].
        - rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NDST (U a) X) in Ha. discriminate Ha.
        - rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NZ (U a)) in Ha; [discriminate Ha | lia | right; lia]. }
      (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.cfg in G in change_no_check G' end). rewrite <- T_entry.
      apply (katD_msteps_acct SEGS Hd HOFF SEGS_wx AA (mkst R (xm_base t) M (seg_rom SEGS))
               (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) mdl _ (lazy_cover_HL mdl AA) Awf MI HH).
      - rewrite restrict_mkst'. exact RUN.
      - intros mdl' MI' SBM HC. rewrite unrestrict_mkst. (lazymatch goal with |- ?G => let G' := eval cbn [RiscvSemantics.ms_mem mkst] in G in change_no_check G' end).
        rewrite (munrestrict_mrestrict_same Hd M M' NH').
        assert (SCR : scratch_ok SEGS M' sp MSTK_M).
        { intros a Ha. unfold MSTK_M in Ha. split.
          - apply GR. apply (store_ok1_defined SEGS M a); [apply SEGnone; lia | apply CPstk; lia].
          - eapply store_ok_mono; [exact GR | apply CPstk; lia]. }
        apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold mem_post in G in change_no_check G' end). exists fx, r, M', mdl'.
        split; [reflexivity|]. split; [exact HFX|].
        split; [apply regs_kept_of_list; exact SAVED|].
        split; [rewrite A10; exact Hdst|].
        split; [exact BYTES|].
        split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); exact (CHG a Ha)|].
        split; [exact SCR|].
        split; [|exact SBM].
        destruct DO as [WOK OWN].
        apply (aap_frame _ _ _ _ HPh W Lc FF B C K M M' mdl' WOK (PRES mdl' MI' SBM)).
        intros a Ha. destruct (CHG a Ha) as [X|X].
        * split; [apply OWN; exact X|]. replace a with (Z_to_bv 64 (dst + (U a - dst))) by (apply bv_eq; rewrite u_Z2bv; lia).
          rewrite BYTES by lia. discriminate.
        * split; [right; right; left; lia|]. apply (proj1 (SCR a ltac:((lazymatch goal with |- ?G => let G' := eval unfold MSTK_M in G in change_no_check G' end); lia))). }
    (* [comment removed for export] *)
    assert (HSP' : (0x10007fff8000 + 2304 <= U spw)%Z /\ (U spw + 16 <= 2 ^ 47)%Z) by lia.
    assert (R1' : getr R 1 = raw) by exact CP1.
    assert (OUT1 : forall a : word, ~ (dst <= U a < dst + n) -> ~ (sp - 2304 <= U a < sp) ->
                   xmset_post dstw cv n (XM1 M raw spw R) a = M a).
    { intros a N1 N2. (lazymatch goal with |- ?G => let G' := eval unfold xmset_post in G in change_no_check G' end). pose proof (u64_range a).
      rewrite wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite repeat_length; lia | rewrite repeat_length; lia].
      apply (XM1_out dstw M raw spw R HSP'). lia. }
    assert (GR1 : mem_grows M (xmset_post dstw cv n (XM1 M raw spw R))).
    { (lazymatch goal with |- ?G => let G' := eval unfold xmset_post in G in change_no_check G' end). eapply mem_grows_trans; [apply XM1_grows | apply wbytes_grows]. }
    assert (BY : forall X i, 0 <= i < n -> xmset_post dstw cv n X (Z_to_bv 64 (dst + i)) = Some (Z_to_bv 8 c)).
    { intros X i Hi. (lazymatch goal with |- ?G => let G' := eval unfold xmset_post in G in change_no_check G' end). rewrite (AsRtIMemmove.wbytes_get_g) by (rewrite repeat_length; lia).
      rewrite repeat_length, u_Z2bv by lia.
      replace (inrng (U dstw) (Z.of_nat (Z.to_nat n)) (dst + i)) with true by (symmetry; apply inrng_true; lia).
      rewrite nth_repeat_lt by lia. f_equal. (lazymatch goal with |- ?G => let G' := eval unfold cbyte in G in change_no_check G' end). apply bv_eq. rewrite !Z_to_bv_unsigned.
      (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 8) with 256. rewrite <- Hc. rewrite Zmod_mod. reflexivity. }
    pose proof (fun z => aap_shdef _ _ _ _ HPh _ _ _ _ _ _ _ z AI) as SHD.
    assert (SH8 : sh_lo AS_HEAPLO mod 8 = 0 /\ AS_HEAPLO mod 8 = 0 /\ sh_lo AS_HEAPLO = 2201439137792) by (repeat split; reflexivity).
    (* [comment removed for export] *)
    assert (NSHg : forall a : word, (exists z, dst <= z < dst + n /\ sh_lo z = U a) -> Hd a = false).
    { intros a (z & Hz & Ez). apply (NSH z Hz a). rewrite Ez. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    assert (GRAN : forall g, 1 <= n -> Sh dst <= g < Sh (dst + n - 1) + 1 -> exists z, dst <= z < dst + n /\ sh_lo z = g).
    { intros g Hn1 Hg. unfold Sh, sh_lo, SB in *.
      pose proof (Z.div_mod dst 8 ltac:(lia)). pose proof (Z.mod_pos_bound dst 8 ltac:(lia)).
      pose proof (Z.div_mod (dst + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (dst + n - 1) 8 ltac:(lia)).
      destruct (Z_lt_le_dec g (Sh (dst + n - 1))) as [L|Ge]; unfold Sh in *.
      - exists (8 * (g - 2147450880) + 7). split; [(nodisj; lia)|].
        replace (8 * (g - 2147450880) + 7) with ((g - 2147450880) * 8 + 7) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small 7 8) by lia. lia.
      - exists (dst + n - 1). split; [lia|]. lia. }
    (* [comment removed for export] *)
    assert (RD1 : forall (a : word) bs, rdn SEGS M a 1%nat = Some bs -> (exists z, dst <= z < dst + n /\ sh_lo z = U a) ->
                  rdn SEGS Mr a 1%nat = Some bs).
    { intros a bs Hr Hz. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). pose proof (u64_range a). rewrite rdn_mrestrict; [exact Hr | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      intros x Hx. cbn in Hx. replace x with a by (apply bv_eq; lia). apply NSHg. exact Hz. }
    assert (RD8 : forall (w : Z) (z : Z), dst <= z < dst + n -> w = down8 (sh_lo z) ->
                  exists bs, rdn SEGS Mr (Z_to_bv 64 w) 8%nat = Some bs).
    { intros w z Hz Ew. pose proof (sh_lo_lt47 z ltac:(lia)) as SZ. pose proof (down8_le (sh_lo z) ltac:(unfold SB in SZ; lia)) as [DL DM].
      assert (LS8 : sh_lo SB = 2415882240 /\ sh_lo SB mod 8 = 0) by (split; reflexivity).
      assert (DEF8 : forall i, w <= i < w + 8 -> M (Z_to_bv 64 i) <> None).
      { destruct RNG as [[RH _] | [_ RL]].
        - assert (LO : sh_lo AS_HEAPLO <= w).
          { subst w. apply down8_ge; [exact (proj1 SH8)|]. apply sh_lo_mono. (lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia. }
          assert (HI : w + 8 <= AS_HEAPLO).
          { subst w. apply down8_lt_top; [exact (proj1 (proj2 SH8))|]. unfold AS_HEAPLO, SB in *. lia. }
          rewrite (proj2 (proj2 SH8)) in LO. unfold AS_HEAPLO in HI.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). right. (lazymatch goal with |- ?G => let G' := eval unfold AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). lia.
        - assert (LO : SB <= w).
          { subst w. apply down8_ge; [reflexivity|]. unfold SB in *. lia. }
          assert (HI : w + 8 <= sh_lo SB).
          { subst w. apply down8_lt_top; [exact (proj2 LS8)|]. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end).
            pose proof (Z.div_le_mono z 2147450879 8 ltac:(lia) ltac:(lia)). change (2147450879 / 8) with 268431359 in *. change (2147450880 / 8) with 268431360 in *. lia. }
          rewrite (proj1 LS8) in HI. unfold SB in LO.
          intros i Hi. apply SHD. (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). left. (lazymatch goal with |- ?G => let G' := eval unfold AS_LO, AS_GAPLO in G in change_no_check G' end). lia. }
      unfold SB in SZ.
      destruct (rdn_defined_ex SEGS M (Z_to_bv 64 w) 8) as (bs & Hbs & _).
      { intros i Hi. rewrite u_Z2bv in Hi by (nodisj; lia). apply DEF8. cbn in Hi. lia. }
      { rewrite u_Z2bv by (nodisj; lia). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
      exists bs. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hbs | rewrite u_Z2bv by (nodisj; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (nodisj; lia) |].
      rewrite u_Z2bv by (nodisj; lia). intros x Hx. cbn in Hx. apply (NSH z Hz x).
      apply (page_base_word8 w); [rewrite Ew; exact DM | (nodisj; lia) | (nodisj; lia) | rewrite u_Z2bv by (nodisj; lia); (nodisj; lia)]. }
    (* [comment removed for export] *)
    destruct (Z.eq_dec n 0) as [N0 | Nn0].
    { (* [comment removed for export] *)
      destruct (asan_memset_icpt_zero SEGS t (TOK fx) Mr (seg_rom SEGS) dstw cv raw spw n (Z_to_bv 8 1) R PRE N0 R1' eq_refl eq_refl eq_refl R12)
        as (r & RUN & A10 & SAVED).
      rewrite AM1_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. apply OUT1; assumption.
      - intros i Hi. apply BY. exact Hi.
      - exact GR1. }
    destruct (Z_le_gt_dec n 64) as [Ns | Nb].
    { (* [comment removed for export] *)
      destruct (acc_last SEGS M dst n ACC ltac:(lia)) as (s1 & Rs1 & Hs1).
      destruct (RD8 (down8 (sh_lo dst)) dst ltac:(lia) eq_refl) as (w0 & Rw0).
      destruct (RD8 (down8 (sh_lo (dst + n - 1))) (dst + n - 1) ltac:(lia) eq_refl) as (w1 & Rw1).
      assert (QH : qc1H SEGS Mr dstw n (mt_g_shoff (rt_m2s (xm_rip t))) (mt_p_shoff (rt_m2s (xm_rip t))) w0 w1 s1).
      { split; rewrite ?Hdst.
        - lia. - lia. - exact K4. - exact K11. - (nodisj; lia).
        - rewrite Sh_is_sh_lo. exact Rw0.
        - rewrite Sh_is_sh_lo. exact Rw1.
        - apply (RD1 _ _ Rs1). apply GRAN; [lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (dst + n - 1) ltac:(lia)). pose proof (sh_lo_mono dst (dst + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
        - exact Hs1.
        - intros a Ha. apply (RD1 a _ (acc_zero SEGS M dst n ACC ltac:(lia) a Ha)). apply GRAN; [lia|]. rewrite !Sh_is_sh_lo in Ha |- *. lia. }
      destruct (asan_memset_icpt_small SEGS t (TOK fx) Mr (seg_rom SEGS) dstw cv raw spw n (Z_to_bv 8 1) R w0 w1 s1 PRE ltac:(lia) QH R1' eq_refl eq_refl eq_refl R12)
        as (r & RUN & A10 & SAVED).
      rewrite AM1_r, POST_r in RUN.
      apply (FIN _ r RUN A10 SAVED).
      - intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
        exfalso. apply Ha. apply OUT1; assumption.
      - intros i Hi. apply BY. exact Hi.
      - exact GR1. }
    { (* [comment removed for export] *)
      destruct (acc_first SEGS M dst n ACC ltac:(lia)) as (s0b & Rs0 & Hs0).
      destruct (acc_last SEGS M dst n ACC ltac:(lia)) as (s1b & Rs1 & Hs1).
      assert (CH : m2sH SEGS (rt_m2s (xm_rip t)) Mr dstw (Z_to_bv 64 0)).
      { split.
        - exact K4. - exact K11. - exact K5. - exact K6. - exact K7. - exact K8. - exact K9. - exact K10.
        - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); (nodisj; lia).
        - lia. - lia. }
      assert (Hn43 : 65 <= n <= 2 ^ 43) by (unfold NMAX in *; lia).
      destruct (asan_memset_icpt_big SEGS t (TOK fx) Mr (seg_rom SEGS) dstw cv raw spw n (Z_to_bv 8 1) R s0b s1b (Z_to_bv 64 0)
                 PRE Hn43 CH ltac:(rewrite Hdst; lia)) as (r & RUN & A10 & SAVED).
      - rewrite Hdst. apply (RD1 _ _ Rs0). apply GRAN; [lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 dst ltac:(lia)). pose proof (sh_lo_mono dst (dst + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - rewrite Hdst. exact Hs0.
      - rewrite Hdst. apply (RD1 _ _ Rs1). apply GRAN; [lia|]. rewrite !Sh_is_sh_lo. pose proof (sh_lo_lt47 (dst + n - 1) ltac:(lia)). pose proof (sh_lo_mono dst (dst + n - 1) ltac:(lia)). rewrite u_Z2bv by (unfold SB in *; lia). lia.
      - rewrite Hdst. exact Hs1.
      - rewrite Hdst. intros a Ha. apply (RD1 a _ (acc_zero_mid SEGS M dst n ACC ltac:(lia) a Ha)). apply GRAN; [lia|].
        unfold Sh, up8, down8 in Ha |- *. clear - Ha.
        pose proof (Z.div_mod (dst + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (dst + 7) 8 ltac:(lia)).
        pose proof (Z.div_mod (dst + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (dst + n) 8 ltac:(lia)).
        rewrite !Z.div_mul in Ha by lia.
        pose proof (Z.div_mod dst 8 ltac:(lia)). pose proof (Z.mod_pos_bound dst 8 ltac:(lia)).
        pose proof (Z.div_mod (dst + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (dst + n - 1) 8 ltac:(lia)). (nodisj; lia).
      - exact R1'. - reflexivity. - reflexivity. - reflexivity. - exact R12.
      - (* [comment removed for export] *)
        assert (AM2_r : XM2 (xm_base t) (xm_rip t) Mr dstw raw spw n R = mrestrict Hd (XM2 (xm_base t) (xm_rip t) M dstw raw spw n R)).
        { clear - FR CP2 CPlo CPhi CR AM1_r. (lazymatch goal with |- ?G => let G' := eval unfold XM2 in G in change_no_check G' end). rewrite AM1_r. (lazymatch goal with |- ?G => let G' := eval unfold rip_mem, ps_frame in G in change_no_check G' end).
          pose proof (u64_range spw).
          destruct (Z.ltb _ _);
          rewrite !(wbytes_mrestrict Hd) by
            (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
             first [hs_arith_goal; rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); (nodisj; lia)
                   | rewrite !at_u by (rewrite ?at_u by (nodisj; lia); (nodisj; lia)); eapply hid_off_sub; [exact FR | (nodisj; lia) | (nodisj; lia)]]);
          reflexivity. }
        rewrite AM2_r, POST_r in RUN.
        apply (FIN _ r RUN A10 SAVED).
        + intros a Ha. destruct (decide (dst <= U a < dst + n)); [left; lia|]. destruct (decide (sp - 2304 <= U a < sp)); [right; lia|].
          exfalso. apply Ha. (lazymatch goal with |- ?G => let G' := eval unfold xmset_post in G in change_no_check G' end). pose proof (u64_range a).
          rewrite wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite repeat_length; (nodisj; lia) | rewrite repeat_length; (nodisj; lia)].
          destruct (Z_lt_le_dec (U a) (sp - 2224)).
          * apply (XM2_low (xm_base t) (xm_rip t) M dstw raw spw n R HSP'). (nodisj; lia).
          * (lazymatch goal with |- ?G => let G' := eval unfold XM2 in G in change_no_check G' end). rewrite rip_mem_outside; [| rewrite at_u by (nodisj; lia); (nodisj; lia) | rewrite at_u by (nodisj; lia); (nodisj; lia)].
            apply (XM1_out dstw M raw spw R HSP'). (nodisj; lia).
        + intros i Hi. apply BY. exact Hi.
        + (lazymatch goal with |- ?G => let G' := eval unfold xmset_post in G in change_no_check G' end). eapply mem_grows_trans; [apply XM2_grows | apply wbytes_grows]. }
  Qed.

End CONTRACT.
End AsIcptXMemset.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtAMemcpyI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset AsRtAMemcpy.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_amcpy_tab : amcpy_tab :=
  {| ac_base := 0x6c76c; ac_rip := asan_rip_tab; ac_mcp := 0xf52e0;
     ac_g_flag := 0xffdd8; ac_p_flag := 0x108259; ac_c_rmc := 0x1011a8 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x6c76c : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

Lemma asan_amcpy_tab_ok : amcpy_tab_ok ASEGS asan_amcpy_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [ac_base ac_rip ac_mcp ac_g_flag ac_p_flag ac_c_rmc asan_amcpy_tab rt_base rt_m2s asan_rip_tab mt_g_shoff asan_m2s_tab_6fb04] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold amcpy_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact asan_memcpy_code.
  - lit 112%Z (0x6c7dc : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 856%Z (0x6cac4 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2s_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 184%Z (0x6c824 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 1020%Z (0x6cb68 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2s_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6c794 D_6c794 F_6c798 D_6c798.
  - lit 112%Z (0x6c7dc : word). gload_tac F_6c7d4 D_6c7d4 F_6c7d8 D_6c7d8.
  - lit 184%Z (0x6c824 : word). gload_tac F_6c81c D_6c81c F_6c820 D_6c820.
  - gload_tac F_6c854 D_6c854 F_6c858 D_6c858.
  - lit 164%Z (0x6c810 : word). lit 856%Z (0x6cac4 : word). eapply (gbnez_of ASEGS _ _ _ _ _ F_6c808 eq_refl D_6c808). apply bv_eq; vm_compute; reflexivity.
  - lit 904%Z (0x6caf4 : word). lit 168%Z (0x6c814 : word). eapply (gbeqz_of ASEGS _ _ _ _ _ F_6caec eq_refl D_6caec). apply bv_eq; vm_compute; reflexivity.
  - lit 236%Z (0x6c858 : word). lit 1020%Z (0x6cb68 : word). eapply (gbnez_of ASEGS _ _ _ _ _ F_6c850 eq_refl D_6c850). apply bv_eq; vm_compute; reflexivity.
  - lit 1068%Z (0x6cb98 : word). lit 240%Z (0x6c85c : word). eapply (gbeqz_of ASEGS _ _ _ _ _ F_6cb90 eq_refl D_6cb90). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
  - apply ret_ok_even. vm_compute. reflexivity.
Qed.



End FPGen1.
End AsRtAMemcpyI.
Module AsRtAMemmoveI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_ammove_tab : ammove_tab :=
  {| mm_base := 0x6ce48; mm_rip := asan_rip_tab; mm_imm := 0x7fee0; mm_g_flag := 0xffdd8; mm_p_flag := 0x108259 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x6ce48 : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

Lemma asan_ammove_tab_ok : ammove_tab_ok ASEGS asan_ammove_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [mm_base mm_rip mm_imm mm_g_flag mm_p_flag asan_ammove_tab rt_base rt_m2s asan_rip_tab mt_g_shoff asan_m2s_tab_6fb04] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold ammove_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact asan_imemmove_code.
  - apply bv_eq; vm_compute; reflexivity.
  - lit 88%Z (0x6cea0 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 556%Z (0x6d074 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1s_words in G in change_no_check G' end). code_ato_vm.
  - lit 164%Z (0x6ceec : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 720%Z (0x6d118 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6ce6c D_6ce6c F_6ce70 D_6ce70.
  - lit 88%Z (0x6cea0 : word). gload_tac F_6ce98 D_6ce98 F_6ce9c D_6ce9c.
  - lit 164%Z (0x6ceec : word). gload_tac F_6cee4 D_6cee4 F_6cee8 D_6cee8.
  - lit 144%Z (0x6ced8 : word). lit 556%Z (0x6d074 : word). eapply (gbnez_of ASEGS _ _ _ _ _ F_6ced0 eq_refl D_6ced0). apply bv_eq; vm_compute; reflexivity.
  - lit 604%Z (0x6d0a4 : word). lit 148%Z (0x6cedc : word). eapply (gbeqz_of ASEGS _ _ _ _ _ F_6d09c eq_refl D_6d09c). apply bv_eq; vm_compute; reflexivity.
  - lit 220%Z (0x6cf24 : word). lit 720%Z (0x6d118 : word). eapply (gbnez_of ASEGS _ _ _ _ _ F_6cf1c eq_refl D_6cf1c). apply bv_eq; vm_compute; reflexivity.
  - lit 768%Z (0x6d148 : word). lit 224%Z (0x6cf28 : word). eapply (gbeqz_of ASEGS _ _ _ _ _ F_6d140 eq_refl D_6d140). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
Qed.



End FPGen1.
End AsRtAMemmoveI.
Module AsRtAMemsetI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_amset_tab : amset_tab :=
  {| am_base := 0x6cc08; am_rip := asan_rip_tab; am_mset := 0xf56e4;
     am_g_flag := 0xffdd8; am_p_flag := 0x108259; am_c_rms := 0x1011b0 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma asan_amset_tab_ok : amset_tab_ok ASEGS asan_amset_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [am_base am_rip am_mset am_g_flag am_p_flag am_c_rms asan_amset_tab rt_base rt_m2s asan_rip_tab mt_g_shoff asan_m2s_tab_6fb04] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold amset_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact asan_memset_code.
  - replace (at_ (0x6cc08 : word) 84) with (0x6cc5c : word) by (apply bv_eq; vm_compute; reflexivity).
    (lazymatch goal with |- ?G => let G' := eval unfold qc1f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - replace (at_ (0x6cc08 : word) 416) with (0x6cda8 : word) by (apply bv_eq; vm_compute; reflexivity).
    (lazymatch goal with |- ?G => let G' := eval unfold qc1s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6cc28 D_6cc28 F_6cc2c D_6cc2c.
  - replace (at_ (0x6cc08 : word) 84) with (0x6cc5c : word) by (apply bv_eq; vm_compute; reflexivity).
    gload_tac F_6cc54 D_6cc54 F_6cc58 D_6cc58.
  - gload_tac F_6cc90 D_6cc90 F_6cc94 D_6cc94.
  - replace (at_ (0x6cc08 : word) 140) with (0x6cc94 : word) by (apply bv_eq; vm_compute; reflexivity).
    replace (at_ (0x6cc08 : word) 416) with (0x6cda8 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply (gbnez_of ASEGS _ _ _ _ _ F_6cc8c eq_refl D_6cc8c). apply bv_eq; vm_compute; reflexivity.
  - replace (at_ (0x6cc08 : word) 464) with (0x6cdd8 : word) by (apply bv_eq; vm_compute; reflexivity).
    replace (at_ (0x6cc08 : word) 144) with (0x6cc98 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply (gbeqz_of ASEGS _ _ _ _ _ F_6cdd0 eq_refl D_6cdd0). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
  - apply ret_ok_even. vm_compute. reflexivity.
Qed.



End FPGen1.
End AsRtAMemsetI.
Require LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtFakeRel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma decode_sb_x0 : forall rs : Z, 1 <= rs <= 31 ->
  decode_any (Z_to_bv 32 (0x23 + rs * 2 ^ 15)) = Some (Store SZ1 (Z_to_bv 5 rs) (Z_to_bv 5 0) (Z_to_bv 12 0), 4%Z).
Proof.
  intros rs Hrs.
  assert (K : rs = 1 \/ rs = 2 \/ rs = 3 \/ rs = 4 \/ rs = 5 \/ rs = 6 \/ rs = 7 \/ rs = 8 \/ rs = 9 \/ rs = 10 \/ rs = 11 \/ rs = 12
              \/ rs = 13 \/ rs = 14 \/ rs = 15 \/ rs = 16 \/ rs = 17 \/ rs = 18 \/ rs = 19 \/ rs = 20 \/ rs = 21 \/ rs = 22 \/ rs = 23
              \/ rs = 24 \/ rs = 25 \/ rs = 26 \/ rs = 27 \/ rs = 28 \/ rs = 29 \/ rs = 30 \/ rs = 31) by lia.
  repeat (destruct K as [-> | K]; [vm_compute; reflexivity|]). subst rs. vm_compute. reflexivity.
Qed.
Lemma is_ecall_sb_x0 : forall rs : Z, 1 <= rs <= 31 -> is_ecall (Z_to_bv 32 (0x23 + rs * 2 ^ 15)) = false.
Proof.
  intros rs Hrs.
  assert (K : rs = 1 \/ rs = 2 \/ rs = 3 \/ rs = 4 \/ rs = 5 \/ rs = 6 \/ rs = 7 \/ rs = 8 \/ rs = 9 \/ rs = 10 \/ rs = 11 \/ rs = 12
              \/ rs = 13 \/ rs = 14 \/ rs = 15 \/ rs = 16 \/ rs = 17 \/ rs = 18 \/ rs = 19 \/ rs = 20 \/ rs = 21 \/ rs = 22 \/ rs = 23
              \/ rs = 24 \/ rs = 25 \/ rs = 26 \/ rs = 27 \/ rs = 28 \/ rs = 29 \/ rs = 30 \/ rs = 31) by lia.
  repeat (destruct K as [-> | K]; [vm_compute; reflexivity|]). subst rs. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_of_overlay : forall segs (M : mem) (a : Z) (bs : list byte) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> length bs = n ->
  (forall i, (i < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0))) ->
  rdn segs M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros segs M a bs n; revert M a bs; induction n as [|n IH]; intros M a bs Ha Hn Hlen HM.
  - destruct bs; [reflexivity | discriminate Hlen].
  - destruct bs as [|b bs']; [discriminate Hlen|]. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
    pose proof (HM 0%nat ltac:(lia)) as H0. cbn [nth Z.of_nat] in H0. rewrite Z.add_0_r in H0. rewrite H0.
    destruct n as [|n'].
    { destruct bs'; [reflexivity | cbn in Hlen; discriminate Hlen]. }
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) by (apply bv_eq; rewrite u_add1 by (wd_ulia); wd_ulia).
    rewrite (IH M (a + 1) bs'); [reflexivity | lia | lia | cbn in Hlen; lia |].
    intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact (HM (S i) ltac:(lia)).
Qed.

Lemma m64_cellN_val : forall segs (M : mem) (a v w : Z),
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  cellN segs M a 8 v -> m64 M a w -> w = v.
Proof.
  intros segs M a v w Ha Hn Hv C (bs & HM & Hlen & Hw).
  unfold cellN in C. rewrite (rdn_of_overlay segs M a bs 8 Ha Hn Hlen HM) in C. injection C as E.
  rewrite <- Hw, E, bytes_le_to_Z_8. unorm. reflexivity.
Qed.

Section FR.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable bt : as_boot.
  Variable HP0 : option Z -> ast -> Prop.
  #[local] Notation SG := (bt_segs bt).
  #[local] Notation IA := (bt_ia bt).
  #[local] Notation AAINVH := (fun h => AAINVP (HP0 h) bt).

  Hypothesis SEGS_wx : wx_segs_nowrap SG.
  (* [comment removed for export] *)
  Hypothesis HOFF : forall h Lc FF B C K M mdl AA, AAINVP (HP0 h) bt Lc FF B C K M mdl -> H_off_segments SG (HL mdl AA).
  (* [comment removed for export] *)
  Hypothesis FS_NOLAZY : forall st Lc FF M mdl z,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bt_fs bt + 0x1000 <= z < bt_fs bt + 0x9000 -> lzb mdl z = false.
  Hypothesis FS_PRIV : forall st Lc FF z,
    WF bt st Lc FF -> bt_fs bt + 0x1000 <= z < bt_fs bt + 0x9000 -> rt_priv IA Lc FF z.

  Lemma app_visible_frames_mono : forall Lc F1 F2 f k a,
    app_visible IA Lc (F1 ++ F2) a -> app_visible IA Lc (F1 ++ (f, k) :: F2) a.
  Proof using.
    intros Lc F1 F2 f k a V.
    assert (SUB : forall x, In x (F1 ++ F2) -> In x (F1 ++ (f, k) :: F2)).
    { intros x Hx. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx]. }
    destruct V as [V | [V | [V | [V | [V | V]]]]].
    - left. exact V.
    - right; left. destruct V as (f' & k' & Hin & R). exists f', k'. split; [apply SUB; exact Hin | exact R].
    - right; right; left. exact V.
    - right; right; right; left. destruct V as (f' & k' & Hin & R). exists f', k'. split; [apply SUB; exact Hin | exact R].
    - right; right; right; right; left. exact V.
    - right; right; right; right; right. exact V.
  Qed.

  Theorem C_fakerel_P : forall {fx : FPState}, FAKEREL SG FXOK IA AAINVH.
  Proof using FS_PRIV FS_NOLAZY HOFF SEGS_wx.
    intros fx h pc rs fx0 R M mdl Lc FF F1 F2 B C K f k flag HFX HALT AI HFF M64 FETCH Hrs Hreg Hpc0 Hpc4.
    cbv beta in AI. destruct AI as (st & W & RP & (Bd & HPst) & MW).
    assert (Hin : In (f, k) FF) by (rewrite HFF; apply in_app_iff; right; left; reflexivity).
    pose proof (fake_frame_facts bt st Lc FF W f k Hin) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & X5 & X6 & X7 & _).
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct R10 as (KH & KG & KF & KW & KWR & KT & KS).
    set (pos := fpos bt f k) in *. set (fs := bt_fs bt) in *.
    unfold FAKE_SIZE in X6, G2. unfold KMAXCLASS in G5. pose proof ceil_rng as CR.
    pose proof (flag_addr_range fs k pos ltac:(lia) G6) as FR.
    (* [comment removed for export] *)
    assert (Eflag : flag = fake_flag_addr fs k pos).
    { apply (m64_cellN_val SG M (f + FS k - 8) (fake_flag_addr fs k pos) flag); [lia | lia | lia | exact (KW f k Hin) | exact M64]. }
    (* [comment removed for export] *)
    destruct R14 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    set (Hd := HL mdl (a_aa st)).
    assert (HDflag : Hd (Z_to_bv 64 flag) = false).
    { subst Hd. apply HL_notlazy; [lia|]. apply (FS_NOLAZY st Lc FF M mdl flag W RP). lia. }
    assert (OKflag : store_ok SG M (Z_to_bv 64 flag) 1%nat = true) by (destruct (KWR flag ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end); lia)) as [_ OK]; exact OK).
    (* [comment removed for export] *)
    pose proof (decode_sb_x0 rs Hrs) as DEC. pose proof (is_ecall_sb_x0 rs Hrs) as NEC.
    assert (Hreg' : getr R (Z_to_bv 5 rs) = Z_to_bv 64 flag).
    { apply bv_eq. rewrite Hreg. unorm. reflexivity. }
    assert (STEP : RiscvSemantics.step SG (restrict Hd (mkst R (Z_to_bv 64 pc) M (seg_rom SG)))
                   = MachineOk (mkst R (v_addi (Z_to_bv 64 pc) 4) (wbytes (mrestrict Hd M) (Z_to_bv 64 flag) (word_to_le_bytes 1 (getr R (Z_to_bv 5 0)))) (seg_rom SG))).
    { rewrite restrict_mkst'.
      rewrite (step_sb SG R (Z_to_bv 64 pc) (mrestrict Hd M) (seg_rom SG) _ (Z_to_bv 5 rs) (Z_to_bv 5 0) (Z_to_bv 12 0) FETCH NEC DEC).
      - rewrite Hreg'. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi_0. reflexivity.
      - rewrite Hreg'. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi_0.
        rewrite store_ok_mrestrict; [exact OKflag | wd_ulia | unorm; intros x Hx;
          replace x with (Z_to_bv 64 flag) by (apply bv_eq; wd_ulia); exact HDflag]. }
    assert (E0 : Z_to_bv 5 0 = (0%bv : reg)) by (apply bv_eq; reflexivity). rewrite E0 in STEP. rewrite getr_zero in STEP. change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in STEP.
    (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.cfg in G in change_no_check G' end).
    apply (katD_step_acct SG Hd (HOFF h Lc FF B C K M mdl (a_aa st) (ex_intro _ st (conj W (conj RP (conj (conj Bd HPst) MW))))) SEGS_wx (a_aa st)
             (mkst R (Z_to_bv 64 pc) M (seg_rom SG)) _ mdl _ (lazy_cover_HL mdl (a_aa st)) B1 B2 HALT eq_refl STEP).
    intros mdl' MI' SBM'. rewrite unrestrict_mkst. (lazymatch goal with |- ?G => let G' := eval cbn [RiscvSemantics.ms_mem mkst] in G in change_no_check G' end).
    set (M' := wbytes M (Z_to_bv 64 flag) [Z_to_bv 8 0]).
    assert (EM : munrestrict Hd M (wbytes (mrestrict Hd M) (Z_to_bv 64 flag) [Z_to_bv 8 0]) = M').
    { rewrite wbytes_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); unorm; intros x Hx;
        replace x with (Z_to_bv 64 flag) by (apply bv_eq; wd_ulia); exact HDflag].
      apply munrestrict_mrestrict_same. intros a Ha. subst M'. rewrite MemsetLibF.MemSplit.wbytes_outside; [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia|].
      (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). destruct (Z.eq_dec (bv_unsigned a) flag) as [E|NE]; [| wd_ulia].
      exfalso. replace a with (Z_to_bv 64 flag) in Ha by (apply bv_eq; wd_ulia). rewrite HDflag in Ha. discriminate Ha. }
    rewrite EM. apply katD_refl.
    exists M', mdl'.
    assert (CHG : forall a : word, M' a <> M a -> bv_unsigned a = flag /\ M' a = Some (Z_to_bv 8 0)).
    { intros a NE. subst M'. destruct (Z.eq_dec (bv_unsigned a) flag) as [E|NE'].
      - split; [exact E|]. replace a with (Z_to_bv 64 flag) by (apply bv_eq; wd_ulia).
        rewrite MemsetLibF.MemSplit.wbytes_inside; [rewrite Z.sub_diag; reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia].
      - exfalso. apply NE. rewrite MemsetLibF.MemSplit.wbytes_outside; [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia]. }
    split; [| split; [| split]].
    - (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. reflexivity.
    - intros a NE. destruct (CHG a NE) as [E _]. split; [exact E|].
      destruct (FS_PRIV st Lc FF flag W ltac:(lia)) as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|].
      intros V. apply P3. rewrite HFF. apply app_visible_frames_mono. exact V.
    - (* [comment removed for export] *)
      exists (op_fake_release st). split; [exact (WF_fake_release bt st Lc FF F1 F2 f k W HFF)|].
      assert (RP' : Rep bt (op_fake_release st) Lc (F1 ++ F2) M' mdl).
      { apply (OPS_REP_fake_release_pf bt st Lc FF F1 F2 M M' mdl f k W RP HFF).
        - intros a NE. destruct (CHG a NE) as [E V]. split; [| rewrite V; discriminate]. rewrite E, Eflag. reflexivity.
        - (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). replace (fake_flag_addr (bt_fs bt) k (fpos bt f k)) with flag by (exact Eflag). subst M'.
          change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
          apply (rdn_wbytes_hit SG [Z_to_bv 8 0] M (Z_to_bv 64 flag)). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). unorm. pose proof ceil_rng. lia. }
      pose proof (same_but_materialized_frame mdl mdl' SBM') as F.
      destruct F as (_ & E1 & E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
      split; [| split; [split; [exact Bd | exact HPst] | exact (model_ivs_wf_sbm mdl mdl' SBM' MW)]].
      unfold op_fake_release in RP' |- *.
      destruct RP' as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
      (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end). repeat (split; [assumption|]) || idtac.
      split; [exact (rep_ledger_sbm bt st mdl mdl' SBM' Q13)|].
      split; [| exact Q15].
      destruct Q14 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end). rewrite E3. repeat (split; [assumption|]). exact C8.
    - exact SBM'.
  Qed.
End FR.
End AsRtFakeRel.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtStkMal1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation W8 w := (word_to_le_bytes 8 w).
#[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

Definition sk1_pos (hint i : Z) : Z := ((hint + i) mod 8192)%Z.
Definition sk1_flag (fs : word) (hint i : Z) : Z := (U fs + 20480 + sk1_pos hint i)%Z.
Definition sk1_frame (fs : word) (hint i : Z) : Z := (U fs + 1085440 + sk1_pos hint i * 128)%Z.
Definition sk1_sh (fs : word) (hint i : Z) : Z := (sk1_frame fs hint i / 8 + 0x7fff8000)%Z.

Definition sk1_mem4 (m : word -> option byte) (fs : word) (hint i0 : Z) (S : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (U fs + 8)) (LE8 (hint + i0 + 1)))
    (Z_to_bv 64 (sk1_flag fs hint i0)) [Z_to_bv 8 1])
    (Z_to_bv 64 (sk1_frame fs hint i0 + 24)) (W8 S))
    (Z_to_bv 64 (sk1_frame fs hint i0 + 120)) (LE8 (sk1_flag fs hint i0)).
Definition sk1_mem (m : word -> option byte) (fs : word) (hint i0 : Z) (S : word) : word -> option byte :=
  wbytes (wbytes (sk1_mem4 m fs hint i0 S) (Z_to_bv 64 (sk1_sh fs hint i0 + 0)) (LE8 0)) (Z_to_bv 64 (sk1_sh fs hint i0 + 8)) (LE8 0).

Lemma sk1_pos_rng : forall hint i, (0 <= sk1_pos hint i < 8192)%Z.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk1_pos in G in change_no_check G' end). apply Z.mod_pos_bound. lia. Qed.
Lemma v_and_mask1 : forall z, v_and (Z_to_bv 64 z) (Z_to_bv 64 8191) = Z_to_bv 64 (z mod 8192).
Proof using. intros z. exact (v_and_maskN (14 - 1) z ltac:(lia)). Qed.
Lemma sk1_sh_rng : forall (fs : word) hint i, (U fs + 2134016 <= 2 ^ 47)%Z ->
  (0x7fff8000 <= sk1_sh fs hint i /\ sk1_sh fs hint i + 16 <= 0x10007fff8000)%Z.
Proof using.
  intros fs hint i H64. pose proof (u64_range fs) as Hfr. (lazymatch goal with |- ?G => let G' := eval unfold sk1_sh, sk1_frame in G in change_no_check G' end). pose proof (sk1_pos_rng hint i) as Hp.
  pose proof (Z.div_pos (U fs + 1085440 + sk1_pos hint i * 128) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (U fs + 1085440 + sk1_pos hint i * 128) 8 (2 ^ 44 - 16) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma v_slli_s1 : forall z, (0 <= z < 2 ^ 32)%Z -> v_slli (Z_to_bv 64 z) 7 = Z_to_bv 64 (z * 128).
Proof using. intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end). rewrite u_Z2bv by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Ltac av_and F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply AsRtFlush.step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

(* [comment removed for export] *)
Definition stk1_words : list (option (bv 32)) :=
  [
   Some W_572d8; Some W_572dc; Some W_572e0; Some W_572e4; Some W_572e8; Some W_572ec; None; None; Some W_572f8;
   Some W_572fc; Some W_57300; Some W_57304; Some W_57308; Some W_5730c; Some W_57310; Some W_57314; Some W_57318;
   Some W_5731c; Some W_57320; Some W_57324; Some W_57328; Some W_5732c; Some W_57330; Some W_57334; Some W_57338;
   Some W_5733c; Some W_57340; Some W_57344; Some W_57348; Some W_5734c; Some W_57350; Some W_57354; Some W_57358;
   Some W_5735c; Some W_57360; Some W_57364; Some W_57368; Some W_5736c; Some W_57370; Some W_57374; Some W_57378;
   Some W_5737c; Some W_57380; Some W_57384; Some W_57388; Some W_5738c; None; None; Some W_57398; Some W_5739c;
   Some W_573a0; Some W_573a4; Some W_573a8; Some W_573ac; Some W_573b0; Some W_573b4; Some W_573b8; Some W_573bc;
   Some W_573c0; Some W_573c4; Some W_573c8; Some W_573cc; Some W_573d0; Some W_573d4; Some W_573d8; Some W_573dc;
   Some W_573e0; Some W_573e4; Some W_573e8; Some W_573ec; Some W_573f0; Some W_573f4; Some W_573f8; Some W_573fc;
   Some W_57400; Some W_57404; Some W_57408; Some W_5740c; Some W_57410; Some W_57414; Some W_57418; Some W_5741c;
   Some W_57420; Some W_57424; Some W_57428; Some W_5742c; Some W_57430; Some W_57434; Some W_57438; Some W_5743c;
   Some W_57440; Some W_57444; Some W_57448; Some W_5744c; Some W_57450; Some W_57454; Some W_57458; Some W_5745c;
   Some W_57460; Some W_57464
  ]%list.

Section STKB.
  Variables (segs : list Segment) (sb : word).
  Variable mt : m2s_tab.
  Hypothesis HC_S : code_ato segs sb 0 stk1_words.
  Hypothesis MTOK : m2s_tab_ok segs mt.
  Hypothesis MTB : mt_base mt = at_ sb 1240.
  Hypothesis Hsb : (U sb mod 2 = 0)%Z /\ (U sb + 30000 < 2 ^ 64)%Z.


  Lemma F_572d8 : fetch_word segs (at_ sb 0) = Some W_572d8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 0 _ HC_S eq_refl). Qed.
  Lemma F_572dc : fetch_word segs (at_ sb 4) = Some W_572dc.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 1 _ HC_S eq_refl). Qed.
  Lemma F_572e0 : fetch_word segs (at_ sb 8) = Some W_572e0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 2 _ HC_S eq_refl). Qed.
  Lemma F_572e4 : fetch_word segs (at_ sb 12) = Some W_572e4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 3 _ HC_S eq_refl). Qed.
  Lemma F_572e8 : fetch_word segs (at_ sb 16) = Some W_572e8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 4 _ HC_S eq_refl). Qed.
  Lemma F_572ec : fetch_word segs (at_ sb 20) = Some W_572ec.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 5 _ HC_S eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma F_572f8 : fetch_word segs (at_ sb 32) = Some W_572f8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 8 _ HC_S eq_refl). Qed.
  Lemma F_572fc : fetch_word segs (at_ sb 36) = Some W_572fc.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 9 _ HC_S eq_refl). Qed.
  Lemma F_57300 : fetch_word segs (at_ sb 40) = Some W_57300.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 10 _ HC_S eq_refl). Qed.
  Lemma F_57304 : fetch_word segs (at_ sb 44) = Some W_57304.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 11 _ HC_S eq_refl). Qed.
  Lemma F_57308 : fetch_word segs (at_ sb 48) = Some W_57308.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 12 _ HC_S eq_refl). Qed.
  Lemma F_5730c : fetch_word segs (at_ sb 52) = Some W_5730c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 13 _ HC_S eq_refl). Qed.



  Lemma F_5731c : fetch_word segs (at_ sb 68) = Some W_5731c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 17 _ HC_S eq_refl). Qed.
  Lemma F_57320 : fetch_word segs (at_ sb 72) = Some W_57320.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 18 _ HC_S eq_refl). Qed.
  Lemma F_57324 : fetch_word segs (at_ sb 76) = Some W_57324.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 19 _ HC_S eq_refl). Qed.
  Lemma F_57328 : fetch_word segs (at_ sb 80) = Some W_57328.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 20 _ HC_S eq_refl). Qed.
  Lemma F_5732c : fetch_word segs (at_ sb 84) = Some W_5732c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 21 _ HC_S eq_refl). Qed.
  Lemma F_57330 : fetch_word segs (at_ sb 88) = Some W_57330.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 22 _ HC_S eq_refl). Qed.
  Lemma F_57334 : fetch_word segs (at_ sb 92) = Some W_57334.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 23 _ HC_S eq_refl). Qed.
  Lemma F_57338 : fetch_word segs (at_ sb 96) = Some W_57338.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 24 _ HC_S eq_refl). Qed.
  Lemma F_5733c : fetch_word segs (at_ sb 100) = Some W_5733c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 25 _ HC_S eq_refl). Qed.
  Lemma F_57340 : fetch_word segs (at_ sb 104) = Some W_57340.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 26 _ HC_S eq_refl). Qed.
  Lemma F_57344 : fetch_word segs (at_ sb 108) = Some W_57344.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 27 _ HC_S eq_refl). Qed.
  Lemma F_57348 : fetch_word segs (at_ sb 112) = Some W_57348.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 28 _ HC_S eq_refl). Qed.
  Lemma F_5734c : fetch_word segs (at_ sb 116) = Some W_5734c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 29 _ HC_S eq_refl). Qed.
  Lemma F_57350 : fetch_word segs (at_ sb 120) = Some W_57350.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 30 _ HC_S eq_refl). Qed.
  Lemma F_57354 : fetch_word segs (at_ sb 124) = Some W_57354.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 31 _ HC_S eq_refl). Qed.
  Lemma F_57358 : fetch_word segs (at_ sb 128) = Some W_57358.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 32 _ HC_S eq_refl). Qed.
  Lemma F_5735c : fetch_word segs (at_ sb 132) = Some W_5735c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 33 _ HC_S eq_refl). Qed.
  Lemma F_57360 : fetch_word segs (at_ sb 136) = Some W_57360.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 34 _ HC_S eq_refl). Qed.
  Lemma F_57364 : fetch_word segs (at_ sb 140) = Some W_57364.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 35 _ HC_S eq_refl). Qed.
  Lemma F_57368 : fetch_word segs (at_ sb 144) = Some W_57368.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 36 _ HC_S eq_refl). Qed.
  Lemma F_5736c : fetch_word segs (at_ sb 148) = Some W_5736c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 37 _ HC_S eq_refl). Qed.
  Lemma F_57370 : fetch_word segs (at_ sb 152) = Some W_57370.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 38 _ HC_S eq_refl). Qed.
  Lemma F_57374 : fetch_word segs (at_ sb 156) = Some W_57374.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 39 _ HC_S eq_refl). Qed.
  Lemma F_57378 : fetch_word segs (at_ sb 160) = Some W_57378.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 40 _ HC_S eq_refl). Qed.
  Lemma F_5737c : fetch_word segs (at_ sb 164) = Some W_5737c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 41 _ HC_S eq_refl). Qed.
  Lemma F_57380 : fetch_word segs (at_ sb 168) = Some W_57380.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 42 _ HC_S eq_refl). Qed.
  Lemma F_57384 : fetch_word segs (at_ sb 172) = Some W_57384.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 43 _ HC_S eq_refl). Qed.





















  Lemma F_573e4 : fetch_word segs (at_ sb 268) = Some W_573e4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 67 _ HC_S eq_refl). Qed.
  Lemma F_573e8 : fetch_word segs (at_ sb 272) = Some W_573e8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 68 _ HC_S eq_refl). Qed.
  Lemma F_573ec : fetch_word segs (at_ sb 276) = Some W_573ec.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 69 _ HC_S eq_refl). Qed.
  Lemma F_573f0 : fetch_word segs (at_ sb 280) = Some W_573f0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 70 _ HC_S eq_refl). Qed.
  Lemma F_573f4 : fetch_word segs (at_ sb 284) = Some W_573f4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 71 _ HC_S eq_refl). Qed.
  Lemma F_573f8 : fetch_word segs (at_ sb 288) = Some W_573f8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 72 _ HC_S eq_refl). Qed.
  Lemma F_573fc : fetch_word segs (at_ sb 292) = Some W_573fc.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 73 _ HC_S eq_refl). Qed.
  Lemma F_57400 : fetch_word segs (at_ sb 296) = Some W_57400.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 74 _ HC_S eq_refl). Qed.
  Lemma F_57404 : fetch_word segs (at_ sb 300) = Some W_57404.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 75 _ HC_S eq_refl). Qed.
  Lemma F_57408 : fetch_word segs (at_ sb 304) = Some W_57408.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 76 _ HC_S eq_refl). Qed.
  Lemma F_5740c : fetch_word segs (at_ sb 308) = Some W_5740c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 77 _ HC_S eq_refl). Qed.
  Lemma F_57410 : fetch_word segs (at_ sb 312) = Some W_57410.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 78 _ HC_S eq_refl). Qed.
  Lemma F_57414 : fetch_word segs (at_ sb 316) = Some W_57414.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 79 _ HC_S eq_refl). Qed.
  Lemma F_57418 : fetch_word segs (at_ sb 320) = Some W_57418.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 80 _ HC_S eq_refl). Qed.
  Lemma F_5741c : fetch_word segs (at_ sb 324) = Some W_5741c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 81 _ HC_S eq_refl). Qed.
  Lemma F_57420 : fetch_word segs (at_ sb 328) = Some W_57420.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 82 _ HC_S eq_refl). Qed.
  Lemma F_57424 : fetch_word segs (at_ sb 332) = Some W_57424.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 83 _ HC_S eq_refl). Qed.
  Lemma F_57428 : fetch_word segs (at_ sb 336) = Some W_57428.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 84 _ HC_S eq_refl). Qed.
  Lemma F_5742c : fetch_word segs (at_ sb 340) = Some W_5742c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 85 _ HC_S eq_refl). Qed.
  Lemma F_57430 : fetch_word segs (at_ sb 344) = Some W_57430.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 86 _ HC_S eq_refl). Qed.
  Lemma F_57434 : fetch_word segs (at_ sb 348) = Some W_57434.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 87 _ HC_S eq_refl). Qed.
  Lemma F_57438 : fetch_word segs (at_ sb 352) = Some W_57438.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 88 _ HC_S eq_refl). Qed.
  Lemma F_5743c : fetch_word segs (at_ sb 356) = Some W_5743c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 89 _ HC_S eq_refl). Qed.
  Lemma F_57440 : fetch_word segs (at_ sb 360) = Some W_57440.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 90 _ HC_S eq_refl). Qed.
  Lemma F_57444 : fetch_word segs (at_ sb 364) = Some W_57444.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 91 _ HC_S eq_refl). Qed.
  Lemma F_57448 : fetch_word segs (at_ sb 368) = Some W_57448.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk1_words 92 _ HC_S eq_refl). Qed.








  Variable m : word -> option byte.
  Variable rom : word -> option byte.
  Variables (ra S resw fs midend s0v s1v s2v : word).
  Variables (hint i0 : Z).
  #[local] Abbreviation FLG := (sk1_flag fs hint i0).
  #[local] Abbreviation FRM := (sk1_frame fs hint i0).
  #[local] Abbreviation SHW := (sk1_sh fs hint i0).
  Hypothesis Rfs : rdn segs m (Z_to_bv 64 (U resw)) 8 = Some (W8 fs).
  Hypothesis Rgc : rdn segs m (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlog : rdn segs m (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20).
  Hypothesis Rhint : rdn segs m (Z_to_bv 64 (U fs + 8)) 8 = Some (LE8 hint).
  Hypothesis Hnz : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs m (Z_to_bv 64 (sk1_flag fs hint j)) 1 = Some [b] /\ U b <> 0%Z.
  Hypothesis Hz : rdn segs m (Z_to_bv 64 FLG) 1 = Some [Z_to_bv 8 0].
  Hypothesis OKh : store_ok segs m (Z_to_bv 64 (U fs + 8)) 8 = true.
  Hypothesis OKf : store_ok segs m (Z_to_bv 64 FLG) 1 = true.
  Hypothesis OK24 : store_ok segs m (Z_to_bv 64 (FRM + 24)) 8 = true.
  Hypothesis OKl : store_ok segs m (Z_to_bv 64 (FRM + 120)) 8 = true.
  Hypothesis OKsh : store_ok segs m (Z_to_bv 64 SHW) 16 = true.
  Hypothesis PHm : m2sH segs mt m (Z_to_bv 64 FRM) midend.
  Hypothesis Hmcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells mt).
  Hypothesis FR1 : rdn segs m (at_ S (-8)) 8 = Some (W8 ra).
  Hypothesis FR2 : rdn segs m (at_ S (-16)) 8 = Some (W8 s0v).
  Hypothesis FR3 : rdn segs m (at_ S (-24)) 8 = Some (W8 s1v).
  Hypothesis FR4 : rdn segs m (at_ S (-32)) 8 = Some (W8 s2v).
  Hypothesis Hfs : (0 < U fs /\ U fs + 2134016 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 2134016 <= U S - 32)%Z.
  Hypothesis Hfsnz : (U fs <> 0)%Z.
  Hypothesis Hhint : (0 <= hint)%Z.
  Hypothesis Hi0 : (0 <= i0 < 8192)%Z.
  Hypothesis HS : (32 <= U S)%Z.
  Hypothesis Hret : ret_ok ra.

  Ltac addr_eq :=
    apply bv_eq; rewrite ?v_addi_0;
    repeat match goal with |- context [v_addi ?b ?e] => change (v_addi b e) with (at_ b e) end;
    (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  Ltac rdm Hr :=
    repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]);
    lazymatch goal with |- rdn _ m _ _ = _ => exact Hr end.
  Ltac cldz F D cc vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 cc : word) by addr_eq end;
          rdm Hr
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Ltac clbu F D cc Hr :=
    chain_step; [reflexivity
      | eapply step_lbu; [exact F | reflexivity | exact D | ];
        gres; rwH; imm_norm;
        lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 cc : word) by addr_eq end;
        rdm Hr
      | step_simpl]; vn.

  Definition LCLOB1 : list reg := [5; 10; 12; 15; 17]%list.

  Lemma sk1_iter : forall (i : Z) r,
    (0 <= i < i0)%Z ->
    getr r 10 = Z_to_bv 64 (8192 - i) -> getr r 12 = Z_to_bv 64 (hint + i) ->
    getr r 13 = Z_to_bv 64 (U fs + 20480) -> getr r 14 = Z_to_bv 64 8191 ->
    exists r',
      msteps segs (mkst r (at_ sb 148) m rom) (mkst r' (at_ sb 148) m rom)
      /\ getr r' 10 = Z_to_bv 64 (8192 - (i + 1)) /\ getr r' 12 = Z_to_bv 64 (hint + (i + 1))
      /\ regs_agree (fun x => In x LCLOB1) r r'.
  Proof using Hi0 Hhint Hfsnz Hfs Hnz S HC_S.
    intros i r Hi Q10 Q12 Q13 Q14. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk1_pos_rng hint i) as Hp.
    destruct (Hnz i Hi) as (b & Rb & Nb). pose proof (u8_range b) as Hb8.
    wd_eexists. split.
    - av_and F_5736c D_5736c (Z_to_bv 64 (sk1_pos hint i)) ltac:(rewrite v_and_mask1; reflexivity).
      av F_57370 D_57370 (Z_to_bv 64 (sk1_flag fs hint i)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, sk1_flag in G in change_no_check G' end); unorm; f_equal; lia).
      clbu F_57374 D_57374 (sk1_flag fs hint i) Rb.
      ab_ft F_57378 D_57378 ltac:(condz).
      av F_5737c D_5737c (Z_to_bv 64 (8192 - (i + 1))) ltac:(rewrite v_addiw_m1 by lia; f_equal; lia).
      av F_57380 D_57380 (Z_to_bv 64 (hint + (i + 1))) ltac:(rewrite v_addi_Z; f_equal; lia).
      ab_tk F_57384 D_57384 ltac:(condz).
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold LCLOB1 in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma sk1_loop : forall (n : nat) (i : Z) r,
    (0 <= i)%Z -> (i + Z.of_nat n = i0)%Z ->
    getr r 10 = Z_to_bv 64 (8192 - i) -> getr r 12 = Z_to_bv 64 (hint + i) ->
    getr r 13 = Z_to_bv 64 (U fs + 20480) -> getr r 14 = Z_to_bv 64 8191 ->
    exists r',
      msteps segs (mkst r (at_ sb 148) m rom) (mkst r' (at_ sb 268) m rom)
      /\ getr r' 12 = Z_to_bv 64 (hint + i0) /\ getr r' 15 = Z_to_bv 64 FLG /\ getr r' 17 = Z_to_bv 64 (sk1_pos hint i0)
      /\ regs_agree (fun x => In x LCLOB1) r r'.
  Proof using Hi0 Hhint Hfsnz Hfs Hz Hnz S HC_S.
    induction n as [|n IH]; intros i r Hi0' Hin Q10 Q12 Q13 Q14.
    - assert (i = i0) by lia. subst i. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
      pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk1_pos_rng hint i0) as Hp.
      wd_eexists. split.
      + av_and F_5736c D_5736c (Z_to_bv 64 (sk1_pos hint i0)) ltac:(rewrite v_and_mask1; reflexivity).
        av F_57370 D_57370 (Z_to_bv 64 FLG) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, sk1_flag in G in change_no_check G' end); unorm; f_equal; lia).
        clbu F_57374 D_57374 (sk1_flag fs hint i0) Hz.
        ab_tk F_57378 D_57378 ltac:(vals_lit; condz).
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold LCLOB1 in G in change_no_check G' end). ra_solve.
    - destruct (sk1_iter i r ltac:(lia) Q10 Q12 Q13 Q14) as (r1 & RUN1 & A10 & A12 & AG1).
      assert (A13 : getr r1 13 = Z_to_bv 64 (U fs + 20480)) by (rewrite (AG1 13 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB1 in G in change_no_check G' end); notin)); exact Q13).
      assert (A14 : getr r1 14 = Z_to_bv 64 8191) by (rewrite (AG1 14 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB1 in G in change_no_check G' end); notin)); exact Q14).
      destruct (IH (i + 1)%Z r1 ltac:(lia) ltac:(lia) A10 A12 A13 A14) as (r' & RUN2 & B12 & B15 & B17 & AG2).
      exists r'. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. repeat (split; [assumption|]).
      eapply regs_agree_trans; eassumption.
  Qed.

  Ltac wsd F D cc OKT :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := Z_to_bv 64 cc);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; addr_eq
        | gres; rwH; reflexivity
        | (lazymatch goal with |- ?G => let G' := eval unfold sk1_mem4 in G in change_no_check G' end); repeat (eapply store_ok_mono; [apply wbytes_grows|]); OKT ]
      | step_simpl]; vn.
  Ltac fldm F D vv FR :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold sk1_mem, sk1_mem4 in G in change_no_check G' end);
          repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]); exact FR
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  Definition S2CLOB1 : list reg := [9; 18; 10; 11; 12; 13; 14; 15; 16]%list.

  Lemma blkS2 : forall r2,
    getr r2 10 = resw -> getr r2 2 = at_ S (-32) -> getr r2 8 = S ->
    exists r,
      msteps segs (mkst r2 (at_ sb 36) m rom) (mkst r (at_ sb 148) m rom)
      /\ getr r 10 = Z_to_bv 64 (8192 - 0) /\ getr r 12 = Z_to_bv 64 (hint + 0)
      /\ getr r 13 = Z_to_bv 64 (U fs + 20480) /\ getr r 14 = Z_to_bv 64 8191
      /\ getr r 11 = Z_to_bv 64 (U fs + 4096)
      /\ getr r 9 = fs /\ getr r 18 = Z_to_bv 64 20 /\ getr r 2 = at_ S (-32) /\ getr r 8 = S
      /\ regs_agree (fun x => In x S2CLOB1) r2 r.
  Proof using Hhint Hfsnz Hfs Rhint Rlog Rgc Rfs HC_S.
    intros r2 Q10 Q2 Q8. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (u64_range resw) as Hrr.
    wd_eexists. split.
    - cldz F_572fc D_572fc (U resw) fs Rfs.
      ab_ft F_57300 D_57300 ltac:(condz).
      clbu F_57304 D_57304 (U fs + 96)%Z Rgc.
      cldz F_57308 D_57308 (U fs + 88)%Z (Z_to_bv 64 20) Rlog.
      ab_tk F_5730c D_5730c ltac:(vals_lit; condz).
      an F_5731c D_5731c. an F_57320 D_57320. an F_57324 D_57324. an F_57328 D_57328.
      ab_ft F_5732c D_5732c ltac:(vm_compute; reflexivity).
      an F_57330 D_57330. an F_57334 D_57334. an F_57338 D_57338. an F_5733c D_5733c. an F_57340 D_57340.
      cldz F_57344 D_57344 (U fs + 8)%Z (Z_to_bv 64 hint) Rhint.
      an F_57348 D_57348. an F_5734c D_5734c.
      av F_57350 D_57350 (Z_to_bv 64 (U fs + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).
      av F_57354 D_57354 (Z_to_bv 64 (U fs + 20480)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).
      an F_57358 D_57358. an F_5735c D_5735c. an F_57360 D_57360.
      av F_57364 D_57364 (Z_to_bv 64 (hint + 8191)) ltac:(rewrite v_add_ZZ; reflexivity).
      av F_57368 D_57368 (Z_to_bv 64 (hint + 8192)) ltac:(rewrite v_addi_Z; f_equal; lia).
      wd_refl.
    - post; try (apply bv_eq; vm_compute; reflexivity). (lazymatch goal with |- ?G => let G' := eval unfold S2CLOB1 in G in change_no_check G' end). ra_solve.
  Qed.

  Definition S3CLOB1 : list reg := [1; 9; 10; 11; 12; 13; 17]%list.

  Lemma blkS3 : forall r4,
    getr r4 12 = Z_to_bv 64 (hint + i0) -> getr r4 15 = Z_to_bv 64 FLG -> getr r4 17 = Z_to_bv 64 (sk1_pos hint i0) ->
    getr r4 11 = Z_to_bv 64 (U fs + 4096) -> getr r4 9 = fs -> getr r4 18 = Z_to_bv 64 20 -> getr r4 8 = S -> getr r4 2 = at_ S (-32) ->
    exists r,
      msteps segs (mkst r4 (at_ sb 268) m rom) (mkst r (at_ sb 1240) (sk1_mem4 m fs hint i0 S) rom)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = at_ sb 328 /\ getr r 9 = Z_to_bv 64 FRM /\ getr r 2 = at_ S (-32)
      /\ regs_agree (fun x => In x S3CLOB1) r4 r.
  Proof using Hhint Hfsnz Hfs OKl OK24 OKf OKh HC_S.
    intros r4 Q12 Q15 Q17 Q11 Q9 Q18 Q8 Q2. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk1_pos_rng hint i0) as Hp.
    assert (HFL : (U fs + 20480 <= FLG < U fs + 28672)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk1_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 1085440 <= FRM /\ FRM + 128 <= U fs + 2134016)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk1_frame in G in change_no_check G' end); lia).
    wd_eexists. split.
    - av F_573e4 D_573e4 (Z_to_bv 64 (hint + i0 + 1)) ltac:(rewrite v_addi_Z; reflexivity).
      an F_573e8 D_573e8. an F_573ec D_573ec.
      av F_573f0 D_573f0 (Z_to_bv 64 (sk1_pos hint i0 * 128)) ltac:(rewrite v_slli_s1 by lia; reflexivity).
      wsd F_573f4 D_573f4 (U fs + 8)%Z ltac:(exact OKh).
      chain_step; [reflexivity
        | eapply step_sb_at with (a := Z_to_bv 64 FLG) (v := Z_to_bv 64 1) (b := Z_to_bv 8 1);
          [exact F_573f8 | reflexivity | exact D_573f8
          | gres; rwH; imm_norm; addr_eq
          | gres; rwH; reflexivity
          | apply bv_eq; vm_compute; reflexivity
          | repeat (eapply store_ok_mono; [apply wbytes_grows|]); exact OKf ]
        | step_simpl]; vn.
      an F_573fc D_573fc. an F_57400 D_57400.
      av F_57404 D_57404 (Z_to_bv 64 (U fs + 36864)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).
      av F_57408 D_57408 (Z_to_bv 64 (1048576 + sk1_pos hint i0 * 128)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).
      av F_5740c D_5740c (Z_to_bv 64 FRM) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, sk1_frame in G in change_no_check G' end); unorm; f_equal; lia).
      wsd F_57410 D_57410 (FRM + 24)%Z ltac:(exact OK24).
      wsd F_57414 D_57414 (FRM + 120)%Z ltac:(exact OKl).
      change (wbytes (wbytes (wbytes (wbytes m _ _) _ _) _ _) _ _) with (sk1_mem4 m fs hint i0 S).
      an F_57418 D_57418. an F_5741c D_5741c.
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold S3CLOB1 in G in change_no_check G' end). ra_solve.
  Qed.

  Definition S4CLOB1 : list reg := [1; 2; 8; 9; 18; 10; 11; 12]%list.

  Lemma blkS4 : forall r6,
    getr r6 10 = Z_to_bv 64 SHW -> getr r6 9 = Z_to_bv 64 FRM -> getr r6 2 = at_ S (-32) ->
    exists r,
      msteps segs (mkst r6 (at_ sb 328) (sk1_mem4 m fs hint i0 S) rom) (mkst r ra (sk1_mem m fs hint i0 S) rom)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = ra /\ getr r 2 = S /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ regs_agree (fun x => In x S4CLOB1) r6 r.
  Proof using Hret Hhint Hfsnz Hfs FR4 FR3 FR2 FR1 OKsh HC_S.
    intros r6 Q10 Q9 Q2. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk1_pos_rng hint i0) as Hp.
    assert (HFL : (U fs + 20480 <= FLG < U fs + 28672)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk1_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 1085440 <= FRM /\ FRM + 128 <= U fs + 2134016)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk1_frame in G in change_no_check G' end); lia).
    pose proof (sk1_sh_rng fs hint i0 ltac:(lia)) as HSH.
    assert (OKS : forall j, (0 <= j)%Z -> (j + 8 <= 16)%Z -> store_ok segs m (Z_to_bv 64 (SHW + j)) 8 = true).
    { intros j Hj0 Hj1. eapply (store_ok_sub segs m (Z_to_bv 64 SHW) _ 16); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | exact OKsh | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ] | rewrite !u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia]. }
    wd_eexists. split.
    - an F_57420 D_57420. an F_57424 D_57424. an F_57428 D_57428.
      wsd F_5742c D_5742c (sk1_sh fs hint i0 + 0)%Z ltac:(apply OKS; lia).
      wsd F_57430 D_57430 (sk1_sh fs hint i0 + 8)%Z ltac:(apply OKS; lia).
      change (wbytes (wbytes (sk1_mem4 m fs hint i0 S) _ _) _ _) with (sk1_mem m fs hint i0 S).
      fldm F_57434 D_57434 ra FR1.
      fldm F_57438 D_57438 s0v FR2.
      fldm F_5743c D_5743c s1v FR3.
      fldm F_57440 D_57440 s2v FR4.
      an F_57444 D_57444.
      aret F_57448 D_57448 ra.
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold S4CLOB1 in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma PH4 : m2sH segs mt (sk1_mem4 m fs hint i0 S) (Z_to_bv 64 FRM) midend.
  Proof using Hfsnz Hfs Hmcells PHm sb.
    destruct Hfs as [Hf0 Hf1]. pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk1_pos_rng hint i0) as Hp.
    assert (HFL : (U fs + 20480 <= FLG < U fs + 28672)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk1_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 1085440 <= FRM /\ FRM + 128 <= U fs + 2134016)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk1_frame in G in change_no_check G' end); lia).
    pose proof Hmcells as HC. unfold m2s_cells in HC.
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
    destruct PHm as [R1 R2 R3 R4 R5 R6 R7 R8 HCx Hlo Hhi].
    constructor; try assumption; (lazymatch goal with |- ?G => let G' := eval unfold sk1_mem4 in G in change_no_check G' end);
      (repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ])); assumption.
  Qed.

  Definition SBCLOB1 : list reg := [1; 2; 5; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list.
  Lemma SB_sub2 : forall x : reg, In x S2CLOB1 -> In x SBCLOB1. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold S2CLOB1, SBCLOB1 in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_subL : forall x : reg, In x LCLOB1 -> In x SBCLOB1. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold LCLOB1, SBCLOB1 in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_sub3 : forall x : reg, In x S3CLOB1 -> In x SBCLOB1. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold S3CLOB1, SBCLOB1 in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_subM : forall x : reg, In x m2s_clob -> In x SBCLOB1. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold m2s_clob, SBCLOB1 in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_sub4 : forall x : reg, In x S4CLOB1 -> In x SBCLOB1. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold S4CLOB1, SBCLOB1 in G in change_no_check G' end). incl_lists. Qed.

  Theorem stkB_run : forall r2,
    getr r2 10 = resw -> getr r2 2 = at_ S (-32) -> getr r2 8 = S ->
    exists r,
      msteps segs (mkst r2 (at_ sb 36) m rom) (mkst r ra (sk1_mem m fs hint i0 S) rom)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = ra /\ getr r 2 = S /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ regs_agree (fun x => In x SBCLOB1) r2 r.
  Proof using Hret Hi0 Hhint Hfsnz Hfs FR4 FR3 FR2 FR1 Hmcells PHm OKsh OKl OK24 OKf OKh Hz Hnz Rhint Rlog Rgc Rfs midend Hsb MTB MTOK HC_S mt.
    intros r2 Q10 Q2 Q8. destruct Hsb as [Hb2 Hb64]. pose proof (u64_range sb) as Hsbr.
    assert (RTM : ret_ok (at_ sb 328)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    destruct (blkS2 r2 Q10 Q2 Q8) as (r3 & RUN3 & A10 & A12 & A13 & A14 & A11 & A9 & A18 & A2 & A8 & AG3).
    destruct (sk1_loop (Z.to_nat i0) 0%Z r3 ltac:(lia) ltac:(lia) A10 A12 A13 A14) as (r4 & RUN4 & B12 & B15 & B17 & AG4).
    assert (B11 : getr r4 11 = Z_to_bv 64 (U fs + 4096)) by (rewrite (AG4 11 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB1 in G in change_no_check G' end); notin)); exact A11).
    assert (B9 : getr r4 9 = fs) by (rewrite (AG4 9 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB1 in G in change_no_check G' end); notin)); exact A9).
    assert (B18 : getr r4 18 = Z_to_bv 64 20) by (rewrite (AG4 18 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB1 in G in change_no_check G' end); notin)); exact A18).
    assert (B8 : getr r4 8 = S) by (rewrite (AG4 8 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB1 in G in change_no_check G' end); notin)); exact A8).
    assert (B2 : getr r4 2 = at_ S (-32)) by (rewrite (AG4 2 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB1 in G in change_no_check G' end); notin)); exact A2).
    destruct (blkS3 r4 B12 B15 B17 B11 B9 B18 B8 B2) as (r5 & RUN5 & C10 & C1 & C9 & C2 & AG5).
    destruct (m2s_run segs mt MTOK (sk1_mem4 m fs hint i0 S) rom (Z_to_bv 64 FRM) midend (at_ sb 328) r5 PH4 C10 C1 RTM)
      as (r6 & RUN6 & D10 & AG6).
    assert (UF : U (Z_to_bv 64 FRM) = FRM).
    { destruct Hfs as [Hf0 Hf1]. pose proof (u64_range fs). pose proof (u64_range S). pose proof (sk1_pos_rng hint i0). (lazymatch goal with |- ?G => let G' := eval unfold sk1_frame in G in change_no_check G' end). rewrite u_Z2bv; lia. }
    rewrite UF in D10. change (Z_to_bv 64 (FRM / 8 + 2147450880)) with (Z_to_bv 64 SHW) in D10.
    assert (D9 : getr r6 9 = Z_to_bv 64 FRM) by (rewrite (AG6 9 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact C9).
    assert (D2 : getr r6 2 = at_ S (-32)) by (rewrite (AG6 2 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact C2).
    destruct (blkS4 r6 D10 D9 D2) as (r7 & RUN7 & E10 & E1 & E2 & E8 & E9 & E18 & AG7).
    exists r7. split.
    - rewrite MTB in RUN6.
      eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|].
      eapply msteps_trans; [exact RUN6 | exact RUN7].
    - repeat (split; [assumption|]).
      eapply regs_agree_trans; [eapply regs_agree_trans; [eapply regs_agree_trans; [eapply regs_agree_trans|]|]|].
      + exact (regs_agree_mono _ _ _ _ SB_sub2 AG3).
      + exact (regs_agree_mono _ _ _ _ SB_subL AG4).
      + exact (regs_agree_mono _ _ _ _ SB_sub3 AG5).
      + exact (regs_agree_mono _ _ _ _ SB_subM AG6).
      + exact (regs_agree_mono _ _ _ _ SB_sub4 AG7).
  Qed.
End STKB.

Section STK.
  Variables (segs : list Segment) (sb : word).
  Variable tg : tlsga_tab.
  Variable mt : m2s_tab.
  Variable c_arg : word.
  Hypothesis HC_S : code_ato segs sb 0 stk1_words.
  Hypothesis TGOK : tlsga_tab_ok segs tg.
  Hypothesis TGHB : tg_hb tg = at_ sb 21076.
  Hypothesis MTOK : m2s_tab_ok segs mt.
  Hypothesis MTB : mt_base mt = at_ sb 1240.
  Hypothesis A24 : gaddr2 segs sb 24 10 10 c_arg.
  Hypothesis Hsb : (U sb mod 2 = 0)%Z /\ (U sb + 30000 < 2 ^ 64)%Z.

  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables (ra S fs midend : word).
  Variable v : tlsga_vals.
  Variables (hint i0 : Z).
  #[local] Abbreviation FLG := (sk1_flag fs hint i0).
  #[local] Abbreviation FRM := (sk1_frame fs hint i0).
  #[local] Abbreviation SHW := (sk1_sh fs hint i0).
  Hypothesis TGH : tlsgaH segs tg mem (at_ S (-32)) v.
  Hypothesis Harg : tv_arg v = c_arg.
  Hypothesis Rfs : rdn segs mem (Z_to_bv 64 (U (tg_res v))) 8 = Some (W8 fs).
  Hypothesis Hres : (U (tg_res v) + 8 <= U S - 208)%Z.
  Hypothesis Rgc : rdn segs mem (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlog : rdn segs mem (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20).
  Hypothesis Rhint : rdn segs mem (Z_to_bv 64 (U fs + 8)) 8 = Some (LE8 hint).
  Hypothesis Hnz : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs mem (Z_to_bv 64 (sk1_flag fs hint j)) 1 = Some [b] /\ U b <> 0%Z.
  Hypothesis Hz : rdn segs mem (Z_to_bv 64 FLG) 1 = Some [Z_to_bv 8 0].
  Hypothesis OKh : store_ok segs mem (Z_to_bv 64 (U fs + 8)) 8 = true.
  Hypothesis OKf : store_ok segs mem (Z_to_bv 64 FLG) 1 = true.
  Hypothesis OK24 : store_ok segs mem (Z_to_bv 64 (FRM + 24)) 8 = true.
  Hypothesis OKl : store_ok segs mem (Z_to_bv 64 (FRM + 120)) 8 = true.
  Hypothesis OKsh : store_ok segs mem (Z_to_bv 64 SHW) 16 = true.
  Hypothesis PH : m2sH segs mt mem (Z_to_bv 64 FRM) midend.
  Hypothesis Hmcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells mt).
  Hypothesis Hfs : (0 < U fs /\ U fs + 2134016 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 2134016 <= U S - 208)%Z.
  Hypothesis Hhint : (0 <= hint)%Z.
  Hypothesis Hi0 : (0 <= i0 < 8192)%Z.
  Hypothesis HS : (208 <= U S)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ S (-32)) 32 = true.
  Hypothesis Hret : ret_ok ra.

  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = S.
  Hypothesis H4 : getr regs 4 = tv_tp v.

  #[local] Abbreviation M1 := (fl_frame mem S ra (getr regs 8) (getr regs 9) (getr regs 18)).

  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ S (-32)) _ 32);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.

  Lemma blkS1 :
    exists r,
      msteps segs (mkst regs (at_ sb 0) mem rom) (mkst r (at_ sb 21076) M1 rom)
      /\ getr r 10 = c_arg /\ getr r 1 = at_ sb 36 /\ getr r 2 = at_ S (-32) /\ getr r 8 = S /\ getr r 4 = tv_tp v
      /\ regs_agree (fun x => In x [1; 2; 8; 10]%list) regs r.
  Proof using H4 H2 H1 Hstk Hfs fs Hsb A24 HC_S.
    pose proof (u64_range S) as HSr. destruct Hsb as [Hb2 Hb64]. destruct A24 as [x24 AX].
    wd_eexists. split.
    - an (F_572d8 segs sb HC_S) D_572d8.
      fsd (F_572dc segs sb HC_S) D_572dc (at_ S (-8)).
      fsd (F_572e0 segs sb HC_S) D_572e0 (at_ S (-16)).
      fsd (F_572e4 segs sb HC_S) D_572e4 (at_ S (-24)).
      fsd (F_572e8 segs sb HC_S) D_572e8 (at_ S (-32)).
      change (wbytes _ _ _) with M1.
      an (F_572ec segs sb HC_S) D_572ec.
      eapply msteps_trans; [eapply AX|]; zlit_at.
      an (F_572f8 segs sb HC_S) D_572f8.
      wd_refl.
    - post; rewrite ?at_0; try reflexivity. ra_solve.
  Qed.

  Theorem stk1_run :
    exists r Mj,
      msteps segs (mkst regs (at_ sb 0) mem rom) (mkst r ra (sk1_mem Mj fs hint i0 S) rom)
      /\ scr_rel mem Mj (U S - 208) (U S)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = ra /\ getr r 2 = S
      /\ regs_agree (fun x => In x m2s_clob) regs r.
  Proof using H4 H2 H1 Hret Hstk Hi0 Hhint Hfs Hmcells PH OKsh OKl OK24 OKf OKh Hz Hnz Rhint Rlog Rgc Hres Rfs Harg TGH v midend Hsb A24 MTB MTOK TGHB TGOK HC_S c_arg mt tg.
    pose proof (u64_range S) as HSr. destruct Hsb as [Hb2 Hb64]. pose proof (u64_range sb) as Hsbr.
    destruct Hfs as [Hf0 Hf1]. pose proof (u64_range fs) as Hfr. pose proof (u64_range (tg_res v)) as Hrr.
    pose proof (sk1_pos_rng hint i0) as Hp.
    assert (RT36 : ret_ok (at_ sb 36)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    assert (US32 : U (at_ S (-32)) = (U S - 32)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    destruct blkS1 as (r1 & RUN1 & A10 & A1 & A2 & A8 & A4 & AG1).
    assert (TGH1 : tlsgaH segs tg M1 (at_ S (-32)) v).
    { apply (tlsgaH_above segs tg mem M1 (at_ S (-32)) v TGH); [apply fl_frame_grows|].
      intros a Ha. apply fl_frame_out; [lia | rewrite US32 in Ha; lia]. }
    rewrite <- Harg in A10.
    destruct (tlsga_run_t segs tg TGOK M1 rom (at_ sb 36) (at_ S (-32)) v r1 TGH1 RT36 A1 A2 A4 A10)
      as (r2 & Mj & RUN2 & SR & B10 & B1 & B2 & AG2).
    rewrite US32 in SR.
    assert (B8 : getr r2 8 = S) by (rewrite (AG2 8 ltac:(notin)); exact A8).
    assert (RDJ : forall c n bs, (0 <= c)%Z -> (c + Z.of_nat n <= U S - 208)%Z ->
                  rdn segs mem (Z_to_bv 64 c) n = Some bs -> rdn segs Mj (Z_to_bv 64 c) n = Some bs).
    { intros c n bs Hc0 Hc Hr.
      apply (scr_rel_rdn segs M1 Mj (U S - 32 - 176) (U S - 32) c n bs SR); [lia | lia | left; lia|].
      apply rd_fl_frame; [lia | lia | lia | exact Hr]. }
    assert (OKJ : forall (a : word) n, store_ok segs mem a n = true -> store_ok segs Mj a n = true).
    { intros a n OK. apply (scr_rel_ok segs M1 Mj _ _ a n SR). apply fl_frame_ok. exact OK. }
    assert (HFL : forall j, (U fs + 20480 <= sk1_flag fs hint j < U fs + 28672)%Z) by (intros j; pose proof (sk1_pos_rng hint j); (lazymatch goal with |- ?G => let G' := eval unfold sk1_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 1085440 <= FRM /\ FRM + 128 <= U fs + 2134016)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk1_frame in G in change_no_check G' end); lia).
    assert (SLOT : forall k vv, (k = 8 \/ k = 16 \/ k = 24 \/ k = 32)%Z ->
                   rdn segs M1 (at_ S (- k)) 8 = Some (W8 vv) -> rdn segs Mj (at_ S (- k)) 8 = Some (W8 vv)).
    { intros k vv Hk Hr. destruct SR as (O & _ & _).
      rewrite (rdn_ext segs 8 Mj M1 (at_ S (- k))); [exact Hr | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u by lia; intros x Hx; apply O; lia]. }
    assert (PHJ : m2sH segs mt Mj (Z_to_bv 64 FRM) midend).
    { pose proof Hmcells as HC. unfold m2s_cells in HC.
      repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
      destruct PH as [R1 R2 R3 R4 R5 R6 R7 R8 HCx Hlo Hhi].
      constructor; try assumption; apply RDJ; try assumption; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia. }
    destruct (stkB_run segs sb mt HC_S MTOK MTB (conj Hb2 Hb64) Mj rom ra S (tg_res v) fs midend (getr regs 8) (getr regs 9) (getr regs 18) hint i0)
      with (r2 := r2) as (r & RUN3 & E10 & E1 & E2 & E8 & E9 & E18 & AG3).
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rfs]. }
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rgc]. }
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rlog]. }
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rhint]. }
    { intros j Hj. destruct (Hnz j Hj) as (b & Rb & Nb). exists b. split; [|exact Nb].
      pose proof (HFL j). apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rb]. }
    { pose proof (HFL i0). apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hz]. }
    { apply OKJ; exact OKh. } { apply OKJ; exact OKf. } { apply OKJ; exact OK24. } { apply OKJ; exact OKl. } { apply OKJ; exact OKsh. }
    { exact PHJ. }
    { exact Hmcells. }
    { apply (SLOT 8%Z ra); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { apply (SLOT 16%Z (getr regs 8)); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { apply (SLOT 24%Z (getr regs 9)); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { apply (SLOT 32%Z (getr regs 18)); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { split; lia. }
    { lia. }
    { exact Hhint. }
    { exact Hi0. }
    { exact Hret. }
    { exact B10. }
    { exact B2. }
    { exact B8. }
    exists r, Mj. split; [|split; [|split; [exact E10 | split; [exact E1 | split; [exact E2|]]]]].
    - rewrite TGHB in RUN2. eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3].
    - apply (scr_rel_trans mem M1 Mj).
      + (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end).
        repeat (apply scr_rel_wb; [ | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ] | wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia | lia ]).
        apply scr_rel_refl.
      + apply (scr_rel_mono M1 Mj _ _ _ _ SR); lia.
    - intros x Hx.
      destruct (In_dec (fun a b : reg => decide (a = b)) x [1; 2; 8; 9; 18]%list) as [I|NI].
      + cbn [In] in I.
        repeat (destruct I as [<-|I]; [first [rewrite E1; symmetry; exact H1 | rewrite E2; symmetry; exact H2 | exact E8 | exact E9 | exact E18] |]).
        destruct I.
      + assert (NB : ~ In x SBCLOB1).
        { intros I. unfold SBCLOB1 in I. unfold m2s_clob in Hx. cbn [In] in I, NI, Hx. am_tauto. }
        rewrite (AG3 x NB). rewrite (AG2 x). 2:{ intros I. unfold m2s_clob in Hx. cbn [In] in I, Hx. am_tauto. }
        apply AG1. intros I. unfold m2s_clob in Hx. cbn [In] in I, NI, Hx. am_tauto.
  Qed.
End STK.

(* [comment removed for export] *)
Definition stk1_tab_ok (segs : list Segment) (t : stk_tab) : Prop :=
  code_ato segs (sk_base t) 0 stk1_words
  /\ tlsga_tab_ok segs (sk_tg t) /\ tg_hb (sk_tg t) = at_ (sk_base t) 21076
  /\ m2s_tab_ok segs (sk_mt t) /\ mt_base (sk_mt t) = at_ (sk_base t) 1240
  /\ gaddr2 segs (sk_base t) 24 10 10 (sk_arg t)
  /\ ((U (sk_base t) mod 2 = 0)%Z /\ (U (sk_base t) + 30000 < 2 ^ 64)%Z).

Record stk1H (segs : list Segment) (t : stk_tab) (mem : word -> option byte) (S fs midend : word) (v : tlsga_vals) (hint i0 : Z) : Prop := SK1H {
  s1h_tls : tlsgaH segs (sk_tg t) mem (at_ S (-32)) v;
  s1h_arg : tv_arg v = sk_arg t;
  s1h_fs : rdn segs mem (Z_to_bv 64 (U (tg_res v))) 8 = Some (W8 fs);
  s1h_res : (U (tg_res v) + 8 <= U S - 208)%Z;
  s1h_gc : rdn segs mem (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0];
  s1h_log : rdn segs mem (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20);
  s1h_hint : rdn segs mem (Z_to_bv 64 (U fs + 8)) 8 = Some (LE8 hint);
  s1h_busy : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs mem (Z_to_bv 64 (sk1_flag fs hint j)) 1 = Some [b] /\ U b <> 0%Z;
  s1h_free : rdn segs mem (Z_to_bv 64 (sk1_flag fs hint i0)) 1 = Some [Z_to_bv 8 0];
  s1h_ok_hint : store_ok segs mem (Z_to_bv 64 (U fs + 8)) 8 = true;
  s1h_ok_flag : store_ok segs mem (Z_to_bv 64 (sk1_flag fs hint i0)) 1 = true;
  s1h_ok_24 : store_ok segs mem (Z_to_bv 64 (sk1_frame fs hint i0 + 24)) 8 = true;
  s1h_ok_last : store_ok segs mem (Z_to_bv 64 (sk1_frame fs hint i0 + 120)) 8 = true;
  s1h_ok_sh : store_ok segs mem (Z_to_bv 64 (sk1_sh fs hint i0)) 16 = true;
  s1h_m2s : m2sH segs (sk_mt t) mem (Z_to_bv 64 (sk1_frame fs hint i0)) midend;
  s1h_mcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells (sk_mt t));
  s1h_geom : (0 < U fs /\ U fs + 2134016 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 2134016 <= U S - 208)%Z;
  s1h_hintr : (0 <= hint)%Z;
  s1h_i0 : (0 <= i0 < 8192)%Z;
  s1h_S : (208 <= U S)%Z;
  s1h_stk : store_ok segs mem (at_ S (-32)) 32 = true }.

Theorem stk1_run_t : forall segs t, stk1_tab_ok segs t ->
  forall mem rom (ra S fs midend : word) v hint i0 regs,
  stk1H segs t mem S fs midend v hint i0 -> ret_ok ra ->
  getr regs 1 = ra -> getr regs 2 = S -> getr regs 4 = tv_tp v ->
  exists r Mj,
    msteps segs (mkst regs (sk_base t) mem rom) (mkst r ra (sk1_mem Mj fs hint i0 S) rom)
    /\ scr_rel mem Mj (U S - 208) (U S)
    /\ getr r 10 = Z_to_bv 64 (sk1_frame fs hint i0) /\ getr r 1 = ra /\ getr r 2 = S
    /\ regs_agree (fun x => In x m2s_clob) regs r.
Proof using.
  intros segs t (C1 & TG & TGB & MT & MTB & A24 & HB) mem rom ra S fs midend v hint i0 regs
         [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21] Hret H1 H2 H4.
  replace (mkst regs (sk_base t) mem rom) with (mkst regs (at_ (sk_base t) 0) mem rom) by (rewrite at_0; reflexivity).
  first [ exact (stk1_run segs (sk_base t) (sk_tg t) (sk_mt t) (sk_arg t) C1 TG TGB MT MTB A24 HB mem rom ra S fs midend v hint i0
           P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 Hret regs H1 H2 H4)
        | exact (stk1_run segs (sk_base t) (sk_tg t) (sk_mt t) (sk_arg t) C1 TG TGB MT MTB A24 HB mem rom ra S fs midend v hint i0
           P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P21 Hret regs H1 H2 H4) ].
Qed.
End FPGen1.
End AsRtStkMal1.
Module AsRtStkMal2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation W8 w := (word_to_le_bytes 8 w).
#[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

Definition sk2_pos (hint i : Z) : Z := ((hint + i) mod 4096)%Z.
Definition sk2_flag (fs : word) (hint i : Z) : Z := (U fs + 28672 + sk2_pos hint i)%Z.
Definition sk2_frame (fs : word) (hint i : Z) : Z := (U fs + 2134016 + sk2_pos hint i * 256)%Z.
Definition sk2_sh (fs : word) (hint i : Z) : Z := (sk2_frame fs hint i / 8 + 0x7fff8000)%Z.

Definition sk2_mem4 (m : word -> option byte) (fs : word) (hint i0 : Z) (S : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (U fs + 16)) (LE8 (hint + i0 + 1)))
    (Z_to_bv 64 (sk2_flag fs hint i0)) [Z_to_bv 8 1])
    (Z_to_bv 64 (sk2_frame fs hint i0 + 24)) (W8 S))
    (Z_to_bv 64 (sk2_frame fs hint i0 + 248)) (LE8 (sk2_flag fs hint i0)).
Definition sk2_mem (m : word -> option byte) (fs : word) (hint i0 : Z) (S : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (sk2_mem4 m fs hint i0 S) (Z_to_bv 64 (sk2_sh fs hint i0 + 0)) (LE8 0)) (Z_to_bv 64 (sk2_sh fs hint i0 + 8)) (LE8 0)) (Z_to_bv 64 (sk2_sh fs hint i0 + 16)) (LE8 0)) (Z_to_bv 64 (sk2_sh fs hint i0 + 24)) (LE8 0).

Lemma sk2_pos_rng : forall hint i, (0 <= sk2_pos hint i < 4096)%Z.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk2_pos in G in change_no_check G' end). apply Z.mod_pos_bound. lia. Qed.
Lemma v_and_mask2 : forall z, v_and (Z_to_bv 64 z) (Z_to_bv 64 4095) = Z_to_bv 64 (z mod 4096).
Proof using. intros z. exact (v_and_maskN (14 - 2) z ltac:(lia)). Qed.
Lemma sk2_sh_rng : forall (fs : word) hint i, (U fs + 3182592 <= 2 ^ 47)%Z ->
  (0x7fff8000 <= sk2_sh fs hint i /\ sk2_sh fs hint i + 32 <= 0x10007fff8000)%Z.
Proof using.
  intros fs hint i H64. pose proof (u64_range fs) as Hfr. (lazymatch goal with |- ?G => let G' := eval unfold sk2_sh, sk2_frame in G in change_no_check G' end). pose proof (sk2_pos_rng hint i) as Hp.
  pose proof (Z.div_pos (U fs + 2134016 + sk2_pos hint i * 256) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (U fs + 2134016 + sk2_pos hint i * 256) 8 (2 ^ 44 - 32) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma v_slli_s2 : forall z, (0 <= z < 2 ^ 32)%Z -> v_slli (Z_to_bv 64 z) 8 = Z_to_bv 64 (z * 256).
Proof using. intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end). rewrite u_Z2bv by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Ltac av_and F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply AsRtFlush.step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

(* [comment removed for export] *)
Definition stk2_words : list (option (bv 32)) :=
  [
   Some W_57468; Some W_5746c; Some W_57470; Some W_57474; Some W_57478; Some W_5747c; None; None; Some W_57488;
   Some W_5748c; Some W_57490; Some W_57494; Some W_57498; Some W_5749c; Some W_574a0; Some W_574a4; Some W_574a8;
   Some W_574ac; Some W_574b0; Some W_574b4; Some W_574b8; Some W_574bc; Some W_574c0; Some W_574c4; Some W_574c8;
   Some W_574cc; Some W_574d0; Some W_574d4; Some W_574d8; Some W_574dc; Some W_574e0; Some W_574e4; Some W_574e8;
   Some W_574ec; Some W_574f0; Some W_574f4; Some W_574f8; Some W_574fc; Some W_57500; Some W_57504; Some W_57508;
   Some W_5750c; Some W_57510; Some W_57514; Some W_57518; Some W_5751c; None; None; Some W_57528; Some W_5752c;
   Some W_57530; Some W_57534; Some W_57538; Some W_5753c; Some W_57540; Some W_57544; Some W_57548; Some W_5754c;
   Some W_57550; Some W_57554; Some W_57558; Some W_5755c; Some W_57560; Some W_57564; Some W_57568; Some W_5756c;
   Some W_57570; Some W_57574; Some W_57578; Some W_5757c; Some W_57580; Some W_57584; Some W_57588; Some W_5758c;
   Some W_57590; Some W_57594; Some W_57598; Some W_5759c; Some W_575a0; Some W_575a4; Some W_575a8; Some W_575ac;
   Some W_575b0; Some W_575b4; Some W_575b8; Some W_575bc; Some W_575c0; Some W_575c4; Some W_575c8; Some W_575cc;
   Some W_575d0; Some W_575d4; Some W_575d8; Some W_575dc; Some W_575e0; Some W_575e4; Some W_575e8; Some W_575ec;
   Some W_575f0; Some W_575f4; Some W_575f8; Some W_575fc; Some W_57600
  ]%list.

Section STKB.
  Variables (segs : list Segment) (sb : word).
  Variable mt : m2s_tab.
  Hypothesis HC_S : code_ato segs sb 0 stk2_words.
  Hypothesis MTOK : m2s_tab_ok segs mt.
  Hypothesis MTB : mt_base mt = at_ sb 840.
  Hypothesis Hsb : (U sb mod 2 = 0)%Z /\ (U sb + 30000 < 2 ^ 64)%Z.


  Lemma F_57468 : fetch_word segs (at_ sb 0) = Some W_57468.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 0 _ HC_S eq_refl). Qed.
  Lemma F_5746c : fetch_word segs (at_ sb 4) = Some W_5746c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 1 _ HC_S eq_refl). Qed.
  Lemma F_57470 : fetch_word segs (at_ sb 8) = Some W_57470.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 2 _ HC_S eq_refl). Qed.
  Lemma F_57474 : fetch_word segs (at_ sb 12) = Some W_57474.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 3 _ HC_S eq_refl). Qed.
  Lemma F_57478 : fetch_word segs (at_ sb 16) = Some W_57478.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 4 _ HC_S eq_refl). Qed.
  Lemma F_5747c : fetch_word segs (at_ sb 20) = Some W_5747c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 5 _ HC_S eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma F_57488 : fetch_word segs (at_ sb 32) = Some W_57488.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 8 _ HC_S eq_refl). Qed.
  Lemma F_5748c : fetch_word segs (at_ sb 36) = Some W_5748c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 9 _ HC_S eq_refl). Qed.
  Lemma F_57490 : fetch_word segs (at_ sb 40) = Some W_57490.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 10 _ HC_S eq_refl). Qed.
  Lemma F_57494 : fetch_word segs (at_ sb 44) = Some W_57494.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 11 _ HC_S eq_refl). Qed.
  Lemma F_57498 : fetch_word segs (at_ sb 48) = Some W_57498.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 12 _ HC_S eq_refl). Qed.
  Lemma F_5749c : fetch_word segs (at_ sb 52) = Some W_5749c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 13 _ HC_S eq_refl). Qed.



  Lemma F_574ac : fetch_word segs (at_ sb 68) = Some W_574ac.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 17 _ HC_S eq_refl). Qed.
  Lemma F_574b0 : fetch_word segs (at_ sb 72) = Some W_574b0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 18 _ HC_S eq_refl). Qed.
  Lemma F_574b4 : fetch_word segs (at_ sb 76) = Some W_574b4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 19 _ HC_S eq_refl). Qed.
  Lemma F_574b8 : fetch_word segs (at_ sb 80) = Some W_574b8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 20 _ HC_S eq_refl). Qed.
  Lemma F_574bc : fetch_word segs (at_ sb 84) = Some W_574bc.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 21 _ HC_S eq_refl). Qed.
  Lemma F_574c0 : fetch_word segs (at_ sb 88) = Some W_574c0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 22 _ HC_S eq_refl). Qed.
  Lemma F_574c4 : fetch_word segs (at_ sb 92) = Some W_574c4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 23 _ HC_S eq_refl). Qed.
  Lemma F_574c8 : fetch_word segs (at_ sb 96) = Some W_574c8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 24 _ HC_S eq_refl). Qed.
  Lemma F_574cc : fetch_word segs (at_ sb 100) = Some W_574cc.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 25 _ HC_S eq_refl). Qed.
  Lemma F_574d0 : fetch_word segs (at_ sb 104) = Some W_574d0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 26 _ HC_S eq_refl). Qed.
  Lemma F_574d4 : fetch_word segs (at_ sb 108) = Some W_574d4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 27 _ HC_S eq_refl). Qed.
  Lemma F_574d8 : fetch_word segs (at_ sb 112) = Some W_574d8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 28 _ HC_S eq_refl). Qed.
  Lemma F_574dc : fetch_word segs (at_ sb 116) = Some W_574dc.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 29 _ HC_S eq_refl). Qed.
  Lemma F_574e0 : fetch_word segs (at_ sb 120) = Some W_574e0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 30 _ HC_S eq_refl). Qed.
  Lemma F_574e4 : fetch_word segs (at_ sb 124) = Some W_574e4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 31 _ HC_S eq_refl). Qed.
  Lemma F_574e8 : fetch_word segs (at_ sb 128) = Some W_574e8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 32 _ HC_S eq_refl). Qed.
  Lemma F_574ec : fetch_word segs (at_ sb 132) = Some W_574ec.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 33 _ HC_S eq_refl). Qed.
  Lemma F_574f0 : fetch_word segs (at_ sb 136) = Some W_574f0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 34 _ HC_S eq_refl). Qed.
  Lemma F_574f4 : fetch_word segs (at_ sb 140) = Some W_574f4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 35 _ HC_S eq_refl). Qed.
  Lemma F_574f8 : fetch_word segs (at_ sb 144) = Some W_574f8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 36 _ HC_S eq_refl). Qed.
  Lemma F_574fc : fetch_word segs (at_ sb 148) = Some W_574fc.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 37 _ HC_S eq_refl). Qed.
  Lemma F_57500 : fetch_word segs (at_ sb 152) = Some W_57500.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 38 _ HC_S eq_refl). Qed.
  Lemma F_57504 : fetch_word segs (at_ sb 156) = Some W_57504.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 39 _ HC_S eq_refl). Qed.
  Lemma F_57508 : fetch_word segs (at_ sb 160) = Some W_57508.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 40 _ HC_S eq_refl). Qed.
  Lemma F_5750c : fetch_word segs (at_ sb 164) = Some W_5750c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 41 _ HC_S eq_refl). Qed.
  Lemma F_57510 : fetch_word segs (at_ sb 168) = Some W_57510.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 42 _ HC_S eq_refl). Qed.
  Lemma F_57514 : fetch_word segs (at_ sb 172) = Some W_57514.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 43 _ HC_S eq_refl). Qed.





















  Lemma F_57574 : fetch_word segs (at_ sb 268) = Some W_57574.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 67 _ HC_S eq_refl). Qed.
  Lemma F_57578 : fetch_word segs (at_ sb 272) = Some W_57578.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 68 _ HC_S eq_refl). Qed.
  Lemma F_5757c : fetch_word segs (at_ sb 276) = Some W_5757c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 69 _ HC_S eq_refl). Qed.
  Lemma F_57580 : fetch_word segs (at_ sb 280) = Some W_57580.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 70 _ HC_S eq_refl). Qed.
  Lemma F_57584 : fetch_word segs (at_ sb 284) = Some W_57584.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 71 _ HC_S eq_refl). Qed.
  Lemma F_57588 : fetch_word segs (at_ sb 288) = Some W_57588.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 72 _ HC_S eq_refl). Qed.
  Lemma F_5758c : fetch_word segs (at_ sb 292) = Some W_5758c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 73 _ HC_S eq_refl). Qed.
  Lemma F_57590 : fetch_word segs (at_ sb 296) = Some W_57590.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 74 _ HC_S eq_refl). Qed.
  Lemma F_57594 : fetch_word segs (at_ sb 300) = Some W_57594.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 75 _ HC_S eq_refl). Qed.
  Lemma F_57598 : fetch_word segs (at_ sb 304) = Some W_57598.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 76 _ HC_S eq_refl). Qed.
  Lemma F_5759c : fetch_word segs (at_ sb 308) = Some W_5759c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 77 _ HC_S eq_refl). Qed.
  Lemma F_575a0 : fetch_word segs (at_ sb 312) = Some W_575a0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 78 _ HC_S eq_refl). Qed.
  Lemma F_575a4 : fetch_word segs (at_ sb 316) = Some W_575a4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 79 _ HC_S eq_refl). Qed.
  Lemma F_575a8 : fetch_word segs (at_ sb 320) = Some W_575a8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 80 _ HC_S eq_refl). Qed.
  Lemma F_575ac : fetch_word segs (at_ sb 324) = Some W_575ac.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 81 _ HC_S eq_refl). Qed.
  Lemma F_575b0 : fetch_word segs (at_ sb 328) = Some W_575b0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 82 _ HC_S eq_refl). Qed.
  Lemma F_575b4 : fetch_word segs (at_ sb 332) = Some W_575b4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 83 _ HC_S eq_refl). Qed.
  Lemma F_575b8 : fetch_word segs (at_ sb 336) = Some W_575b8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 84 _ HC_S eq_refl). Qed.
  Lemma F_575bc : fetch_word segs (at_ sb 340) = Some W_575bc.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 85 _ HC_S eq_refl). Qed.
  Lemma F_575c0 : fetch_word segs (at_ sb 344) = Some W_575c0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 86 _ HC_S eq_refl). Qed.
  Lemma F_575c4 : fetch_word segs (at_ sb 348) = Some W_575c4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 87 _ HC_S eq_refl). Qed.
  Lemma F_575c8 : fetch_word segs (at_ sb 352) = Some W_575c8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 88 _ HC_S eq_refl). Qed.
  Lemma F_575cc : fetch_word segs (at_ sb 356) = Some W_575cc.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 89 _ HC_S eq_refl). Qed.
  Lemma F_575d0 : fetch_word segs (at_ sb 360) = Some W_575d0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 90 _ HC_S eq_refl). Qed.
  Lemma F_575d4 : fetch_word segs (at_ sb 364) = Some W_575d4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 91 _ HC_S eq_refl). Qed.
  Lemma F_575d8 : fetch_word segs (at_ sb 368) = Some W_575d8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 92 _ HC_S eq_refl). Qed.
  Lemma F_575dc : fetch_word segs (at_ sb 372) = Some W_575dc.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 93 _ HC_S eq_refl). Qed.
  Lemma F_575e0 : fetch_word segs (at_ sb 376) = Some W_575e0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 94 _ HC_S eq_refl). Qed.
  Lemma F_575e4 : fetch_word segs (at_ sb 380) = Some W_575e4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk2_words 95 _ HC_S eq_refl). Qed.








  Variable m : word -> option byte.
  Variable rom : word -> option byte.
  Variables (ra S resw fs midend s0v s1v s2v : word).
  Variables (hint i0 : Z).
  #[local] Abbreviation FLG := (sk2_flag fs hint i0).
  #[local] Abbreviation FRM := (sk2_frame fs hint i0).
  #[local] Abbreviation SHW := (sk2_sh fs hint i0).
  Hypothesis Rfs : rdn segs m (Z_to_bv 64 (U resw)) 8 = Some (W8 fs).
  Hypothesis Rgc : rdn segs m (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlog : rdn segs m (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20).
  Hypothesis Rhint : rdn segs m (Z_to_bv 64 (U fs + 16)) 8 = Some (LE8 hint).
  Hypothesis Hnz : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs m (Z_to_bv 64 (sk2_flag fs hint j)) 1 = Some [b] /\ U b <> 0%Z.
  Hypothesis Hz : rdn segs m (Z_to_bv 64 FLG) 1 = Some [Z_to_bv 8 0].
  Hypothesis OKh : store_ok segs m (Z_to_bv 64 (U fs + 16)) 8 = true.
  Hypothesis OKf : store_ok segs m (Z_to_bv 64 FLG) 1 = true.
  Hypothesis OK24 : store_ok segs m (Z_to_bv 64 (FRM + 24)) 8 = true.
  Hypothesis OKl : store_ok segs m (Z_to_bv 64 (FRM + 248)) 8 = true.
  Hypothesis OKsh : store_ok segs m (Z_to_bv 64 SHW) 32 = true.
  Hypothesis PHm : m2sH segs mt m (Z_to_bv 64 FRM) midend.
  Hypothesis Hmcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells mt).
  Hypothesis FR1 : rdn segs m (at_ S (-8)) 8 = Some (W8 ra).
  Hypothesis FR2 : rdn segs m (at_ S (-16)) 8 = Some (W8 s0v).
  Hypothesis FR3 : rdn segs m (at_ S (-24)) 8 = Some (W8 s1v).
  Hypothesis FR4 : rdn segs m (at_ S (-32)) 8 = Some (W8 s2v).
  Hypothesis Hfs : (0 < U fs /\ U fs + 3182592 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 3182592 <= U S - 32)%Z.
  Hypothesis Hfsnz : (U fs <> 0)%Z.
  Hypothesis Hhint : (0 <= hint)%Z.
  Hypothesis Hi0 : (0 <= i0 < 4096)%Z.
  Hypothesis HS : (32 <= U S)%Z.
  Hypothesis Hret : ret_ok ra.

  Ltac addr_eq :=
    apply bv_eq; rewrite ?v_addi_0;
    repeat match goal with |- context [v_addi ?b ?e] => change (v_addi b e) with (at_ b e) end;
    (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  Ltac rdm Hr :=
    repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]);
    lazymatch goal with |- rdn _ m _ _ = _ => exact Hr end.
  Ltac cldz F D cc vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 cc : word) by addr_eq end;
          rdm Hr
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Ltac clbu F D cc Hr :=
    chain_step; [reflexivity
      | eapply step_lbu; [exact F | reflexivity | exact D | ];
        gres; rwH; imm_norm;
        lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 cc : word) by addr_eq end;
        rdm Hr
      | step_simpl]; vn.

  Definition LCLOB2 : list reg := [5; 10; 12; 15; 17]%list.

  Lemma sk2_iter : forall (i : Z) r,
    (0 <= i < i0)%Z ->
    getr r 10 = Z_to_bv 64 (4096 - i) -> getr r 12 = Z_to_bv 64 (hint + i) ->
    getr r 13 = Z_to_bv 64 (U fs + 28672) -> getr r 14 = Z_to_bv 64 4095 ->
    exists r',
      msteps segs (mkst r (at_ sb 148) m rom) (mkst r' (at_ sb 148) m rom)
      /\ getr r' 10 = Z_to_bv 64 (4096 - (i + 1)) /\ getr r' 12 = Z_to_bv 64 (hint + (i + 1))
      /\ regs_agree (fun x => In x LCLOB2) r r'.
  Proof using Hi0 Hhint Hfsnz Hfs Hnz S HC_S.
    intros i r Hi Q10 Q12 Q13 Q14. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk2_pos_rng hint i) as Hp.
    destruct (Hnz i Hi) as (b & Rb & Nb). pose proof (u8_range b) as Hb8.
    wd_eexists. split.
    - av_and F_574fc D_574fc (Z_to_bv 64 (sk2_pos hint i)) ltac:(rewrite v_and_mask2; reflexivity).
      av F_57500 D_57500 (Z_to_bv 64 (sk2_flag fs hint i)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, sk2_flag in G in change_no_check G' end); unorm; f_equal; lia).
      clbu F_57504 D_57504 (sk2_flag fs hint i) Rb.
      ab_ft F_57508 D_57508 ltac:(condz).
      av F_5750c D_5750c (Z_to_bv 64 (4096 - (i + 1))) ltac:(rewrite v_addiw_m1 by lia; f_equal; lia).
      av F_57510 D_57510 (Z_to_bv 64 (hint + (i + 1))) ltac:(rewrite v_addi_Z; f_equal; lia).
      ab_tk F_57514 D_57514 ltac:(condz).
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold LCLOB2 in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma sk2_loop : forall (n : nat) (i : Z) r,
    (0 <= i)%Z -> (i + Z.of_nat n = i0)%Z ->
    getr r 10 = Z_to_bv 64 (4096 - i) -> getr r 12 = Z_to_bv 64 (hint + i) ->
    getr r 13 = Z_to_bv 64 (U fs + 28672) -> getr r 14 = Z_to_bv 64 4095 ->
    exists r',
      msteps segs (mkst r (at_ sb 148) m rom) (mkst r' (at_ sb 268) m rom)
      /\ getr r' 12 = Z_to_bv 64 (hint + i0) /\ getr r' 15 = Z_to_bv 64 FLG /\ getr r' 17 = Z_to_bv 64 (sk2_pos hint i0)
      /\ regs_agree (fun x => In x LCLOB2) r r'.
  Proof using Hi0 Hhint Hfsnz Hfs Hz Hnz S HC_S.
    induction n as [|n IH]; intros i r Hi0' Hin Q10 Q12 Q13 Q14.
    - assert (i = i0) by lia. subst i. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
      pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk2_pos_rng hint i0) as Hp.
      wd_eexists. split.
      + av_and F_574fc D_574fc (Z_to_bv 64 (sk2_pos hint i0)) ltac:(rewrite v_and_mask2; reflexivity).
        av F_57500 D_57500 (Z_to_bv 64 FLG) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, sk2_flag in G in change_no_check G' end); unorm; f_equal; lia).
        clbu F_57504 D_57504 (sk2_flag fs hint i0) Hz.
        ab_tk F_57508 D_57508 ltac:(vals_lit; condz).
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold LCLOB2 in G in change_no_check G' end). ra_solve.
    - destruct (sk2_iter i r ltac:(lia) Q10 Q12 Q13 Q14) as (r1 & RUN1 & A10 & A12 & AG1).
      assert (A13 : getr r1 13 = Z_to_bv 64 (U fs + 28672)) by (rewrite (AG1 13 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB2 in G in change_no_check G' end); notin)); exact Q13).
      assert (A14 : getr r1 14 = Z_to_bv 64 4095) by (rewrite (AG1 14 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB2 in G in change_no_check G' end); notin)); exact Q14).
      destruct (IH (i + 1)%Z r1 ltac:(lia) ltac:(lia) A10 A12 A13 A14) as (r' & RUN2 & B12 & B15 & B17 & AG2).
      exists r'. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. repeat (split; [assumption|]).
      eapply regs_agree_trans; eassumption.
  Qed.

  Ltac wsd F D cc OKT :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := Z_to_bv 64 cc);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; addr_eq
        | gres; rwH; reflexivity
        | (lazymatch goal with |- ?G => let G' := eval unfold sk2_mem4 in G in change_no_check G' end); repeat (eapply store_ok_mono; [apply wbytes_grows|]); OKT ]
      | step_simpl]; vn.
  Ltac fldm F D vv FR :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold sk2_mem, sk2_mem4 in G in change_no_check G' end);
          repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]); exact FR
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  Definition S2CLOB2 : list reg := [9; 18; 10; 11; 12; 13; 14; 15; 16]%list.

  Lemma blkS2 : forall r2,
    getr r2 10 = resw -> getr r2 2 = at_ S (-32) -> getr r2 8 = S ->
    exists r,
      msteps segs (mkst r2 (at_ sb 36) m rom) (mkst r (at_ sb 148) m rom)
      /\ getr r 10 = Z_to_bv 64 (4096 - 0) /\ getr r 12 = Z_to_bv 64 (hint + 0)
      /\ getr r 13 = Z_to_bv 64 (U fs + 28672) /\ getr r 14 = Z_to_bv 64 4095
      /\ getr r 11 = Z_to_bv 64 (U fs + 4096)
      /\ getr r 9 = fs /\ getr r 18 = Z_to_bv 64 20 /\ getr r 2 = at_ S (-32) /\ getr r 8 = S
      /\ regs_agree (fun x => In x S2CLOB2) r2 r.
  Proof using Hhint Hfsnz Hfs Rhint Rlog Rgc Rfs HC_S.
    intros r2 Q10 Q2 Q8. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (u64_range resw) as Hrr.
    wd_eexists. split.
    - cldz F_5748c D_5748c (U resw) fs Rfs.
      ab_ft F_57490 D_57490 ltac:(condz).
      clbu F_57494 D_57494 (U fs + 96)%Z Rgc.
      cldz F_57498 D_57498 (U fs + 88)%Z (Z_to_bv 64 20) Rlog.
      ab_tk F_5749c D_5749c ltac:(vals_lit; condz).
      an F_574ac D_574ac. an F_574b0 D_574b0. an F_574b4 D_574b4. an F_574b8 D_574b8.
      ab_ft F_574bc D_574bc ltac:(vm_compute; reflexivity).
      an F_574c0 D_574c0. an F_574c4 D_574c4. an F_574c8 D_574c8. an F_574cc D_574cc. an F_574d0 D_574d0.
      cldz F_574d4 D_574d4 (U fs + 16)%Z (Z_to_bv 64 hint) Rhint.
      an F_574d8 D_574d8. an F_574dc D_574dc.
      av F_574e0 D_574e0 (Z_to_bv 64 (U fs + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).
      av F_574e4 D_574e4 (Z_to_bv 64 (U fs + 28672)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).
      an F_574e8 D_574e8. an F_574ec D_574ec. an F_574f0 D_574f0.
      av F_574f4 D_574f4 (Z_to_bv 64 (hint + 4095)) ltac:(rewrite v_add_ZZ; reflexivity).
      av F_574f8 D_574f8 (Z_to_bv 64 (hint + 4096)) ltac:(rewrite v_addi_Z; f_equal; lia).
      wd_refl.
    - post; try (apply bv_eq; vm_compute; reflexivity). (lazymatch goal with |- ?G => let G' := eval unfold S2CLOB2 in G in change_no_check G' end). ra_solve.
  Qed.

  Definition S3CLOB2 : list reg := [1; 9; 10; 11; 12; 13; 17]%list.

  Lemma blkS3 : forall r4,
    getr r4 12 = Z_to_bv 64 (hint + i0) -> getr r4 15 = Z_to_bv 64 FLG -> getr r4 17 = Z_to_bv 64 (sk2_pos hint i0) ->
    getr r4 11 = Z_to_bv 64 (U fs + 4096) -> getr r4 9 = fs -> getr r4 18 = Z_to_bv 64 20 -> getr r4 8 = S -> getr r4 2 = at_ S (-32) ->
    exists r,
      msteps segs (mkst r4 (at_ sb 268) m rom) (mkst r (at_ sb 840) (sk2_mem4 m fs hint i0 S) rom)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = at_ sb 332 /\ getr r 9 = Z_to_bv 64 FRM /\ getr r 2 = at_ S (-32)
      /\ regs_agree (fun x => In x S3CLOB2) r4 r.
  Proof using Hhint Hfsnz Hfs OKl OK24 OKf OKh HC_S.
    intros r4 Q12 Q15 Q17 Q11 Q9 Q18 Q8 Q2. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk2_pos_rng hint i0) as Hp.
    assert (HFL : (U fs + 28672 <= FLG < U fs + 32768)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk2_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 2134016 <= FRM /\ FRM + 256 <= U fs + 3182592)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk2_frame in G in change_no_check G' end); lia).
    wd_eexists. split.
    - av F_57574 D_57574 (Z_to_bv 64 (hint + i0 + 1)) ltac:(rewrite v_addi_Z; reflexivity).
      an F_57578 D_57578. an F_5757c D_5757c.
      wsd F_57580 D_57580 (U fs + 16)%Z ltac:(exact OKh).
      chain_step; [reflexivity
        | eapply step_sb_at with (a := Z_to_bv 64 FLG) (v := Z_to_bv 64 1) (b := Z_to_bv 8 1);
          [exact F_57584 | reflexivity | exact D_57584
          | gres; rwH; imm_norm; addr_eq
          | gres; rwH; reflexivity
          | apply bv_eq; vm_compute; reflexivity
          | repeat (eapply store_ok_mono; [apply wbytes_grows|]); exact OKf ]
        | step_simpl]; vn.
      an F_57588 D_57588. an F_5758c D_5758c.
      av F_57590 D_57590 (Z_to_bv 64 (sk2_pos hint i0 * 256)) ltac:(rewrite v_slli_s2 by lia; reflexivity).
      an F_57594 D_57594.
      av F_57598 D_57598 (Z_to_bv 64 (U fs + 36864)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).
      av F_5759c D_5759c (Z_to_bv 64 (2097152 + sk2_pos hint i0 * 256)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).
      av F_575a0 D_575a0 (Z_to_bv 64 FRM) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, sk2_frame in G in change_no_check G' end); unorm; f_equal; lia).
      wsd F_575a4 D_575a4 (FRM + 24)%Z ltac:(exact OK24).
      wsd F_575a8 D_575a8 (FRM + 248)%Z ltac:(exact OKl).
      change (wbytes (wbytes (wbytes (wbytes m _ _) _ _) _ _) _ _) with (sk2_mem4 m fs hint i0 S).
      an F_575ac D_575ac. an F_575b0 D_575b0.
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold S3CLOB2 in G in change_no_check G' end). ra_solve.
  Qed.

  Definition S4CLOB2 : list reg := [1; 2; 8; 9; 18; 10; 11; 12]%list.

  Lemma blkS4 : forall r6,
    getr r6 10 = Z_to_bv 64 SHW -> getr r6 9 = Z_to_bv 64 FRM -> getr r6 2 = at_ S (-32) ->
    exists r,
      msteps segs (mkst r6 (at_ sb 332) (sk2_mem4 m fs hint i0 S) rom) (mkst r ra (sk2_mem m fs hint i0 S) rom)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = ra /\ getr r 2 = S /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ regs_agree (fun x => In x S4CLOB2) r6 r.
  Proof using Hret Hhint Hfsnz Hfs FR4 FR3 FR2 FR1 OKsh HC_S.
    intros r6 Q10 Q9 Q2. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk2_pos_rng hint i0) as Hp.
    assert (HFL : (U fs + 28672 <= FLG < U fs + 32768)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk2_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 2134016 <= FRM /\ FRM + 256 <= U fs + 3182592)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk2_frame in G in change_no_check G' end); lia).
    pose proof (sk2_sh_rng fs hint i0 ltac:(lia)) as HSH.
    assert (OKS : forall j, (0 <= j)%Z -> (j + 8 <= 32)%Z -> store_ok segs m (Z_to_bv 64 (SHW + j)) 8 = true).
    { intros j Hj0 Hj1. eapply (store_ok_sub segs m (Z_to_bv 64 SHW) _ 32); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | exact OKsh | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ] | rewrite !u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia]. }
    wd_eexists. split.
    - an F_575b4 D_575b4. an F_575b8 D_575b8. an F_575bc D_575bc.
      wsd F_575c0 D_575c0 (sk2_sh fs hint i0 + 0)%Z ltac:(apply OKS; lia).
      wsd F_575c4 D_575c4 (sk2_sh fs hint i0 + 8)%Z ltac:(apply OKS; lia).
      wsd F_575c8 D_575c8 (sk2_sh fs hint i0 + 16)%Z ltac:(apply OKS; lia).
      wsd F_575cc D_575cc (sk2_sh fs hint i0 + 24)%Z ltac:(apply OKS; lia).
      change (wbytes (wbytes (wbytes (wbytes (sk2_mem4 m fs hint i0 S) _ _) _ _) _ _) _ _) with (sk2_mem m fs hint i0 S).
      fldm F_575d0 D_575d0 ra FR1.
      fldm F_575d4 D_575d4 s0v FR2.
      fldm F_575d8 D_575d8 s1v FR3.
      fldm F_575dc D_575dc s2v FR4.
      an F_575e0 D_575e0.
      aret F_575e4 D_575e4 ra.
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold S4CLOB2 in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma PH4 : m2sH segs mt (sk2_mem4 m fs hint i0 S) (Z_to_bv 64 FRM) midend.
  Proof using Hfsnz Hfs Hmcells PHm sb.
    destruct Hfs as [Hf0 Hf1]. pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk2_pos_rng hint i0) as Hp.
    assert (HFL : (U fs + 28672 <= FLG < U fs + 32768)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk2_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 2134016 <= FRM /\ FRM + 256 <= U fs + 3182592)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk2_frame in G in change_no_check G' end); lia).
    pose proof Hmcells as HC. unfold m2s_cells in HC.
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
    destruct PHm as [R1 R2 R3 R4 R5 R6 R7 R8 HCx Hlo Hhi].
    constructor; try assumption; (lazymatch goal with |- ?G => let G' := eval unfold sk2_mem4 in G in change_no_check G' end);
      (repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ])); assumption.
  Qed.

  Definition SBCLOB2 : list reg := [1; 2; 5; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list.
  Lemma SB_sub2 : forall x : reg, In x S2CLOB2 -> In x SBCLOB2. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold S2CLOB2, SBCLOB2 in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_subL : forall x : reg, In x LCLOB2 -> In x SBCLOB2. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold LCLOB2, SBCLOB2 in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_sub3 : forall x : reg, In x S3CLOB2 -> In x SBCLOB2. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold S3CLOB2, SBCLOB2 in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_subM : forall x : reg, In x m2s_clob -> In x SBCLOB2. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold m2s_clob, SBCLOB2 in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_sub4 : forall x : reg, In x S4CLOB2 -> In x SBCLOB2. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold S4CLOB2, SBCLOB2 in G in change_no_check G' end). incl_lists. Qed.

  Theorem stkB_run : forall r2,
    getr r2 10 = resw -> getr r2 2 = at_ S (-32) -> getr r2 8 = S ->
    exists r,
      msteps segs (mkst r2 (at_ sb 36) m rom) (mkst r ra (sk2_mem m fs hint i0 S) rom)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = ra /\ getr r 2 = S /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ regs_agree (fun x => In x SBCLOB2) r2 r.
  Proof using Hret Hi0 Hhint Hfsnz Hfs FR4 FR3 FR2 FR1 Hmcells PHm OKsh OKl OK24 OKf OKh Hz Hnz Rhint Rlog Rgc Rfs midend Hsb MTB MTOK HC_S mt.
    intros r2 Q10 Q2 Q8. destruct Hsb as [Hb2 Hb64]. pose proof (u64_range sb) as Hsbr.
    assert (RTM : ret_ok (at_ sb 332)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    destruct (blkS2 r2 Q10 Q2 Q8) as (r3 & RUN3 & A10 & A12 & A13 & A14 & A11 & A9 & A18 & A2 & A8 & AG3).
    destruct (sk2_loop (Z.to_nat i0) 0%Z r3 ltac:(lia) ltac:(lia) A10 A12 A13 A14) as (r4 & RUN4 & B12 & B15 & B17 & AG4).
    assert (B11 : getr r4 11 = Z_to_bv 64 (U fs + 4096)) by (rewrite (AG4 11 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB2 in G in change_no_check G' end); notin)); exact A11).
    assert (B9 : getr r4 9 = fs) by (rewrite (AG4 9 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB2 in G in change_no_check G' end); notin)); exact A9).
    assert (B18 : getr r4 18 = Z_to_bv 64 20) by (rewrite (AG4 18 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB2 in G in change_no_check G' end); notin)); exact A18).
    assert (B8 : getr r4 8 = S) by (rewrite (AG4 8 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB2 in G in change_no_check G' end); notin)); exact A8).
    assert (B2 : getr r4 2 = at_ S (-32)) by (rewrite (AG4 2 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB2 in G in change_no_check G' end); notin)); exact A2).
    destruct (blkS3 r4 B12 B15 B17 B11 B9 B18 B8 B2) as (r5 & RUN5 & C10 & C1 & C9 & C2 & AG5).
    destruct (m2s_run segs mt MTOK (sk2_mem4 m fs hint i0 S) rom (Z_to_bv 64 FRM) midend (at_ sb 332) r5 PH4 C10 C1 RTM)
      as (r6 & RUN6 & D10 & AG6).
    assert (UF : U (Z_to_bv 64 FRM) = FRM).
    { destruct Hfs as [Hf0 Hf1]. pose proof (u64_range fs). pose proof (u64_range S). pose proof (sk2_pos_rng hint i0). (lazymatch goal with |- ?G => let G' := eval unfold sk2_frame in G in change_no_check G' end). rewrite u_Z2bv; lia. }
    rewrite UF in D10. change (Z_to_bv 64 (FRM / 8 + 2147450880)) with (Z_to_bv 64 SHW) in D10.
    assert (D9 : getr r6 9 = Z_to_bv 64 FRM) by (rewrite (AG6 9 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact C9).
    assert (D2 : getr r6 2 = at_ S (-32)) by (rewrite (AG6 2 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact C2).
    destruct (blkS4 r6 D10 D9 D2) as (r7 & RUN7 & E10 & E1 & E2 & E8 & E9 & E18 & AG7).
    exists r7. split.
    - rewrite MTB in RUN6.
      eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|].
      eapply msteps_trans; [exact RUN6 | exact RUN7].
    - repeat (split; [assumption|]).
      eapply regs_agree_trans; [eapply regs_agree_trans; [eapply regs_agree_trans; [eapply regs_agree_trans|]|]|].
      + exact (regs_agree_mono _ _ _ _ SB_sub2 AG3).
      + exact (regs_agree_mono _ _ _ _ SB_subL AG4).
      + exact (regs_agree_mono _ _ _ _ SB_sub3 AG5).
      + exact (regs_agree_mono _ _ _ _ SB_subM AG6).
      + exact (regs_agree_mono _ _ _ _ SB_sub4 AG7).
  Qed.
End STKB.

Section STK.
  Variables (segs : list Segment) (sb : word).
  Variable tg : tlsga_tab.
  Variable mt : m2s_tab.
  Variable c_arg : word.
  Hypothesis HC_S : code_ato segs sb 0 stk2_words.
  Hypothesis TGOK : tlsga_tab_ok segs tg.
  Hypothesis TGHB : tg_hb tg = at_ sb 20676.
  Hypothesis MTOK : m2s_tab_ok segs mt.
  Hypothesis MTB : mt_base mt = at_ sb 840.
  Hypothesis A24 : gaddr2 segs sb 24 10 10 c_arg.
  Hypothesis Hsb : (U sb mod 2 = 0)%Z /\ (U sb + 30000 < 2 ^ 64)%Z.

  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables (ra S fs midend : word).
  Variable v : tlsga_vals.
  Variables (hint i0 : Z).
  #[local] Abbreviation FLG := (sk2_flag fs hint i0).
  #[local] Abbreviation FRM := (sk2_frame fs hint i0).
  #[local] Abbreviation SHW := (sk2_sh fs hint i0).
  Hypothesis TGH : tlsgaH segs tg mem (at_ S (-32)) v.
  Hypothesis Harg : tv_arg v = c_arg.
  Hypothesis Rfs : rdn segs mem (Z_to_bv 64 (U (tg_res v))) 8 = Some (W8 fs).
  Hypothesis Hres : (U (tg_res v) + 8 <= U S - 208)%Z.
  Hypothesis Rgc : rdn segs mem (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlog : rdn segs mem (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20).
  Hypothesis Rhint : rdn segs mem (Z_to_bv 64 (U fs + 16)) 8 = Some (LE8 hint).
  Hypothesis Hnz : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs mem (Z_to_bv 64 (sk2_flag fs hint j)) 1 = Some [b] /\ U b <> 0%Z.
  Hypothesis Hz : rdn segs mem (Z_to_bv 64 FLG) 1 = Some [Z_to_bv 8 0].
  Hypothesis OKh : store_ok segs mem (Z_to_bv 64 (U fs + 16)) 8 = true.
  Hypothesis OKf : store_ok segs mem (Z_to_bv 64 FLG) 1 = true.
  Hypothesis OK24 : store_ok segs mem (Z_to_bv 64 (FRM + 24)) 8 = true.
  Hypothesis OKl : store_ok segs mem (Z_to_bv 64 (FRM + 248)) 8 = true.
  Hypothesis OKsh : store_ok segs mem (Z_to_bv 64 SHW) 32 = true.
  Hypothesis PH : m2sH segs mt mem (Z_to_bv 64 FRM) midend.
  Hypothesis Hmcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells mt).
  Hypothesis Hfs : (0 < U fs /\ U fs + 3182592 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 3182592 <= U S - 208)%Z.
  Hypothesis Hhint : (0 <= hint)%Z.
  Hypothesis Hi0 : (0 <= i0 < 4096)%Z.
  Hypothesis HS : (208 <= U S)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ S (-32)) 32 = true.
  Hypothesis Hret : ret_ok ra.

  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = S.
  Hypothesis H4 : getr regs 4 = tv_tp v.

  #[local] Abbreviation M1 := (fl_frame mem S ra (getr regs 8) (getr regs 9) (getr regs 18)).

  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ S (-32)) _ 32);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.

  Lemma blkS1 :
    exists r,
      msteps segs (mkst regs (at_ sb 0) mem rom) (mkst r (at_ sb 20676) M1 rom)
      /\ getr r 10 = c_arg /\ getr r 1 = at_ sb 36 /\ getr r 2 = at_ S (-32) /\ getr r 8 = S /\ getr r 4 = tv_tp v
      /\ regs_agree (fun x => In x [1; 2; 8; 10]%list) regs r.
  Proof using H4 H2 H1 Hstk Hfs fs Hsb A24 HC_S.
    pose proof (u64_range S) as HSr. destruct Hsb as [Hb2 Hb64]. destruct A24 as [x24 AX].
    wd_eexists. split.
    - an (F_57468 segs sb HC_S) D_57468.
      fsd (F_5746c segs sb HC_S) D_5746c (at_ S (-8)).
      fsd (F_57470 segs sb HC_S) D_57470 (at_ S (-16)).
      fsd (F_57474 segs sb HC_S) D_57474 (at_ S (-24)).
      fsd (F_57478 segs sb HC_S) D_57478 (at_ S (-32)).
      change (wbytes _ _ _) with M1.
      an (F_5747c segs sb HC_S) D_5747c.
      eapply msteps_trans; [eapply AX|]; zlit_at.
      an (F_57488 segs sb HC_S) D_57488.
      wd_refl.
    - post; rewrite ?at_0; try reflexivity. ra_solve.
  Qed.

  Theorem stk2_run :
    exists r Mj,
      msteps segs (mkst regs (at_ sb 0) mem rom) (mkst r ra (sk2_mem Mj fs hint i0 S) rom)
      /\ scr_rel mem Mj (U S - 208) (U S)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = ra /\ getr r 2 = S
      /\ regs_agree (fun x => In x m2s_clob) regs r.
  Proof using H4 H2 H1 Hret Hstk Hi0 Hhint Hfs Hmcells PH OKsh OKl OK24 OKf OKh Hz Hnz Rhint Rlog Rgc Hres Rfs Harg TGH v midend Hsb A24 MTB MTOK TGHB TGOK HC_S c_arg mt tg.
    pose proof (u64_range S) as HSr. destruct Hsb as [Hb2 Hb64]. pose proof (u64_range sb) as Hsbr.
    destruct Hfs as [Hf0 Hf1]. pose proof (u64_range fs) as Hfr. pose proof (u64_range (tg_res v)) as Hrr.
    pose proof (sk2_pos_rng hint i0) as Hp.
    assert (RT36 : ret_ok (at_ sb 36)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    assert (US32 : U (at_ S (-32)) = (U S - 32)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    destruct blkS1 as (r1 & RUN1 & A10 & A1 & A2 & A8 & A4 & AG1).
    assert (TGH1 : tlsgaH segs tg M1 (at_ S (-32)) v).
    { apply (tlsgaH_above segs tg mem M1 (at_ S (-32)) v TGH); [apply fl_frame_grows|].
      intros a Ha. apply fl_frame_out; [lia | rewrite US32 in Ha; lia]. }
    rewrite <- Harg in A10.
    destruct (tlsga_run_t segs tg TGOK M1 rom (at_ sb 36) (at_ S (-32)) v r1 TGH1 RT36 A1 A2 A4 A10)
      as (r2 & Mj & RUN2 & SR & B10 & B1 & B2 & AG2).
    rewrite US32 in SR.
    assert (B8 : getr r2 8 = S) by (rewrite (AG2 8 ltac:(notin)); exact A8).
    assert (RDJ : forall c n bs, (0 <= c)%Z -> (c + Z.of_nat n <= U S - 208)%Z ->
                  rdn segs mem (Z_to_bv 64 c) n = Some bs -> rdn segs Mj (Z_to_bv 64 c) n = Some bs).
    { intros c n bs Hc0 Hc Hr.
      apply (scr_rel_rdn segs M1 Mj (U S - 32 - 176) (U S - 32) c n bs SR); [lia | lia | left; lia|].
      apply rd_fl_frame; [lia | lia | lia | exact Hr]. }
    assert (OKJ : forall (a : word) n, store_ok segs mem a n = true -> store_ok segs Mj a n = true).
    { intros a n OK. apply (scr_rel_ok segs M1 Mj _ _ a n SR). apply fl_frame_ok. exact OK. }
    assert (HFL : forall j, (U fs + 28672 <= sk2_flag fs hint j < U fs + 32768)%Z) by (intros j; pose proof (sk2_pos_rng hint j); (lazymatch goal with |- ?G => let G' := eval unfold sk2_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 2134016 <= FRM /\ FRM + 256 <= U fs + 3182592)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk2_frame in G in change_no_check G' end); lia).
    assert (SLOT : forall k vv, (k = 8 \/ k = 16 \/ k = 24 \/ k = 32)%Z ->
                   rdn segs M1 (at_ S (- k)) 8 = Some (W8 vv) -> rdn segs Mj (at_ S (- k)) 8 = Some (W8 vv)).
    { intros k vv Hk Hr. destruct SR as (O & _ & _).
      rewrite (rdn_ext segs 8 Mj M1 (at_ S (- k))); [exact Hr | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u by lia; intros x Hx; apply O; lia]. }
    assert (PHJ : m2sH segs mt Mj (Z_to_bv 64 FRM) midend).
    { pose proof Hmcells as HC. unfold m2s_cells in HC.
      repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
      destruct PH as [R1 R2 R3 R4 R5 R6 R7 R8 HCx Hlo Hhi].
      constructor; try assumption; apply RDJ; try assumption; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia. }
    destruct (stkB_run segs sb mt HC_S MTOK MTB (conj Hb2 Hb64) Mj rom ra S (tg_res v) fs midend (getr regs 8) (getr regs 9) (getr regs 18) hint i0)
      with (r2 := r2) as (r & RUN3 & E10 & E1 & E2 & E8 & E9 & E18 & AG3).
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rfs]. }
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rgc]. }
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rlog]. }
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rhint]. }
    { intros j Hj. destruct (Hnz j Hj) as (b & Rb & Nb). exists b. split; [|exact Nb].
      pose proof (HFL j). apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rb]. }
    { pose proof (HFL i0). apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hz]. }
    { apply OKJ; exact OKh. } { apply OKJ; exact OKf. } { apply OKJ; exact OK24. } { apply OKJ; exact OKl. } { apply OKJ; exact OKsh. }
    { exact PHJ. }
    { exact Hmcells. }
    { apply (SLOT 8%Z ra); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { apply (SLOT 16%Z (getr regs 8)); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { apply (SLOT 24%Z (getr regs 9)); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { apply (SLOT 32%Z (getr regs 18)); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { split; lia. }
    { lia. }
    { exact Hhint. }
    { exact Hi0. }
    { exact Hret. }
    { exact B10. }
    { exact B2. }
    { exact B8. }
    exists r, Mj. split; [|split; [|split; [exact E10 | split; [exact E1 | split; [exact E2|]]]]].
    - rewrite TGHB in RUN2. eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3].
    - apply (scr_rel_trans mem M1 Mj).
      + (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end).
        repeat (apply scr_rel_wb; [ | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ] | wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia | lia ]).
        apply scr_rel_refl.
      + apply (scr_rel_mono M1 Mj _ _ _ _ SR); lia.
    - intros x Hx.
      destruct (In_dec (fun a b : reg => decide (a = b)) x [1; 2; 8; 9; 18]%list) as [I|NI].
      + cbn [In] in I.
        repeat (destruct I as [<-|I]; [first [rewrite E1; symmetry; exact H1 | rewrite E2; symmetry; exact H2 | exact E8 | exact E9 | exact E18] |]).
        destruct I.
      + assert (NB : ~ In x SBCLOB2).
        { intros I. unfold SBCLOB2 in I. unfold m2s_clob in Hx. cbn [In] in I, NI, Hx. am_tauto. }
        rewrite (AG3 x NB). rewrite (AG2 x). 2:{ intros I. unfold m2s_clob in Hx. cbn [In] in I, Hx. am_tauto. }
        apply AG1. intros I. unfold m2s_clob in Hx. cbn [In] in I, NI, Hx. am_tauto.
  Qed.
End STK.

(* [comment removed for export] *)
Definition stk2_tab_ok (segs : list Segment) (t : stk_tab) : Prop :=
  code_ato segs (sk_base t) 0 stk2_words
  /\ tlsga_tab_ok segs (sk_tg t) /\ tg_hb (sk_tg t) = at_ (sk_base t) 20676
  /\ m2s_tab_ok segs (sk_mt t) /\ mt_base (sk_mt t) = at_ (sk_base t) 840
  /\ gaddr2 segs (sk_base t) 24 10 10 (sk_arg t)
  /\ ((U (sk_base t) mod 2 = 0)%Z /\ (U (sk_base t) + 30000 < 2 ^ 64)%Z).

Record stk2H (segs : list Segment) (t : stk_tab) (mem : word -> option byte) (S fs midend : word) (v : tlsga_vals) (hint i0 : Z) : Prop := SK2H {
  s2h_tls : tlsgaH segs (sk_tg t) mem (at_ S (-32)) v;
  s2h_arg : tv_arg v = sk_arg t;
  s2h_fs : rdn segs mem (Z_to_bv 64 (U (tg_res v))) 8 = Some (W8 fs);
  s2h_res : (U (tg_res v) + 8 <= U S - 208)%Z;
  s2h_gc : rdn segs mem (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0];
  s2h_log : rdn segs mem (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20);
  s2h_hint : rdn segs mem (Z_to_bv 64 (U fs + 16)) 8 = Some (LE8 hint);
  s2h_busy : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs mem (Z_to_bv 64 (sk2_flag fs hint j)) 1 = Some [b] /\ U b <> 0%Z;
  s2h_free : rdn segs mem (Z_to_bv 64 (sk2_flag fs hint i0)) 1 = Some [Z_to_bv 8 0];
  s2h_ok_hint : store_ok segs mem (Z_to_bv 64 (U fs + 16)) 8 = true;
  s2h_ok_flag : store_ok segs mem (Z_to_bv 64 (sk2_flag fs hint i0)) 1 = true;
  s2h_ok_24 : store_ok segs mem (Z_to_bv 64 (sk2_frame fs hint i0 + 24)) 8 = true;
  s2h_ok_last : store_ok segs mem (Z_to_bv 64 (sk2_frame fs hint i0 + 248)) 8 = true;
  s2h_ok_sh : store_ok segs mem (Z_to_bv 64 (sk2_sh fs hint i0)) 32 = true;
  s2h_m2s : m2sH segs (sk_mt t) mem (Z_to_bv 64 (sk2_frame fs hint i0)) midend;
  s2h_mcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells (sk_mt t));
  s2h_geom : (0 < U fs /\ U fs + 3182592 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 3182592 <= U S - 208)%Z;
  s2h_hintr : (0 <= hint)%Z;
  s2h_i0 : (0 <= i0 < 4096)%Z;
  s2h_S : (208 <= U S)%Z;
  s2h_stk : store_ok segs mem (at_ S (-32)) 32 = true }.

Theorem stk2_run_t : forall segs t, stk2_tab_ok segs t ->
  forall mem rom (ra S fs midend : word) v hint i0 regs,
  stk2H segs t mem S fs midend v hint i0 -> ret_ok ra ->
  getr regs 1 = ra -> getr regs 2 = S -> getr regs 4 = tv_tp v ->
  exists r Mj,
    msteps segs (mkst regs (sk_base t) mem rom) (mkst r ra (sk2_mem Mj fs hint i0 S) rom)
    /\ scr_rel mem Mj (U S - 208) (U S)
    /\ getr r 10 = Z_to_bv 64 (sk2_frame fs hint i0) /\ getr r 1 = ra /\ getr r 2 = S
    /\ regs_agree (fun x => In x m2s_clob) regs r.
Proof using.
  intros segs t (C1 & TG & TGB & MT & MTB & A24 & HB) mem rom ra S fs midend v hint i0 regs
         [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21] Hret H1 H2 H4.
  replace (mkst regs (sk_base t) mem rom) with (mkst regs (at_ (sk_base t) 0) mem rom) by (rewrite at_0; reflexivity).
  first [ exact (stk2_run segs (sk_base t) (sk_tg t) (sk_mt t) (sk_arg t) C1 TG TGB MT MTB A24 HB mem rom ra S fs midend v hint i0
           P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 Hret regs H1 H2 H4)
        | exact (stk2_run segs (sk_base t) (sk_tg t) (sk_mt t) (sk_arg t) C1 TG TGB MT MTB A24 HB mem rom ra S fs midend v hint i0
           P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P21 Hret regs H1 H2 H4) ].
Qed.
End FPGen1.
End AsRtStkMal2.
Module AsRtStkMal3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation W8 w := (word_to_le_bytes 8 w).
#[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

Definition sk3_pos (hint i : Z) : Z := ((hint + i) mod 2048)%Z.
Definition sk3_flag (fs : word) (hint i : Z) : Z := (U fs + 32768 + sk3_pos hint i)%Z.
Definition sk3_frame (fs : word) (hint i : Z) : Z := (U fs + 3182592 + sk3_pos hint i * 512)%Z.
Definition sk3_sh (fs : word) (hint i : Z) : Z := (sk3_frame fs hint i / 8 + 0x7fff8000)%Z.

Definition sk3_mem4 (m : word -> option byte) (fs : word) (hint i0 : Z) (S : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (U fs + 24)) (LE8 (hint + i0 + 1)))
    (Z_to_bv 64 (sk3_flag fs hint i0)) [Z_to_bv 8 1])
    (Z_to_bv 64 (sk3_frame fs hint i0 + 24)) (W8 S))
    (Z_to_bv 64 (sk3_frame fs hint i0 + 504)) (LE8 (sk3_flag fs hint i0)).
Definition sk3_mem (m : word -> option byte) (fs : word) (hint i0 : Z) (S : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (sk3_mem4 m fs hint i0 S) (Z_to_bv 64 (sk3_sh fs hint i0 + 0)) (LE8 0)) (Z_to_bv 64 (sk3_sh fs hint i0 + 8)) (LE8 0)) (Z_to_bv 64 (sk3_sh fs hint i0 + 16)) (LE8 0)) (Z_to_bv 64 (sk3_sh fs hint i0 + 24)) (LE8 0)) (Z_to_bv 64 (sk3_sh fs hint i0 + 32)) (LE8 0)) (Z_to_bv 64 (sk3_sh fs hint i0 + 40)) (LE8 0)) (Z_to_bv 64 (sk3_sh fs hint i0 + 48)) (LE8 0)) (Z_to_bv 64 (sk3_sh fs hint i0 + 56)) (LE8 0).

Lemma sk3_pos_rng : forall hint i, (0 <= sk3_pos hint i < 2048)%Z.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk3_pos in G in change_no_check G' end). apply Z.mod_pos_bound. lia. Qed.
Lemma v_and_mask3 : forall z, v_and (Z_to_bv 64 z) (Z_to_bv 64 2047) = Z_to_bv 64 (z mod 2048).
Proof using. intros z. exact (v_and_maskN (14 - 3) z ltac:(lia)). Qed.
Lemma sk3_sh_rng : forall (fs : word) hint i, (U fs + 4231168 <= 2 ^ 47)%Z ->
  (0x7fff8000 <= sk3_sh fs hint i /\ sk3_sh fs hint i + 64 <= 0x10007fff8000)%Z.
Proof using.
  intros fs hint i H64. pose proof (u64_range fs) as Hfr. (lazymatch goal with |- ?G => let G' := eval unfold sk3_sh, sk3_frame in G in change_no_check G' end). pose proof (sk3_pos_rng hint i) as Hp.
  pose proof (Z.div_pos (U fs + 3182592 + sk3_pos hint i * 512) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (U fs + 3182592 + sk3_pos hint i * 512) 8 (2 ^ 44 - 64) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma v_slli_s3 : forall z, (0 <= z < 2 ^ 32)%Z -> v_slli (Z_to_bv 64 z) 9 = Z_to_bv 64 (z * 512).
Proof using. intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end). rewrite u_Z2bv by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Ltac av_and F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply AsRtFlush.step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

(* [comment removed for export] *)
Definition stk3_words : list (option (bv 32)) :=
  [
   Some W_57604; Some W_57608; Some W_5760c; Some W_57610; Some W_57614; Some W_57618; None; None; Some W_57624;
   Some W_57628; Some W_5762c; Some W_57630; Some W_57634; Some W_57638; Some W_5763c; Some W_57640; Some W_57644;
   Some W_57648; Some W_5764c; Some W_57650; Some W_57654; Some W_57658; Some W_5765c; Some W_57660; Some W_57664;
   Some W_57668; Some W_5766c; Some W_57670; Some W_57674; Some W_57678; Some W_5767c; Some W_57680; Some W_57684;
   Some W_57688; Some W_5768c; Some W_57690; Some W_57694; Some W_57698; Some W_5769c; Some W_576a0; Some W_576a4;
   Some W_576a8; Some W_576ac; Some W_576b0; Some W_576b4; Some W_576b8; None; None; Some W_576c4; Some W_576c8;
   Some W_576cc; Some W_576d0; Some W_576d4; Some W_576d8; Some W_576dc; Some W_576e0; Some W_576e4; Some W_576e8;
   Some W_576ec; Some W_576f0; Some W_576f4; Some W_576f8; Some W_576fc; Some W_57700; Some W_57704; Some W_57708;
   Some W_5770c; Some W_57710; Some W_57714; Some W_57718; Some W_5771c; Some W_57720; Some W_57724; Some W_57728;
   Some W_5772c; Some W_57730; Some W_57734; Some W_57738; Some W_5773c; Some W_57740; Some W_57744; Some W_57748;
   Some W_5774c; Some W_57750; Some W_57754; Some W_57758; Some W_5775c; Some W_57760; Some W_57764; Some W_57768;
   Some W_5776c; Some W_57770; Some W_57774; Some W_57778; Some W_5777c; Some W_57780; Some W_57784; Some W_57788;
   Some W_5778c; Some W_57790; Some W_57794; Some W_57798; Some W_5779c; Some W_577a0; Some W_577a4; Some W_577a8;
   Some W_577ac
  ]%list.

Section STKB.
  Variables (segs : list Segment) (sb : word).
  Variable mt : m2s_tab.
  Hypothesis HC_S : code_ato segs sb 0 stk3_words.
  Hypothesis MTOK : m2s_tab_ok segs mt.
  Hypothesis MTB : mt_base mt = at_ sb 428.
  Hypothesis Hsb : (U sb mod 2 = 0)%Z /\ (U sb + 30000 < 2 ^ 64)%Z.


  Lemma F_57604 : fetch_word segs (at_ sb 0) = Some W_57604.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 0 _ HC_S eq_refl). Qed.
  Lemma F_57608 : fetch_word segs (at_ sb 4) = Some W_57608.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 1 _ HC_S eq_refl). Qed.
  Lemma F_5760c : fetch_word segs (at_ sb 8) = Some W_5760c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 2 _ HC_S eq_refl). Qed.
  Lemma F_57610 : fetch_word segs (at_ sb 12) = Some W_57610.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 3 _ HC_S eq_refl). Qed.
  Lemma F_57614 : fetch_word segs (at_ sb 16) = Some W_57614.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 4 _ HC_S eq_refl). Qed.
  Lemma F_57618 : fetch_word segs (at_ sb 20) = Some W_57618.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 5 _ HC_S eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma F_57624 : fetch_word segs (at_ sb 32) = Some W_57624.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 8 _ HC_S eq_refl). Qed.
  Lemma F_57628 : fetch_word segs (at_ sb 36) = Some W_57628.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 9 _ HC_S eq_refl). Qed.
  Lemma F_5762c : fetch_word segs (at_ sb 40) = Some W_5762c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 10 _ HC_S eq_refl). Qed.
  Lemma F_57630 : fetch_word segs (at_ sb 44) = Some W_57630.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 11 _ HC_S eq_refl). Qed.
  Lemma F_57634 : fetch_word segs (at_ sb 48) = Some W_57634.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 12 _ HC_S eq_refl). Qed.
  Lemma F_57638 : fetch_word segs (at_ sb 52) = Some W_57638.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 13 _ HC_S eq_refl). Qed.



  Lemma F_57648 : fetch_word segs (at_ sb 68) = Some W_57648.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 17 _ HC_S eq_refl). Qed.
  Lemma F_5764c : fetch_word segs (at_ sb 72) = Some W_5764c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 18 _ HC_S eq_refl). Qed.
  Lemma F_57650 : fetch_word segs (at_ sb 76) = Some W_57650.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 19 _ HC_S eq_refl). Qed.
  Lemma F_57654 : fetch_word segs (at_ sb 80) = Some W_57654.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 20 _ HC_S eq_refl). Qed.
  Lemma F_57658 : fetch_word segs (at_ sb 84) = Some W_57658.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 21 _ HC_S eq_refl). Qed.
  Lemma F_5765c : fetch_word segs (at_ sb 88) = Some W_5765c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 22 _ HC_S eq_refl). Qed.
  Lemma F_57660 : fetch_word segs (at_ sb 92) = Some W_57660.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 23 _ HC_S eq_refl). Qed.
  Lemma F_57664 : fetch_word segs (at_ sb 96) = Some W_57664.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 24 _ HC_S eq_refl). Qed.
  Lemma F_57668 : fetch_word segs (at_ sb 100) = Some W_57668.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 25 _ HC_S eq_refl). Qed.
  Lemma F_5766c : fetch_word segs (at_ sb 104) = Some W_5766c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 26 _ HC_S eq_refl). Qed.
  Lemma F_57670 : fetch_word segs (at_ sb 108) = Some W_57670.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 27 _ HC_S eq_refl). Qed.
  Lemma F_57674 : fetch_word segs (at_ sb 112) = Some W_57674.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 28 _ HC_S eq_refl). Qed.
  Lemma F_57678 : fetch_word segs (at_ sb 116) = Some W_57678.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 29 _ HC_S eq_refl). Qed.
  Lemma F_5767c : fetch_word segs (at_ sb 120) = Some W_5767c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 30 _ HC_S eq_refl). Qed.
  Lemma F_57680 : fetch_word segs (at_ sb 124) = Some W_57680.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 31 _ HC_S eq_refl). Qed.
  Lemma F_57684 : fetch_word segs (at_ sb 128) = Some W_57684.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 32 _ HC_S eq_refl). Qed.
  Lemma F_57688 : fetch_word segs (at_ sb 132) = Some W_57688.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 33 _ HC_S eq_refl). Qed.
  Lemma F_5768c : fetch_word segs (at_ sb 136) = Some W_5768c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 34 _ HC_S eq_refl). Qed.
  Lemma F_57690 : fetch_word segs (at_ sb 140) = Some W_57690.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 35 _ HC_S eq_refl). Qed.
  Lemma F_57694 : fetch_word segs (at_ sb 144) = Some W_57694.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 36 _ HC_S eq_refl). Qed.
  Lemma F_57698 : fetch_word segs (at_ sb 148) = Some W_57698.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 37 _ HC_S eq_refl). Qed.
  Lemma F_5769c : fetch_word segs (at_ sb 152) = Some W_5769c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 38 _ HC_S eq_refl). Qed.
  Lemma F_576a0 : fetch_word segs (at_ sb 156) = Some W_576a0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 39 _ HC_S eq_refl). Qed.
  Lemma F_576a4 : fetch_word segs (at_ sb 160) = Some W_576a4.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 40 _ HC_S eq_refl). Qed.
  Lemma F_576a8 : fetch_word segs (at_ sb 164) = Some W_576a8.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 41 _ HC_S eq_refl). Qed.
  Lemma F_576ac : fetch_word segs (at_ sb 168) = Some W_576ac.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 42 _ HC_S eq_refl). Qed.
  Lemma F_576b0 : fetch_word segs (at_ sb 172) = Some W_576b0.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 43 _ HC_S eq_refl). Qed.





















  Lemma F_57710 : fetch_word segs (at_ sb 268) = Some W_57710.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 67 _ HC_S eq_refl). Qed.
  Lemma F_57714 : fetch_word segs (at_ sb 272) = Some W_57714.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 68 _ HC_S eq_refl). Qed.
  Lemma F_57718 : fetch_word segs (at_ sb 276) = Some W_57718.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 69 _ HC_S eq_refl). Qed.
  Lemma F_5771c : fetch_word segs (at_ sb 280) = Some W_5771c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 70 _ HC_S eq_refl). Qed.
  Lemma F_57720 : fetch_word segs (at_ sb 284) = Some W_57720.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 71 _ HC_S eq_refl). Qed.
  Lemma F_57724 : fetch_word segs (at_ sb 288) = Some W_57724.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 72 _ HC_S eq_refl). Qed.
  Lemma F_57728 : fetch_word segs (at_ sb 292) = Some W_57728.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 73 _ HC_S eq_refl). Qed.
  Lemma F_5772c : fetch_word segs (at_ sb 296) = Some W_5772c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 74 _ HC_S eq_refl). Qed.
  Lemma F_57730 : fetch_word segs (at_ sb 300) = Some W_57730.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 75 _ HC_S eq_refl). Qed.
  Lemma F_57734 : fetch_word segs (at_ sb 304) = Some W_57734.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 76 _ HC_S eq_refl). Qed.
  Lemma F_57738 : fetch_word segs (at_ sb 308) = Some W_57738.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 77 _ HC_S eq_refl). Qed.
  Lemma F_5773c : fetch_word segs (at_ sb 312) = Some W_5773c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 78 _ HC_S eq_refl). Qed.
  Lemma F_57740 : fetch_word segs (at_ sb 316) = Some W_57740.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 79 _ HC_S eq_refl). Qed.
  Lemma F_57744 : fetch_word segs (at_ sb 320) = Some W_57744.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 80 _ HC_S eq_refl). Qed.
  Lemma F_57748 : fetch_word segs (at_ sb 324) = Some W_57748.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 81 _ HC_S eq_refl). Qed.
  Lemma F_5774c : fetch_word segs (at_ sb 328) = Some W_5774c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 82 _ HC_S eq_refl). Qed.
  Lemma F_57750 : fetch_word segs (at_ sb 332) = Some W_57750.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 83 _ HC_S eq_refl). Qed.
  Lemma F_57754 : fetch_word segs (at_ sb 336) = Some W_57754.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 84 _ HC_S eq_refl). Qed.
  Lemma F_57758 : fetch_word segs (at_ sb 340) = Some W_57758.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 85 _ HC_S eq_refl). Qed.
  Lemma F_5775c : fetch_word segs (at_ sb 344) = Some W_5775c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 86 _ HC_S eq_refl). Qed.
  Lemma F_57760 : fetch_word segs (at_ sb 348) = Some W_57760.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 87 _ HC_S eq_refl). Qed.
  Lemma F_57764 : fetch_word segs (at_ sb 352) = Some W_57764.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 88 _ HC_S eq_refl). Qed.
  Lemma F_57768 : fetch_word segs (at_ sb 356) = Some W_57768.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 89 _ HC_S eq_refl). Qed.
  Lemma F_5776c : fetch_word segs (at_ sb 360) = Some W_5776c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 90 _ HC_S eq_refl). Qed.
  Lemma F_57770 : fetch_word segs (at_ sb 364) = Some W_57770.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 91 _ HC_S eq_refl). Qed.
  Lemma F_57774 : fetch_word segs (at_ sb 368) = Some W_57774.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 92 _ HC_S eq_refl). Qed.
  Lemma F_57778 : fetch_word segs (at_ sb 372) = Some W_57778.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 93 _ HC_S eq_refl). Qed.
  Lemma F_5777c : fetch_word segs (at_ sb 376) = Some W_5777c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 94 _ HC_S eq_refl). Qed.
  Lemma F_57780 : fetch_word segs (at_ sb 380) = Some W_57780.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 95 _ HC_S eq_refl). Qed.
  Lemma F_57784 : fetch_word segs (at_ sb 384) = Some W_57784.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 96 _ HC_S eq_refl). Qed.
  Lemma F_57788 : fetch_word segs (at_ sb 388) = Some W_57788.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 97 _ HC_S eq_refl). Qed.
  Lemma F_5778c : fetch_word segs (at_ sb 392) = Some W_5778c.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 98 _ HC_S eq_refl). Qed.
  Lemma F_57790 : fetch_word segs (at_ sb 396) = Some W_57790.   (* [comment removed for export] *)
  Proof using HC_S. exact (code_ato_get segs sb 0 stk3_words 99 _ HC_S eq_refl). Qed.








  Variable m : word -> option byte.
  Variable rom : word -> option byte.
  Variables (ra S resw fs midend s0v s1v s2v : word).
  Variables (hint i0 : Z).
  #[local] Abbreviation FLG := (sk3_flag fs hint i0).
  #[local] Abbreviation FRM := (sk3_frame fs hint i0).
  #[local] Abbreviation SHW := (sk3_sh fs hint i0).
  Hypothesis Rfs : rdn segs m (Z_to_bv 64 (U resw)) 8 = Some (W8 fs).
  Hypothesis Rgc : rdn segs m (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlog : rdn segs m (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20).
  Hypothesis Rhint : rdn segs m (Z_to_bv 64 (U fs + 24)) 8 = Some (LE8 hint).
  Hypothesis Hnz : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs m (Z_to_bv 64 (sk3_flag fs hint j)) 1 = Some [b] /\ U b <> 0%Z.
  Hypothesis Hz : rdn segs m (Z_to_bv 64 FLG) 1 = Some [Z_to_bv 8 0].
  Hypothesis OKh : store_ok segs m (Z_to_bv 64 (U fs + 24)) 8 = true.
  Hypothesis OKf : store_ok segs m (Z_to_bv 64 FLG) 1 = true.
  Hypothesis OK24 : store_ok segs m (Z_to_bv 64 (FRM + 24)) 8 = true.
  Hypothesis OKl : store_ok segs m (Z_to_bv 64 (FRM + 504)) 8 = true.
  Hypothesis OKsh : store_ok segs m (Z_to_bv 64 SHW) 64 = true.
  Hypothesis PHm : m2sH segs mt m (Z_to_bv 64 FRM) midend.
  Hypothesis Hmcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells mt).
  Hypothesis FR1 : rdn segs m (at_ S (-8)) 8 = Some (W8 ra).
  Hypothesis FR2 : rdn segs m (at_ S (-16)) 8 = Some (W8 s0v).
  Hypothesis FR3 : rdn segs m (at_ S (-24)) 8 = Some (W8 s1v).
  Hypothesis FR4 : rdn segs m (at_ S (-32)) 8 = Some (W8 s2v).
  Hypothesis Hfs : (0 < U fs /\ U fs + 4231168 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 4231168 <= U S - 32)%Z.
  Hypothesis Hfsnz : (U fs <> 0)%Z.
  Hypothesis Hhint : (0 <= hint)%Z.
  Hypothesis Hi0 : (0 <= i0 < 2048)%Z.
  Hypothesis HS : (32 <= U S)%Z.
  Hypothesis Hret : ret_ok ra.

  Ltac addr_eq :=
    apply bv_eq; rewrite ?v_addi_0;
    repeat match goal with |- context [v_addi ?b ?e] => change (v_addi b e) with (at_ b e) end;
    (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  Ltac rdm Hr :=
    repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]);
    lazymatch goal with |- rdn _ m _ _ = _ => exact Hr end.
  Ltac cldz F D cc vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 cc : word) by addr_eq end;
          rdm Hr
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Ltac clbu F D cc Hr :=
    chain_step; [reflexivity
      | eapply step_lbu; [exact F | reflexivity | exact D | ];
        gres; rwH; imm_norm;
        lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 cc : word) by addr_eq end;
        rdm Hr
      | step_simpl]; vn.

  Definition LCLOB3 : list reg := [5; 10; 12; 15; 17]%list.

  Lemma sk3_iter : forall (i : Z) r,
    (0 <= i < i0)%Z ->
    getr r 10 = Z_to_bv 64 (2048 - i) -> getr r 12 = Z_to_bv 64 (hint + i) ->
    getr r 13 = Z_to_bv 64 (U fs + 32768) -> getr r 14 = Z_to_bv 64 2047 ->
    exists r',
      msteps segs (mkst r (at_ sb 148) m rom) (mkst r' (at_ sb 148) m rom)
      /\ getr r' 10 = Z_to_bv 64 (2048 - (i + 1)) /\ getr r' 12 = Z_to_bv 64 (hint + (i + 1))
      /\ regs_agree (fun x => In x LCLOB3) r r'.
  Proof using Hi0 Hhint Hfsnz Hfs Hnz S HC_S.
    intros i r Hi Q10 Q12 Q13 Q14. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk3_pos_rng hint i) as Hp.
    destruct (Hnz i Hi) as (b & Rb & Nb). pose proof (u8_range b) as Hb8.
    wd_eexists. split.
    - av_and F_57698 D_57698 (Z_to_bv 64 (sk3_pos hint i)) ltac:(rewrite v_and_mask3; reflexivity).
      av F_5769c D_5769c (Z_to_bv 64 (sk3_flag fs hint i)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, sk3_flag in G in change_no_check G' end); unorm; f_equal; lia).
      clbu F_576a0 D_576a0 (sk3_flag fs hint i) Rb.
      ab_ft F_576a4 D_576a4 ltac:(condz).
      av F_576a8 D_576a8 (Z_to_bv 64 (2048 - (i + 1))) ltac:(rewrite v_addiw_m1 by lia; f_equal; lia).
      av F_576ac D_576ac (Z_to_bv 64 (hint + (i + 1))) ltac:(rewrite v_addi_Z; f_equal; lia).
      ab_tk F_576b0 D_576b0 ltac:(condz).
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold LCLOB3 in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma sk3_loop : forall (n : nat) (i : Z) r,
    (0 <= i)%Z -> (i + Z.of_nat n = i0)%Z ->
    getr r 10 = Z_to_bv 64 (2048 - i) -> getr r 12 = Z_to_bv 64 (hint + i) ->
    getr r 13 = Z_to_bv 64 (U fs + 32768) -> getr r 14 = Z_to_bv 64 2047 ->
    exists r',
      msteps segs (mkst r (at_ sb 148) m rom) (mkst r' (at_ sb 268) m rom)
      /\ getr r' 12 = Z_to_bv 64 (hint + i0) /\ getr r' 15 = Z_to_bv 64 FLG /\ getr r' 17 = Z_to_bv 64 (sk3_pos hint i0)
      /\ regs_agree (fun x => In x LCLOB3) r r'.
  Proof using Hi0 Hhint Hfsnz Hfs Hz Hnz S HC_S.
    induction n as [|n IH]; intros i r Hi0' Hin Q10 Q12 Q13 Q14.
    - assert (i = i0) by lia. subst i. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
      pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk3_pos_rng hint i0) as Hp.
      wd_eexists. split.
      + av_and F_57698 D_57698 (Z_to_bv 64 (sk3_pos hint i0)) ltac:(rewrite v_and_mask3; reflexivity).
        av F_5769c D_5769c (Z_to_bv 64 FLG) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, sk3_flag in G in change_no_check G' end); unorm; f_equal; lia).
        clbu F_576a0 D_576a0 (sk3_flag fs hint i0) Hz.
        ab_tk F_576a4 D_576a4 ltac:(vals_lit; condz).
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold LCLOB3 in G in change_no_check G' end). ra_solve.
    - destruct (sk3_iter i r ltac:(lia) Q10 Q12 Q13 Q14) as (r1 & RUN1 & A10 & A12 & AG1).
      assert (A13 : getr r1 13 = Z_to_bv 64 (U fs + 32768)) by (rewrite (AG1 13 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB3 in G in change_no_check G' end); notin)); exact Q13).
      assert (A14 : getr r1 14 = Z_to_bv 64 2047) by (rewrite (AG1 14 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB3 in G in change_no_check G' end); notin)); exact Q14).
      destruct (IH (i + 1)%Z r1 ltac:(lia) ltac:(lia) A10 A12 A13 A14) as (r' & RUN2 & B12 & B15 & B17 & AG2).
      exists r'. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. repeat (split; [assumption|]).
      eapply regs_agree_trans; eassumption.
  Qed.

  Ltac wsd F D cc OKT :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := Z_to_bv 64 cc);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; addr_eq
        | gres; rwH; reflexivity
        | (lazymatch goal with |- ?G => let G' := eval unfold sk3_mem4 in G in change_no_check G' end); repeat (eapply store_ok_mono; [apply wbytes_grows|]); OKT ]
      | step_simpl]; vn.
  Ltac fldm F D vv FR :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold sk3_mem, sk3_mem4 in G in change_no_check G' end);
          repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]); exact FR
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  Definition S2CLOB3 : list reg := [9; 18; 10; 11; 12; 13; 14; 15; 16]%list.

  Lemma blkS2 : forall r2,
    getr r2 10 = resw -> getr r2 2 = at_ S (-32) -> getr r2 8 = S ->
    exists r,
      msteps segs (mkst r2 (at_ sb 36) m rom) (mkst r (at_ sb 148) m rom)
      /\ getr r 10 = Z_to_bv 64 (2048 - 0) /\ getr r 12 = Z_to_bv 64 (hint + 0)
      /\ getr r 13 = Z_to_bv 64 (U fs + 32768) /\ getr r 14 = Z_to_bv 64 2047
      /\ getr r 11 = Z_to_bv 64 (U fs + 4096)
      /\ getr r 9 = fs /\ getr r 18 = Z_to_bv 64 20 /\ getr r 2 = at_ S (-32) /\ getr r 8 = S
      /\ regs_agree (fun x => In x S2CLOB3) r2 r.
  Proof using Hhint Hfsnz Hfs Rhint Rlog Rgc Rfs HC_S.
    intros r2 Q10 Q2 Q8. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (u64_range resw) as Hrr.
    wd_eexists. split.
    - cldz F_57628 D_57628 (U resw) fs Rfs.
      ab_ft F_5762c D_5762c ltac:(condz).
      clbu F_57630 D_57630 (U fs + 96)%Z Rgc.
      cldz F_57634 D_57634 (U fs + 88)%Z (Z_to_bv 64 20) Rlog.
      ab_tk F_57638 D_57638 ltac:(vals_lit; condz).
      an F_57648 D_57648. an F_5764c D_5764c. an F_57650 D_57650. an F_57654 D_57654.
      ab_ft F_57658 D_57658 ltac:(vm_compute; reflexivity).
      an F_5765c D_5765c. an F_57660 D_57660. an F_57664 D_57664. an F_57668 D_57668. an F_5766c D_5766c.
      cldz F_57670 D_57670 (U fs + 24)%Z (Z_to_bv 64 hint) Rhint.
      an F_57674 D_57674. an F_57678 D_57678.
      av F_5767c D_5767c (Z_to_bv 64 (U fs + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).
      av F_57680 D_57680 (Z_to_bv 64 (U fs + 32768)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).
      an F_57684 D_57684. an F_57688 D_57688. an F_5768c D_5768c.
      av F_57690 D_57690 (Z_to_bv 64 (hint + 2047)) ltac:(rewrite v_add_ZZ; reflexivity).
      av F_57694 D_57694 (Z_to_bv 64 (hint + 2048)) ltac:(rewrite v_addi_Z; f_equal; lia).
      wd_refl.
    - post; try (apply bv_eq; vm_compute; reflexivity). (lazymatch goal with |- ?G => let G' := eval unfold S2CLOB3 in G in change_no_check G' end). ra_solve.
  Qed.

  Definition S3CLOB3 : list reg := [1; 9; 10; 11; 12; 13; 17]%list.

  Lemma blkS3 : forall r4,
    getr r4 12 = Z_to_bv 64 (hint + i0) -> getr r4 15 = Z_to_bv 64 FLG -> getr r4 17 = Z_to_bv 64 (sk3_pos hint i0) ->
    getr r4 11 = Z_to_bv 64 (U fs + 4096) -> getr r4 9 = fs -> getr r4 18 = Z_to_bv 64 20 -> getr r4 8 = S -> getr r4 2 = at_ S (-32) ->
    exists r,
      msteps segs (mkst r4 (at_ sb 268) m rom) (mkst r (at_ sb 428) (sk3_mem4 m fs hint i0 S) rom)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = at_ sb 332 /\ getr r 9 = Z_to_bv 64 FRM /\ getr r 2 = at_ S (-32)
      /\ regs_agree (fun x => In x S3CLOB3) r4 r.
  Proof using Hhint Hfsnz Hfs OKl OK24 OKf OKh HC_S.
    intros r4 Q12 Q15 Q17 Q11 Q9 Q18 Q8 Q2. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk3_pos_rng hint i0) as Hp.
    assert (HFL : (U fs + 32768 <= FLG < U fs + 34816)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk3_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 3182592 <= FRM /\ FRM + 512 <= U fs + 4231168)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk3_frame in G in change_no_check G' end); lia).
    wd_eexists. split.
    - av F_57710 D_57710 (Z_to_bv 64 (hint + i0 + 1)) ltac:(rewrite v_addi_Z; reflexivity).
      an F_57714 D_57714. an F_57718 D_57718.
      wsd F_5771c D_5771c (U fs + 24)%Z ltac:(exact OKh).
      chain_step; [reflexivity
        | eapply step_sb_at with (a := Z_to_bv 64 FLG) (v := Z_to_bv 64 1) (b := Z_to_bv 8 1);
          [exact F_57720 | reflexivity | exact D_57720
          | gres; rwH; imm_norm; addr_eq
          | gres; rwH; reflexivity
          | apply bv_eq; vm_compute; reflexivity
          | repeat (eapply store_ok_mono; [apply wbytes_grows|]); exact OKf ]
        | step_simpl]; vn.
      an F_57724 D_57724. an F_57728 D_57728.
      av F_5772c D_5772c (Z_to_bv 64 (sk3_pos hint i0 * 512)) ltac:(rewrite v_slli_s3 by lia; reflexivity).
      an F_57730 D_57730.
      av F_57734 D_57734 (Z_to_bv 64 (U fs + 36864)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).
      av F_57738 D_57738 (Z_to_bv 64 (3145728 + sk3_pos hint i0 * 512)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).
      av F_5773c D_5773c (Z_to_bv 64 FRM) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, sk3_frame in G in change_no_check G' end); unorm; f_equal; lia).
      wsd F_57740 D_57740 (FRM + 24)%Z ltac:(exact OK24).
      wsd F_57744 D_57744 (FRM + 504)%Z ltac:(exact OKl).
      change (wbytes (wbytes (wbytes (wbytes m _ _) _ _) _ _) _ _) with (sk3_mem4 m fs hint i0 S).
      an F_57748 D_57748. an F_5774c D_5774c.
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold S3CLOB3 in G in change_no_check G' end). ra_solve.
  Qed.

  Definition S4CLOB3 : list reg := [1; 2; 8; 9; 18; 10; 11; 12]%list.

  Lemma blkS4 : forall r6,
    getr r6 10 = Z_to_bv 64 SHW -> getr r6 9 = Z_to_bv 64 FRM -> getr r6 2 = at_ S (-32) ->
    exists r,
      msteps segs (mkst r6 (at_ sb 332) (sk3_mem4 m fs hint i0 S) rom) (mkst r ra (sk3_mem m fs hint i0 S) rom)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = ra /\ getr r 2 = S /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ regs_agree (fun x => In x S4CLOB3) r6 r.
  Proof using Hret Hhint Hfsnz Hfs FR4 FR3 FR2 FR1 OKsh HC_S.
    intros r6 Q10 Q9 Q2. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk3_pos_rng hint i0) as Hp.
    assert (HFL : (U fs + 32768 <= FLG < U fs + 34816)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk3_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 3182592 <= FRM /\ FRM + 512 <= U fs + 4231168)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk3_frame in G in change_no_check G' end); lia).
    pose proof (sk3_sh_rng fs hint i0 ltac:(lia)) as HSH.
    assert (OKS : forall j, (0 <= j)%Z -> (j + 8 <= 64)%Z -> store_ok segs m (Z_to_bv 64 (SHW + j)) 8 = true).
    { intros j Hj0 Hj1. eapply (store_ok_sub segs m (Z_to_bv 64 SHW) _ 64); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | exact OKsh | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ] | rewrite !u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia]. }
    wd_eexists. split.
    - an F_57750 D_57750. an F_57754 D_57754. an F_57758 D_57758.
      wsd F_5775c D_5775c (sk3_sh fs hint i0 + 0)%Z ltac:(apply OKS; lia).
      wsd F_57760 D_57760 (sk3_sh fs hint i0 + 8)%Z ltac:(apply OKS; lia).
      wsd F_57764 D_57764 (sk3_sh fs hint i0 + 16)%Z ltac:(apply OKS; lia).
      wsd F_57768 D_57768 (sk3_sh fs hint i0 + 24)%Z ltac:(apply OKS; lia).
      wsd F_5776c D_5776c (sk3_sh fs hint i0 + 32)%Z ltac:(apply OKS; lia).
      wsd F_57770 D_57770 (sk3_sh fs hint i0 + 40)%Z ltac:(apply OKS; lia).
      wsd F_57774 D_57774 (sk3_sh fs hint i0 + 48)%Z ltac:(apply OKS; lia).
      wsd F_57778 D_57778 (sk3_sh fs hint i0 + 56)%Z ltac:(apply OKS; lia).
      change (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (sk3_mem4 m fs hint i0 S) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) with (sk3_mem m fs hint i0 S).
      fldm F_5777c D_5777c ra FR1.
      fldm F_57780 D_57780 s0v FR2.
      fldm F_57784 D_57784 s1v FR3.
      fldm F_57788 D_57788 s2v FR4.
      an F_5778c D_5778c.
      aret F_57790 D_57790 ra.
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold S4CLOB3 in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma PH4 : m2sH segs mt (sk3_mem4 m fs hint i0 S) (Z_to_bv 64 FRM) midend.
  Proof using Hfsnz Hfs Hmcells PHm sb.
    destruct Hfs as [Hf0 Hf1]. pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk3_pos_rng hint i0) as Hp.
    assert (HFL : (U fs + 32768 <= FLG < U fs + 34816)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk3_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 3182592 <= FRM /\ FRM + 512 <= U fs + 4231168)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk3_frame in G in change_no_check G' end); lia).
    pose proof Hmcells as HC. unfold m2s_cells in HC.
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
    destruct PHm as [R1 R2 R3 R4 R5 R6 R7 R8 HCx Hlo Hhi].
    constructor; try assumption; (lazymatch goal with |- ?G => let G' := eval unfold sk3_mem4 in G in change_no_check G' end);
      (repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ])); assumption.
  Qed.

  Definition SBCLOB3 : list reg := [1; 2; 5; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list.
  Lemma SB_sub2 : forall x : reg, In x S2CLOB3 -> In x SBCLOB3. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold S2CLOB3, SBCLOB3 in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_subL : forall x : reg, In x LCLOB3 -> In x SBCLOB3. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold LCLOB3, SBCLOB3 in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_sub3 : forall x : reg, In x S3CLOB3 -> In x SBCLOB3. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold S3CLOB3, SBCLOB3 in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_subM : forall x : reg, In x m2s_clob -> In x SBCLOB3. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold m2s_clob, SBCLOB3 in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_sub4 : forall x : reg, In x S4CLOB3 -> In x SBCLOB3. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold S4CLOB3, SBCLOB3 in G in change_no_check G' end). incl_lists. Qed.

  Theorem stkB_run : forall r2,
    getr r2 10 = resw -> getr r2 2 = at_ S (-32) -> getr r2 8 = S ->
    exists r,
      msteps segs (mkst r2 (at_ sb 36) m rom) (mkst r ra (sk3_mem m fs hint i0 S) rom)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = ra /\ getr r 2 = S /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ regs_agree (fun x => In x SBCLOB3) r2 r.
  Proof using Hret Hi0 Hhint Hfsnz Hfs FR4 FR3 FR2 FR1 Hmcells PHm OKsh OKl OK24 OKf OKh Hz Hnz Rhint Rlog Rgc Rfs midend Hsb MTB MTOK HC_S mt.
    intros r2 Q10 Q2 Q8. destruct Hsb as [Hb2 Hb64]. pose proof (u64_range sb) as Hsbr.
    assert (RTM : ret_ok (at_ sb 332)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    destruct (blkS2 r2 Q10 Q2 Q8) as (r3 & RUN3 & A10 & A12 & A13 & A14 & A11 & A9 & A18 & A2 & A8 & AG3).
    destruct (sk3_loop (Z.to_nat i0) 0%Z r3 ltac:(lia) ltac:(lia) A10 A12 A13 A14) as (r4 & RUN4 & B12 & B15 & B17 & AG4).
    assert (B11 : getr r4 11 = Z_to_bv 64 (U fs + 4096)) by (rewrite (AG4 11 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB3 in G in change_no_check G' end); notin)); exact A11).
    assert (B9 : getr r4 9 = fs) by (rewrite (AG4 9 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB3 in G in change_no_check G' end); notin)); exact A9).
    assert (B18 : getr r4 18 = Z_to_bv 64 20) by (rewrite (AG4 18 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB3 in G in change_no_check G' end); notin)); exact A18).
    assert (B8 : getr r4 8 = S) by (rewrite (AG4 8 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB3 in G in change_no_check G' end); notin)); exact A8).
    assert (B2 : getr r4 2 = at_ S (-32)) by (rewrite (AG4 2 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB3 in G in change_no_check G' end); notin)); exact A2).
    destruct (blkS3 r4 B12 B15 B17 B11 B9 B18 B8 B2) as (r5 & RUN5 & C10 & C1 & C9 & C2 & AG5).
    destruct (m2s_run segs mt MTOK (sk3_mem4 m fs hint i0 S) rom (Z_to_bv 64 FRM) midend (at_ sb 332) r5 PH4 C10 C1 RTM)
      as (r6 & RUN6 & D10 & AG6).
    assert (UF : U (Z_to_bv 64 FRM) = FRM).
    { destruct Hfs as [Hf0 Hf1]. pose proof (u64_range fs). pose proof (u64_range S). pose proof (sk3_pos_rng hint i0). (lazymatch goal with |- ?G => let G' := eval unfold sk3_frame in G in change_no_check G' end). rewrite u_Z2bv; lia. }
    rewrite UF in D10. change (Z_to_bv 64 (FRM / 8 + 2147450880)) with (Z_to_bv 64 SHW) in D10.
    assert (D9 : getr r6 9 = Z_to_bv 64 FRM) by (rewrite (AG6 9 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact C9).
    assert (D2 : getr r6 2 = at_ S (-32)) by (rewrite (AG6 2 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact C2).
    destruct (blkS4 r6 D10 D9 D2) as (r7 & RUN7 & E10 & E1 & E2 & E8 & E9 & E18 & AG7).
    exists r7. split.
    - rewrite MTB in RUN6.
      eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|].
      eapply msteps_trans; [exact RUN6 | exact RUN7].
    - repeat (split; [assumption|]).
      eapply regs_agree_trans; [eapply regs_agree_trans; [eapply regs_agree_trans; [eapply regs_agree_trans|]|]|].
      + exact (regs_agree_mono _ _ _ _ SB_sub2 AG3).
      + exact (regs_agree_mono _ _ _ _ SB_subL AG4).
      + exact (regs_agree_mono _ _ _ _ SB_sub3 AG5).
      + exact (regs_agree_mono _ _ _ _ SB_subM AG6).
      + exact (regs_agree_mono _ _ _ _ SB_sub4 AG7).
  Qed.
End STKB.

Section STK.
  Variables (segs : list Segment) (sb : word).
  Variable tg : tlsga_tab.
  Variable mt : m2s_tab.
  Variable c_arg : word.
  Hypothesis HC_S : code_ato segs sb 0 stk3_words.
  Hypothesis TGOK : tlsga_tab_ok segs tg.
  Hypothesis TGHB : tg_hb tg = at_ sb 20264.
  Hypothesis MTOK : m2s_tab_ok segs mt.
  Hypothesis MTB : mt_base mt = at_ sb 428.
  Hypothesis A24 : gaddr2 segs sb 24 10 10 c_arg.
  Hypothesis Hsb : (U sb mod 2 = 0)%Z /\ (U sb + 30000 < 2 ^ 64)%Z.

  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables (ra S fs midend : word).
  Variable v : tlsga_vals.
  Variables (hint i0 : Z).
  #[local] Abbreviation FLG := (sk3_flag fs hint i0).
  #[local] Abbreviation FRM := (sk3_frame fs hint i0).
  #[local] Abbreviation SHW := (sk3_sh fs hint i0).
  Hypothesis TGH : tlsgaH segs tg mem (at_ S (-32)) v.
  Hypothesis Harg : tv_arg v = c_arg.
  Hypothesis Rfs : rdn segs mem (Z_to_bv 64 (U (tg_res v))) 8 = Some (W8 fs).
  Hypothesis Hres : (U (tg_res v) + 8 <= U S - 208)%Z.
  Hypothesis Rgc : rdn segs mem (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlog : rdn segs mem (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20).
  Hypothesis Rhint : rdn segs mem (Z_to_bv 64 (U fs + 24)) 8 = Some (LE8 hint).
  Hypothesis Hnz : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs mem (Z_to_bv 64 (sk3_flag fs hint j)) 1 = Some [b] /\ U b <> 0%Z.
  Hypothesis Hz : rdn segs mem (Z_to_bv 64 FLG) 1 = Some [Z_to_bv 8 0].
  Hypothesis OKh : store_ok segs mem (Z_to_bv 64 (U fs + 24)) 8 = true.
  Hypothesis OKf : store_ok segs mem (Z_to_bv 64 FLG) 1 = true.
  Hypothesis OK24 : store_ok segs mem (Z_to_bv 64 (FRM + 24)) 8 = true.
  Hypothesis OKl : store_ok segs mem (Z_to_bv 64 (FRM + 504)) 8 = true.
  Hypothesis OKsh : store_ok segs mem (Z_to_bv 64 SHW) 64 = true.
  Hypothesis PH : m2sH segs mt mem (Z_to_bv 64 FRM) midend.
  Hypothesis Hmcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells mt).
  Hypothesis Hfs : (0 < U fs /\ U fs + 4231168 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 4231168 <= U S - 208)%Z.
  Hypothesis Hhint : (0 <= hint)%Z.
  Hypothesis Hi0 : (0 <= i0 < 2048)%Z.
  Hypothesis HS : (208 <= U S)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ S (-32)) 32 = true.
  Hypothesis Hret : ret_ok ra.

  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = S.
  Hypothesis H4 : getr regs 4 = tv_tp v.

  #[local] Abbreviation M1 := (fl_frame mem S ra (getr regs 8) (getr regs 9) (getr regs 18)).

  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ S (-32)) _ 32);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.

  Lemma blkS1 :
    exists r,
      msteps segs (mkst regs (at_ sb 0) mem rom) (mkst r (at_ sb 20264) M1 rom)
      /\ getr r 10 = c_arg /\ getr r 1 = at_ sb 36 /\ getr r 2 = at_ S (-32) /\ getr r 8 = S /\ getr r 4 = tv_tp v
      /\ regs_agree (fun x => In x [1; 2; 8; 10]%list) regs r.
  Proof using H4 H2 H1 Hstk Hfs fs Hsb A24 HC_S.
    pose proof (u64_range S) as HSr. destruct Hsb as [Hb2 Hb64]. destruct A24 as [x24 AX].
    wd_eexists. split.
    - an (F_57604 segs sb HC_S) D_57604.
      fsd (F_57608 segs sb HC_S) D_57608 (at_ S (-8)).
      fsd (F_5760c segs sb HC_S) D_5760c (at_ S (-16)).
      fsd (F_57610 segs sb HC_S) D_57610 (at_ S (-24)).
      fsd (F_57614 segs sb HC_S) D_57614 (at_ S (-32)).
      change (wbytes _ _ _) with M1.
      an (F_57618 segs sb HC_S) D_57618.
      eapply msteps_trans; [eapply AX|]; zlit_at.
      an (F_57624 segs sb HC_S) D_57624.
      wd_refl.
    - post; rewrite ?at_0; try reflexivity. ra_solve.
  Qed.

  Theorem stk3_run :
    exists r Mj,
      msteps segs (mkst regs (at_ sb 0) mem rom) (mkst r ra (sk3_mem Mj fs hint i0 S) rom)
      /\ scr_rel mem Mj (U S - 208) (U S)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = ra /\ getr r 2 = S
      /\ regs_agree (fun x => In x m2s_clob) regs r.
  Proof using H4 H2 H1 Hret Hstk Hi0 Hhint Hfs Hmcells PH OKsh OKl OK24 OKf OKh Hz Hnz Rhint Rlog Rgc Hres Rfs Harg TGH v midend Hsb A24 MTB MTOK TGHB TGOK HC_S c_arg mt tg.
    pose proof (u64_range S) as HSr. destruct Hsb as [Hb2 Hb64]. pose proof (u64_range sb) as Hsbr.
    destruct Hfs as [Hf0 Hf1]. pose proof (u64_range fs) as Hfr. pose proof (u64_range (tg_res v)) as Hrr.
    pose proof (sk3_pos_rng hint i0) as Hp.
    assert (RT36 : ret_ok (at_ sb 36)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    assert (US32 : U (at_ S (-32)) = (U S - 32)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    destruct blkS1 as (r1 & RUN1 & A10 & A1 & A2 & A8 & A4 & AG1).
    assert (TGH1 : tlsgaH segs tg M1 (at_ S (-32)) v).
    { apply (tlsgaH_above segs tg mem M1 (at_ S (-32)) v TGH); [apply fl_frame_grows|].
      intros a Ha. apply fl_frame_out; [lia | rewrite US32 in Ha; lia]. }
    rewrite <- Harg in A10.
    destruct (tlsga_run_t segs tg TGOK M1 rom (at_ sb 36) (at_ S (-32)) v r1 TGH1 RT36 A1 A2 A4 A10)
      as (r2 & Mj & RUN2 & SR & B10 & B1 & B2 & AG2).
    rewrite US32 in SR.
    assert (B8 : getr r2 8 = S) by (rewrite (AG2 8 ltac:(notin)); exact A8).
    assert (RDJ : forall c n bs, (0 <= c)%Z -> (c + Z.of_nat n <= U S - 208)%Z ->
                  rdn segs mem (Z_to_bv 64 c) n = Some bs -> rdn segs Mj (Z_to_bv 64 c) n = Some bs).
    { intros c n bs Hc0 Hc Hr.
      apply (scr_rel_rdn segs M1 Mj (U S - 32 - 176) (U S - 32) c n bs SR); [lia | lia | left; lia|].
      apply rd_fl_frame; [lia | lia | lia | exact Hr]. }
    assert (OKJ : forall (a : word) n, store_ok segs mem a n = true -> store_ok segs Mj a n = true).
    { intros a n OK. apply (scr_rel_ok segs M1 Mj _ _ a n SR). apply fl_frame_ok. exact OK. }
    assert (HFL : forall j, (U fs + 32768 <= sk3_flag fs hint j < U fs + 34816)%Z) by (intros j; pose proof (sk3_pos_rng hint j); (lazymatch goal with |- ?G => let G' := eval unfold sk3_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 3182592 <= FRM /\ FRM + 512 <= U fs + 4231168)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk3_frame in G in change_no_check G' end); lia).
    assert (SLOT : forall k vv, (k = 8 \/ k = 16 \/ k = 24 \/ k = 32)%Z ->
                   rdn segs M1 (at_ S (- k)) 8 = Some (W8 vv) -> rdn segs Mj (at_ S (- k)) 8 = Some (W8 vv)).
    { intros k vv Hk Hr. destruct SR as (O & _ & _).
      rewrite (rdn_ext segs 8 Mj M1 (at_ S (- k))); [exact Hr | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u by lia; intros x Hx; apply O; lia]. }
    assert (PHJ : m2sH segs mt Mj (Z_to_bv 64 FRM) midend).
    { pose proof Hmcells as HC. unfold m2s_cells in HC.
      repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
      destruct PH as [R1 R2 R3 R4 R5 R6 R7 R8 HCx Hlo Hhi].
      constructor; try assumption; apply RDJ; try assumption; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia. }
    destruct (stkB_run segs sb mt HC_S MTOK MTB (conj Hb2 Hb64) Mj rom ra S (tg_res v) fs midend (getr regs 8) (getr regs 9) (getr regs 18) hint i0)
      with (r2 := r2) as (r & RUN3 & E10 & E1 & E2 & E8 & E9 & E18 & AG3).
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rfs]. }
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rgc]. }
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rlog]. }
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rhint]. }
    { intros j Hj. destruct (Hnz j Hj) as (b & Rb & Nb). exists b. split; [|exact Nb].
      pose proof (HFL j). apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rb]. }
    { pose proof (HFL i0). apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hz]. }
    { apply OKJ; exact OKh. } { apply OKJ; exact OKf. } { apply OKJ; exact OK24. } { apply OKJ; exact OKl. } { apply OKJ; exact OKsh. }
    { exact PHJ. }
    { exact Hmcells. }
    { apply (SLOT 8%Z ra); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { apply (SLOT 16%Z (getr regs 8)); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { apply (SLOT 24%Z (getr regs 9)); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { apply (SLOT 32%Z (getr regs 18)); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { split; lia. }
    { lia. }
    { exact Hhint. }
    { exact Hi0. }
    { exact Hret. }
    { exact B10. }
    { exact B2. }
    { exact B8. }
    exists r, Mj. split; [|split; [|split; [exact E10 | split; [exact E1 | split; [exact E2|]]]]].
    - rewrite TGHB in RUN2. eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3].
    - apply (scr_rel_trans mem M1 Mj).
      + (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end).
        repeat (apply scr_rel_wb; [ | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ] | wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia | lia ]).
        apply scr_rel_refl.
      + apply (scr_rel_mono M1 Mj _ _ _ _ SR); lia.
    - intros x Hx.
      destruct (In_dec (fun a b : reg => decide (a = b)) x [1; 2; 8; 9; 18]%list) as [I|NI].
      + cbn [In] in I.
        repeat (destruct I as [<-|I]; [first [rewrite E1; symmetry; exact H1 | rewrite E2; symmetry; exact H2 | exact E8 | exact E9 | exact E18] |]).
        destruct I.
      + assert (NB : ~ In x SBCLOB3).
        { intros I. unfold SBCLOB3 in I. unfold m2s_clob in Hx. cbn [In] in I, NI, Hx. tauto. }
        rewrite (AG3 x NB). rewrite (AG2 x). 2:{ intros I. unfold m2s_clob in Hx. cbn [In] in I, Hx. tauto. }
        apply AG1. intros I. unfold m2s_clob in Hx. cbn [In] in I, NI, Hx. tauto.
  Qed.
End STK.

(* [comment removed for export] *)
Definition stk3_tab_ok (segs : list Segment) (t : stk_tab) : Prop :=
  code_ato segs (sk_base t) 0 stk3_words
  /\ tlsga_tab_ok segs (sk_tg t) /\ tg_hb (sk_tg t) = at_ (sk_base t) 20264
  /\ m2s_tab_ok segs (sk_mt t) /\ mt_base (sk_mt t) = at_ (sk_base t) 428
  /\ gaddr2 segs (sk_base t) 24 10 10 (sk_arg t)
  /\ ((U (sk_base t) mod 2 = 0)%Z /\ (U (sk_base t) + 30000 < 2 ^ 64)%Z).

Record stk3H (segs : list Segment) (t : stk_tab) (mem : word -> option byte) (S fs midend : word) (v : tlsga_vals) (hint i0 : Z) : Prop := SK3H {
  s3h_tls : tlsgaH segs (sk_tg t) mem (at_ S (-32)) v;
  s3h_arg : tv_arg v = sk_arg t;
  s3h_fs : rdn segs mem (Z_to_bv 64 (U (tg_res v))) 8 = Some (W8 fs);
  s3h_res : (U (tg_res v) + 8 <= U S - 208)%Z;
  s3h_gc : rdn segs mem (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0];
  s3h_log : rdn segs mem (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20);
  s3h_hint : rdn segs mem (Z_to_bv 64 (U fs + 24)) 8 = Some (LE8 hint);
  s3h_busy : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs mem (Z_to_bv 64 (sk3_flag fs hint j)) 1 = Some [b] /\ U b <> 0%Z;
  s3h_free : rdn segs mem (Z_to_bv 64 (sk3_flag fs hint i0)) 1 = Some [Z_to_bv 8 0];
  s3h_ok_hint : store_ok segs mem (Z_to_bv 64 (U fs + 24)) 8 = true;
  s3h_ok_flag : store_ok segs mem (Z_to_bv 64 (sk3_flag fs hint i0)) 1 = true;
  s3h_ok_24 : store_ok segs mem (Z_to_bv 64 (sk3_frame fs hint i0 + 24)) 8 = true;
  s3h_ok_last : store_ok segs mem (Z_to_bv 64 (sk3_frame fs hint i0 + 504)) 8 = true;
  s3h_ok_sh : store_ok segs mem (Z_to_bv 64 (sk3_sh fs hint i0)) 64 = true;
  s3h_m2s : m2sH segs (sk_mt t) mem (Z_to_bv 64 (sk3_frame fs hint i0)) midend;
  s3h_mcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells (sk_mt t));
  s3h_geom : (0 < U fs /\ U fs + 4231168 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 4231168 <= U S - 208)%Z;
  s3h_hintr : (0 <= hint)%Z;
  s3h_i0 : (0 <= i0 < 2048)%Z;
  s3h_S : (208 <= U S)%Z;
  s3h_stk : store_ok segs mem (at_ S (-32)) 32 = true }.

Theorem stk3_run_t : forall segs t, stk3_tab_ok segs t ->
  forall mem rom (ra S fs midend : word) v hint i0 regs,
  stk3H segs t mem S fs midend v hint i0 -> ret_ok ra ->
  getr regs 1 = ra -> getr regs 2 = S -> getr regs 4 = tv_tp v ->
  exists r Mj,
    msteps segs (mkst regs (sk_base t) mem rom) (mkst r ra (sk3_mem Mj fs hint i0 S) rom)
    /\ scr_rel mem Mj (U S - 208) (U S)
    /\ getr r 10 = Z_to_bv 64 (sk3_frame fs hint i0) /\ getr r 1 = ra /\ getr r 2 = S
    /\ regs_agree (fun x => In x m2s_clob) regs r.
Proof using.
  intros segs t (C1 & TG & TGB & MT & MTB & A24 & HB) mem rom ra S fs midend v hint i0 regs
         [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21] Hret H1 H2 H4.
  replace (mkst regs (sk_base t) mem rom) with (mkst regs (at_ (sk_base t) 0) mem rom) by (rewrite at_0; reflexivity).
  first [ exact (stk3_run segs (sk_base t) (sk_tg t) (sk_mt t) (sk_arg t) C1 TG TGB MT MTB A24 HB mem rom ra S fs midend v hint i0
           P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 Hret regs H1 H2 H4)
        | exact (stk3_run segs (sk_base t) (sk_tg t) (sk_mt t) (sk_arg t) C1 TG TGB MT MTB A24 HB mem rom ra S fs midend v hint i0
           P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P21 Hret regs H1 H2 H4) ].
Qed.
End FPGen1.
End AsRtStkMal3.
Module AsRtStkMalK.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 AsRtStkMal1 AsRtStkMal2 AsRtStkMal3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation W8 w := (word_to_le_bytes 8 w).
#[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

(* [comment removed for export] *)
Definition stk_mem (m : word -> option byte) (hc fl f last sh : Z) (nsh : nat) (hint' : Z) (S : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 hc) (LE8 hint')) (Z_to_bv 64 fl) [Z_to_bv 8 1]) (Z_to_bv 64 (f + 24)) (W8 S)) (Z_to_bv 64 last) (LE8 fl))
    (Z_to_bv 64 sh) (zeros nsh).

Lemma le8_0_zeros : LE8 0 = zeros 8.
Proof using. vm_compute. reflexivity. Qed.
Lemma wb_zeros_app : forall m (sh : Z) (n1 n2 n : nat) (o : Z), o = Z.of_nat n1 -> n = (n1 + n2)%nat ->
  (0 <= sh)%Z -> (sh + Z.of_nat n < 2 ^ 64)%Z ->
  wbytes (wbytes m (Z_to_bv 64 sh) (zeros n1)) (Z_to_bv 64 (sh + o)) (zeros n2) = wbytes m (Z_to_bv 64 sh) (zeros n).
Proof using.
  intros m sh n1 n2 n o -> -> H0 H1. (lazymatch goal with |- ?G => let G' := eval unfold zeros in G in change_no_check G' end). rewrite repeat_app. rewrite MemsetLibF.RefMemcpyLib.wbytes_app. rewrite repeat_length.
  f_equal. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). rewrite (u_Z2bv sh) by lia. rewrite !u_Z2bv by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint zch (m : word -> option byte) (sh : Z) (j n : nat) : word -> option byte :=
  match n with
  | O => m
  | Datatypes.S n' => zch (wbytes m (Z_to_bv 64 (sh + 8 * Z.of_nat j)) (LE8 0)) sh (Datatypes.S j) n'
  end.
Lemma zch_eq : forall n j m sh, (0 <= sh)%Z -> (sh + 8 * Z.of_nat (j + n) < 2 ^ 64)%Z ->
  zch (wbytes m (Z_to_bv 64 sh) (zeros (8 * j))) sh j n = wbytes m (Z_to_bv 64 sh) (zeros (8 * (j + n))).
Proof using.
  induction n as [|n IH]; intros j m sh H0 H1.
  - (lazymatch goal with |- ?G => let G' := eval cbn [zch] in G in change_no_check G' end). rewrite Nat.add_0_r. reflexivity.
  - (lazymatch goal with |- ?G => let G' := eval cbn [zch] in G in change_no_check G' end). rewrite le8_0_zeros.
    rewrite (wb_zeros_app m sh (8 * j) 8 (8 * Datatypes.S j) (8 * Z.of_nat j) ltac:(lia) ltac:(lia) H0 ltac:(lia)).
    rewrite (IH (Datatypes.S j) m sh H0 ltac:(lia)). f_equal. f_equal. lia.
Qed.
Lemma zch_eq0 : forall n m sh, (0 <= sh)%Z -> (sh + 8 * Z.of_nat n < 2 ^ 64)%Z ->
  zch m sh 0 n = wbytes m (Z_to_bv 64 sh) (zeros (8 * n)).
Proof using. intros n m sh H0 H1. exact (zch_eq n 0%nat m sh H0 H1). Qed.

Lemma sk0_mem_eq : forall m fs hint i0 S,
  sk0_mem m fs hint i0 S = stk_mem m (U fs) (sk0_flag fs hint i0) (sk0_frame fs hint i0) (sk0_frame fs hint i0 + 56) (sk0_sh fs hint i0) 8 (hint + i0 + 1) S.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk0_mem, sk0_mem4, stk_mem in G in change_no_check G' end). rewrite le8_0_zeros. reflexivity. Qed.
Lemma sk1_mem_eq : forall m fs hint i0 S, (0 <= sk1_sh fs hint i0)%Z -> (sk1_sh fs hint i0 + 16 < 2 ^ 64)%Z ->
  sk1_mem m fs hint i0 S = stk_mem m (U fs + 8) (sk1_flag fs hint i0) (sk1_frame fs hint i0) (sk1_frame fs hint i0 + 120) (sk1_sh fs hint i0) 16 (hint + i0 + 1) S.
Proof using.
  intros m fs hint i0 S H0 H1. (lazymatch goal with |- ?G => let G' := eval unfold sk1_mem, stk_mem in G in change_no_check G' end). set (X := sk1_mem4 m fs hint i0 S).
  change (wbytes (wbytes X _ _) _ _) with (zch X (sk1_sh fs hint i0) 0 2).
  rewrite (zch_eq0 2 X _ H0 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia)). reflexivity.
Qed.
Lemma sk2_mem_eq : forall m fs hint i0 S, (0 <= sk2_sh fs hint i0)%Z -> (sk2_sh fs hint i0 + 32 < 2 ^ 64)%Z ->
  sk2_mem m fs hint i0 S = stk_mem m (U fs + 16) (sk2_flag fs hint i0) (sk2_frame fs hint i0) (sk2_frame fs hint i0 + 248) (sk2_sh fs hint i0) 32 (hint + i0 + 1) S.
Proof using.
  intros m fs hint i0 S H0 H1. (lazymatch goal with |- ?G => let G' := eval unfold sk2_mem, stk_mem in G in change_no_check G' end). set (X := sk2_mem4 m fs hint i0 S).
  change (wbytes (wbytes (wbytes (wbytes X _ _) _ _) _ _) _ _) with (zch X (sk2_sh fs hint i0) 0 4).
  rewrite (zch_eq0 4 X _ H0 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia)). reflexivity.
Qed.
Lemma sk3_mem_eq : forall m fs hint i0 S, (0 <= sk3_sh fs hint i0)%Z -> (sk3_sh fs hint i0 + 64 < 2 ^ 64)%Z ->
  sk3_mem m fs hint i0 S = stk_mem m (U fs + 24) (sk3_flag fs hint i0) (sk3_frame fs hint i0) (sk3_frame fs hint i0 + 504) (sk3_sh fs hint i0) 64 (hint + i0 + 1) S.
Proof using.
  intros m fs hint i0 S H0 H1. (lazymatch goal with |- ?G => let G' := eval unfold sk3_mem, stk_mem in G in change_no_check G' end). set (X := sk3_mem4 m fs hint i0 S).
  change (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes X _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) with (zch X (sk3_sh fs hint i0) 0 8).
  rewrite (zch_eq0 8 X _ H0 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia)). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MEM.
  Variables (segs : list Segment) (m : word -> option byte).
  Variables (hc fl f last sh : Z) (nsh : nat) (hint' : Z) (S : word).
  (* [comment removed for export] *)
  Hypothesis Hb : (0 <= hc /\ 0 <= fl /\ 0 <= f /\ 0 <= last /\ 0 <= sh)%Z
                  /\ (hc + 8 < 2 ^ 64 /\ fl + 1 < 2 ^ 64 /\ f + 32 < 2 ^ 64 /\ last + 8 < 2 ^ 64 /\ sh + Z.of_nat nsh < 2 ^ 64)%Z.
  Hypothesis Hd : (hc + 8 <= fl /\ fl + 1 <= f + 24 /\ f + 32 <= last /\ (sh + Z.of_nat nsh <= hc \/ last + 8 <= sh))%Z.
  #[local] Abbreviation MF := (stk_mem m hc fl f last sh nsh hint' S).

  Ltac ws := wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval unfold zeros in G in change_no_check G' end); rewrite ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite ?u_Z2bv by lia; lia ].

  Lemma stk_mem_out : forall a : word,
    ~ (hc <= U a < hc + 8)%Z -> U a <> fl -> ~ (f + 24 <= U a < f + 32)%Z -> ~ (last <= U a < last + 8)%Z -> ~ (sh <= U a < sh + Z.of_nat nsh)%Z ->
    MF a = m a.
  Proof using Hd Hb.
    intros a N1 N2 N3 N4 N5. destruct Hb as (B0 & B1). (lazymatch goal with |- ?G => let G' := eval unfold stk_mem in G in change_no_check G' end).
    rewrite !MemsetLibF.MemSplit.wbytes_outside; [reflexivity | ws ..].
  Qed.
  Lemma stk_mem_grows : mem_grows m MF.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold stk_mem in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma stk_mem_def : forall a : word, MF a <> m a -> MF a <> None.
  Proof using Hd Hb.
    intros a NE. destruct Hb as (B0 & B1). pose proof (u64_range a) as Ha. unfold stk_mem in *.
    destruct (Z_lt_le_dec (U a) sh) as [C1|C1]; [|destruct (Z_lt_le_dec (U a) (sh + Z.of_nat nsh)) as [C2|C2]].
    2:{ rewrite MemsetLibF.MemSplit.wbytes_inside; [discriminate | ws | ws]. }
    all: rewrite MemsetLibF.MemSplit.wbytes_outside in NE |- * by ws.
    all: destruct (Z_lt_le_dec (U a) last) as [D1|D1]; [|destruct (Z_lt_le_dec (U a) (last + 8)) as [D2|D2]];
         try (rewrite MemsetLibF.MemSplit.wbytes_inside; [discriminate | ws | ws]);
         rewrite MemsetLibF.MemSplit.wbytes_outside in NE |- * by ws;
         (destruct (Z_lt_le_dec (U a) (f + 24)) as [E1|E1]; [|destruct (Z_lt_le_dec (U a) (f + 32)) as [E2|E2]]);
         try (rewrite MemsetLibF.MemSplit.wbytes_inside; [discriminate | ws | ws]);
         rewrite MemsetLibF.MemSplit.wbytes_outside in NE |- * by ws;
         (destruct (Z.eq_dec (U a) fl) as [F1|F1]; [rewrite MemsetLibF.MemSplit.wbytes_inside; [discriminate | ws | ws]|]);
         rewrite MemsetLibF.MemSplit.wbytes_outside in NE |- * by ws;
         (destruct (Z_lt_le_dec (U a) hc) as [G1|G1]; [|destruct (Z_lt_le_dec (U a) (hc + 8)) as [G2|G2]]);
         try (rewrite MemsetLibF.MemSplit.wbytes_inside; [discriminate | ws | ws]);
         rewrite MemsetLibF.MemSplit.wbytes_outside in NE by ws; exfalso; apply NE; reflexivity.
  Qed.
  Lemma stk_mem_hint : rdn segs MF (Z_to_bv 64 hc) 8 = Some (LE8 hint').
  Proof using Hd Hb.
    destruct Hb as (B0 & B1). (lazymatch goal with |- ?G => let G' := eval unfold stk_mem in G in change_no_check G' end).
    do 4 (rewrite rdn_wbytes_out; [| ws | ws | ws]). apply rdn_wbytes_hit8; ws.
  Qed.
  Lemma stk_mem_flag : rdn segs MF (Z_to_bv 64 fl) 1 = Some [Z_to_bv 8 1].
  Proof using Hd Hb.
    destruct Hb as (B0 & B1). (lazymatch goal with |- ?G => let G' := eval unfold stk_mem in G in change_no_check G' end).
    do 3 (rewrite rdn_wbytes_out; [| ws | ws | ws]). exact (rdn_wbytes_hit segs [Z_to_bv 8 1] _ (Z_to_bv 64 fl) ltac:(ws)).
  Qed.

  Lemma stk_mem_last : rdn segs MF (Z_to_bv 64 last) 8 = Some (LE8 fl).
  Proof using Hd Hb.
    destruct Hb as (B0 & B1). (lazymatch goal with |- ?G => let G' := eval unfold stk_mem in G in change_no_check G' end).
    rewrite rdn_wbytes_out; [| ws | ws | ws]. apply rdn_wbytes_hit8; ws.
  Qed.
  Lemma stk_mem_sh : forall i, (0 <= i < Z.of_nat nsh)%Z -> MF (Z_to_bv 64 (sh + i)) = Some (Z_to_bv 8 0).
  Proof using Hd Hb.
    intros i Hi. destruct Hb as (B0 & B1). (lazymatch goal with |- ?G => let G' := eval unfold stk_mem in G in change_no_check G' end).
    rewrite MemsetLibF.MemSplit.wbytes_inside; [| ws | ws]. (lazymatch goal with |- ?G => let G' := eval unfold zeros in G in change_no_check G' end). apply (f_equal Some). apply nth_repeat.
  Qed.
End MEM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NK (k : Z) : Z := (2 ^ (14 - k))%Z.
Definition FSK (k : Z) : Z := (64 * 2 ^ k)%Z.
Definition FOFFK (k : Z) : Z := (4096 + (16384 - 2 ^ (14 - k)) * 2)%Z.
Definition skf_pos (k hint i : Z) : Z := ((hint + i) mod NK k)%Z.
Definition skf_flag (k fs hint i : Z) : Z := (fs + FOFFK k + skf_pos k hint i)%Z.
Definition skf_frame (k fs hint i : Z) : Z := (fs + 36864 + k * 2 ^ 20 + FSK k * skf_pos k hint i)%Z.
Definition skf_sh (k fs hint i : Z) : Z := (skf_frame k fs hint i / 8 + 0x7fff8000)%Z.

Ltac kpow := change (2 ^ (14 - 0))%Z with 16384%Z in *; change (2 ^ (14 - 1))%Z with 8192%Z in *; change (2 ^ (14 - 2))%Z with 4096%Z in *;
             change (2 ^ (14 - 3))%Z with 2048%Z in *; change (2 ^ 20)%Z with 1048576%Z in *;
             change (2 ^ 0)%Z with 1%Z in *; change (2 ^ 1)%Z with 2%Z in *; change (2 ^ 2)%Z with 4%Z in *; change (2 ^ 3)%Z with 8%Z in *.
Lemma sk0_flag_eq : forall fs hint i, sk0_flag fs hint i = skf_flag 0 (U fs) hint i.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk0_flag, sk_pos, skf_flag, skf_pos, FOFFK, NK in G in change_no_check G' end). kpow. lia. Qed.
Lemma sk0_frame_eq : forall fs hint i, sk0_frame fs hint i = skf_frame 0 (U fs) hint i.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk0_frame, sk_pos, skf_frame, skf_pos, FSK, NK in G in change_no_check G' end). kpow. lia. Qed.
Lemma sk0_sh_eq : forall fs hint i, sk0_sh fs hint i = skf_sh 0 (U fs) hint i.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk0_sh, skf_sh in G in change_no_check G' end). rewrite sk0_frame_eq. reflexivity. Qed.
Lemma sk1_flag_eq : forall fs hint i, sk1_flag fs hint i = skf_flag 1 (U fs) hint i.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk1_flag, sk1_pos, skf_flag, skf_pos, FOFFK, NK in G in change_no_check G' end). kpow. lia. Qed.
Lemma sk1_frame_eq : forall fs hint i, sk1_frame fs hint i = skf_frame 1 (U fs) hint i.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk1_frame, sk1_pos, skf_frame, skf_pos, FSK, NK in G in change_no_check G' end). kpow. lia. Qed.
Lemma sk1_sh_eq : forall fs hint i, sk1_sh fs hint i = skf_sh 1 (U fs) hint i.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk1_sh, skf_sh in G in change_no_check G' end). rewrite sk1_frame_eq. reflexivity. Qed.
Lemma sk2_flag_eq : forall fs hint i, sk2_flag fs hint i = skf_flag 2 (U fs) hint i.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk2_flag, sk2_pos, skf_flag, skf_pos, FOFFK, NK in G in change_no_check G' end). kpow. lia. Qed.
Lemma sk2_frame_eq : forall fs hint i, sk2_frame fs hint i = skf_frame 2 (U fs) hint i.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk2_frame, sk2_pos, skf_frame, skf_pos, FSK, NK in G in change_no_check G' end). kpow. lia. Qed.
Lemma sk2_sh_eq : forall fs hint i, sk2_sh fs hint i = skf_sh 2 (U fs) hint i.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk2_sh, skf_sh in G in change_no_check G' end). rewrite sk2_frame_eq. reflexivity. Qed.
Lemma sk3_flag_eq : forall fs hint i, sk3_flag fs hint i = skf_flag 3 (U fs) hint i.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk3_flag, sk3_pos, skf_flag, skf_pos, FOFFK, NK in G in change_no_check G' end). kpow. lia. Qed.
Lemma sk3_frame_eq : forall fs hint i, sk3_frame fs hint i = skf_frame 3 (U fs) hint i.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk3_frame, sk3_pos, skf_frame, skf_pos, FSK, NK in G in change_no_check G' end). kpow. lia. Qed.
Lemma sk3_sh_eq : forall fs hint i, sk3_sh fs hint i = skf_sh 3 (U fs) hint i.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk3_sh, skf_sh in G in change_no_check G' end). rewrite sk3_frame_eq. reflexivity. Qed.

Definition stkK_tab_ok (segs : list Segment) (k : Z) (t : stk_tab) : Prop :=
  (k = 0%Z -> stk0_tab_ok segs t) /\ (k = 1%Z -> stk1_tab_ok segs t) /\ (k = 2%Z -> stk2_tab_ok segs t) /\ (k = 3%Z -> stk3_tab_ok segs t).

(* [comment removed for export] *)
Record stkKH (segs : list Segment) (t : stk_tab) (k : Z) (mem : word -> option byte) (S fs midend : word) (v : tlsga_vals) (hint i0 : Z) : Prop := SKKH {
  kh_tls : tlsgaH segs (sk_tg t) mem (at_ S (-32)) v;
  kh_arg : tv_arg v = sk_arg t;
  kh_fs : rdn segs mem (Z_to_bv 64 (U (tg_res v))) 8 = Some (W8 fs);
  kh_res : (U (tg_res v) <> 0)%Z /\ (U (tg_res v) + 8 <= U S - 208)%Z;
  kh_gc : rdn segs mem (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0];
  kh_log : rdn segs mem (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20);
  kh_hint : rdn segs mem (Z_to_bv 64 (U fs + 8 * k)) 8 = Some (LE8 hint);
  kh_busy : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs mem (Z_to_bv 64 (skf_flag k (U fs) hint j)) 1 = Some [b] /\ U b <> 0%Z;
  kh_free : rdn segs mem (Z_to_bv 64 (skf_flag k (U fs) hint i0)) 1 = Some [Z_to_bv 8 0];
  kh_ok_hint : store_ok segs mem (Z_to_bv 64 (U fs + 8 * k)) 8 = true;
  kh_ok_flag : store_ok segs mem (Z_to_bv 64 (skf_flag k (U fs) hint i0)) 1 = true;
  kh_ok_24 : store_ok segs mem (Z_to_bv 64 (skf_frame k (U fs) hint i0 + 24)) 8 = true;
  kh_ok_last : store_ok segs mem (Z_to_bv 64 (skf_frame k (U fs) hint i0 + (FSK k - 8))) 8 = true;
  kh_ok_sh : store_ok segs mem (Z_to_bv 64 (skf_sh k (U fs) hint i0)) (Z.to_nat (FSK k / 8)) = true;
  kh_m2s : m2sH segs (sk_mt t) mem (Z_to_bv 64 (skf_frame k (U fs) hint i0)) midend;
  kh_mcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells (sk_mt t));
  kh_geom : (0 < U fs /\ U fs + 4231168 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 4231168 <= U S - 208)%Z;
  kh_hintr : (0 <= hint)%Z;
  kh_i0 : (0 <= i0 < NK k)%Z;
  kh_S : (208 <= U S)%Z;
  kh_stk : store_ok segs mem (at_ S (-32)) 32 = true }.

(* [comment removed for export] *)
Definition stkK_mem (k : Z) (m : word -> option byte) (fs hint i0 : Z) (S : word) : word -> option byte :=
  stk_mem m (fs + 8 * k) (skf_flag k fs hint i0) (skf_frame k fs hint i0) (skf_frame k fs hint i0 + (FSK k - 8)) (skf_sh k fs hint i0)
          (Z.to_nat (FSK k / 8)) (hint + i0 + 1) S.

Theorem stk_run_k : forall segs k t, (0 <= k <= 3)%Z -> stkK_tab_ok segs k t ->
  forall mem rom (ra S fs midend : word) v hint i0 regs,
  stkKH segs t k mem S fs midend v hint i0 -> ret_ok ra ->
  getr regs 1 = ra -> getr regs 2 = S -> getr regs 4 = tv_tp v ->
  exists r Mj,
    msteps segs (mkst regs (sk_base t) mem rom) (mkst r ra (stkK_mem k Mj (U fs) hint i0 S) rom)
    /\ scr_rel mem Mj (U S - 208) (U S)
    /\ getr r 10 = Z_to_bv 64 (skf_frame k (U fs) hint i0) /\ getr r 1 = ra /\ getr r 2 = S
    /\ regs_agree (fun x => In x m2s_clob) regs r.
Proof using.
  intros segs k t Hk (T0 & T1 & T2 & T3) mem rom ra S fs midend v hint i0 regs
         [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21] Hret H1 H2 H4.
  destruct P17 as [G1 G2]. pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr.
  assert (KC : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3)%Z) by lia.
  destruct KC as [-> | [-> | [-> | ->]]]; (lazymatch goal with |- ?G => let G' := eval unfold stkK_mem in G in change_no_check G' end).
  - assert (PRE : stk0H segs t mem S fs midend v hint i0).
    { replace (U fs + 8 * 0)%Z with (U fs) in P7, P10 by lia.
      change (FSK 0 - 8)%Z with 56%Z in P13. change (Z.to_nat (FSK 0 / 8)) with 8%nat in P14.
      change (NK 0) with 16384%Z in P19.
      rewrite <- sk0_flag_eq in P9, P11. rewrite <- sk0_frame_eq in P12, P13, P15. rewrite <- sk0_sh_eq in P14.
      constructor; [exact P1 | exact P2 | exact P3 | exact P4 | exact P5 | exact P6 | exact P7
        | (intros j Hj; rewrite sk0_flag_eq; exact (P8 j Hj)) | exact P9 | exact P10 | exact P11 | exact P12 | exact P13 | exact P14
        | exact P15 | exact P16 | (split; lia) | exact P18 | exact P19 | exact P20 | exact P21]. }
    destruct (stk0_run_t segs t (T0 eq_refl) mem rom ra S fs midend v hint i0 regs PRE Hret H1 H2 H4) as (r & Mj & RUN & REST).
    exists r, Mj. rewrite sk0_mem_eq in RUN. rewrite sk0_flag_eq, sk0_frame_eq, sk0_sh_eq in RUN. rewrite sk0_frame_eq in REST.
    rewrite Z.add_0_r. split; [exact RUN | exact REST].
  - assert (PRE : stk1H segs t mem S fs midend v hint i0).
    { change (8 * 1)%Z with 8%Z in P7, P10.
      change (FSK 1 - 8)%Z with 120%Z in P13. change (Z.to_nat (FSK 1 / 8)) with 16%nat in P14.
      change (NK 1) with 8192%Z in P19.
      rewrite <- sk1_flag_eq in P9, P11. rewrite <- sk1_frame_eq in P12, P13, P15. rewrite <- sk1_sh_eq in P14.
      constructor; [exact P1 | exact P2 | exact P3 | exact (proj2 P4) | exact P5 | exact P6 | exact P7
        | (intros j Hj; rewrite sk1_flag_eq; exact (P8 j Hj)) | exact P9 | exact P10 | exact P11 | exact P12 | exact P13 | exact P14
        | exact P15 | exact P16 | (split; lia) | exact P18 | exact P19 | exact P20 | exact P21]. }
    destruct (stk1_run_t segs t (T1 eq_refl) mem rom ra S fs midend v hint i0 regs PRE Hret H1 H2 H4) as (r & Mj & RUN & REST).
    exists r, Mj. pose proof (sk1_sh_rng fs hint i0 ltac:(lia)) as SHR.
    rewrite (sk1_mem_eq Mj fs hint i0 S ltac:(lia) ltac:(lia)) in RUN. rewrite sk1_flag_eq, sk1_frame_eq, sk1_sh_eq in RUN. rewrite sk1_frame_eq in REST.
    split; [exact RUN | exact REST].
  - assert (PRE : stk2H segs t mem S fs midend v hint i0).
    { change (8 * 2)%Z with 16%Z in P7, P10.
      change (FSK 2 - 8)%Z with 248%Z in P13. change (Z.to_nat (FSK 2 / 8)) with 32%nat in P14.
      change (NK 2) with 4096%Z in P19.
      rewrite <- sk2_flag_eq in P9, P11. rewrite <- sk2_frame_eq in P12, P13, P15. rewrite <- sk2_sh_eq in P14.
      constructor; [exact P1 | exact P2 | exact P3 | exact (proj2 P4) | exact P5 | exact P6 | exact P7
        | (intros j Hj; rewrite sk2_flag_eq; exact (P8 j Hj)) | exact P9 | exact P10 | exact P11 | exact P12 | exact P13 | exact P14
        | exact P15 | exact P16 | (split; lia) | exact P18 | exact P19 | exact P20 | exact P21]. }
    destruct (stk2_run_t segs t (T2 eq_refl) mem rom ra S fs midend v hint i0 regs PRE Hret H1 H2 H4) as (r & Mj & RUN & REST).
    exists r, Mj. pose proof (sk2_sh_rng fs hint i0 ltac:(lia)) as SHR.
    rewrite (sk2_mem_eq Mj fs hint i0 S ltac:(lia) ltac:(lia)) in RUN. rewrite sk2_flag_eq, sk2_frame_eq, sk2_sh_eq in RUN. rewrite sk2_frame_eq in REST.
    split; [exact RUN | exact REST].
  - assert (PRE : stk3H segs t mem S fs midend v hint i0).
    { change (8 * 3)%Z with 24%Z in P7, P10.
      change (FSK 3 - 8)%Z with 504%Z in P13. change (Z.to_nat (FSK 3 / 8)) with 64%nat in P14.
      change (NK 3) with 2048%Z in P19.
      rewrite <- sk3_flag_eq in P9, P11. rewrite <- sk3_frame_eq in P12, P13, P15. rewrite <- sk3_sh_eq in P14.
      constructor; [exact P1 | exact P2 | exact P3 | exact (proj2 P4) | exact P5 | exact P6 | exact P7
        | (intros j Hj; rewrite sk3_flag_eq; exact (P8 j Hj)) | exact P9 | exact P10 | exact P11 | exact P12 | exact P13 | exact P14
        | exact P15 | exact P16 | (split; lia) | exact P18 | exact P19 | exact P20 | exact P21]. }
    destruct (stk3_run_t segs t (T3 eq_refl) mem rom ra S fs midend v hint i0 regs PRE Hret H1 H2 H4) as (r & Mj & RUN & REST).
    exists r, Mj. pose proof (sk3_sh_rng fs hint i0 ltac:(lia)) as SHR.
    rewrite (sk3_mem_eq Mj fs hint i0 S ltac:(lia) ltac:(lia)) in RUN. rewrite sk3_flag_eq, sk3_frame_eq, sk3_sh_eq in RUN. rewrite sk3_frame_eq in REST.
    split; [exact RUN | exact REST].
Qed.

(* [comment removed for export] *)
Lemma stkKH_mrestrict : forall segs t k (Hd : word -> bool) mem (S fs midend : word) v hint i0,
  (0 <= k <= 3)%Z ->
  stkKH segs t k mem S fs midend v hint i0 ->
  Forall (fun c => hid_off Hd (fst (fst c)) (Z.of_nat (snd (fst c)))) (tg_reads (sk_tg t) v) ->
  hid_off Hd (U (tg_res v)) 8 -> hid_off Hd (U fs) 4231168 ->
  hid_off Hd (skf_sh k (U fs) hint i0) (FSK k / 8) ->
  Forall (fun c => hid_off Hd c 8) (m2s_cells (sk_mt t)) -> hid_off Hd (U S - 208) 208 ->
  stkKH segs t k (mrestrict Hd mem) S fs midend v hint i0.
Proof using.
  intros segs t k Hd mem S fs midend v hint i0 Hk
         [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21] HTG HRES HFS HSH HMC HSCR.
  pose proof (u64_range S) as HSr. pose proof (u64_range fs) as Hfr. pose proof (u64_range (tg_res v)) as Hrr.
  destruct P17 as [G1 G2]. destruct P4 as [P4a P4b].
  assert (NKr : (1 <= NK k <= 16384)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold NK in G in change_no_check G' end); assert (KC : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3)%Z) by lia; destruct KC as [-> | [-> | [-> | ->]]]; split; vm_compute; intro X; discriminate X).
  assert (FSr : (64 <= FSK k <= 512 /\ FSK k mod 8 = 0 /\ FOFFK k + NK k <= 36864 /\ 4096 <= FOFFK k /\ 36864 + k * 2 ^ 20 + FSK k * NK k <= 4231168)%Z).
  { (lazymatch goal with |- ?G => let G' := eval unfold FSK, FOFFK, NK in G in change_no_check G' end). assert (KC : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3)%Z) by lia. destruct KC as [-> | [-> | [-> | ->]]]; repeat split; vm_compute; first [reflexivity | (intro X; discriminate X)]. }
  destruct FSr as (FS1 & FS2 & FO1 & FO2 & FZ).
  assert (POS : forall j, (0 <= skf_pos k hint j < NK k)%Z) by (intros j; (lazymatch goal with |- ?G => let G' := eval unfold skf_pos in G in change_no_check G' end); apply Z.mod_pos_bound; lia).
  assert (FLr : forall j, (U fs + 4096 <= skf_flag k (U fs) hint j < U fs + 36864)%Z) by (intros j; pose proof (POS j); (lazymatch goal with |- ?G => let G' := eval unfold skf_flag in G in change_no_check G' end); lia).
  assert (FRr : (U fs + 36864 <= skf_frame k (U fs) hint i0 /\ skf_frame k (U fs) hint i0 + FSK k <= U fs + 4231168)%Z).
  { pose proof (POS i0) as PP. (lazymatch goal with |- ?G => let G' := eval unfold skf_frame in G in change_no_check G' end). split; [nia | nia]. }
  assert (SHr : (0 <= skf_sh k (U fs) hint i0 /\ skf_sh k (U fs) hint i0 + FSK k / 8 < 2 ^ 64)%Z).
  { (lazymatch goal with |- ?G => let G' := eval unfold skf_sh in G in change_no_check G' end). pose proof (Z.div_pos (skf_frame k (U fs) hint i0) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (skf_frame k (U fs) hint i0) 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (FSK k) 8 64 ltac:(lia) ltac:(lia)). lia. }
  assert (RR : forall c n bs, (0 <= c)%Z -> (c + Z.of_nat n < 2 ^ 64)%Z -> hid_off Hd c (Z.of_nat n) ->
               rdn segs mem (Z_to_bv 64 c) n = Some bs -> rdn segs (mrestrict Hd mem) (Z_to_bv 64 c) n = Some bs).
  { intros c n bs Hc0 Hc HH Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact HH]. }
  assert (OK : forall c n, (0 <= c)%Z -> (c + Z.of_nat n < 2 ^ 64)%Z -> hid_off Hd c (Z.of_nat n) ->
               store_ok segs mem (Z_to_bv 64 c) n = true -> store_ok segs (mrestrict Hd mem) (Z_to_bv 64 c) n = true).
  { intros c n Hc0 Hc HH Hr. rewrite store_ok_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact HH]. }
  assert (SUB : forall lo n, (U fs <= lo)%Z -> (lo + n <= U fs + 4231168)%Z -> hid_off Hd lo n) by (intros lo n A B x Hx; apply HFS; lia).
  constructor.
  - apply tlsgaH_mrestrict; [exact P1 | exact HTG |]. intros x Hx. apply HSCR. rewrite at_u in Hx by lia. lia.
  - exact P2.
  - apply RR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact HRES | exact P3].
  - split; assumption.
  - apply RR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | apply SUB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P5].
  - apply RR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | apply SUB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P6].
  - apply RR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | apply SUB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P7].
  - intros j Hj. destruct (P8 j Hj) as (b & Rb & Nb). exists b. split; [|exact Nb]. pose proof (FLr j).
    apply RR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | apply SUB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rb].
  - pose proof (FLr i0). apply RR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | apply SUB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P9].
  - apply OK; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | apply SUB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P10].
  - pose proof (FLr i0). apply OK; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | apply SUB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P11].
  - apply OK; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | apply SUB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P12].
  - apply OK; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | apply SUB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P13].
  - apply OK; [lia | rewrite Z2Nat.id by lia; lia | rewrite Z2Nat.id by lia; exact HSH | exact P14].
  - destruct P15 as [R1 R2 R3 R4 R5 R6 R7 R8 HCx Hlo Hhi].
    pose proof P16 as PC. pose proof HMC as HC'. unfold m2s_cells in PC, HC'.
    repeat match type of PC with Forall _ (_ :: _) => apply Forall_cons_iff in PC; destruct PC as [? PC] end.
    repeat match type of HC' with Forall _ (_ :: _) => apply Forall_cons_iff in HC'; destruct HC' as [? HC'] end.
    constructor; try assumption; (apply RR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); assumption | assumption]).
  - exact P16.
  - split; assumption.
  - exact P18.
  - exact P19.
  - exact P20.
  - rewrite store_ok_mrestrict; [exact P21 | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HSCR; lia].
Qed.
End FPGen1.
End AsRtStkMalK.
Module AsRtStkLiftG.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 AsRtStkCount AsRtStkMalK.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hide (P : Prop) : Prop := P.

Section Glue.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma scr_rel_unrestrict : forall (Hd : word -> bool) (M Mj : word -> option byte) lo hi,
  scr_rel (mrestrict Hd M) Mj lo hi -> hid_off Hd lo (hi - lo) ->
  Mj = mrestrict Hd (munrestrict Hd M Mj) /\ scr_rel M (munrestrict Hd M Mj) lo hi
  /\ (forall a, Hd a = true -> munrestrict Hd M Mj a = M a).
Proof using.
  intros Hd M Mj lo hi (O & G & D) HO.
  assert (HID : forall a : word, Hd a = true -> Mj a = None).
  { intros a Ha. rewrite O; [(lazymatch goal with |- ?G => let G' := eval unfold mrestrict in G in change_no_check G' end); rewrite Ha; reflexivity|].
    destruct (Z_lt_le_dec (U a) lo); [left; lia|]. destruct (Z_lt_le_dec (U a) hi); [|right; lia].
    exfalso. rewrite (HO a) in Ha by lia. discriminate Ha. }
  split; [|split].
  - apply functional_extensionality. intros a. (lazymatch goal with |- ?G => let G' := eval unfold mrestrict, munrestrict in G in change_no_check G' end). destruct (Hd a) eqn:E; [apply HID; exact E | reflexivity].
  - split; [|split].
    + intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold munrestrict in G in change_no_check G' end). destruct (Hd a) eqn:E; [reflexivity|]. rewrite (O a Ha). (lazymatch goal with |- ?G => let G' := eval unfold mrestrict in G in change_no_check G' end). rewrite E. reflexivity.
    + intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold munrestrict in G in change_no_check G' end). destruct (Hd a) eqn:E; [exact Ha|]. apply G. (lazymatch goal with |- ?G => let G' := eval unfold mrestrict in G in change_no_check G' end). rewrite E. exact Ha.
    + intros a NE. unfold munrestrict in *. destruct (Hd a) eqn:E; [exfalso; apply NE; reflexivity|]. apply D. (lazymatch goal with |- ?G => let G' := eval unfold mrestrict in G in change_no_check G' end). rewrite E. exact NE.
  - intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold munrestrict in G in change_no_check G' end). rewrite Ha. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stk_mem_mrestrict : forall (Hd : word -> bool) m hc fl f last sh nsh hint' (S : word),
  (0 <= hc /\ 0 <= fl /\ 0 <= f /\ 0 <= last /\ 0 <= sh) ->
  (hc + 8 < 2 ^ 64 /\ fl + 1 < 2 ^ 64 /\ f + 32 < 2 ^ 64 /\ last + 8 < 2 ^ 64 /\ sh + Z.of_nat nsh < 2 ^ 64) ->
  hid_off Hd hc 8 -> hid_off Hd fl 1 -> hid_off Hd (f + 24) 8 -> hid_off Hd last 8 -> hid_off Hd sh (Z.of_nat nsh) ->
  stk_mem (mrestrict Hd m) hc fl f last sh nsh hint' S = mrestrict Hd (stk_mem m hc fl f last sh nsh hint' S).
Proof using.
  intros Hd m hc fl f last sh nsh hint' S B0 B1 H1 H2 H3 H4 H5. (lazymatch goal with |- ?G => let G' := eval unfold stk_mem in G in change_no_check G' end).
  rewrite !wbytes_mrestrict; [reflexivity | | | | | | | | | |];
    wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval unfold zeros in G in change_no_check G' end); rewrite ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
    rewrite ?u_Z2bv by lia; first [lia | assumption].
Qed.

(* [comment removed for export] *)
Lemma fcount_kcount : forall k FF, fcount k FF = kcount k FF.
Proof using. intros k FF. induction FF as [|f r IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [fcount kcount] in G in change_no_check G' end). rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma skf_flag_vocab : forall k fs hint i, skf_flag k fs hint i = fake_flag_addr fs k (skf_pos k hint i).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold skf_flag, fake_flag_addr, fake_flags_off, FOFFK in G in change_no_check G' end). lia. Qed.
Lemma skf_frame_vocab : forall k fs hint i, skf_frame k fs hint i = fake_frame_addr fs k (skf_pos k hint i).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold skf_frame, fake_frame_addr, FSK, FS in G in change_no_check G' end). lia. Qed.



(* [comment removed for export] *)
Lemma store_ok_pointwise : forall segs (m : word -> option byte) (a : word) n,
  U a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, U a <= U x < U a + Z.of_nat n -> store_ok segs m x 1%nat = true) ->
  store_ok segs m a n = true.
Proof using.
  intros segs m a n Hn F. apply store_ok_of_all; [exact Hn|]. intros x Hx. specialize (F x Hx). cbn [store_ok] in F.
  destruct (wview segs m x); [discriminate | discriminate F].
Qed.
Lemma store_ok_defined : forall segs (m : word -> option byte) (a : word) n,
  U a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, U a <= U x < U a + Z.of_nat n -> m x <> None) ->
  store_ok segs m a n = true.
Proof using.
  intros segs m a n Hn F. apply store_ok_of_all; [exact Hn|]. intros x Hx. specialize (F x Hx). (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end).
  destruct (m x); [discriminate | exfalso; apply F; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma stk_mem_last_m64 : forall (m : word -> option byte) hc fl f last sh nsh hint' (S : word),
  (0 <= last /\ 0 <= sh) -> (last + 8 < 2 ^ 64 /\ sh + Z.of_nat nsh < 2 ^ 64) ->
  (sh + Z.of_nat nsh <= last \/ last + 8 <= sh) -> 0 <= fl < 2 ^ 64 ->
  m64 (stk_mem m hc fl f last sh nsh hint' S) last fl.
Proof using.
  intros m hc fl f last sh nsh hint' S (B0 & B1) (B2 & B3) Dj Hfl. exists (word_to_le_bytes 8 (Z_to_bv 64 fl)).
  split; [|split].
  - intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold stk_mem in G in change_no_check G' end).
    rewrite MemsetLibF.MemSplit.wbytes_outside; [| (lazymatch goal with |- ?G => let G' := eval unfold zeros in G in change_no_check G' end); rewrite repeat_length, u_Z2bv by lia; lia
                                      | (lazymatch goal with |- ?G => let G' := eval unfold zeros in G in change_no_check G' end); rewrite repeat_length, !u_Z2bv by lia; lia].
    rewrite MemsetLibF.MemSplit.wbytes_inside; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                     | rewrite length_N_to_le_bytes, !u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    rewrite !u_Z2bv by lia. replace (last + Z.of_nat i - last) with (Z.of_nat i) by lia. rewrite Nat2Z.id. reflexivity.
  - apply length_N_to_le_bytes.
  - rewrite bytes_le_to_Z_8. apply u_Z2bv; lia.
Qed.
End Glue.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stk_vals (bt : as_boot) (arg off dtvp dtv1 keysp : Z) : tlsga_vals :=
  TGV (Z_to_bv 64 arg) (Z_to_bv 64 (ia_tp (bt_ia bt))) (Z_to_bv 64 off) (Z_to_bv 64 dtvp) (Z_to_bv 64 dtv1) (Z_to_bv 64 keysp)
      (Z_to_bv 64 (bt_tctx bt)) (Z_to_bv 64 (bt_thread bt)) (Z_to_bv 64 (bt_tp bt + 0x738)) (Z_to_bv 64 (bt_tp bt + 0x814))
      (Z_to_bv 64 (bt_dtls bt)) (Z_to_bv 64 (bt_tp bt)).

Definition stk_consts (t : stk_tab) (tp tctx arg off dtvp dtv1 keysp : Z) : list (Z * nat * Z) :=
  let tg := sk_tg t in let mt := sk_mt t in
  [ (tg_c_inited tg, 1%nat, 1); (tg_c_rtga tg, 8%nat, bv_unsigned (tg_tga tg)); (arg, 8%nat, 1); (arg + 8, 8%nat, off);
    (tp - 8, 8%nat, dtvp); (dtvp + 8, 8%nat, dtv1); (tg_c_tsd tg, 1%nat, 1); (tg_c_tsd tg + 4, 4%nat, 0);
    (tp - 88, 8%nat, keysp); (keysp, 8%nat, tctx);
    (tg_g_cf tg, 8%nat, tg_p_cf tg); (tg_p_cf tg + 137, 1%nat, 1); (tg_g_verb tg, 8%nat, tg_p_verb tg); (tg_p_verb tg, 4%nat, 0);
    (tg_c_tlsd tg, 8%nat, 8);
    (mt_g_shoff mt, 8%nat, mt_p_shoff mt); (mt_p_shoff mt, 8%nat, 0x7fff8000); (mt_g_midbeg mt, 8%nat, mt_p_midbeg mt);
    (mt_p_midbeg mt, 8%nat, 0); (mt_g_midend mt, 8%nat, mt_p_midend mt); (mt_p_midend mt, 8%nat, 0);
    (mt_g_hiend mt, 8%nat, mt_p_hiend mt); (mt_p_hiend mt, 8%nat, 0x7fffffffffff) ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma frame_apart : forall fs k pos k' pos', 0 <= k <= 3 -> 0 <= k' <= 3 -> 0 <= pos < FCAP k -> 0 <= pos' < FCAP k' ->
  (k, pos) <> (k', pos') ->
  fake_frame_addr fs k pos + FS k <= fake_frame_addr fs k' pos' \/ fake_frame_addr fs k' pos' + FS k' <= fake_frame_addr fs k pos.
Proof.
  intros fs k pos k' pos' Hk Hk' Hp Hp' NE. unfold fake_frame_addr, FS, FCAP in *.
  assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia. assert (K' : k' = 0 \/ k' = 1 \/ k' = 2 \/ k' = 3) by lia.
  destruct K as [-> | [-> | [-> | ->]]]; destruct K' as [-> | [-> | [-> | ->]]]; cbn in *;
    try lia; (assert (pos <> pos') by (intros ->; apply NE; reflexivity); lia).
Qed.

Lemma frame_al8 : forall fs k pos, 0 <= k <= 3 -> fs mod 4096 = 0 ->
  fake_frame_addr fs k pos mod 8 = 0 /\ FS k mod 8 = 0 /\ 64 <= FS k <= 512.
Proof.
  intros fs k pos Hk Hfs. (lazymatch goal with |- ?G => let G' := eval unfold fake_frame_addr, FS in G in change_no_check G' end).
  assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct K as [-> | [-> | [-> | ->]]]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (split; [Z.div_mod_to_equations; lia | split; [reflexivity | lia]]).
Qed.

(* [comment removed for export] *)
Lemma sh_apart_l : forall b n f, 0 <= b -> 0 <= n -> f mod 8 = 0 -> b + n <= f -> sh_hi b n <= sh_lo f.
Proof. intros b n f Hb Hn Hf Hle. (lazymatch goal with |- ?G => let G' := eval unfold sh_hi, sh_lo in G in change_no_check G' end). Z.div_mod_to_equations. lia. Qed.
Lemma sh_apart_r : forall f m b, 0 <= f -> (f + m) mod 8 = 0 -> f + m <= b -> sh_hi f m <= sh_lo b.
Proof. intros f m b Hf Hfm Hle. (lazymatch goal with |- ?G => let G' := eval unfold sh_hi, sh_lo in G in change_no_check G' end). Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma sh_in_maps : forall f n z, 0 <= f -> 0 <= n -> (f + n <= AS_LO \/ AS_HEAPLO <= f) -> f + n <= 2 ^ 47 ->
  sh_lo f <= z < sh_hi f n -> shmaps z.
Proof.
  intros f n z Hf Hn Hb H47 Hz. unfold shmaps, sh_lo, sh_hi, AS_LO, AS_GAPLO, AS_GAPHI, AS_HEAPLO, SB in *.
  destruct Hb as [Hb|Hb]; [left | right]; Z.div_mod_to_equations; lia.
Qed.

Section Facts.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl : Model).
  Hypothesis W : WF bt st Lc FF.
  Hypothesis RP : Rep bt st Lc FF M mdl.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Variable AA : list (Z * Z).
  #[local] Abbreviation Hd := (HL mdl AA).

  (* [comment removed for export] *)
  Lemma const_row : forall a n v, In (a, n, v) (bt_consts bt) -> (0 < n)%nat ->
    cellN SG M a n v /\ ia_img_lo IA <= a /\ a + Z.of_nat n <= ia_img_hi IA.
  Proof using RP W mdl FF Lc st RC.
    intros a n v Hin Hn.
    pose proof (read_consts bt st Lc FF M mdl RP) as CH. unfold cells_hold in CH. rewrite Forall_forall in CH.
    split; [exact (CH _ Hin)|].
    assert (K1 : img_kind bt a).
    { apply (img_kinds bt st Lc FF W). left. exists (a, n, v). split; [exact Hin|]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). lia. }
    assert (K2 : img_kind bt (a + Z.of_nat n - 1)).
    { apply (img_kinds bt st Lc FF W). left. exists (a, n, v). split; [exact Hin|]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). lia. }
    destruct K1 as [K1 _]. destruct K2 as [K2 _]. lia.
  Qed.

  Lemma hid_notlazy : forall lo n, 0 <= lo -> lo + n <= 2 ^ 64 -> (forall z, lo <= z < lo + n -> lzb mdl z = false) -> hid_off Hd lo n.
  Proof using.
    intros lo n H0 H1 F x Hx. pose proof (u64_range x) as Hxr.
    rewrite <- (Z_to_bv_bv_unsigned 64 x). apply HL_notlazy; [lia | exact (F _ Hx)].
  Qed.
  Lemma hid_img : forall lo n, ia_img_lo IA <= lo -> lo + n <= ia_img_hi IA -> hid_off Hd lo n.
  Proof using RP W M FF Lc st RC.
    intros lo n H0 H1. pose proof (img_lits bt st Lc FF W) as [I1 I2]. unfold AS_LO in I2.
    apply hid_notlazy; [lia | lia |]. intros z Hz. apply (rep_nolazy_img bt st Lc FF M mdl W RP). lia.
  Qed.
  Lemma hid_stack : forall lo n, CEIL <= lo -> lo + n <= 2 ^ 64 -> hid_off Hd lo n.
  Proof using RP M FF Lc st bt.
    intros lo n H0 H1. pose proof ceil_rng as CR. apply hid_notlazy; [lia | lia |].
    intros z Hz. apply (rep_nolazy_stack bt st Lc FF M mdl RP). lia.
  Qed.
  Lemma hid_fs : forall lo n, bt_fs bt <= lo -> lo + n <= bt_fs bt + FAKE_SIZE -> hid_off Hd lo n.
  Proof using RP W M FF Lc st RC.
    intros lo n H0 H1. pose proof ceil_rng as CR. pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & X5 & X6 & _).
    apply hid_notlazy; [lia | lia |]. intros z Hz. apply (rep_nolazy_fs bt st Lc FF M mdl W RP). lia.
  Qed.
  Lemma hid_thread : forall lo n, bt_thread bt <= lo -> lo + n <= bt_thread bt + PG -> hid_off Hd lo n.
  Proof using RP W M FF Lc st RC.
    intros lo n H0 H1. pose proof ceil_rng as CR. pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & _).
    apply hid_notlazy; [lia | lia |]. intros z Hz. apply (rep_nolazy_thread bt st Lc FF M mdl W RP). lia.
  Qed.
  Lemma hid_tctx : forall lo n, bt_tctx bt <= lo -> lo + n <= bt_tctx bt + 0x10000 -> hid_off Hd lo n.
  Proof using RP W M FF Lc st RC.
    intros lo n H0 H1. pose proof ceil_rng as CR. pose proof (fixed_facts bt st Lc FF W) as (_ & _ & X3 & X4 & _).
    apply hid_notlazy; [lia | lia |]. intros z Hz. apply (rep_nolazy_tctx bt st Lc FF M mdl W RP). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma dtls_facts : 0 < bt_dtls bt /\ bt_dtls bt + PG <= CEIL /\ In (bt_dtls bt, bt_dtls bt + PG) (bt_fixed bt).
  Proof using W FF Lc st.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (RNG & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IND & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ IND)) as ((A1 & _ & A3 & _ & _) & _). repeat split; assumption.
  Qed.
  Lemma hid_dtls : forall lo n, bt_dtls bt <= lo -> lo + n <= bt_dtls bt + PG -> hid_off Hd lo n.
  Proof using RP W M FF Lc st RC.
    intros lo n H0 H1. pose proof ceil_rng as CR. destruct dtls_facts as (D1 & D2 & D3).
    apply hid_notlazy; [lia | lia |]. intros z Hz.
    apply (rep_nolazy_fixed bt st Lc FF M mdl W RP _ _ z D3); unfold KSPACE, PG in *; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma hid_fs_shadow : forall lo n,
    (forall l h, In (l, h) (SHC IA (bt_fs bt)) -> range_allowed AA l h) ->
    sh_lo (bt_fs bt) <= lo -> lo + n <= sh_hi (bt_fs bt) FAKE_SIZE -> hid_off Hd lo n.
  Proof using.
    intros lo n B3 H0 H1 x Hx.
    apply (HL_allowed_page mdl AA (sh_lo (bt_fs bt)) (sh_hi (bt_fs bt) FAKE_SIZE) (bv_unsigned x) x).
    - apply B3. (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end). right; right; left. reflexivity.
    - lia.
    - rewrite Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fs_place : 0 < bt_fs bt /\ bt_fs bt + FAKE_SIZE <= CEIL /\ bt_fs bt mod 4096 = 0
    /\ (bt_fs bt + FAKE_SIZE <= ia_img_lo IA \/ ia_img_hi IA <= bt_fs bt) /\ (bt_fs bt + FAKE_SIZE <= AS_LO \/ AS_HEAPLO <= bt_fs bt)
    /\ In (bt_fs bt, bt_fs bt + FAKE_SIZE) (bt_fixed bt).
  Proof using W FF Lc st.
    pose proof (fs_range bt st Lc FF W) as ((D1 & D2 & D3 & D4 & D5) & D6). unfold PG in D6.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & INFS & _) & _).
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma fresh_priv : forall k pos a, 0 <= k <= KMAXCLASS -> 0 <= pos < FCAP k ->
    ~ In (fake_frame_addr (bt_fs bt) k pos, k) FF ->
    (bt_fs bt <= a < bt_fs bt + 0x9000
     \/ fake_frame_addr (bt_fs bt) k pos <= a < fake_frame_addr (bt_fs bt) k pos + FS k
     \/ sh_lo (fake_frame_addr (bt_fs bt) k pos) <= a < sh_hi (fake_frame_addr (bt_fs bt) k pos) (FS k)) ->
    rt_priv IA Lc FF a.
  Proof using W st.
    intros k pos a Hk Hpos NI Ha. unfold KMAXCLASS in Hk.
    destruct fs_place as (P1 & P2 & P3 & P4 & P5 & INFS). pose proof ceil_rng as CR.
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    set (fs := bt_fs bt) in *. set (f := fake_frame_addr fs k pos) in *.
    pose proof (frame_geom k pos fs ltac:((lazymatch goal with |- ?G => let G' := eval unfold KMAXCLASS in G in change_no_check G' end); lia) Hpos ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); exact P3)) as G. cbn zeta in G. fold f in G.
    destruct G as (G1 & G2 & _ & _ & _ & _).
    destruct (frame_al8 fs k pos Hk P3) as (A8 & F8 & FR). fold f in A8.
    (* [comment removed for export] *)
    assert (FAP : forall f' k', In (f', k') FF -> (f + FS k <= f' \/ f' + FS k' <= f) /\ f' mod 8 = 0 /\ FS k' mod 8 = 0
                                 /\ fs + 0x9000 <= f' /\ f' + FS k' <= fs + FAKE_SIZE /\ 0 <= FS k').
    { intros f' k' Hin. destruct (fake_frame_facts bt st Lc FF W f' k' Hin) as (F1 & F2 & _ & F4 & F5 & F6 & F7).
      unfold KMAXCLASS in F5. fold fs in F1, F2, F7.
      destruct (frame_al8 fs k' (fpos bt f' k') F5 P3) as (A8' & F8' & _). rewrite <- F7 in A8'.
      split; [| repeat split; assumption || lia].
      rewrite F7. apply frame_apart; try assumption. intros E. injection E as E1 E2. apply NI. subst k'. (lazymatch goal with |- ?G => let G' := eval unfold f in G in change_no_check G' end). rewrite E2. rewrite <- F7. exact Hin. }
    (* [comment removed for export] *)
    assert (BAP : forall p n, In (p, n) Lc -> 1 <= n /\ 0 <= p /\ (p + up8 n <= fs \/ fs + FAKE_SIZE <= p) /\ n <= up8 n /\ up8 n mod 8 = 0 /\ p mod 8 = 0
                              /\ (p + up8 n <= AS_LO \/ AS_HEAPLO <= p) /\ p + up8 n <= CEIL).
    { intros p n Hin. destruct (live_ext bt st Lc FF W p n Hin) as (lo & hi & E & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
      pose proof (up8_facts n ltac:(lia)) as (U1 & U2 & U3 & U4).
      destruct (live_ext_vs_fixed bt st Lc FF W p n lo hi _ _ Hin E INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, KSPACE in G in change_no_check G' end); lia)) as [D|D];
        unfold AsAinvOpsPf3b.boxed in Y12; (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [assumption|]);
        (split; [clear -Y9; Z.div_mod_to_equations; lia|]); (split; [lia | lia]). }
    assert (OFFB : forall z, fs <= z < fs + FAKE_SIZE -> z < CEIL /\ ~ (ia_img_lo IA <= z < ia_img_hi IA) /\ (z < AS_LO \/ AS_HEAPLO <= z)) by (intros z Hz; lia).
    destruct Ha as [Ha | [Ha | Ha]].
    - (* [comment removed for export] *)
      destruct (OFFB a ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end); lia)) as (Z1 & Z2 & Z3). split; [exact Z1|]. split; [exact Z2|].
      destruct (heap_not_shadowish bt st Lc FF W Lc a ltac:(intros p n H; exact H) Z3) as (N1 & N2 & N3 & N4).
      intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
      + destruct V as (p & n & Hin & Hpa). destruct (BAP p n Hin) as (B1 & B2 & B3 & B4 & _). unfold FAKE_SIZE in B3. lia.
      + destruct V as (f' & k' & Hin & Hfa). destruct (FAP f' k' Hin) as (_ & _ & _ & Q1 & _). lia.
    - (* [comment removed for export] *)
      destruct (OFFB a ltac:(lia)) as (Z1 & Z2 & Z3). split; [exact Z1|]. split; [exact Z2|].
      destruct (heap_not_shadowish bt st Lc FF W Lc a ltac:(intros p n H; exact H) Z3) as (N1 & N2 & N3 & N4).
      intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
      + destruct V as (p & n & Hin & Hpa). destruct (BAP p n Hin) as (B1 & B2 & B3 & B4 & _). lia.
      + destruct V as (f' & k' & Hin & Hfa). destruct (FAP f' k' Hin) as (Q0 & _). lia.
    - (* [comment removed for export] *)
      assert (SHR : SB + fs / 8 <= sh_lo f /\ sh_hi f (FS k) = SB + (f + FS k) / 8 /\ sh_lo f = SB + f / 8 /\ AS_LO < SB /\ SB + (f + FS k) / 8 <= AS_HEAPLO
                    /\ SB + (f + FS k) / 8 <= SB + CEIL / 8).
      { (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, AS_LO, AS_HEAPLO, SB in G in change_no_check G' end). clear -G1 G2 A8 F8 P1 P2 CR. unfold FAKE_SIZE in *. Z.div_mod_to_equations. lia. }
      destruct SHR as (S1 & S2 & S3 & S4 & S5 & S6). rewrite S2, S3 in Ha.
      split; [unfold AS_HEAPLO in S5; lia|]. split; [lia|].
      intros [V | [V | [V | [V | [V | V]]]]].
      + destruct V as (p & n & Hin & Hpa). destruct (BAP p n Hin) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). lia.
      + destruct V as (f' & k' & Hin & Hfa). destruct (FAP f' k' Hin) as (_ & _ & _ & Q1 & Q2 & Q3).
        destruct (OFFB f' ltac:(lia)) as (_ & _ & Z3). destruct (OFFB (f' + FS k' - 1) ltac:(lia)) as (_ & _ & Z3'). lia.
      + destruct V as (p & n & Hin & Hs). destruct (BAP p n Hin) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        destruct B3 as [B3|B3].
        * pose proof (sh_apart_l p n f B2 ltac:(lia) A8 ltac:(lia)). lia.
        * assert (E8 : (f + FS k) mod 8 = 0) by (clear -A8 F8; Z.div_mod_to_equations; lia).
          pose proof (sh_apart_r f (FS k) p ltac:(lia) E8 ltac:(unfold FAKE_SIZE in *; lia)). rewrite S2 in H. lia.
      + destruct V as (f' & k' & Hin & Hs). destruct (FAP f' k' Hin) as (Q0 & Q8 & QF & Q1 & Q2 & Q3).
        destruct Q0 as [Q0|Q0].
        * assert (E8 : (f + FS k) mod 8 = 0) by (clear -A8 F8; Z.div_mod_to_equations; lia).
          pose proof (sh_apart_r f (FS k) f' ltac:(lia) E8 Q0). rewrite S2 in H. lia.
        * pose proof (sh_apart_l f' (FS k') f ltac:(lia) Q3 A8 Q0). lia.
      + unfold in_stack_shadow, sh_lo in V. lia.
      + unfold in_image_shadow in V. destruct P4 as [P4|P4].
        * assert (E8 : (f + FS k) mod 8 = 0) by (clear -A8 F8; Z.div_mod_to_equations; lia).
          pose proof (sh_apart_r f (FS k) (ia_img_lo IA) ltac:(lia) E8 ltac:(unfold FAKE_SIZE in *; lia)). rewrite S2 in H. lia.
        * unfold sh_lo, sh_hi in V. assert (P4' : ia_img_hi IA <= f) by lia. clear -V Ha A8 P4'. Z.div_mod_to_equations. lia.
  Qed.
End Facts.
End AsRtStkLiftG.
Module AsRtXMemcpyI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset AsRtXMemcpy.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_xmcpy_tab : xmcpy_tab :=
  {| xc_base := 0x6d968; xc_rip := asan_rip_tab; xc_mcp := 0xf52e0;
     xc_g_flag := 0xffdd8; xc_p_flag := 0x108259; xc_c_rmc := 0x1011a8 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x6d968 : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

Lemma asan_xmcpy_tab_ok : xmcpy_tab_ok ASEGS asan_xmcpy_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [xc_base xc_rip xc_mcp xc_g_flag xc_p_flag xc_c_rmc asan_xmcpy_tab rt_base rt_m2s asan_rip_tab mt_g_shoff asan_m2s_tab_6fb04] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold xmcpy_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact asan_memcpy_code.
  - lit 116%Z (0x6d9dc : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 868%Z (0x6dccc : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2s_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 188%Z (0x6da24 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 1124%Z (0x6ddcc : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2s_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6d994 D_6d994 F_6d998 D_6d998.
  - lit 116%Z (0x6d9dc : word). gload_tac F_6d9d4 D_6d9d4 F_6d9d8 D_6d9d8.
  - lit 188%Z (0x6da24 : word). gload_tac F_6da1c D_6da1c F_6da20 D_6da20.
  - gload_tac F_6da54 D_6da54 F_6da58 D_6da58.
  - lit 168%Z (0x6da10 : word). lit 868%Z (0x6dccc : word). eapply (gbnez_of ASEGS _ _ _ _ _ F_6da08 eq_refl D_6da08). apply bv_eq; vm_compute; reflexivity.
  - lit 916%Z (0x6dcfc : word). lit 172%Z (0x6da14 : word). eapply (gbeqz_of ASEGS _ _ _ _ _ F_6dcf4 eq_refl D_6dcf4). apply bv_eq; vm_compute; reflexivity.
  - lit 240%Z (0x6da58 : word). lit 1124%Z (0x6ddcc : word). eapply (gbnez_of ASEGS _ _ _ _ _ F_6da50 eq_refl D_6da50). apply bv_eq; vm_compute; reflexivity.
  - lit 1172%Z (0x6ddfc : word). lit 244%Z (0x6da5c : word). eapply (gbeqz_of ASEGS _ _ _ _ _ F_6ddf4 eq_refl D_6ddf4). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
  - apply ret_ok_even. vm_compute. reflexivity.
Qed.



End FPGen1.
End AsRtXMemcpyI.
Module AsRtXMemmoveI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove AsRtXMemmove.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_xmmove_tab : xmmove_tab :=
  {| ym_base := 0x6d4a8; ym_rip := asan_rip_tab; ym_imm := 0x7fee0; ym_g_flag := 0xffdd8; ym_p_flag := 0x108259 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x6d4a8 : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

Lemma asan_xmmove_tab_ok : xmmove_tab_ok ASEGS asan_xmmove_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [ym_base ym_rip ym_imm ym_g_flag ym_p_flag asan_xmmove_tab rt_base rt_m2s asan_rip_tab mt_g_shoff asan_m2s_tab_6fb04] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold xmmove_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact asan_imemmove_code.
  - apply bv_eq; vm_compute; reflexivity.
  - lit 92%Z (0x6d504 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 564%Z (0x6d6dc : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1s_words in G in change_no_check G' end). code_ato_vm.
  - lit 168%Z (0x6d550 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 820%Z (0x6d7dc : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6d4d0 D_6d4d0 F_6d4d4 D_6d4d4.
  - lit 92%Z (0x6d504 : word). gload_tac F_6d4fc D_6d4fc F_6d500 D_6d500.
  - lit 168%Z (0x6d550 : word). gload_tac F_6d548 D_6d548 F_6d54c D_6d54c.
  - lit 148%Z (0x6d53c : word). lit 564%Z (0x6d6dc : word). eapply (gbnez_of ASEGS _ _ _ _ _ F_6d534 eq_refl D_6d534). apply bv_eq; vm_compute; reflexivity.
  - lit 612%Z (0x6d70c : word). lit 152%Z (0x6d540 : word). eapply (gbeqz_of ASEGS _ _ _ _ _ F_6d704 eq_refl D_6d704). apply bv_eq; vm_compute; reflexivity.
  - lit 224%Z (0x6d588 : word). lit 820%Z (0x6d7dc : word). eapply (gbnez_of ASEGS _ _ _ _ _ F_6d580 eq_refl D_6d580). apply bv_eq; vm_compute; reflexivity.
  - lit 868%Z (0x6d80c : word). lit 228%Z (0x6d58c : word). eapply (gbeqz_of ASEGS _ _ _ _ _ F_6d804 eq_refl D_6d804). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
Qed.



End FPGen1.
End AsRtXMemmoveI.
Module AsRtXMemsetI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset AsRtXMemset.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_xmset_tab : xmset_tab :=
  {| xm_base := 0x6d1b8; xm_rip := asan_rip_tab; xm_mset := 0xf56e4;
     xm_g_flag := 0xffdd8; xm_p_flag := 0x108259; xm_c_rms := 0x1011b0 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x6d1b8 : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

Lemma asan_xmset_tab_ok : xmset_tab_ok ASEGS asan_xmset_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [xm_base xm_rip xm_mset xm_g_flag xm_p_flag xm_c_rms asan_xmset_tab rt_base rt_m2s asan_rip_tab mt_g_shoff asan_m2s_tab_6fb04] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold xmset_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact asan_memset_code.
  - lit 88%Z (0x6d210 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 428%Z (0x6d364 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6d1dc D_6d1dc F_6d1e0 D_6d1e0.
  - lit 88%Z (0x6d210 : word). gload_tac F_6d208 D_6d208 F_6d20c D_6d20c.
  - gload_tac F_6d244 D_6d244 F_6d248 D_6d248.
  - lit 144%Z (0x6d248 : word). lit 428%Z (0x6d364 : word). eapply (gbnez_of ASEGS _ _ _ _ _ F_6d240 eq_refl D_6d240). apply bv_eq; vm_compute; reflexivity.
  - lit 476%Z (0x6d394 : word). lit 148%Z (0x6d24c : word). eapply (gbeqz_of ASEGS _ _ _ _ _ F_6d38c eq_refl D_6d38c). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
  - apply ret_ok_even. vm_compute. reflexivity.
Qed.



End FPGen1.
End AsRtXMemsetI.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 AsRtStkCount AsRtStkMalK AsRtStkLiftG.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SL.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable bt : as_boot.
  Variable HP0 : option Z -> ast -> Prop.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation AAINVH := (fun h => AAINVP (HP0 h) bt).
  #[local] Abbreviation U := bv_unsigned.

  Hypothesis SEGS_wx : wx_segs_nowrap SG.
  Hypothesis SEGS_hull : forall a, find_segment SG a 1 <> None -> ia_img_lo IA <= a < ia_img_hi IA.
  Hypothesis HOFF : forall h Lc FF B C K M mdl AA, AAINVP (HP0 h) bt Lc FF B C K M mdl -> H_off_segments SG (HL mdl AA).
  (* [comment removed for export] *)
  Hypothesis HP0_hint : forall h st k v, HP0 h st -> HP0 h (set_hint st k v).

  Variable k : Z.
  Hypothesis Hk : 0 <= k <= 3.
  Variable t : stk_tab.
  Hypothesis TOK : forall fx : FPState, @stkK_tab_ok fx SG k t.
  Hypothesis T_entry : sk_base t = Z_to_bv 64 (ia_stkmal IA k).
  (* [comment removed for export] *)
  Variables (arg off dtvp dtv1 keysp : Z).
  Hypothesis V_arg : sk_arg t = Z_to_bv 64 arg.
  Hypothesis V_rng : 0 <= dtvp /\ 0 <= off < 2 ^ 64 /\ 0 <= dtv1 < 2 ^ 64.
  Hypothesis V_res : (off + dtv1) mod 2 ^ 64 = ia_tp IA.
  Hypothesis BT_TP : bt_tp bt = ia_tp IA.
  Hypothesis BT_TLSFS : bt_tls_fs bt = ia_tp IA.
  Hypothesis IMG_LOW : ia_img_lo IA <= FAKE_SIZE.
  Hypothesis K_consts : Forall (fun c => In c (bt_consts bt)) (stk_consts t (ia_tp IA) (bt_tctx bt) arg off dtvp dtv1 keysp).

  #[local] Abbreviation VV := (stk_vals bt arg off dtvp dtv1 keysp).

  Theorem C_stkmal_P : STKMAL SG FXOK IA AAINVH (bt_fs bt) k.
  Proof using K_consts IMG_LOW BT_TLSFS BT_TP V_res V_rng V_arg keysp dtv1 dtvp off arg T_entry TOK t Hk HP0_hint HOFF SEGS_hull SEGS_wx.
    intros h fx R M mdl Lc FF B C K ret sp (Hk' & HALT & HFX & AI & CP & CNT).
    pose proof AI as (st & W & RP & (Bd & HPst) & MW).
    destruct CP as (CP1 & CPr & CPe & CP2 & CPa & CPc & CPh & CP4 & CPstk). unfold MSTK_F in CPc, CPstk.
    pose proof ceil_rng as CR.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & _).
    destruct (fs_place bt st Lc FF W) as (P1 & P2 & P3 & P4 & P5 & INFS).
    pose proof (P4 : hide _) as P4h. pose proof (P5 : hide _) as P5h. clear P4 P5.
    destruct (dtls_facts bt st Lc FF W) as (D1 & D2 & D3).
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    destruct R10 as (KH & KG & KF & KW & KWR & KT & KS & KD1 & KD2).
    destruct R14 as (B1 & B2 & B3 & _).
    pose proof (read_tls bt st Lc FF M mdl RP) as (T48 & T56 & _ & _).
    pose proof (read_thread bt st Lc FF M mdl RP) as (_ & _ & _ & _ & _ & _ & TC152 & _).
    pose proof W as (_ & _ & _ & _ & _ & (WK1 & WK2 & WK3) & _).
    set (fs := bt_fs bt) in *. set (hint := a_hint st k). set (AA := a_aa st). set (Hd := HL mdl AA).
    set (S := getr R 2). set (tg := sk_tg t). set (mt := sk_mt t).
    assert (HS : U S = sp) by exact CP2.
    pose proof (u64_range S) as HSr.
    unfold FAKE_SIZE, PG, AS_LO, AS_HEAPLO in *.
    (* [comment removed for export] *)
    pose proof K_consts as KC. unfold stk_consts in KC. fold tg mt in KC.
    repeat match type of KC with Forall _ (_ :: _) => apply Forall_cons_iff in KC; destruct KC as [?KR KC] end. clear KC.
    repeat match goal with KR : In (_, ?n, _) (bt_consts bt) |- _ =>
      let X := fresh "CR" in pose proof (const_row bt st Lc FF M mdl W RP _ _ _ KR ltac:(lia)) as X; clear KR end.
    assert (TPR : ia_img_lo IA + 88 <= ia_tp IA /\ ia_tp IA + 16 <= ia_img_hi IA).
    { assert (K2 : img_kind bt (bt_tls_fs bt + 15)) by (apply (img_kinds bt st Lc FF W); right; right; right; left; lia).
      destruct K2 as [K2 _]. rewrite BT_TLSFS in K2. match goal with H : cellN _ _ (ia_tp IA - 88) _ _ /\ _ |- _ => destruct H as (_ & ? & _) end. lia. }
    (* [comment removed for export] *)
    assert (ROW : forall a n v bs, cellN SG M a n v -> bs = word_to_le_bytes n (Z_to_bv 64 v) -> 0 <= a -> a + Z.of_nat n <= CEIL ->
              hid_off Hd a (Z.of_nat n) ->
              (0 <= a /\ a + Z.of_nat n <= CEIL /\ rdn SG M (Z_to_bv 64 a) n = Some bs) /\ hid_off Hd a (Z.of_nat n)).
    { intros a n v bs CE -> H0 H1 HH. split; [|exact HH]. split; [exact H0|]. split; [exact H1 | exact CE]. }
    assert (ROWI : forall a n v bs, cellN SG M a n v /\ ia_img_lo IA <= a /\ a + Z.of_nat n <= ia_img_hi IA -> bs = word_to_le_bytes n (Z_to_bv 64 v) ->
              (0 <= a /\ a + Z.of_nat n <= CEIL /\ rdn SG M (Z_to_bv 64 a) n = Some bs) /\ hid_off Hd a (Z.of_nat n)).
    { intros a n v bs (CE & L1 & L2) E. apply (ROW a n v bs CE E); [lia | lia |]. apply (hid_img bt st Lc FF M mdl W RP AA); lia. }
    assert (TGR : Forall (fun c => (0 <= fst (fst c) /\ fst (fst c) + Z.of_nat (snd (fst c)) <= CEIL
                                    /\ rdn SG M (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (snd c))
                                   /\ hid_off Hd (fst (fst c)) (Z.of_nat (snd (fst c)))) (tg_reads tg VV)).
    { (lazymatch goal with |- ?G => let G' := eval unfold tg_reads in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [stk_vals tv_arg tv_tp tv_off tv_dtvp tv_dtv1 tv_keysp tv_T tv_A tv_tlsb tv_tlse tv_g12 tv_dbeg] in G in change_no_check G' end).
      repeat match goal with H : cellN _ _ _ _ _ /\ _ /\ _ |- _ => let c := fresh "CE" in let l := fresh "L" in let u := fresh "L" in
                 pose proof H as (c & l & u); revert H end. intros.
      rewrite !(u_Z2bv arg), !(u_Z2bv (ia_tp IA)), !(u_Z2bv dtvp), !(u_Z2bv keysp), !(u_Z2bv (bt_tctx bt)), !(u_Z2bv (bt_thread bt)), !(u_Z2bv (bt_dtls bt)) by lia.
      repeat apply Forall_cons; try apply Forall_nil; (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
      all: try (match goal with H : cellN _ _ ?a _ _ /\ _ /\ _ |- (_ <= ?a /\ _) /\ _ => apply (ROWI _ _ _ _ H) end;
                first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity]).
      - apply (ROW _ _ _ _ TC152 eq_refl); [lia | lia |]. apply (hid_tctx bt st Lc FF M mdl W RP AA); lia.
      - apply (ROW _ _ _ _ T48 eq_refl); [lia | lia |]. apply (hid_thread bt st Lc FF M mdl W RP AA); (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia.
      - apply (ROW _ _ _ _ T56 eq_refl); [lia | lia |]. apply (hid_thread bt st Lc FF M mdl W RP AA); (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia.
      - rewrite <- BT_TLSFS. apply (ROW _ _ _ _ KD1 eq_refl); [lia | lia |]. apply (hid_img bt st Lc FF M mdl W RP AA); lia.
      - apply (ROW _ _ _ _ KD2 eq_refl); [lia | lia |]. apply (hid_dtls bt st Lc FF M mdl W RP AA); (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia. }
    (* [comment removed for export] *)
    assert (MTX : (forall p : word, (0x10007fff8000 <= U p \/ U p <= 0x7fff7fff) -> U p <= 0x7fffffffffff -> m2sH SG mt M p (Z_to_bv 64 0))
                  /\ Forall (fun c => 0 <= c /\ c + 8 <= ia_img_hi IA) (m2s_cells mt)
                  /\ Forall (fun c => hid_off Hd c 8) (m2s_cells mt)).
    { repeat match goal with H : cellN _ _ _ _ _ /\ _ /\ _ |- _ => let c := fresh "CE" in let l := fresh "L" in let u := fresh "L" in
               destruct H as (c & l & u) end.
      split; [|split].
      - intros p Hlo Hhi. constructor; try assumption. (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; apply (hid_img bt st Lc FF M mdl W RP AA); lia. }
    destruct MTX as (MTH & MTC & MTHID).
    repeat match goal with H : cellN _ _ _ _ _ /\ _ /\ _ |- _ => clear H end.
    (* [comment removed for export] *)
    set (busy := fun p => existsb (fun fk : Z * Z => Z.eqb (fst fk) (fake_frame_addr fs k p) && Z.eqb (snd fk) k) FF).
    assert (NKp : 0 < FCAP k) by ((lazymatch goal with |- ?G => let G' := eval unfold FCAP in G in change_no_check G' end); apply Z.pow_pos_nonneg; lia).
    destruct (free_probe_of_count k (FCAP k) hint busy (fake_frame_addr fs k) FF NKp (WK3 k)) as (i0 & Hi0 & FREE & BUSY).
    { intros p q _ _ E. exact (ffa_inj_pos fs k p q ltac:(lia) E). }
    { intros p Hp Bp. unfold busy in Bp. apply existsb_exists in Bp. destruct Bp as ([f' k'] & Hin & E). cbn [fst snd] in E.
      apply andb_prop in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1, E2. subst f' k'. exact Hin. }
    { rewrite <- fcount_kcount. exact CNT. }
    set (pos := (hint + i0) mod FCAP k).
    assert (Hpos : 0 <= pos < FCAP k) by (apply Z.mod_pos_bound; exact NKp).
    set (f := fake_frame_addr fs k pos).
    assert (NI : ~ In (f, k) FF).
    { intros Hin. assert (Bt : busy pos = true).
      { (lazymatch goal with |- ?G => let G' := eval unfold busy in G in change_no_check G' end). apply existsb_exists. exists (f, k). split; [exact Hin|]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite !Z.eqb_refl. reflexivity. }
      unfold pos in Bt. rewrite FREE in Bt. discriminate Bt. }
    pose proof (frame_geom k pos fs ltac:((lazymatch goal with |- ?G => let G' := eval unfold KMAXCLASS in G in change_no_check G' end); lia) Hpos ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); exact P3)) as G. cbn zeta in G. fold f in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6). unfold FAKE_SIZE in G2.
    destruct (frame_al8 fs k pos Hk P3) as (A8 & F8 & _). fold f in A8.
    (* [comment removed for export] *)
    assert (Epos : forall j, skf_pos k hint j = (hint + j) mod FCAP k) by reflexivity.
    assert (Efl : forall j, skf_flag k fs hint j = fake_flag_addr fs k ((hint + j) mod FCAP k)) by (intros j; rewrite skf_flag_vocab; reflexivity).
    assert (Efr : skf_frame k fs hint i0 = f) by (rewrite skf_frame_vocab; reflexivity).
    assert (Esh : skf_sh k fs hint i0 = sh_lo f) by ((lazymatch goal with |- ?G => let G' := eval unfold skf_sh in G in change_no_check G' end); rewrite Efr; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end); lia).
    assert (EFS : FSK k = FS k) by reflexivity.
    assert (FLR : forall j, fs + 4096 <= skf_flag k fs hint j < fs + 36864).
    { intros j. rewrite Efl. apply flag_addr_range; [lia | apply Z.mod_pos_bound; exact NKp]. }
    assert (BUSYrd : forall j, 0 <= j < i0 -> rdn SG M (Z_to_bv 64 (skf_flag k fs hint j)) 1 = Some [Z_to_bv 8 1]).
    { intros j Hj. rewrite Efl.
      pose proof (KF k ((hint + j) mod FCAP k) ltac:(lia) ltac:(apply Z.mod_pos_bound; exact NKp)) as BY.
      fold fs in BY. change (existsb _ FF) with (busy ((hint + j) mod FCAP k)) in BY. rewrite (BUSY j Hj) in BY. exact BY. }
    assert (FREErd : rdn SG M (Z_to_bv 64 (skf_flag k fs hint i0)) 1 = Some [Z_to_bv 8 0]).
    { rewrite Efl. pose proof (KF k pos ltac:(lia) Hpos) as BY.
      fold fs in BY. change (existsb _ FF) with (busy pos) in BY. unfold pos in BY at 2. rewrite FREE in BY. exact BY. }
    clear BUSY FREE. clearbody busy. clear busy.
    set (fsw := Z_to_bv 64 fs).
    assert (Ufs : U fsw = fs) by ((lazymatch goal with |- ?G => let G' := eval unfold fsw in G in change_no_check G' end); apply u_Z2bv; lia).
    assert (RES : U (tg_res VV) = ia_tp IA).
    { (lazymatch goal with |- ?G => let G' := eval unfold tg_res, v_add in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [stk_vals tv_off tv_dtv1] in G in change_no_check G' end). rewrite (u_Z2bv off), (u_Z2bv dtv1) by lia. rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end).
      change (bv_modulus 64) with (2 ^ 64). exact V_res. }
    assert (WRfs : forall lo n, fs <= lo -> lo + Z.of_nat n <= fs + 11571200 -> store_ok SG M (Z_to_bv 64 lo) n = true).
    { intros lo n H0 H1. apply store_ok_pointwise; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. rewrite u_Z2bv by lia. intros x Hx.
      destruct (KWR (U x) ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end); fold fs; lia)) as [_ OK]. rewrite Z_to_bv_bv_unsigned in OK. exact OK. }
    assert (SHM : forall z, sh_lo f <= z < sh_hi f (FS k) -> shmaps z).
    { intros z Hz. unfold hide in P5h. apply (sh_in_maps f (FS k) z); (lazymatch goal with |- ?G => let G' := eval unfold AS_LO, AS_HEAPLO in G in change_no_check G' end); lia. }
    assert (SHE : sh_hi f (FS k) = sh_lo f + FS k / 8 /\ 2147450880 <= sh_lo f /\ sh_lo f + FS k / 8 <= 17594333495296
                  /\ sh_lo fs <= sh_lo f /\ sh_lo f + FS k / 8 <= sh_hi fs FAKE_SIZE).
    { (lazymatch goal with |- ?G => let G' := eval unfold sh_hi, sh_lo, SB, FAKE_SIZE in G in change_no_check G' end). clear -G1 G2 G4 A8 F8 P1 P2 CR. Z.div_mod_to_equations. lia. }
    destruct SHE as (SH1 & SH2 & SH3 & SH4 & SH5).
    assert (NSH0 : 0 <= FS k / 8) by (clear -G4; Z.div_mod_to_equations; lia).
    assert (US32 : U (at_ S (-32)) = sp - 32) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (STKOK : forall lo n, sp - 256 <= lo -> lo + Z.of_nat n <= sp -> store_ok SG M (Z_to_bv 64 lo) n = true).
    { intros lo n H0 H1. apply store_ok_pointwise; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. rewrite u_Z2bv by lia. intros x Hx. apply CPstk. lia. }
    (* [comment removed for export] *)
    assert (PRE : stkKH SG t k M S fsw (Z_to_bv 64 0) VV hint i0).
    { constructor.
      - (* [comment removed for export] *)
        split; [|split; [|split; [|split; [|split; [|split]]]]].
        + eapply Forall_impl; [|exact TGR]. intros [[c n] bs] ((Q1 & Q2 & Q3) & _). cbn [fst snd] in *. rewrite US32.
          split; [exact Q1|]. split; [lia | exact Q3].
        + (lazymatch goal with |- ?G => let G' := eval cbn [stk_vals tv_T] in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
        + (lazymatch goal with |- ?G => let G' := eval cbn [stk_vals tv_A] in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
        + (lazymatch goal with |- ?G => let G' := eval cbn [stk_vals tv_g12] in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
        + (lazymatch goal with |- ?G => let G' := eval cbn [stk_vals tv_dbeg] in G in change_no_check G' end). rewrite BT_TP. rewrite u_Z2bv by lia. lia.
        + rewrite US32. lia.
        + replace (at_ (at_ S (-32)) (-176)) with (Z_to_bv 64 (sp - 208)) by (apply bv_eq; rewrite at_u by (rewrite US32; lia); rewrite US32, u_Z2bv by lia; lia).
          apply STKOK; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
      - symmetry. exact V_arg.
      - rewrite RES, <- BT_TLSFS. exact KT.
      - rewrite RES. split; lia.
      - rewrite Ufs. exact KG.
      - rewrite Ufs. exact KS.
      - rewrite Ufs. exact (KH k ltac:(lia)).
      - intros j Hj. rewrite Ufs. exists (Z_to_bv 8 1). split; [exact (BUSYrd j Hj) | vm_compute; discriminate].
      - rewrite Ufs. exact FREErd.
      - rewrite Ufs. apply WRfs; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
      - rewrite Ufs. pose proof (FLR i0). apply WRfs; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
      - rewrite Ufs, Efr. apply WRfs; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
      - rewrite Ufs, Efr, EFS. apply WRfs; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
      - rewrite Ufs, Esh, EFS. apply store_ok_defined; [rewrite u_Z2bv by lia; rewrite (Z2Nat.id _ NSH0); lia|].
        rewrite u_Z2bv by lia. rewrite (Z2Nat.id _ NSH0). intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (proj1 R19). apply SHM. lia.
      - (* [comment removed for export] *)
        rewrite Ufs, Efr. fold mt. unfold hide in P5h. apply MTH; first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ].
      - rewrite Ufs. fold mt. eapply Forall_impl; [|exact MTC]. intros c Hc. cbv beta in Hc. unfold FAKE_SIZE in IMG_LOW. unfold hide in P4h. lia.
      - rewrite Ufs. lia.
      - exact (WK3 k).
      - exact Hi0.
      - lia.
      - replace (at_ S (-32)) with (Z_to_bv 64 (sp - 32)) by (apply bv_eq; rewrite US32, u_Z2bv by lia; lia).
        apply STKOK; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    (* [comment removed for export] *)
    assert (HIDFS : hid_off Hd fs 11571200) by (apply (hid_fs bt st Lc FF M mdl W RP AA); (lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end); fold fs; lia).
    assert (HIDSH : hid_off Hd (sh_lo f) (FS k / 8)) by (apply (hid_fs_shadow bt mdl AA _ _ B3); fold fs; lia).
    assert (HIDSCR : hid_off Hd (sp - 208) 208) by (apply (hid_stack bt st Lc FF M mdl RP AA); lia).
    assert (PREr : stkKH SG t k (mrestrict Hd M) S fsw (Z_to_bv 64 0) VV hint i0).
    { apply (stkKH_mrestrict SG t k Hd M S fsw (Z_to_bv 64 0) VV hint i0 Hk PRE).
      - eapply Forall_impl; [|exact TGR]. intros c (_ & HH). exact HH.
      - rewrite RES. apply (hid_img bt st Lc FF M mdl W RP AA); lia.
      - rewrite Ufs. intros x Hx. apply HIDFS. lia.
      - rewrite Ufs, Esh, EFS. exact HIDSH.
      - exact MTHID.
      - rewrite HS. exact HIDSCR. }
    assert (RETOK : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u_Z2bv by lia; exact CPe).
    destruct (@stk_run_k fx SG k t Hk (TOK fx) (mrestrict Hd M) (seg_rom SG) (Z_to_bv 64 ret) S fsw (Z_to_bv 64 0) VV hint i0 R
                PREr RETOK CP1 eq_refl CP4) as (r & Mj & RUN & SR & A10 & A1 & A2 & AG).
    rewrite HS in SR. rewrite Ufs in RUN. rewrite Ufs, Efr in A10.
    destruct (scr_rel_unrestrict Hd M Mj (sp - 208) sp SR ltac:(replace (sp - (sp - 208)) with 208 by lia; exact HIDSCR)) as (EMj & SRu & HIDEQ).
    set (Mj' := munrestrict Hd M Mj) in *.
    (* [comment removed for export] *)
    set (hc := fs + 8 * k). set (fl := skf_flag k fs hint i0). set (last := f + (FS k - 8)).
    pose proof (FLR i0) as FLi. fold fl in FLi.
    remember (Z.to_nat (FS k / 8)) as nsh eqn:Ensh.
    assert (NSHZ : Z.of_nat nsh = FS k / 8) by (rewrite Ensh; apply Z2Nat.id; exact NSH0).
    assert (Ensh' : hide (nsh = Z.to_nat (FS k / 8))) by exact Ensh. clear Ensh.
    assert (HB : (0 <= hc /\ 0 <= fl /\ 0 <= f /\ 0 <= last /\ 0 <= sh_lo f)
                 /\ hc + 8 < 2 ^ 64 /\ fl + 1 < 2 ^ 64 /\ f + 32 < 2 ^ 64 /\ last + 8 < 2 ^ 64 /\ sh_lo f + Z.of_nat nsh < 2 ^ 64).
    { rewrite NSHZ. (lazymatch goal with |- ?G => let G' := eval unfold hc, last in G in change_no_check G' end). lia. }
    assert (HDJ : hide (hc + 8 <= fl /\ fl + 1 <= f + 24 /\ f + 32 <= last /\ (sh_lo f + Z.of_nat nsh <= hc \/ last + 8 <= sh_lo f))).
    { unfold hide in P5h |- *. rewrite NSHZ. (lazymatch goal with |- ?G => let G' := eval unfold hc, last in G in change_no_check G' end). split; [lia|]. split; [lia|]. split; [lia|].
      destruct P5h as [P5|P5]; [right | left]; lia. }
    assert (EMEM : stkK_mem k Mj fs hint i0 S = mrestrict Hd (stkK_mem k Mj' fs hint i0 S)).
    { (lazymatch goal with |- ?G => let G' := eval unfold stkK_mem in G in change_no_check G' end). rewrite Efr, Esh, EFS. fold hc fl last. unfold hide in Ensh'. rewrite <- Ensh'. rewrite EMj at 1.
      apply stk_mem_mrestrict; [exact (proj1 HB) | exact (proj2 HB) | | | | |].
      - intros x Hx. apply HIDFS. unfold hc in Hx. lia.
      - intros x Hx. apply HIDFS. lia.
      - intros x Hx. apply HIDFS. lia.
      - intros x Hx. apply HIDFS. unfold last in Hx. lia.
      - rewrite NSHZ. exact HIDSH. }
    set (M' := stkK_mem k Mj' fs hint i0 S) in *.
    assert (M'def : M' = stk_mem Mj' hc fl f last (sh_lo f) nsh (hint + i0 + 1) S).
    { (lazymatch goal with |- ?G => let G' := eval unfold M', stkK_mem in G in change_no_check G' end). rewrite Efr, Esh, EFS. unfold hide in Ensh'. rewrite <- Ensh'. reflexivity. }
    assert (OUT : forall a : word, ~ (sp - 208 <= U a < sp) -> ~ (hc <= U a < hc + 8) -> U a <> fl -> ~ (f + 24 <= U a < f + 32) ->
                  ~ (last <= U a < last + 8) -> ~ (sh_lo f <= U a < sh_lo f + FS k / 8) -> M' a = M a).
    { intros a N0 N1 N2 N3 N4 N5. rewrite M'def.
      rewrite (stk_mem_out Mj' hc fl f last (sh_lo f) nsh (hint + i0 + 1) S HB HDJ a N1 N2 N3 N4 ltac:(rewrite NSHZ; exact N5)).
      apply (proj1 SRu). lia. }
    assert (NH' : forall a : word, Hd a = true -> M' a = M a).
    { intros a Ha. apply OUT.
      - intros Hx. rewrite (HIDSCR a) in Ha; [discriminate Ha | lia].
      - intros Hx. rewrite (HIDFS a) in Ha; [discriminate Ha | unfold hc in Hx; lia].
      - intros Hx. rewrite (HIDFS a) in Ha; [discriminate Ha | lia].
      - intros Hx. rewrite (HIDFS a) in Ha; [discriminate Ha | lia].
      - intros Hx. rewrite (HIDFS a) in Ha; [discriminate Ha | unfold last in Hx; lia].
      - intros Hx. rewrite (HIDSH a Hx) in Ha. discriminate Ha. }
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.cfg in G in change_no_check G' end). rewrite <- T_entry.
    apply (katD_msteps_acct SG Hd (HOFF h Lc FF B C K M mdl AA AI) SEGS_wx AA (mkst R (sk_base t) M (seg_rom SG))
             (mkst r (Z_to_bv 64 ret) (mrestrict Hd M') (seg_rom SG)) mdl _ (lazy_cover_HL mdl AA) B1 B2 HALT).
    { rewrite restrict_mkst'. rewrite <- EMEM. exact RUN. }
    intros mdl' MI' SBM HC. rewrite unrestrict_mkst. (lazymatch goal with |- ?G => let G' := eval cbn [RiscvSemantics.ms_mem mkst] in G in change_no_check G' end).
    rewrite (munrestrict_mrestrict_same Hd M M' NH').
    apply katD_refl.
    (* [comment removed for export] *)
    assert (GRm : mem_grows M M').
    { rewrite M'def. eapply mem_grows_trans; [exact (proj1 (proj2 SRu)) | apply stk_mem_grows]. }
    assert (CHG : forall a : word, M' a <> M a ->
              (sp - 208 <= U a < sp \/ hc <= U a < hc + 8 \/ U a = fl \/ f + 24 <= U a < f + 32 \/ last <= U a < last + 8
               \/ sh_lo f <= U a < sh_lo f + FS k / 8) /\ M' a <> None).
    { intros a NE. split.
      - assert (Dc0 : (sp - 208 <= U a < sp) \/ ~ (sp - 208 <= U a < sp)) by (clear; lia). destruct Dc0 as [Dc0|Dc0]; [left; exact Dc0 | right].
        assert (Dc1 : (hc <= U a < hc + 8) \/ ~ (hc <= U a < hc + 8)) by (clear; lia). destruct Dc1 as [Dc1|Dc1]; [left; exact Dc1 | right].
        assert (Dc2 : U a = fl \/ U a <> fl) by (clear; lia). destruct Dc2 as [Dc2|Dc2]; [left; exact Dc2 | right].
        assert (Dc3 : (f + 24 <= U a < f + 32) \/ ~ (f + 24 <= U a < f + 32)) by (clear; lia). destruct Dc3 as [Dc3|Dc3]; [left; exact Dc3 | right].
        assert (Dc4 : (last <= U a < last + 8) \/ ~ (last <= U a < last + 8)) by (clear; lia). destruct Dc4 as [Dc4|Dc4]; [left; exact Dc4 | right].
        assert (Dc5 : (sh_lo f <= U a < sh_lo f + FS k / 8) \/ ~ (sh_lo f <= U a < sh_lo f + FS k / 8)) by (clear; lia).
        destruct Dc5 as [Dc5|Dc5]; [exact Dc5|]. exfalso. apply NE. exact (OUT a Dc0 Dc1 Dc2 Dc3 Dc4 Dc5).
      - destruct (decide (M' a = Mj' a)) as [E|NE'].
        + rewrite E. apply (proj2 (proj2 SRu)). rewrite <- E. exact NE.
        + rewrite M'def in NE' |- *. exact (stk_mem_def Mj' hc fl f last (sh_lo f) nsh (hint + i0 + 1) S HB HDJ a NE'). }
    (* [comment removed for export] *)
    set (nh := (hint + i0 + 1) mod 2 ^ 64).
    assert (Hnh : 0 <= nh < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    assert (Hk3 : 0 <= k <= KMAXCLASS) by ((lazymatch goal with |- ?G => let G' := eval unfold KMAXCLASS in G in change_no_check G' end); lia).
    assert (Efl0 : fl = fake_flag_addr fs k pos) by ((lazymatch goal with |- ?G => let G' := eval unfold fl in G in change_no_check G' end); rewrite Efl; reflexivity).
    pose proof (WF_fake_alloc bt st Lc FF k pos nh W Hk3 Hpos (proj1 Hnh) NI) as W2. fold fs f in W2.
    assert (RP2 : Rep bt (op_fake_alloc st k nh) Lc ((f, k) :: FF) M' mdl').
    { apply (OPS_REP_fake_alloc_pf bt st Lc FF M M' mdl mdl' k pos nh W RP Hk3 Hpos Hnh NI).
      - intros a NE. destruct (CHG a NE) as [CC DEF]. split; [|exact DEF]. (lazymatch goal with |- ?G => let G' := eval unfold foot_fake_alloc in G in change_no_check G' end). fold fs f.
        destruct CC as [CC | [CC | [CC | [CC | [CC | CC]]]]].
        + right; right; right; right. lia.
        + left. unfold hc in CC. lia.
        + right; left. lia.
        + right; right; left. lia.
        + right; right; left. unfold last in CC. lia.
        + right; right; right; left. rewrite SH1. lia.
      - fold fs hc. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite M'def.
        rewrite (stk_mem_hint SG Mj' hc fl f last (sh_lo f) nsh (hint + i0 + 1) S HB HDJ). f_equal. f_equal.
        apply bv_eq. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap, nh in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity.
      - fold fs. rewrite <- Efl0. (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite M'def.
        exact (stk_mem_flag SG Mj' hc fl f last (sh_lo f) nsh (hint + i0 + 1) S HB HDJ).
      - intros k' pos' Hk2 Hpos' NEQ. fold fs.
        pose proof (flag_addr_range fs k' pos' Hk2 Hpos') as FR'.
        assert (UE : U (Z_to_bv 64 (fake_flag_addr fs k' pos')) = fake_flag_addr fs k' pos') by (apply u_Z2bv; lia).
        destruct (decide (M' (Z_to_bv 64 (fake_flag_addr fs k' pos')) = M (Z_to_bv 64 (fake_flag_addr fs k' pos')))) as [E|NE]; [exact E|].
        exfalso. destruct (CHG _ NE) as [CC _]. rewrite UE in CC. clear UE.
        destruct CC as [CC | [CC | [CC | [CC | [CC | CC]]]]]; try (unfold hc, last in *; lia); [| unfold hide in P5h; lia].
        rewrite Efl0 in CC. destruct (flag_addr_inj fs k' pos' k pos Hk2 Hpos' ltac:(lia) Hpos CC) as [-> ->]. apply NEQ. reflexivity.
      - fold fs f. rewrite <- Efl0. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). replace (f + FS k - 8) with last by ((lazymatch goal with |- ?G => let G' := eval unfold last in G in change_no_check G' end); lia). rewrite M'def.
        exact (stk_mem_last SG Mj' hc fl f last (sh_lo f) nsh (hint + i0 + 1) S HB HDJ).
      - fold fs f. intros i Hi. rewrite SH1 in Hi. replace i with (sh_lo f + (i - sh_lo f)) by lia. rewrite M'def.
        rewrite (stk_mem_sh Mj' hc fl f last (sh_lo f) nsh (hint + i0 + 1) S HB HDJ) by (rewrite NSHZ; lia). discriminate.
      - exact SBM.
      - exact MI'. }
    assert (AI2 : AAINVP (HP0 h) bt Lc ((f, k) :: FF) B C K M' mdl').
    { exists (op_fake_alloc st k nh). split; [exact W2|]. split; [exact RP2|]. split; [split; [exact Bd | apply HP0_hint; exact HPst]|].
      exact (model_ivs_wf_sbm mdl mdl' SBM MW). }
    pose proof (AAINV_props_all bt (HP0 h)) as PR.
    destruct (aap_fzone _ _ _ _ PR Lc ((f, k) :: FF) B C K M' mdl' f k AI2 (or_introl eq_refl)) as (_ & Z2 & Z3 & Z4 & Z5).
    assert (Uf : U (Z_to_bv 64 f) = f) by (apply u_Z2bv; lia).
    assert (SEGnone : forall a : word, CEIL <= U a -> find_segment SG (U a) 1 = None).
    { intros a Ha. destruct (find_segment SG (U a) 1) eqn:E; [|reflexivity]. exfalso.
      pose proof (SEGS_hull (U a) ltac:(rewrite E; discriminate)). lia. }
    (lazymatch goal with |- ?G => let G' := eval unfold stkmal_post in G in change_no_check G' end). exists fx, r, M', mdl', (Z_to_bv 64 f), fl. rewrite Uf.
    split; [reflexivity|]. split; [exact HFX|].
    split. { apply regs_kept_of_list. intros x Hx. unfold saved_regs in Hx. cbn [In] in Hx.
             destruct Hx as [<- | Hx]; [exact A2|].
             apply AG. intros Hc. unfold m2s_clob in Hc. cbn [In] in Hc.
             repeat (destruct Hx as [<- | Hx]; [decompose [or] Hc; first [discriminate | contradiction]|]). exact Hx. }
    split; [exact A10|].
    split; [exact Z3|]. split; [exact Z2|]. split; [exact Z4|]. split; [exact Z5|].
    split. { intros b m Hin. destruct (aap_bfdisj _ _ _ _ PR Lc ((f, k) :: FF) B C K M' mdl' b m f k AI2 Hin (or_introl eq_refl)); [right | left]; assumption. }
    split. { intros f' k' Hin. exact (aap_fdisj _ _ _ _ PR Lc ((f, k) :: FF) B C K M' mdl' [] FF f k f' k' AI2 eq_refl Hin). }
    split. { intros a Ha. destruct (KWR (U a) ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end); fold fs; lia)) as [DEF OK]. rewrite Z_to_bv_bv_unsigned in DEF, OK.
             split; [apply GRm; exact DEF | eapply store_ok_mono; [exact GRm | exact OK]]. }
    split. { replace (f + FS k - 8) with last by ((lazymatch goal with |- ?G => let G' := eval unfold last in G in change_no_check G' end); lia). rewrite M'def.
             apply stk_mem_last_m64; [(lazymatch goal with |- ?G => let G' := eval unfold last in G in change_no_check G' end); lia | rewrite NSHZ; (lazymatch goal with |- ?G => let G' := eval unfold last in G in change_no_check G' end); lia | | lia].
             unfold hide in HDJ. rewrite NSHZ in HDJ |- *. unfold hc, last in *. unfold hide in P5h. lia. }
    split. { intros i Hi. rewrite M'def. apply (stk_mem_sh Mj' hc fl f last (sh_lo f) nsh (hint + i0 + 1) S HB HDJ). rewrite NSHZ. exact Hi. }
    split. { intros a Ha. eapply store_ok_mono; [exact GRm|]. (lazymatch goal with |- ?G => let G' := eval cbn [store_ok] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end).
             pose proof (proj1 R19 (U a) (SHM (U a) Ha)) as DEF. rewrite Z_to_bv_bv_unsigned in DEF. destruct (M a); [reflexivity | exfalso; apply DEF; reflexivity]. }
    split. { intros a NE. destruct (CHG a NE) as [CC _]. (lazymatch goal with |- ?G => let G' := eval unfold as_changed, MSTK_F in G in change_no_check G' end).
             destruct CC as [CC | CC]; [left; lia | right; left].
             apply (fresh_priv bt st Lc FF W k pos (U a) Hk3 Hpos NI). fold fs f.
             destruct CC as [CC | [CC | [CC | [CC | CC]]]].
             - left. unfold hc in CC. lia.
             - left. lia.
             - right; left. lia.
             - right; left. unfold last in CC. lia.
             - right; right. rewrite SH1. exact CC. }
    split. { intros a _ DEF. apply GRm. exact DEF. }
    split. { intros a Ha. unfold MSTK_F in Ha. pose proof (CPstk a Ha) as OK. split.
             - apply GRm. apply (store_ok1_defined SG M a); [apply SEGnone; lia | exact OK].
             - eapply store_ok_mono; [exact GRm | exact OK]. }
    split; [exact AI2 | exact SBM].
  Qed.
End SL.
