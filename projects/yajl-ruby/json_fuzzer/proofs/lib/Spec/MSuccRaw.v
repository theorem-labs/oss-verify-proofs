(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes NodesMat NodesCfg Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl RawAlloc KArith KInv KLink KStep KLive KArena
  MI_Tree MI_Inv MI_Kit MI_Contracts MI_WMalloc MI_Sim
  LB_Kernel LB_Embed LB_Tables LB_Inv LB_Sum LB_Bound LB_Tree LB_StmtA LB_WFree LB_Raw LB_WMalloc LB_Alloc
  KLiveCfg MSuccIface MSucc MLen MSuccTall MSuccEmbed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section RC__.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition P16 (c : Z) : Z := 16.
(* [comment removed for export] *)
Definition ABLKc : Z := NUSERc + 3 * PGSZ.
(* [comment removed for export] *)
Definition LMAXc : Z := PHI P16 + NHELDc * ABLKc.
(* [comment removed for export] *)
Definition RCMAXc : Z := 1024.
(* [comment removed for export] *)
Definition VMINc : Z := LMAXc + ABLKc.

Lemma PHI16_val : PHI P16 = 229943296.
Proof. vm_compute. reflexivity. Qed.
Lemma NCAP16_val : NCAP P16 = 9553.
Proof. vm_compute. reflexivity. Qed.
Lemma ABLKc_val : ABLKc = 134230016.
Proof. reflexivity. Qed.
Lemma LMAXc_val : LMAXc = 1974933504.
Proof. unfold LMAXc. rewrite PHI16_val. reflexivity. Qed.
Lemma VMINc_val : VMINc = 2109163520.
Proof. unfold VMINc. rewrite LMAXc_val. reflexivity. Qed.

(* [comment removed for export] *)
Lemma window_numerics : ABLKc * (LMAXc / PGSZ + RCMAXc + 1) <= alloc_ceiling - PGSZ.
Proof.
  rewrite LMAXc_val, ABLKc_val. unfold RCMAXc, PGSZ. pose proof alloc_ceiling_ge.
  change (1974933504 / 4096) with 482161. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition HEADc (X : list (bptr * Z)) (s : PState) (mo : Model) : Prop :=
  (QI X P16 s mo /\ Z.of_nat (length X) <= NHELDc /\ Forall (fun xb => 0 <= snd xb <= NUSERc) X)
  /\ VMINc <= vm_limit (m_vmmaps mo)
  /\ rcost (vm_reserved (m_vmmaps mo)) <= RCMAXc.

Lemma HEADc_QI X s mo : HEADc X s mo -> QI X P16 s mo.
Proof. intros [[H _] _]. exact H. Qed.

Lemma HEADc_KL X s mo : HEADc X s mo -> minv mo /\ m_halted mo = None.
Proof.
  intros [[[(st & L & BL & LS & _ & _ & _ & _ & HK & _) _] _] _].
  split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)].
Qed.

Lemma HEADc_perm X Y s mo : Permutation X Y -> HEADc X s mo -> HEADc Y s mo.
Proof.
  intros HP [(HQ & HL & HF) [HV HR]]. split; [| split; assumption]. split; [eapply QI_perm; eauto|].
  split; [rewrite <- (Permutation_length HP); exact HL|]. eapply Permutation_Forall; eauto.
Qed.

Lemma HEADc_other X s s' mo : HEADc X s mo -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> HEADc X s' mo.
Proof.
  intros [(HQ & HL & HF) [HV HR]] Em Eb. split; [| split; assumption]. split; [| split; assumption].
  destruct HQ as [(st & L & BL & LS & E & INV & SI & HAQ & HK & HLI & HP & HLV) HB]. split; [| exact HB].
  exists st, L, BL, LS. rewrite Em, Eb. repeat (split; [assumption|]). exact HLV.
Qed.

(* [comment removed for export] *)
Lemma HEADc_after_node X s s' mo n rsp mo' evs :
  HEADc X s mo -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s ->
  lazy_free_node n -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo ->
  HEADc X s' mo'.
Proof.
  intros [(HQ & HL & HF) [HV HR]] Em Eb Hl Hst Hvm.
  split; [| rewrite Hvm; split; assumption]. split; [| split; assumption].
  apply (QI_other X P16 s s' mo'); [| exact Em| exact Eb].
  eapply QI_after_node; eauto.
Qed.

Lemma HEADc_with_tid X s mo (t : word) :
  (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z -> HEADc X s mo -> HEADc X s (with_tid t mo).
Proof.
  intros Ht [(HQ & HL & HF) [HV HR]].
  assert (Ev : m_vmmaps (with_tid t mo) = m_vmmaps mo) by (destruct mo; reflexivity).
  split; [| rewrite Ev; split; assumption]. split; [apply QI_with_tid; assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zcount_le_len {A} (f : A -> bool) (l : list A) : zcount f l <= Z.of_nat (length l).
Proof. unfold zcount, zlen. pose proof (List.filter_length_le f l). lia. Qed.

Lemma bigb_le n : 0 <= n <= NUSERc -> 0 <= bigb n <= ABLKc.
Proof.
  intros Hn. unfold bigb. destruct (MMAP_THRESHOLD <=? n); [| unfold ABLKc, PGSZ; rewrite NUSERc_val; lia].
  pose proof (round_up_pg_le (n + IB + UNIT)) as [H0 H1].
  unfold ABLKc, IB, UNIT, PGSZ in *. rewrite NUSERc_val in *. lia.
Qed.

Lemma R63X_le X : Forall (fun xb => 0 <= snd xb <= NUSERc) X -> 0 <= R63X X <= Z.of_nat (length X) * ABLKc.
Proof.
  induction 1 as [|[p n] X Hx HX IH]; [unfold R63X, zsum; cbn; lia|].
  rewrite R63X_cons. cbn [length snd] in *. pose proof (bigb_le n Hx). rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma ROOMX_P16 X n : Z.of_nat (length X) + 1 <= NHELDc -> ROOMX X P16 n.
Proof.
  intros HL. rewrite NHELDc_val in HL. split; [| split]; [intros _ | intros _ |]; unfold P16.
  - unfold LRX. pose proof (zcount_le_len (fun xb : bptr * Z => negb (MMAP_THRESHOLD <=? snd xb) && (size_to_class (snd xb) =? size_to_class n)) X). lia.
  - unfold n63X. pose proof (zcount_le_len (fun xb : bptr * Z => MMAP_THRESHOLD <=? snd xb) X). lia.
  - unfold zlen. lia.
Qed.

(* [comment removed for export] *)
Lemma mspec_vmc {A} (P : assn PState) (m : Monad.M PState A) (Q : A -> assn PState) v :
  mspec P m Q -> mspec (fun s mo => P s mo /\ vmc mo = v) m (fun a s mo => Q a s mo /\ vmc mo = v).
Proof.
  intros H s mo [HP Hv]. unfold etwf.
  assert (W : forall {R} (t : itree node R) mo (P0 : R -> Model -> Prop), twf t mo P0 -> vmc mo = v -> twf t mo (fun r mo' => P0 r mo' /\ vmc mo' = v)).
  { intros R t. induction t as [r|n k IH]; intros mo0 P0 HT Hv0; cbn in *; [auto|].
    destruct HT as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH; [exact (Hk _ _ _ Hst)|].
    rewrite (vmc_nstep _ _ _ _ _ Hst). exact Hv0. }
  eapply twf_mono; [apply (W _ (m s) mo _ (H s mo HP) Hv)|]. intros [|[a s1]] mo1; cbn; tauto.
Qed.

Theorem HEADc_malloc X n s mo : 0 <= n <= NUSERc -> HEADc X s mo -> Z.of_nat (length X) + 1 <= NHELDc ->
  mspec (fun s' mo' => s' = s /\ mo' = mo) (raw_malloc n)
        (fun r s' mo' => match r with Some p => HEADc ((p, n) :: X) s' mo' | None => HEADc X s' mo' end).
Proof.
  intros Hn [(HQ & HL0 & HF) [HV HR]] HL.
  pose proof (R63X_le X HF) as RX. pose proof (bigb_le n Hn) as BN.
  assert (PRE : QI X P16 s mo /\ ROOMX X P16 n /\ PHI P16 + R63X X + bigb n <= LBUDGET).
  { split; [exact HQ|]. split; [apply ROOMX_P16; lia|].
    unfold LBUDGET. rewrite PHI16_val. rewrite NHELDc_val in HL. unfold ABLKc, PGSZ in *. rewrite NUSERc_val in *. nia. }
  eapply mspec_conseq; [apply (mspec_vmc _ _ _ (vmc mo) (raw_malloc_LQ X P16 n ltac:(lia)))| |].
  - intros s' mo' [-> ->]. split; [exact PRE| reflexivity].
  - intros r s' mo' [HQ' Ev]. unfold vmc in Ev. injection Ev as E1 E2.
    destruct r as [p|]; (split; [| rewrite E1, E2; split; [exact HV| exact HR]]).
    + destruct HQ' as [HQ' _]. split; [exact HQ'|]. split; [cbn [length]; rewrite Nat2Z.inj_succ; lia|].
      constructor; [cbn; lia| exact HF].
    + split; [exact HQ'|]. split; [exact HL0| exact HF].
Qed.

Theorem HEADc_free X (p : bptr) n s mo : HEADc ((p, n) :: X) s mo ->
  mspec (fun s' mo' => s' = s /\ mo' = mo) (raw_free p) (fun _ s' mo' => HEADc X s' mo').
Proof.
  intros [(HQ & HL & HF) [HV HR]].
  eapply mspec_conseq; [apply (mspec_vmc _ _ _ (vmc mo) (raw_free_LQ X P16 p n))| |].
  - intros s' mo' [-> ->]. split; [exact HQ| reflexivity].
  - intros [] s' mo' [HQ2 Ev]. unfold vmc in Ev. injection Ev as E1 E2. split; [| rewrite E1, E2; split; [exact HV| exact HR]].
    split; [exact HQ2|]. split.
    + cbn [length] in HL. rewrite Nat2Z.inj_succ in HL. lia.
    + inversion HF; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shift_bound st L BL LS : INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P16 ->
  0 <= c_meta_alloc_shift (s_ctx st) /\ Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)) * PGSZ <= ABLKc.
Proof.
  intros INV SI HAQ. pose proof (proj1 (ir_shift _ _ _ (proj1 INV))) as S0.
  set (sh := c_meta_alloc_shift (s_ctx st)) in *.
  split; [exact S0|]. rewrite Z.shiftl_mul_pow2 by exact S0.
  pose proof (aq_carved _ _ _ HAQ) as C. rewrite NCAP16_val in C.
  assert (P14 : 2 ^ sh <= 2 ^ 14).
  { destruct (Z.le_gt_cases 1 sh) as [S1|S1].
    - pose proof (qm_shift _ _ _ SI S1) as Q. fold sh in Q.
      assert (2 ^ sh <= 200) by lia. etransitivity; [exact H|]. cbn; lia.
    - assert (sh = 0) by lia. rewrite H. cbn. lia. }
  change (2 ^ 14) with 16384 in P14. unfold ABLKc, PGSZ. rewrite NUSERc_val. lia.
Qed.

Theorem raw_malloc_ctall X n s mo :
  HEADc X s mo -> Z.of_nat (length X) + 1 <= NHELDc -> 0 <= n <= NUSERc ->
  ctall (raw_malloc n s) mo (fun p _ => exists q, fst p = Some q).
Proof.
  intros [(HQ & HL0 & HF) [HV HR]] HL Hn.
  destruct HQ as [(st & L & BL & LS & E & INV & SI & HAQ & HK & HLI & HP & HLV) HB].
  pose proof (R63X_eq _ _ HP) as R63E. pose proof (R63X_le X HF) as RX. pose proof (bigb_le n Hn) as BN.
  assert (HRM : ROOM BL P16 n) by (apply (ROOMX_eq X BL P16 n HP); apply ROOMX_P16; lia).
  assert (HBB : PHI P16 + R63 BL + bigb n <= LMAXc + 3 * PGSZ).
  { unfold LMAXc. rewrite <- R63E. rewrite NHELDc_val in *. unfold ABLKc, PGSZ in *. rewrite NUSERc_val in *. nia. }
  (* [comment removed for export] *)
  assert (QT : qtree LMAXc L (cmalloc (ps_m s) n) (fun _ _ => True)).
  { rewrite <- E.
    eapply (qtree_of_full8 pans0 pupd0 pans0_range (RR := MREL)).
    - exact (malloc_INVL st L BL LS n INV ltac:(lia)).
    - exact (malloc_fbnd8 malloc_core_fq_proof st L BL LS P16 n LMAXc INV SI HAQ ltac:(lia) HRM HBB).
    - exact (malloc_control pans0 pupd0 pans0_range st n tt).
    - intros; exact I. }
  (* [comment removed for export] *)
  destruct (shift_bound st L BL LS INV SI HAQ) as [S0 SH].
  assert (LK : lok ABLKc TrueP (cmalloc (ps_m s) n)).
  { apply (cmalloc_lok ABLKc NUSERc (c_meta_alloc_shift (s_ctx st))).
    - exact S0.
    - unfold GLEN, ABLKc, PGSZ. rewrite NUSERc_val. lia.
    - exact SH.
    - unfold ABLKc, IB, UNIT, PGSZ. lia.
    - rewrite <- E. unfold shf. rewrite ctx_strip. unfold ctx. lia.
    - exact Hn. }
  assert (SK : sok SOMEP (cmalloc (ps_m s) n)).
  { apply cmalloc_sok. unfold size_overflows. apply Z.leb_gt. rewrite NUSERc_val in Hn. lia. }
  (* [comment removed for export] *)
  assert (GB : gm L + BB L <= LMAXc).
  { pose proof (regions_bound x0 st L BL LS P16 INV SI HAQ eq_refl) as RB. pose proof (ledger_bound x0 st L BL LS INV) as LBd.
    unfold ORPH in RB. cbn [x_orph x0] in RB. unfold PGSZ in *. lia. }
  (* [comment removed for export] *)
  unfold raw_malloc, mbind, mget. apply ctall_ebind. unfold ctall at 1. cbn [tall fst snd].
  apply ctall_ebind.
  eapply ctall_mono.
  { apply (membed_cfg LMAXc ABLKc RCMAXc VMINc) with (v := vmc mo) (Post := fun _ _ => True) (G := fun _ _ => True) (L := L).
    - rewrite LMAXc_val. lia.
    - rewrite ABLKc_val. split; [lia| reflexivity].
    - exact window_numerics.
    - unfold VMINc. lia.
    - unfold vmc. cbn [fst snd]. split; [exact HR| exact HV].
    - intros s1 s2 mo1 mo2 _ _ _ _. exact I.
    - exact QT.
    - exact LK.
    - exact SK.
    - exact HK.
    - exact HLI.
    - exact I.
    - exact GB.
    - reflexivity. }
  intros [[st' r] s1] mo' Hs. cbn [fst snd] in Hs |- *.
  unfold mupd, mret, ctall. cbn. destruct r as [c|]; [eexists; reflexivity| destruct Hs].
Qed.

(* [comment removed for export] *)
Theorem malloc_succ X n s mo :
  HEADc X s mo -> Z.of_nat (length X) + 1 <= NHELDc -> 0 <= n <= NUSERc ->
  ctall (raw_malloc n s) mo (fun p mo' => exists q, fst p = Some q /\ HEADc ((q, n) :: X) (snd p) mo').
Proof.
  intros H HL Hn.
  pose proof (HEADc_malloc X n s mo Hn H HL s mo (conj eq_refl eq_refl)) as M. apply ctall_of_etwf in M.
  pose proof (raw_malloc_ctall X n s mo H HL Hn) as C.
  eapply ctall_mono; [exact (ctall_conj _ _ _ _ C M)|].
  intros [r s'] mo' [[q Hq] HM]. cbn [fst snd] in *. subst r. exists q. split; [reflexivity| exact HM].
Qed.

Theorem free_ctall X (p : bptr) n s mo :
  HEADc ((p, n) :: X) s mo ->
  ctall (raw_free p s) mo (fun u mo' => HEADc X (snd u) mo').
Proof.
  intros H. pose proof (HEADc_free X p n s mo H s mo (conj eq_refl eq_refl)) as M. apply ctall_of_etwf in M.
  eapply ctall_mono; [exact M|]. intros [[] s'] mo' HM. exact HM.
Qed.

(* [comment removed for export] *)
Lemma QI_bptr_irrel (p1 p2 : bptr) n X P s mo : fst p1 = fst p2 -> QI ((p1, n) :: X) P s mo -> QI ((p2, n) :: X) P s mo.
Proof.
  intros E [(st & L & BL & LS & Es & INV & SI & HAQ & HK & HLI & HP & HLV) HB]. split.
  - exists st, L, BL, LS. repeat (split; [assumption|]). split; [| exact HLV].
    revert HP. cbn [map xs fst snd]. unfold xs at 1 3. cbn [fst snd]. rewrite E. exact (fun H => H).
  - rewrite R63X_cons in *. exact HB.
Qed.

Lemma HEADc_bptr_irrel (p1 p2 : bptr) n X s mo : fst p1 = fst p2 -> HEADc ((p1, n) :: X) s mo -> HEADc ((p2, n) :: X) s mo.
Proof.
  intros E [(HQ & HL & HF) [HV HR]]. split; [| split; assumption]. split; [eapply QI_bptr_irrel; eauto|].
  split; [exact HL|]. inversion HF; subst. constructor; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma P16_nonneg : forall c, 0 <= P16 c.
Proof. intros c. unfold P16. lia. Qed.

Lemma PHI_P16_budget : PHI P16 <= LBUDGET.
Proof. rewrite PHI16_val. unfold LBUDGET. lia. Qed.

(* [comment removed for export] *)
Theorem HEADc_init_lim : forall segs brk0 mbase sp lim inp (t : word),
  bv_unsigned sp = rc_sp -> sp_window_lo <= rc_sp <= sp_window_hi ->
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  VMINc <= lim ->
  rcost (segments_reserved segs) <= RCMAXc ->
  (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z ->
  HEADc [] (ps_init (reservedZ segs)) (with_tid t (init_model (segments_reserved segs) brk0 mbase sp lim inp)).
Proof.
  intros segs brk0 mbase sp lim inp t Hsp Hspw Hv Hpos Hceil Hlim Hrc Ht.
  split; [| split].
  - split; [| split; [rewrite NHELDc_val; cbn; lia| constructor]].
    apply QI_with_tid; [exact Ht|]. apply QI_init; auto using P16_nonneg, PHI_P16_budget.
  - replace (m_vmmaps (with_tid t (init_model (segments_reserved segs) brk0 mbase sp lim inp))) with
      (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)) by (symmetry; apply m_vmmaps_with_tid).
    rewrite m_vmmaps_init_model. cbn [vm_limit]. exact Hlim.
  - replace (m_vmmaps (with_tid t (init_model (segments_reserved segs) brk0 mbase sp lim inp))) with
      (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)) by (symmetry; apply m_vmmaps_with_tid).
    rewrite m_vmmaps_init_model. cbn [vm_reserved]. exact Hrc.
Qed.

(* [comment removed for export] *)
Lemma VMINc_le_2G : VMINc <= 2147483648.   (* [comment removed for export] *)
Proof. rewrite VMINc_val. lia. Qed.
Lemma VMINc_le_source : VMINc <= source_alloc_limit.
Proof. rewrite VMINc_val. unfold source_alloc_limit. lia. Qed.
Lemma VMINc_le_target : VMINc <= target_alloc_limit.
Proof. rewrite VMINc_val. unfold target_alloc_limit. lia. Qed.

(* [comment removed for export] *)
Theorem HEADc_init : forall segs brk0 mbase sp lim inp (t : word),
  bv_unsigned sp = rc_sp -> sp_window_lo <= rc_sp <= sp_window_hi ->
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  (lim = source_alloc_limit \/ lim = target_alloc_limit) ->
  rcost (segments_reserved segs) <= RCMAXc ->
  (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z ->
  HEADc [] (ps_init (reservedZ segs)) (with_tid t (init_model (segments_reserved segs) brk0 mbase sp lim inp)).
Proof.
  intros segs brk0 mbase sp lim inp t Hsp Hspw Hv Hpos Hceil Hlim Hrc Ht.
  apply HEADc_init_lim; try assumption.
  destruct Hlim as [-> | ->]; [apply VMINc_le_source | apply VMINc_le_target].
Qed.

End RC__.
