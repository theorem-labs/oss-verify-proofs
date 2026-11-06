(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages LazyModel NodesA Shadow BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanFakeStack AsanPS AsanKern AsanClient AsanDepot
  AsanBudget AsanBudget2 AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_base A_alloc_iface A_live A_policy5 A_budget5 A_slack5 AI_shadow AI_lowshadow AYajlRep AF_fakestack_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sh (a : Z) : Z := A_SB + a / 8.

Definition S0_ivs5 (E : aenv) (F : Z) : list (Z * Z) :=
  [ (0x7fff7000, 0x8fff7000)
  ; (pgdn (sh (ae_space_beg E)), pgup (sh (ae_space_beg E + 2^37)))
  ; (pgdn (sh alloc_ceiling), kHighMemBeg)
  ; (pgdn (sh F), pgup (sh (F + kFsBytes)))
  ; (ae_store_blk E, ae_store_blk E + 2^23)
  ; (ae_space_beg E + 2^37, ae_space_beg E + 2^37 + 4096) ].

Lemma kHighMemBeg_val : kHighMemBeg = 0x10007fff8000.
Proof. reflexivity. Qed.
Lemma A_SB_val : A_SB = 0x7fff8000.
Proof. reflexivity. Qed.
Lemma kFsBytes_val : kFsBytes = 11571200.
Proof. reflexivity. Qed.

Lemma pgdn_pgup_le : forall a b, a <= b -> pgdn a <= pgup b.
Proof. intros a b H. unfold pgup, pgdn. Z.div_mod_to_equations; lia. Qed.
Lemma sh_mono : forall a b, a <= b -> sh a <= sh b.
Proof. intros a b H. unfold sh. Z.div_mod_to_equations; nia. Qed.

Lemma S0_ivs5_ok : forall E F, Forall (fun iv => fst iv <= snd iv) (S0_ivs5 E F).
Proof.
  intros E F. unfold S0_ivs5. pose proof alloc_ceiling_range as CR.
  repeat constructor; cbn [fst snd]; try lia.
  - apply pgdn_pgup_le, sh_mono. lia.
  - rewrite kHighMemBeg_val. eapply Z.le_trans; [apply pgdn_le|]. unfold sh. rewrite A_SB_val. clear -CR. Z.div_mod_to_equations; lia.
  - apply pgdn_pgup_le, sh_mono. rewrite kFsBytes_val. lia.
Qed.

(* [comment removed for export] *)
Lemma A0_pages_cons : forall iv l, A0_pages (iv :: l) = (snd iv - fst iv) / 4096 + 2 + A0_pages l.
Proof. reflexivity. Qed.
Lemma A0_pages_app : forall l1 l2, A0_pages (l1 ++ l2) = A0_pages l1 + A0_pages l2.
Proof. induction l1 as [|iv l1 IH]; intros l2; [reflexivity|]. cbn [app]. rewrite !A0_pages_cons, IH. lia. Qed.

Lemma S0_pages5_bound : forall E F, A0_pages (S0_ivs5 E F) <= 4330000.
Proof.
  intros E F. unfold S0_ivs5. rewrite !A0_pages_cons. change (A0_pages []) with 0. cbn [fst snd].
  pose proof alloc_ceiling_range as CR. rewrite kHighMemBeg_val, kFsBytes_val.
  unfold pgup, pgdn, sh. rewrite A_SB_val. clear -CR. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition ay_cells (m : mem) : Prop :=
     rw_cells asegs m AY_CALLBACKS (callbacks_cells ayc)
  /\ rw_cells asegs m AY_BUF_ALLOC_ERROR (buf_alloc_error_cells ayc)
  /\ rw_cells asegs m AY_NOOP_ALLOCS anoop_allocs_cells.

(* [comment removed for export] *)
Definition sstats_ok (a : astate) : Prop :=
  ss_cur (as_sec_stats a) = sec_bytes a /\ 0 <= ss_max (as_sec_stats a) < 2^62.

Lemma sstats_ok_init : forall E, sstats_ok (astate0 E).
Proof. intros E. unfold sstats_ok, sec_bytes. cbn. lia. Qed.

(* [comment removed for export] *)
Definition csmall (a : astate) : Prop := forall cb cm, as_chunks a !! cb = Some cm -> cm_n cm <= 2^27.

Lemma csmall_init : forall E, csmall (astate0 E).
Proof. intros E cb cm H. cbn in H. rewrite lookup_empty in H. discriminate. Qed.

(* [comment removed for export] *)
Section Bundle.
(* [comment removed for export] *)
Variable StdioRep : stdout_st -> mem -> Prop.   (* [comment removed for export] *)
Variable RTMisc : aenv -> mem -> Prop.         (* [comment removed for export] *)
(* [comment removed for export] *)
Variable E0 : aenv.
Variable FSB0 : Z.                               (* [comment removed for export] *)
(* [comment removed for export] *)
Variable HR0 : list (Z * Z).
(* [comment removed for export] *)
Variables L0 RES0 : list (word * word).
(* [comment removed for export] *)
Variable EB0 : Z.

(* [comment removed for export] *)
Definition A0 : list (Z * Z) := S0_ivs5 E0 FSB0 ++ HR0.
Definition aS (s : aps) : word -> Prop := A_policy5.aS A0 s.
Definition aN (s : aps) : nat := A_policy5.aN A0 s.
Definition aNz (s : aps) : Z := A_policy5.aNz A0 s.
Definition aEB (s : aps) : Z := A_policy5.aEB EB0 s.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KMISC (mo : Model) : Prop :=
  m_halted mo = None /\ minvA mo /\ vm_limit (m_vmmaps mo) = 2^39.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENVOK (s : aps) : Prop :=
  let E := aps_env s in
     app_mem (ae_store_blk E) (2^23) /\ ae_store_blk E + 2^23 <= alloc_ceiling
  /\ app_mem (aps_fsbase s) kFsBytes /\ aps_fsbase s + kFsBytes <= alloc_ceiling
  /\ kHighMemBeg <= ae_resv_beg E
  /\ (aps_fsbase s + kFsBytes <= ae_store_blk E \/ ae_store_blk E + 2^23 <= aps_fsbase s)
  /\ In (aps_fsbase s, kFsBytes) (ae_reserved E)
  /\ ae_fs_beg E = aps_fsbase s /\ ae_fs_len E = kFsBytes
  /\ aps_env s = E0 /\ aps_fsbase s = FSB0
  /\ (fst (ae_img E) = 0x10000 /\ 0x5f3000 <= snd (ae_img E)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition blocks_match (LB : list ablock) (a : astate) : Prop :=
  Permutation (map (fun b => (ab_addr b, ab_size b)) LB) (live_blocks a).

(* [comment removed for export] *)
Definition AHK (s : aps) (LB : list ablock) (LF : list fblock) (m : mem) (mo : Model) : Prop :=
  let E := aps_env s in let a := aps_alloc s in
     ARep asegs E (AsanDepot.DepotR asegs E) a m  (* [comment removed for export] *) /\ AWf E [] [] a (* [comment removed for export] *) /\ AKern E a mo (* [comment removed for export] *) /\ KVM L0 RES0 mo a (* [comment removed for export] *)
  /\ res_ok a (* [comment removed for export] *) /\ AQbound a (* [comment removed for export] *) /\ depot_inv E a (* [comment removed for export] *) /\ binv a (* [comment removed for export] *)
  /\ blocks_match LB a (* [comment removed for export] *)
  /\ FSRep asegs E (aps_fsbase s) (aps_fs s) LF m (* [comment removed for export] *)
  /\ icp_globals asegs m A_SB (* [comment removed for export] *) /\ ay_statics m (* [comment removed for export] *) /\ low_shadow_ok m (* [comment removed for export] *) /\ RTMisc E m (* [comment removed for export] *)
  /\ StdioRep (aps_so s) m (* [comment removed for export] *)
  /\ KMISC mo (* [comment removed for export] *)
  /\ LI (aS s) (aN s) (aEB s) mo (* [comment removed for export] *) /\ BUDGET s LB (* [comment removed for export] *)
  /\ mem_inv asegs m (* [comment removed for export] *) /\ ENVOK s (* [comment removed for export] *)
  /\ ay_cells m (* [comment removed for export] *)
  /\ sstats_ok a (* [comment removed for export] *)
  /\ csmall a (* [comment removed for export] *).

Ltac ahk_open H :=
  destruct H as (Hrep & Hwf & Hkern & Hkvm & Hres & Hqb & Hdi & Hbinv & Hbm & Hfs & Hicp & Hyst & Hlow & Hrt & Hso & Hkm & Hli & Hbud & Hmi & Henv & Hycl & Hss & Hcs).
Ltac ahk_split := unfold AHK; cbn zeta; repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AHK_mem_inv : forall s LB LF m mo, AHK s LB LF m mo -> mem_inv asegs m.
Proof. intros s LB LF m mo H. ahk_open H. exact Hmi. Qed.

Lemma AHK_ay_statics : forall s LB LF m mo, AHK s LB LF m mo -> ay_statics m.
Proof. intros s LB LF m mo H. ahk_open H. exact Hyst. Qed.

Lemma AHK_icp_globals : forall s LB LF m mo, AHK s LB LF m mo -> icp_globals asegs m A_SB.
Proof. intros s LB LF m mo H. ahk_open H. exact Hicp. Qed.

Lemma AHK_low_shadow : forall s LB LF m mo, AHK s LB LF m mo -> low_shadow_ok m.
Proof. intros s LB LF m mo H. ahk_open H. exact Hlow. Qed.

Lemma AHK_ay_cells : forall s LB LF m mo, AHK s LB LF m mo -> ay_cells m.
Proof. intros s LB LF m mo H. ahk_open H. exact Hycl. Qed.

Lemma AHK_sstats : forall s LB LF m mo, AHK s LB LF m mo -> sstats_ok (aps_alloc s).
Proof. intros s LB LF m mo H. ahk_open H. exact Hss. Qed.

Lemma AHK_csmall : forall s LB LF m mo, AHK s LB LF m mo -> csmall (aps_alloc s).
Proof. intros s LB LF m mo H. ahk_open H. exact Hcs. Qed.

Lemma AHK_halted : forall s LB LF m mo, AHK s LB LF m mo -> m_halted mo = None.
Proof. intros s LB LF m mo H. ahk_open H. exact (proj1 Hkm). Qed.

Lemma AHK_minvA : forall s LB LF m mo, AHK s LB LF m mo -> minvA mo.
Proof. intros s LB LF m mo H. ahk_open H. exact (proj1 (proj2 Hkm)). Qed.

Lemma AHK_limit : forall s LB LF m mo, AHK s LB LF m mo -> vm_limit (m_vmmaps mo) = 2^39.
Proof. intros s LB LF m mo H. ahk_open H. exact (proj2 (proj2 Hkm)). Qed.

Lemma AHK_LI : forall s LB LF m mo, AHK s LB LF m mo -> LI (aS s) (aN s) (aEB s) mo.
Proof. intros s LB LF m mo H. ahk_open H. exact Hli. Qed.

Lemma AHK_kia : forall s LB LF m mo, AHK s LB LF m mo -> KIA (aS s) (aN s) (aEB s) mo.
Proof. intros s LB LF m mo H. ahk_open H. destruct Hkm as (Kh & Kmi & _). split; [exact Hli| split; [exact Kmi| exact Kh]]. Qed.

Lemma AHK_KVM : forall s LB LF m mo, AHK s LB LF m mo -> KVM L0 RES0 mo (aps_alloc s).
Proof. intros s LB LF m mo H. ahk_open H. exact Hkvm. Qed.

Lemma AHK_env : forall s LB LF m mo, AHK s LB LF m mo -> aps_env s = E0 /\ aps_fsbase s = FSB0.
Proof. intros s LB LF m mo H. ahk_open H. destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & _). auto. Qed.

Lemma AHK_img : forall s LB LF m mo, AHK s LB LF m mo -> fst (ae_img (aps_env s)) = 0x10000 /\ 0x5f3000 <= snd (ae_img (aps_env s)).
Proof. intros s LB LF m mo H. ahk_open H. destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EI). exact EI. Qed.

Lemma AHK_budget : forall s LB LF m mo, AHK s LB LF m mo -> BUDGET s LB.
Proof. intros s LB LF m mo H. ahk_open H. exact Hbud. Qed.

Lemma AHK_blocks_match : forall s LB LF m mo, AHK s LB LF m mo -> blocks_match LB (aps_alloc s).
Proof. intros s LB LF m mo H. ahk_open H. exact Hbm. Qed.

(* [comment removed for export] *)
Lemma AHK_budget_caps : forall s LB LF m mo, AHK s LB LF m mo ->
  DEP LB <= kInitialCredit /\ as_ndepot_ins (aps_alloc s) <= kInitialCredit
  /\ as_nprim_ever (aps_alloc s) <= kInitialCredit /\ zlen (as_residue (aps_alloc s)) <= kInitialCredit.
Proof. intros s LB LF m mo H. ahk_open H. exact (BUDGET_caps s LB Hbud). Qed.

(* [comment removed for export] *)
Lemma AHK_perm : forall s LB LB' LF LF' m mo,
  AHK s LB LF m mo -> Permutation LB LB' -> Permutation LF LF' -> AHK s LB' LF' m mo.
Proof.
  intros s LB LB' LF LF' m mo H HPB HPF. ahk_open H. ahk_split.
  - unfold blocks_match in *. eapply Permutation_trans; [| exact Hbm]. apply Permutation_map. apply Permutation_sym. exact HPB.
  - eapply FSRep_perm; [exact Hfs | exact HPF].
  - eapply BUDGET_perm; [exact HPB| exact Hbud].
Qed.

(* [comment removed for export] *)
Lemma AKern_frame : forall E a mo mo',
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> AKern E a mo -> AKern E a mo'.
Proof.
  intros E a mo mo' HV HL K. destruct K. constructor; unfold eager_rw, inside, clear_of, clear_ofp in *; rewrite ?HV, ?HL; auto.
Qed.

Lemma KVM_frame : forall mo mo' a, m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> KVM L0 RES0 mo a -> KVM L0 RES0 mo' a.
Proof. intros mo mo' a HV HL K. unfold KVM, model_ivs_wf in *. rewrite HV, HL. exact K. Qed.

Lemma LI_frame : forall S N EB mo mo',
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_vm_materialized mo' = m_vm_materialized mo ->
  LI S N EB mo -> LI S N EB mo'.
Proof.
  intros S N EB mo mo' HV HL HM [L1 L2 L3 L4 L5].
  assert (EU : eager_used mo' = eager_used mo) by (unfold eager_used; rewrite HV, HL; reflexivity).
  constructor; rewrite ?HM, ?EU, ?HV; assumption.
Qed.

Lemma AHK_magree : forall s LB LF m mo mo',
  AHK s LB LF m mo -> magree mo mo' -> LI (aS s) (aN s) (aEB s) mo' -> AHK s LB LF m mo'.
Proof.
  intros s LB LF m mo mo' H Hag HLI. pose proof (magree_frame _ _ Hag) as (Ffds & Fvm & Flz & Ffs & Fh & Ftid & _).
  ahk_open H. destruct Hkm as (Kh & Kmi & Klim). unfold AHK, KMISC; cbn zeta; repeat match goal with |- _ /\ _ => split end; try assumption.
  all: first [ eapply AKern_frame; [exact Fvm | exact Flz | exact Hkern]
             | eapply KVM_frame; [exact Fvm | exact Flz | exact Hkvm]
             | rewrite Fh; exact Kh
             | rewrite Fvm; exact Klim
             | eapply minvA_by_fields; [exact Ffds | exact Ffs | exact Ftid | rewrite Fvm; reflexivity | exact Kmi] ].
Qed.

(* [comment removed for export] *)
Lemma AHK_vmsame : forall s LB LF m mo mo',
  AHK s LB LF m mo -> vm_same mo mo' -> minvA mo' -> m_halted mo' = None -> AHK s LB LF m mo'.
Proof.
  intros s LB LF m mo mo' H VS MI HH. ahk_open H. unfold vm_same in VS. destruct Hkm as (Kh & Kmi & Klim).
  assert (E1 : m_vm_materialized mo' = m_vm_materialized mo) by (unfold m_vm_materialized; rewrite VS; reflexivity).
  assert (E2 : m_vm_lazy mo' = m_vm_lazy mo) by (unfold m_vm_lazy; rewrite VS; reflexivity).
  assert (E3 : m_vmmaps mo' = m_vmmaps mo) by (unfold m_vmmaps; rewrite VS; reflexivity).
  unfold AHK, KMISC; cbn zeta; repeat match goal with |- _ /\ _ => split end; try assumption.
  - eapply AKern_frame; [exact E3| exact E2| exact Hkern].
  - eapply KVM_frame; [exact E3| exact E2| exact Hkvm].
  - rewrite E3. exact Klim.
  - eapply LI_frame; [exact E3| exact E2| exact E1| exact Hli].
Qed.

(* [comment removed for export] *)
Lemma AHK_vmsame_fs : forall s LB LF m mo mo',
  AHK s LB LF m mo -> vm_same mo mo' -> minvA mo' -> m_halted mo' = None -> m_fs mo' = m_fs mo -> AHK s LB LF m mo'.
Proof. intros s LB LF m mo mo' H VS MI HH _. exact (AHK_vmsame s LB LF m mo mo' H VS MI HH). Qed.

(* [comment removed for export] *)
Lemma live_blocks_chunk : forall a A n,
  In (A, n) (live_blocks a) ->
  exists cb cm i, as_chunks a !! cb = Some cm /\ cm_user_beg cm = A /\ cm_n cm = n /\ cm_state cm = CAllocated i.
Proof.
  intros a A n H. unfold live_blocks in H. apply in_map_iff in H. destruct H as ([cb cm] & E & Hf).
  apply filter_In in Hf. destruct Hf as [Hin Hst]. cbn in E, Hst. injection E as <- <-.
  destruct (cm_state cm) as [i|i j] eqn:Hs; [|discriminate].
  exists cb, cm, i. split; [|auto].
  apply (elem_of_map_to_list (as_chunks a) cb cm). apply base.list_elem_of_In. exact Hin.
Qed.

Lemma blocks_match_In : forall LB a b, blocks_match LB a -> In b LB -> In (ab_addr b, ab_size b) (live_blocks a).
Proof.
  intros LB a b BM Hb. eapply Permutation_in; [exact BM|]. apply in_map_iff. exists b. auto.
Qed.

(* [comment removed for export] *)
Lemma AHK_live_small : forall s LB LF m mo A n, AHK s LB LF m mo -> In (A, n) (live_blocks (aps_alloc s)) -> n <= 2^27.
Proof.
  intros s LB LF m mo A n H Hin. ahk_open H. destruct (live_blocks_chunk _ _ _ Hin) as (cb & cm & i & Hcm & _ & <- & _). exact (Hcs cb cm Hcm).
Qed.

(* [comment removed for export] *)
Lemma live_small_is_primary : forall E P D a cb cm,
  AWf E P D a -> as_chunks a !! cb = Some cm -> cm_n cm <= 64512 -> exists c, cm_prim cm = Some c.
Proof.
  intros E P D a cb cm WF Hcm Hn. destruct WF as (_ & _ & _ & [K1 _] & _). destruct (K1 _ _ Hcm) as (_ & B & _ & D0 & _).
  destruct (cm_prim cm) as [c|]; [exists c; reflexivity|]. exfalso. destruct D0 as [NP _].
  pose proof (proj2 (from_primary_iff (cm_n cm) ltac:(lia)) Hn). congruence.
Qed.

(* [comment removed for export] *)
Definition ayR (s : aps) (mo : Model) (s' : aps) (mo' : Model) : Prop :=
  aps_env s' = aps_env s /\ aps_fsbase s' = aps_fsbase s.
Lemma ayR_refl : forall s mo, ayR s mo s mo. Proof. intros; split; reflexivity. Qed.
Lemma ayR_trans : forall s1 mo1 s2 mo2 s3 mo3, ayR s1 mo1 s2 mo2 -> ayR s2 mo2 s3 mo3 -> ayR s1 mo1 s3 mo3.
Proof. intros s1 mo1 s2 mo2 s3 mo3 [A B] [C D]. split; congruence. Qed.
Lemma AHK_ayR : forall s LB LF m mo s' LB' LF' m' mo',
  AHK s LB LF m mo -> AHK s' LB' LF' m' mo' -> ayR s mo s' mo'.
Proof.
  intros s LB LF m mo s' LB' LF' m' mo' H H'. destruct (AHK_env _ _ _ _ _ H) as [EE EFS]. destruct (AHK_env _ _ _ _ _ H') as [EE' EFS'].
  split; congruence.
Qed.
(* [comment removed for export] *)
Lemma ayfuzz_rel_intro : forall s mo s' mo', ayR s mo s' mo' -> aps_credit s - Ymax <= aps_credit s' -> ayfuzz_rel s mo s' mo'.
Proof. intros s mo s' mo' [A B] C. unfold ayfuzz_rel, Ymax in *. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
(* [comment removed for export] *)
Hypothesis HS_tot : gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat.

Lemma A0_ok : Forall (fun iv => fst iv <= snd iv) A0.
Proof. unfold A0. apply Forall_app. split; [apply S0_ivs5_ok| exact (proj1 HR0_ok)]. Qed.

Lemma A0_pages_bound : A0_pages A0 <= 4330000 + 8192.
Proof. unfold A0. rewrite A0_pages_app. pose proof (S0_pages5_bound E0 FSB0). pose proof (proj2 HR0_ok). clear -H H0. lia. Qed.

(* [comment removed for export] *)
Lemma BUDGET_STATIC_ok : BUDGET_STATIC A0 EB0 <= 2^39.
Proof.
  unfold BUDGET_STATIC. pose proof A0_pages_bound. pose proof EB0_ok. unfold kInitialCredit. clear -H H0. lia.
Qed.

(* [comment removed for export] *)
Lemma AHK_aS_card : forall s LB LF m mo l, AHK s LB LF m mo -> List.NoDup l -> Forall (aS s) l -> (length l <= aN s)%nat.
Proof. intros s LB LF m mo l _ ND F. exact (aS_card A0 (aps_alloc s) l ND F). Qed.

Lemma AHK_aN_bound : forall s, Z.of_nat (aN s) <= aNz s.
Proof. intros s. unfold aN, aNz, A_policy5.aN, A_policy5.aNz. apply (aN_bound A0 A0_ok). Qed.

Theorem AHK_budget_headroom : forall s LB LF m mo, AHK s LB LF m mo ->
  aEB s + 4096 * aNz s + 4096 * aps_credit s <= BUDGET_STATIC A0 EB0.
Proof.
  intros s LB LF m mo H. ahk_open H. destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & _).
  rewrite EE in Hwf, Hdi. pose proof ENV_depot as [K0 [_ F0]].
  exact (budget_headroom A0 EB0 E0 s LB A0_ok (proj1 EB0_ok) Hwf Hqb Hdi Hbinv Hbm Hbud K0 F0).
Qed.

(* [comment removed for export] *)
Theorem AHK_osl : forall s LB LF m mo R, AHK s LB LF m mo -> 0 <= R <= aps_credit s -> OSL aEB aNz R s mo.
Proof.
  intros s LB LF m mo R H HR. pose proof (AHK_budget_headroom s LB LF m mo H) as BH. ahk_open H.
  destruct Hkm as (_ & _ & Klim). unfold OSL. rewrite Klim. pose proof BUDGET_STATIC_ok. clear -BH HR H. lia.
Qed.

(* [comment removed for export] *)
Lemma PSL_side_numerics : forall SZ CNT, SZ <= 2^46 -> 0 <= CNT <= 256 ->
  4096 + NMAXA + (SZ + CNT * (NMAXA + 4095)) + FOGW + ADYN + OPSLACK <= alloc_ceiling.
Proof. intros SZ CNT HS HC. pose proof alloc_ceiling_range. unfold FOGW, ADYN, OPSLACK in *. unfold NMAXA in *. clear -H HS HC. nia. Qed.

(* [comment removed for export] *)
Theorem AHK_psl : forall s LB LF m mo, AHK s LB LF m mo -> nbig LB <= 8000 -> PSL OPSLACK (m_vmmaps mo).
Proof.
  intros s LB LF m mo H NB. ahk_open H. destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & _).
  destruct HS_tot as [HS HC].
  rewrite EE in Hwf, Hdi. pose proof ENV_depot as [K0 F0].
  apply (PSL_open_call E0 L0 RES0 mo s LB (2^46) 256 Hkvm HS); auto.
  - pose proof (proj1 (Nat2Z.inj_le _ _) HC). lia.
  - lia.
  - apply PSL_side_numerics; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma live_blocks_init : forall E, live_blocks (astate0 E) = [].
Proof. intros E. reflexivity. Qed.
Lemma blocks_match_init : forall E, blocks_match [] (astate0 E).
Proof. intros E. unfold blocks_match. rewrite live_blocks_init. apply Permutation_refl. Qed.
Lemma amaps_init : forall E, amaps (astate0 E) = [].
Proof. intros E. reflexivity. Qed.
Lemma a_eager_bytes_init : forall E, a_eager_bytes (astate0 E) = 0.
Proof. intros E. reflexivity. Qed.
Lemma aEB_init : aEB (aps_init E0 FSB0) = EB0.
Proof. unfold aEB, A_policy5.aEB, aEBa. cbn [aps_alloc aps_init]. rewrite a_eager_bytes_init. change (zlen (as_node_blocks (astate0 E0))) with 0. clear. lia. Qed.
Lemma aS_init : forall w, aS (aps_init E0 FSB0) w <-> (bv_unsigned w mod 4096 = 0 /\ in_ivs_Z A0 (bv_unsigned w)).
Proof.
  clear HR0_ok EB0_ok ENV_depot HS_tot. intros w. unfold aS, A_policy5.aS, aSa, in_interiors, in_stores. cbn [aps_alloc aps_init astate0 as_sec as_residue as_store_blocks]. cbn.
  split; [| intros [A B]; split; [exact A| left; exact B]]. intros [A [B|[(sc & F & _)|[F|(b & F & _)]]]]; [split; [exact A| exact B]| destruct F| destruct F| destruct F].
Qed.
Lemma aNz_init : aNz (aps_init E0 FSB0) = A0_pages A0.
Proof. unfold aNz, A_policy5.aNz, aNza, interiors_bound. cbn [aps_alloc aps_init astate0 as_sec as_residue as_store_blocks]. change (zlen []) with 0. cbn [foldr]. clear. lia. Qed.
Lemma aN_init_bound : Z.of_nat (aN (aps_init E0 FSB0)) <= A0_pages A0.
Proof. rewrite <- aNz_init. apply AHK_aN_bound. Qed.
(* [comment removed for export] *)
Lemma li_budget_init : aEB (aps_init E0 FSB0) + Z.of_nat (aN (aps_init E0 FSB0)) * 4096 <= 2^39.
Proof.
  rewrite aEB_init. pose proof aN_init_bound. pose proof BUDGET_STATIC_ok as B. unfold BUDGET_STATIC, kInitialCredit in B. clear -H B. lia.
Qed.
Lemma BUDGET_init5 : BUDGET (aps_init E0 FSB0) [].
Proof. apply BUDGET_init. Qed.

End Bundle.
End RC__1.

(* [comment removed for export] *)
Ltac ahk_open H :=
  destruct H as (Hrep & Hwf & Hkern & Hkvm & Hres & Hqb & Hdi & Hbinv & Hbm & Hfs & Hicp & Hyst & Hlow & Hrt & Hso & Hkm & Hli & Hbud & Hmi & Henv & Hycl & Hss & Hcs).
