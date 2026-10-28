(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ModelAmb PropExec CatExec CatSim StoreOk Frame Hoare ShapeAlg ShapeLaws Spec Spec04 AgentLib RefMemcpyLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0ReadBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0ReadChunk.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0ReadChunk U.S0World.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TargetPre.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TargetPre.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadChunk.S0ReadStage OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadChunk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0World OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.S0WorldVM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0StdioDefs U.S0ExitBase U.S0Exit U.S0Printf0 U.S0HarnStmt U.S0TRDefs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require AllocIface.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TRWalk U.S0TRInv U.S0TargetRun.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0StdioDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ExitBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Exit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Printf0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0HarnStmt OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap.AllocIface.GlueEqv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRWalk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetRun.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import EvtBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocTight AllocCover.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0GrowStmt.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TRWalk.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRWalk.S0GrowWalk.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Notation F0 := (bvmap_empty : bvmap 5 word) (only parsing).
Notation FC0 := (Z_to_bv 32 0) (only parsing).
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma modelG_canon : forall path stdin0 fs0 tid off V MD,
  vm_only (modelG path stdin0 fs0 tid off V) MD -> m_vm_lazy MD = [] -> m_vm_materialized MD = [] ->
  MD = modelG path stdin0 fs0 tid off (m_vmmaps MD).
Proof.
  (intros path stdin0 fs0 tid off V MD; cps_intros (E1 & E2 & E3 & E4 & E5 & E6); intros HL HM).   (* [comment removed for export] *)
  destruct MD as [fd vm io fsys proc lim tm]. cbn in *.
  unfold m_vm_lazy, m_vm_materialized, m_vmmaps in *. cbn in HL, HM |- *.
  destruct vm as [maps lazy mat]. cbn in *. subst. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lb_remove_pair : forall (p q : bid) (r n A c : Z), p <> q ->
  lb_remove q [(p, r, n); (q, A, c)] = [(p, r, n)].
Proof.
  intros p q r n A c NE. unfold lb_remove. cbn [List.filter blk_id fst].
  destruct (bid_eqb_spec p q); [congruence|]. destruct (bid_eqb_spec q q); [| congruence]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_CB_split : forall m A (n1 n2 : nat) bs,
  rw_cells s0segs m A [CB (n1 + n2) bs] ->
  rw_cells s0segs m A [CB n1 (firstn n1 bs)] /\ rw_cells s0segs m (A + Z.of_nat n1) [CB n2 (skipn n1 bs)].
Proof.
  intros m A n1 n2 bs [[WF BA] WR]. cbn in WF. destruct WF as [LEN _].
  cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. cbn [cells_size csize] in WR. rewrite Nat.add_0_r in WR.
  rewrite <- (firstn_skipn n1 bs) in BA. apply (proj1 (bytes_at_app _ _ _ _ _)) in BA as [B1 B2].
  rewrite firstn_length_le in B2 by lia.
  cps_destruct WR as (W0 & W1 & W).
  split; (split; [split; [cbn; split; [| exact I] |] |]).
  - rewrite firstn_length_le by lia. reflexivity.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B1.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
  - rewrite skipn_length. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B2.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat n1 + i) with (A + (Z.of_nat n1 + i)) by lia. apply W. lia.
Qed.

Lemma rw_CB_join : forall m A (n1 n2 : nat) bs1 bs2,
  rw_cells s0segs m A [CB n1 bs1] -> rw_cells s0segs m (A + Z.of_nat n1) [CB n2 bs2] ->
  rw_cells s0segs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
  intros m A n1 n2 bs1 bs2 [[WF1 B1] W1] [[WF2 B2] W2]. cbn in WF1, WF2. destruct WF1 as [L1 _]. destruct WF2 as [L2 _].
  cbn [cells_bytes cbytes] in B1, B2. rewrite app_nil_r in B1, B2. cbn [cells_size csize] in W1, W2. rewrite Nat.add_0_r in W1, W2.
  split; [split; [cbn; split; [rewrite app_length; lia| exact I]|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (proj2 (bytes_at_app _ _ _ _ _)). rewrite L1. split; assumption.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. cps_destruct W1 as (W10 & W11 & W1'). cps_destruct W2 as (W20 & W21 & W2').
    split; [lia|]. split; [lia|]. intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat n1)); [apply W1'; lia|].
    replace (A + i) with (A + Z.of_nat n1 + (i - Z.of_nat n1)) by lia. apply W2'. lia.
Qed.

(* [comment removed for export] *)
Lemma pref_length_le : forall n l, 0 <= n <= Z.of_nat (length l) -> length (pref n l) = Z.to_nat n.
Proof. intros n l Hn. unfold pref. rewrite firstn_length_le; lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Grow.
  Context (AI : AllocIface s0segs S0_layout) (AT : AllocTight s0segs S0_layout AI) (AC : AllocCover s0segs S0_layout AI).
  Hypothesis HARN : harn_spec AI AC S0I.
  Hypothesis HTC : tight_cover_stmt AI AT AC.
  Hypothesis PF0 : printf0_first_stmt PF0_S0.
  Hypothesis HE0W : grow_entry_stmt AI AT.
  Hypothesis OOM : oom_tail_stmt.          (* [comment removed for export] *)
  Hypothesis REF : refused_tail_stmt.      (* [comment removed for export] *)

  Local Notation L := S0_layout.
  Local Notation RSEGS := Ubsan.M.loaded_segments.

  Section Run.
    Variables (sp0 p1 mb gm tid : word) (path content : list byte) (stdin0 : AmbIn) (fs0 : Fs).
    Hypothesis Hfile : fs_lookup fs0 path = Some content.
    Let Lc : Z := Z.of_nat (length content).
    Let spz : Z := bv_unsigned sp0.
    Let tidz : Z := bv_unsigned tid.
    Hypothesis HL : 65536 <= Lc.
    Hypothesis SP0 : 0x7fff80000000 <= spz <= 0x800000000000 /\ spz mod 16 = 0.
    Hypothesis TID : 0 < tidz < 2 ^ 22.
    Variable hw : Z.                                            (* [comment removed for export] *)
    Hypothesis HWR : 0 <= hw < 2 ^ 64.
    Hypothesis alloc_ceiling_val : alloc_ceiling = spz - 8388608. (* [comment removed for export] *)

    Local Notation modelG := (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadChunk.S0ReadStage.modelG path stdin0 fs0 tid).
    (* [comment removed for export] *)
    Definition TREF : TSet := t_die msg_refused fs0.
    Definition KT : TSet := t_target content fs0.

    Lemma Hvsp : valid_sp sp0.
    Proof. unfold valid_sp, sp_window_lo, sp_window_hi. subst spz. lia. Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition leafkit (M : word -> option byte) : Prop :=
      Forall (fun iv => img_clear M (fst iv) (snd iv)) gw_ivs
      /\ S0World.cell M 0x44138 4 tidz /\ S0World.cell M 0x44118 8 0x44118 /\ S0World.cell M 0x64450 8 run_guard /\ S0World.cell M 0x644a0 8 4096 /\ S0World.cell M 0x644d8 8 hw.

    (* [comment removed for export] *)
    Definition leaf_addr (a : Z) : Prop :=
      (0x32000 <= a < 0x34090) \/ in_ivs (tl gw_ivs) a
      \/ (0x44138 <= a < 0x4413c) \/ (0x44118 <= a < 0x44120) \/ (0x64450 <= a < 0x64458) \/ (0x644a0 <= a < 0x644a8) \/ (0x644d8 <= a < 0x644e0).

    Record kit (M : word -> option byte) : Prop := KIT {
      k_stk : stk s0segs M (spz - 8388608) (spz - 128);
      k_top : wr_at s0segs M (spz - 48) 48;
      k_mi : mem_inv s0segs M;
      k_err : exists e, rw_cells s0segs M 0x4413c [C4 e];
      k_stat : statics spz tidz M;
      k_so : stdout_untouched M;
      k_leaf : leafkit M }.

    (* [comment removed for export] *)
    Definition kit_addr (a : Z) : Prop :=
      statics_addr spz a \/ stdout_addr a \/ leaf_addr a \/ (spz - 48 <= a < spz).

    Lemma in_ivs_tl_re_ivs : forall a, in_ivs (tl gw_ivs) a -> 0x34091 <= a < 0x66000 /\ ~ (0x644e8 <= a < 0x64888) /\ ~ (0x4413c <= a < 0x44140) /\ ~ (READ_STAGE <= a < READ_STAGE + 65536).
    Proof. intros a Ha. unfold READ_STAGE. cbn in Ha. lia. Qed.

    Lemma leaf_pres : forall P M M', pres P M M' -> mem_inv s0segs M' -> (forall a, leaf_addr a -> P a) -> leafkit M -> leafkit M'.
    Proof.
      (intros P M M' HP MI' HS; cps_intros (IMG & C1 & C2 & C3 & C4 & C5)).
      assert (CL : forall a n v, S0World.cell M a n v -> (forall x, a <= x < a + Z.of_nat n -> leaf_addr x) -> 0 <= a -> a + Z.of_nat n <= 2^64 -> S0World.cell M' a n v).
      { intros a n v Cc HA Ha Hn. unfold S0World.cell in *. rewrite <- Cc. change (Z_to_bv 64 a) with (wa a). apply (pres_rdn P); auto. }
      split; [| split; [| split; [| split; [| split]]]].
      - apply Forall_forall. intros [lo hi] Hin. pose proof (proj1 (Forall_forall _ _) IMG _ Hin) as Cc. cbn [fst snd] in Cc |- *.
        assert (CASE : (lo, hi) = (0x10000, 0x34090) \/ In (lo, hi) (tl gw_ivs)) by (destruct Hin as [E|IN]; [left; symmetry; exact E| right; exact IN]).
        intros a Ha. destruct (Z.lt_ge_cases a 0x32000) as [LT|GE].
        + apply (mem_inv_pristine_ro M' MI' a). destruct CASE as [E|IN]; [injection E as E1 E2; subst lo hi; lia|].
          exfalso. pose proof (in_ivs_tl_re_ivs a) as X. cbn [in_ivs tl gw_ivs] in X. cbn in IN.
          repeat (destruct IN as [E|IN]; [injection E as E1 E2; subst lo hi; lia|]). exact IN.
        + assert (HPa : P a).
          { apply HS. destruct CASE as [E|IN]; [injection E as E1 E2; subst lo hi; left; lia| right; left].
            clear -IN Ha. cbn in IN. cbn. repeat (destruct IN as [E|IN]; [injection E as E1 E2; subst lo hi; tauto|]). destruct IN. }
          assert (R : 0 <= a < 2^64) by (destruct CASE as [E|IN]; [injection E as E1 E2; subst lo hi; lia| pose proof (in_ivs_tl_re_ivs a) as X; cbn in IN; repeat (destruct IN as [E|IN]; [injection E as E1 E2; subst lo hi; lia|]); destruct IN]).
          destruct (HP a R HPa) as [E _]. unfold wa in E. rewrite E. apply Cc. exact Ha.
      - apply CL; [exact C1| intros; right; right; left; lia| lia| cbn; lia].
      - apply CL; [exact C2| intros; right; right; right; left; cbn in H; lia| lia| cbn; lia].
      - apply CL; [exact C3| intros; do 4 right; left; cbn in H; lia| lia| cbn; lia].
      - apply CL; [exact C4| intros; do 5 right; left; cbn in H; lia| lia| cbn; lia].
      - apply CL; [exact C5| intros; do 6 right; cbn in H; lia| lia| cbn; lia].
    Qed.

    Lemma alloc_ceiling_sp : alloc_ceiling <= spz - 8388608.
    Proof. rewrite alloc_ceiling_val. lia. Qed.

    Lemma kit_addr_client : forall LB a, kit_addr a -> client_addr L LB (spz - 128) a.
    Proof.
      intros LB a [Ha|[Ha|[Ha|Ha]]].
      - apply (statics_client spz); [lia| exact Ha].
      - unfold stdout_addr, SO_FILE, SO_BUF in Ha. right; left. unfold L, S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp]. lia.
      - right; left. unfold L, S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp].
        destruct Ha as [Ha|[Ha|Ha]]; [lia| pose proof (in_ivs_tl_re_ivs a Ha); lia| lia].
      - left. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma kit_pres : forall P M M' e',
      kit M -> pres P M M' -> (forall a, kit_addr a -> P a) ->
      stk s0segs M' (spz - 8388608) (spz - 128) -> mem_inv s0segs M' -> rw_cells s0segs M' 0x4413c [C4 e'] -> kit M'.
    Proof.
      intros P M M' e' [ST TOP MI ERR STAT SO LEAF] HP HS ST' MI' ERR'. pose proof SP0 as [SPR _].
      constructor.
      - exact ST'.
      - eapply pres_wr_at; [exact HP| exact TOP|]. intros a Ha. apply HS. do 3 right. lia.
      - exact MI'.
      - exists e'. exact ERR'.
      - eapply statics_pres; [exact HP| | exact SPR| exact STAT]. intros a Ha. apply HS. left; exact Ha.
      - eapply stdout_untouched_pres; [exact HP| | exact SO]. intros a Ha. apply HS. right; left; exact Ha.
      - eapply leaf_pres; [exact HP| exact MI'| | exact LEAF]. intros a Ha. apply HS. right; right; left; exact Ha.
    Qed.

    (* [comment removed for export] *)
    Lemma kit_alloc : forall LB M M' e',
      kit M -> heap_pres s0segs L LB (spz - 128) M M' -> mem_inv s0segs M' ->
      stk s0segs M' (spz - 8388608) (spz - 128) -> rw_cells s0segs M' (errno_cell L) [C4 e'] -> kit M'.
    Proof.
      intros LB M M' e' K HP MI' ST' ERR'. eapply (kit_pres _ M M' e' K (pres_of_heap_pres _ _ _ _ _ HP)); [| exact ST'| exact MI'| exact ERR'].
      intros a Ha. apply kit_addr_client. exact Ha.
    Qed.

    (* [comment removed for export] *)
    Lemma kit_munch : forall W M M',
      kit M -> munch W M M' -> wmono s0segs M M' -> mem_inv s0segs M' ->
      Forall (fun iv => 0x66000 <= fst iv /\ snd iv <= alloc_ceiling) W -> kit M'.
    Proof.
      intros W M M' K MU WM MI' HW. pose proof alloc_ceiling_sp as ACS. pose proof SP0 as [SPR _].
      assert (OUT : forall a, a < 0x66000 \/ alloc_ceiling <= a -> outside W a).
      { intros a Ha. clear -HW Ha. induction W as [|[lo hi] W IH]; cbn; [exact I|]. apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2.
        split; [lia| apply IH; exact HW]. }
      assert (DJ : forall a n, a + n <= 0x66000 \/ alloc_ceiling <= a -> disjoint_from W a n).
      { intros a n Ha. clear -HW Ha. induction W as [|[lo hi] W IH]; cbn; [exact I|]. apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2.
        split; [lia| apply IH; exact HW]. }
      destruct (k_err M K) as [e ERR].
      eapply (kit_pres (outside W) M M' e K (pres_of_munch _ _ _ MU WM)); [| | exact MI'|].
      - intros a Ha. apply OUT. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
        + unfold statics_addr, OFL in Ha. cbn [in_ivs S_IVS] in Ha. lia.
        + unfold stdout_addr, SO_FILE, SO_BUF in Ha. lia.
        + destruct Ha as [Ha|[Ha|Ha]]; [lia| pose proof (in_ivs_tl_re_ivs a Ha); lia| lia].
        + lia.
      - eapply pres_stk; [exact (pres_of_munch _ _ _ MU WM)| exact (k_stk M K)|]. intros a Ha. apply OUT. lia.
      - eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. cbn. apply DJ. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma kit_read : forall M M' (b n : Z),
      kit M -> frame_mod M M' (lit_regions [(spz - 136, 8); (b, n); (READ_STAGE, 65536)]) -> 0x66000 <= b -> 0 <= n -> b + n <= alloc_ceiling -> kit M'.
    Proof.
      intros M M' b n K FM Hb Hn0 Hn. pose proof alloc_ceiling_val as ACV. pose proof alloc_ceiling_sp as ACS. pose proof SP0 as [SPR _].
      assert (RS : Forall (fun r : Z * Z => 0 <= fst r < 2 ^ 64) [(spz - 136, 8); (b, n); (READ_STAGE, 65536)]) by (unfold READ_STAGE; apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_nil).
      pose proof (pres_of_frame_mod _ M M' RS FM) as HP.
      pose proof (munch_of_frame_mod _ M M' RS FM) as MU. cbn [ivs_of_regions] in MU.
      assert (MI' : mem_inv s0segs M').
      { eapply mem_inv_munch; [exact MU| | exact (k_mi M K)]. unfold READ_STAGE. apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_nil. }
      destruct (k_err M K) as [e ERR].
      eapply (kit_pres _ M M' e K HP); [| | exact MI'|].
      - intros a Ha. cbn. unfold READ_STAGE. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
        + unfold statics_addr, OFL in Ha. cbn [in_ivs S_IVS] in Ha. lia.
        + unfold stdout_addr, SO_FILE, SO_BUF in Ha. lia.
        + destruct Ha as [Ha|[Ha|Ha]]; [lia| pose proof (in_ivs_tl_re_ivs a Ha) as X; unfold READ_STAGE in X; lia| lia].
        + lia.
      - eapply stk_grows; [exact (k_stk M K)| exact (proj2 FM)| lia].
      - eapply pres_rw_cells; [exact HP| exact ERR|]. cbn. unfold READ_STAGE. intros; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma stack_writable_of : forall M, kit M -> stack_writable M sp0.
    Proof.
      intros M K. pose proof SP0 as [SPR _]. pose proof (k_stk M K) as ST. pose proof (k_top M K) as TOP. pose proof (st_mf _ _ _ (k_stat M K)) as FR.
      assert (W : forall a, spz - 8388608 <= a < spz -> wview s0segs M (wa a) <> None).
      { intros a Ha. destruct (Z.lt_ge_cases a (spz - 128)) as [A|A]; [| destruct (Z.lt_ge_cases a (spz - 48)) as [B|B]].
        - cps_destruct ST as (_ & _ & ST3). apply (proj1 (ST3 a ltac:(lia))).
        - destruct FR as [junk8 [_ (_ & _ & WR)]]. cbn [cells_size csize Nat.add] in WR. replace a with (spz - 128 + (a - (spz - 128))) by lia. apply WR. lia.
        - cps_destruct TOP as (_ & _ & WR). replace a with (spz - 48 + (a - (spz - 48))) by lia. apply WR. lia. }
      intros d m Hd Hm. change (bv_unsigned sp0) with spz.
      pose proof (wr_at_store_ok s0segs M (spz - 8388608) 8388608 d m) as X.
      unfold wa in X. apply X; [| lia| lia]. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Lemma ref_leaf : forall (R : bvmap 5 word) M MD,
      getr R 2 = Z_to_bv 64 (spz - 128) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x441e0 ->
      kit M -> m_halted MD = None -> m_vm_lazy MD = [] ->
      fd_lookup (m_fds MD) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_fs MD = fs0 ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x137c8) M (seg_rom RSEGS)) MD) TREF.
    Proof.
      intros R M MD R2 R3 R4 K Hh Hl Hfd Hfs. unfold TREF. rewrite <- Hfs.
      cps_destruct (k_leaf M K) as (IMG & C1 & C2 & C3 & C4 & C5).
      apply (REF sp0 MD tidz hw R M Hvsp Hh Hl Hfd R2 R3 R4 (stack_writable_of M K) IMG C1 TID C2 C3 C4 C5 HWR).
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Definition SXCHK : bool :=
      forallb (fun x => bv_unsigned (sxb (Z_to_bv 8 x)) =? (if x <? 128 then x else x - 256 + 2 ^ 64)) (zlist (Z.to_nat 256) 0).
    Lemma sxchk_ok : SXCHK = true.
    Proof. vm_compute. reflexivity. Qed.
    Lemma sxb_hdr : forall b : byte,
      sxb b = Z_to_bv 64 (if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b - 256 + 2 ^ 64).
    Proof.
      intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
      pose proof sxchk_ok as K. unfold SXCHK in K. rewrite forallb_forall in K.
      specialize (K (bv_unsigned b) (in_zlist 256 0 (bv_unsigned b) ltac:(lia))). apply Z.eqb_eq in K.
      replace (Z_to_bv 8 (bv_unsigned b)) with b in K by (apply bv_eq; rewrite Z_to_bv_small; [reflexivity| change (bv_modulus 8) with 256%Z; lia]).
      apply bv_eq. rewrite K. symmetry. apply Z_to_bv_small. unfold bv_modulus. destruct (Z.ltb_spec (bv_unsigned b) 128); lia.
    Qed.

    Lemma end_phase : forall (bufA cap : Z) (p : bid) (s : ai_AS AI) (V : VmMaps) (R : bvmap 5 word) (M : word -> option byte),
      getr R 2 = Z_to_bv 64 (spz - 128) -> getr R 4 = Z_to_bv 64 0x441e0 -> getr R 9 = Z_to_bv 64 bufA -> getr R 19 = Z_to_bv 64 Lc ->
      getr R 22 = Z_to_bv 64 READ_STAGE ->                      (* [comment removed for export] *)
      Lc < cap -> cap <= 2 ^ 26 ->
      ai_inv AI s [(p, bufA, cap)] M (model_post V stdin0 fs0 tid) -> at_tight AT s [(p, bufA, cap)] (model_post V stdin0 fs0 tid) ->
      ai_aux AI M spz -> kit M ->
      rw_cells s0segs M bufA [CB (length content) content] ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1367c) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) KT.
    Proof.
      intros bufA cap p s V R M R2 R4 R9 R19 R22 HLc Hcap INV TI AUX K BUF. pose proof SP0 as [SPR SPA].
      destruct (ai_inv_model AI INV) as [Hh Hl].
      pose proof (ai_inv_blocks AI INV (or_introl eq_refl)) as BOK. cbn [blk_addr blk_size fst snd] in BOK.
      cps_destruct BOK as (BK1 & BK2 & BK3 & BK4 & BK5). cbn [al_img_lo al_img_hi S0_layout] in BK5. rewrite alloc_ceiling_val in BK4.
      assert (BLO : 0x66000 <= bufA) by lia.
      assert (CR : 0 <= hdr_cfglen content < 32768) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
      (* [comment removed for export] *)
      assert (LEN6 : (6 <= length content)%nat) by lia.
      set (b0 := nth 0 content (Z_to_bv 8 0)). set (b1 := nth 1 content (Z_to_bv 8 0)).
      set (cfg := hdr_cfglen content).
      assert (Hcfg : (bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768 = cfg) by reflexivity.
      set (q := (Z.to_nat cfg + 2)%nat).
      set (c0 := nth q content (Z_to_bv 8 0)). set (c1 := nth (q + 1) content (Z_to_bv 8 0)).
      set (c2 := nth (q + 2) content (Z_to_bv 8 0)). set (c3 := nth (q + 3) content (Z_to_bv 8 0)).
      assert (HB01 : rw_cells s0segs M bufA [C1 b0; C1 b1]).
      { change [C1 b0; C1 b1] with ([C1 b0] ++ [C1 b1]). apply rw_cells_app.
        - replace bufA with (bufA + Z.of_nat 0) at 1 by lia. apply (rw_cells_byte M bufA (length content) content 0 BUF). lia.
        - cbn [cells_size csize Nat.add]. apply (rw_cells_byte M bufA (length content) content 1 BUF). lia. }
      assert (HC : rw_cells s0segs M (bufA + cfg + 2) [C1 c0; C1 c1; C1 c2; C1 c3]).
      { change [C1 c0; C1 c1; C1 c2; C1 c3] with ([C1 c0] ++ [C1 c1] ++ [C1 c2] ++ [C1 c3]).
        apply rw_cells_app; [| apply rw_cells_app; [| apply rw_cells_app]]; cbn [cells_size csize Nat.add].
        - replace (bufA + cfg + 2) with (bufA + Z.of_nat q) by lia. apply (rw_cells_byte M bufA (length content) content q BUF). lia.
        - replace (bufA + cfg + 2 + Z.of_nat 1) with (bufA + Z.of_nat (q + 1)) by lia. apply (rw_cells_byte M bufA (length content) content (q + 1) BUF). lia.
        - replace (bufA + cfg + 2 + Z.of_nat 1 + Z.of_nat 1) with (bufA + Z.of_nat (q + 2)) by lia. apply (rw_cells_byte M bufA (length content) content (q + 2) BUF). lia.
        - replace (bufA + cfg + 2 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1) with (bufA + Z.of_nat (q + 3)) by lia. apply (rw_cells_byte M bufA (length content) content (q + 3) BUF). lia. }
      (* [comment removed for export] *)
      apply realizes_to_mkR. unfold mkR_of. rewrite R2, R4, R9, R19, R22.
      eapply (evt_realizes s0segs); [exact Hh | exact Hl | |].
      { eapply (hdr_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 FC0 M bufA Lc cfg b0 b1 c0 c1 c2 c3);
          [lia | exact BLO | lia | exact Hcfg | exact HB01 | exact HC | exact (k_mi M K)]. }
      intros ms' ->. rewrite MS_mkst.
      destruct (k_err M K) as [e ERR].
      unfold KT. change fs0 with (m_fs (model_post V stdin0 fs0 tid)).
      destruct (HTC _ _ _ _ INV TI) as [C21 [K0 [VMC K0LE]]].
      eapply (run_cps AI AC HARN PF0 spz tidz spz bufA cap content (model_post V stdin0 fs0 tid) _ M s [(p, bufA, cap)] p e K0); try reflexivity.
      all: first [ exact SP0 | exact alloc_ceiling_val | exact TID | exact BLO | exact (k_stk M K) | exact (k_mi M K) | exact (k_stat M K) | exact (k_so M K)
                 | exact BUF | exact ERR | exact INV | exact AUX | exact C21 | exact VMC | exact K0LE | idtac ].
      - transitivity (Z_to_bv 64 (bufA + cfg + 6)); [reflexivity| f_equal; lia].
      - transitivity (Z_to_bv 64 (Lc - cfg + -6)); [reflexivity| f_equal; lia].
      - transitivity (Z_to_bv 64 (Lc - cfg + -6)); [reflexivity| f_equal; lia].
      - transitivity (sxb b1); [reflexivity| subst b1; unfold hdr_b1; apply sxb_hdr].
      - lia.
      - lia.
      - (* [comment removed for export] *)
        destruct (k_leaf M K) as (IMG & _). pose proof (proj1 (Forall_forall _ _) IMG (0x440d9, 0x44110) ltac:(cbn; tauto)) as PR. cbn [fst snd] in PR.
        eapply rw_C1_pristine; [intros a Ha; apply PR; lia | lia | lia | solve_img | vm_compute; reflexivity].
      - left. reflexivity.
      - lia.
      - intros n Hn. apply (at_sys AT INV TI). unfold MAX_REQ. lia.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Lemma cap_of_pos : forall j, 0 <= j -> 65536 <= cap_of j.
    Proof. intros j Hj. unfold cap_of. pose proof (Z.pow_le_mono_r 2 0 j ltac:(lia) Hj). change (2 ^ 0) with 1 in H. nia. Qed.
    Lemma cap_of_succ : forall j, 0 <= j -> cap_of (j + 1) = 2 * cap_of j.
    Proof. intros j Hj. unfold cap_of. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. Qed.
    Lemma cap_of_le : forall j, 0 <= j <= 10 -> cap_of j <= 2 ^ 26.
    Proof. intros j Hj. unfold cap_of. pose proof (Z.pow_le_mono_r 2 j 10 ltac:(lia) ltac:(lia)). change (2 ^ 10) with 1024 in H. change (2 ^ 26) with (65536 * 1024). nia. Qed.

    Record fullst (j bufA : Z) (pb : bid) (s : ai_AS AI) (V : VmMaps) (R : bvmap 5 word) (M : word -> option byte) : Prop := FULLST {
      f_j : 0 <= j <= 10;
      f_cap : cap_of j <= Lc;
      f_r2 : getr R 2 = Z_to_bv 64 (spz - 128);
      f_r3 : getr R 3 = Z_to_bv 64 0x10800;
      f_r4 : getr R 4 = Z_to_bv 64 0x441e0;
      f_r19 : getr R 19 = Z_to_bv 64 (cap_of j);
      f_r20 : getr R 20 = Z_to_bv 64 3;
      f_r21 : getr R 21 = Z_to_bv 64 (cap_of j);
      f_r22 : getr R 22 = Z_to_bv 64 READ_STAGE;               (* [comment removed for export] *)
      f_r23 : getr R 23 = Z_to_bv 64 bufA;                     (* [comment removed for export] *)
      f_inv : ai_inv AI s [(pb, bufA, cap_of j)] M (modelG (cap_of j) V);
      f_tight : at_tight AT s [(pb, bufA, cap_of j)] (modelG (cap_of j) V);
      f_aux : ai_aux AI M spz;
      f_kit : kit M;
      f_buf : rw_cells s0segs M bufA [CB (Z.to_nat (cap_of j)) (pref (cap_of j) content)] }.

    (* [comment removed for export] *)
    Lemma buf_after_read : forall M M' (r held len' : Z) junk,
      0 <= held <= len' -> len' <= Lc -> 0x66000 <= r -> r + len' <= alloc_ceiling ->
      rw_cells s0segs M r [CB (Z.to_nat held) (pref held content)] ->
      rw_cells s0segs M (r + held) [CB (Z.to_nat (len' - held)) junk] ->
      loop_post_mem content M M' spz r held len' ->
      rw_cells s0segs M' r [CB (Z.to_nat len') (pref len' content)].
    Proof.
      intros M M' r held len' junk Hh Hl Hr Hrl B1 B2 [FM RD]. pose proof alloc_ceiling_val as ACV. pose proof SP0 as [SPR _].
      assert (RS : Forall (fun q : Z * Z => 0 <= fst q < 2 ^ 64) [(spz - 136, 8); (r + held, len' - held); (READ_STAGE, 65536)]) by (unfold READ_STAGE; apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_nil).
      pose proof (pres_of_frame_mod _ M M' RS FM) as HP.
      replace (Z.to_nat len') with (Z.to_nat held + Z.to_nat (len' - held))%nat by lia.
      replace (pref len' content) with (pref held content ++ pref (len' - held) (dropz held content))
        by (rewrite pref_app by lia; f_equal; lia).
      apply rw_CB_join.
      - eapply pres_rw_cells; [exact HP| exact B1|]. cbn [cells_size csize Nat.add]. intros a Ha. cbn. unfold READ_STAGE. lia.
      - replace (r + Z.of_nat (Z.to_nat held)) with (r + held) by lia.
        destruct B2 as [[WF _] WR]. cbn in WF. destruct WF as [LJ _]. cbn [cells_size csize] in WR. rewrite Nat.add_0_r in WR.
        split; [split; [cbn; split; [apply pref_length_le; rewrite dropz_length by lia; lia| exact I]|]|].
        + cbn [cells_bytes cbytes]. rewrite app_nil_r.
          pose proof (bytes_at_of_rdn (Z.to_nat (len' - held)) M' (r + held) _ RD ltac:(lia) ltac:(lia)) as BA. exact BA.
        + cbn [cells_size csize]. rewrite Nat.add_0_r. eapply wr_at_transport; [exact WR| exact (wmono_of_frame_mod _ _ _ FM)].
    Qed.

    Lemma cwo_block : forall (p : bid) r n LB lo hi, r <= lo -> hi <= r + n -> client_write_ok L ((p, r, n) :: LB) (lo, hi).
    Proof. intros. right; right. exists (p, r, n). split; [left; reflexivity|]. cbn. lia. Qed.

    (* [comment removed for export] *)
    Lemma cwo_stage : forall LB, client_write_ok L LB (READ_STAGE, READ_STAGE + 65536).
    Proof.
      intros. right; left. unfold READ_STAGE. cbn [fst snd al_rw_lo al_img_hi al_static S0_layout]. split; [lia|]. split; [lia|].
      intros a Ha. unfold S0_static. lia.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Lemma mid_phase : forall (j r : Z) (p : bid) (s : ai_AS AI) (V : VmMaps) (R : bvmap 5 word) (M : word -> option byte) (junk : list byte) (K : TSet),
      0 <= j <= 9 -> cap_of j <= Lc ->
      getr R 2 = Z_to_bv 64 (spz - 128) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x441e0 ->
      getr R 9 = Z_to_bv 64 r -> getr R 19 = Z_to_bv 64 (cap_of j) -> getr R 20 = Z_to_bv 64 3 -> getr R 21 = Z_to_bv 64 (cap_of (j + 1)) ->
      getr R 22 = Z_to_bv 64 READ_STAGE ->                      (* [comment removed for export] *)
      ai_inv AI s [(p, r, cap_of (j + 1))] M (modelG (cap_of j) V) -> at_tight AT s [(p, r, cap_of (j + 1))] (modelG (cap_of j) V) ->
      ai_aux AI M spz -> kit M ->
      rw_cells s0segs M r [CB (Z.to_nat (cap_of j)) (pref (cap_of j) content)] ->
      rw_cells s0segs M (r + cap_of j) [CB (Z.to_nat (cap_of j)) junk] ->
      (cap_of (j + 1) <= Lc -> forall R' M', fullst (j + 1) r p s V R' M' ->
         realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x13614) M' (seg_rom RSEGS)) (modelG (cap_of (j + 1)) V)) K) ->
      (Lc < cap_of (j + 1) -> K = KT) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1364c) M (seg_rom RSEGS)) (modelG (cap_of j) V)) K.
    Proof.
      intros j r p s V R M junk K Hj Hcap R2 R3 R4 R9 R19 R20 R21 R22 INV TI AUX K0 B1 B2 HFULL HEND.
      pose proof SP0 as [SPR SPA]. pose proof alloc_ceiling_val as ACV. pose proof alloc_ceiling_sp as ACS.
      pose proof (cap_of_pos j ltac:(lia)) as CP. pose proof (cap_of_succ j ltac:(lia)) as CS. pose proof (cap_of_le (j + 1) ltac:(lia)) as CL.
      set (cap := cap_of j) in *. set (cap' := cap_of (j + 1)) in *.
      destruct (ai_inv_model AI INV) as [Hh Hl].
      pose proof (ai_inv_blocks AI INV (or_introl eq_refl)) as BOK. cbn [blk_addr blk_size fst snd] in BOK.
      cps_destruct BOK as (BK1 & BK2 & BK3 & BK4 & BK5). cbn [al_img_lo al_img_hi S0_layout] in BK5.
      assert (BLO : 0x66000 <= r) by lia.
      apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile (Z.to_nat cap') R M spz r cap cap' K); try lia.
      - repeat split; assumption.
      - apply (store_ok_of_stk M (spz - 8388608) (spz - 128)); [exact (k_stk M K0)| lia| cbn; lia].
      - destruct B2 as [_ WR]. cbn [cells_size csize] in WR. rewrite Nat.add_0_r in WR.
        pose proof (wr_at_store_ok s0segs M (r + cap) _ 0 (Z.to_nat (cap' - cap)) WR ltac:(lia) ltac:(lia)) as X.
        unfold wa in X. replace (r + cap + 0) with (r + cap) in X by lia. exact X.
      - (* [comment removed for export] *)
        (intros HcL R' M'; cps_intros (P2 & P9 & P23 & P19 & PK); intros PM).
        assert (KEEP : forall k : reg, In k S7ReadChunkW.loop_kept -> getr R' k = getr R k) by exact PK.
        destruct PM as [FM RD].
        assert (RS : Forall (fun q : Z * Z => 0 <= fst q < 2 ^ 64) [(spz - 136, 8); (r + cap, cap' - cap); (READ_STAGE, 65536)]) by (unfold READ_STAGE; apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_nil).
        pose proof (munch_of_frame_mod _ M M' RS FM) as MU. cbn [ivs_of_regions] in MU. pose proof (wmono_of_frame_mod _ _ _ FM) as WM.
        apply (HFULL HcL R' M'). constructor.
        + lia.
        + exact HcL.
        + exact P2.
        + rewrite (KEEP 3%bv) by (cbv; tauto). exact R3.
        + rewrite (KEEP 4%bv) by (cbv; tauto). exact R4.
        + exact P19.
        + rewrite (KEEP 20%bv) by (cbv; tauto). exact R20.
        + rewrite (KEEP 21%bv) by (cbv; tauto). exact R21.
        + rewrite (KEEP 22%bv) by (cbv; tauto). exact R22.
        + exact P23.
        + eapply (ai_inv_model_frame AI (MD:=modelG cap V)); [| reflexivity| reflexivity].
          eapply (ai_inv_frame AI); [exact INV| exact MU| exact WM|].
          apply Forall_cons; [apply cwo_stack; lia|]. apply Forall_cons; [apply cwo_block; lia|]. apply Forall_cons; [apply cwo_stage| apply Forall_nil].
        + eapply (at_model_frame AT (MD:=modelG cap V)); [exact TI| reflexivity| reflexivity].
        + eapply (ai_aux_frame AI); [exact AUX| exact MU| exact WM|].
          apply Forall_cons; [cbn; split; [lia| unfold S0_static; intros; lia]|]. apply Forall_cons; [cbn; split; [lia| unfold S0_static; intros; lia]|]. apply Forall_cons; [unfold READ_STAGE; cbn; split; [lia| unfold S0_static; intros; lia]| apply Forall_nil].
        + eapply kit_read; [exact K0| exact FM| lia| lia| lia].
        + assert (B2' : rw_cells s0segs M (r + cap) [CB (Z.to_nat (cap' - cap)) junk]) by (replace (cap' - cap) with cap by lia; exact B2).
          eapply buf_after_read; [ | | | | exact B1| exact B2'| split; [exact FM| exact RD]]; lia.
      - (* [comment removed for export] *)
        (intros HLc R' M'; cps_intros (P2 & P9 & P23 & P19 & PK); intros PM). rewrite (HEND HLc).
        assert (KEEP : forall k : reg, In k S7ReadChunkW.loop_kept -> getr R' k = getr R k) by exact PK.
        destruct PM as [FM RD].
        assert (RS : Forall (fun q : Z * Z => 0 <= fst q < 2 ^ 64) [(spz - 136, 8); (r + cap, Lc - cap); (READ_STAGE, 65536)]) by (unfold READ_STAGE; apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_nil).
        pose proof (munch_of_frame_mod _ M M' RS FM) as MU. cbn [ivs_of_regions] in MU. pose proof (wmono_of_frame_mod _ _ _ FM) as WM.
        apply (end_phase r cap' p s V R' M'); try assumption.
        + rewrite (KEEP 4%bv) by (cbv; tauto). exact R4.
        + rewrite (KEEP 22%bv) by (cbv; tauto). exact R22.
        + eapply (ai_inv_model_frame AI (MD:=modelG cap V)); [| reflexivity| reflexivity].
          eapply (ai_inv_frame AI); [exact INV| exact MU| exact WM|].
          apply Forall_cons; [apply cwo_stack; lia|]. apply Forall_cons; [apply cwo_block; lia|]. apply Forall_cons; [apply cwo_stage| apply Forall_nil].
        + eapply (at_model_frame AT (MD:=modelG cap V)); [exact TI| reflexivity| reflexivity].
        + eapply (ai_aux_frame AI); [exact AUX| exact MU| exact WM|].
          apply Forall_cons; [cbn; split; [lia| unfold S0_static; intros; lia]|]. apply Forall_cons; [cbn; split; [lia| unfold S0_static; intros; lia]|]. apply Forall_cons; [unfold READ_STAGE; cbn; split; [lia| unfold S0_static; intros; lia]| apply Forall_nil].
        + eapply kit_read; [exact K0| exact FM| lia| lia| lia].
        + assert (B2s : rw_cells s0segs M (r + cap) [CB (Z.to_nat (Lc - cap) + (Z.to_nat cap - Z.to_nat (Lc - cap))) junk]).
          { replace (Z.to_nat (Lc - cap) + (Z.to_nat cap - Z.to_nat (Lc - cap)))%nat with (Z.to_nat cap) by lia. exact B2. }
          destruct (rw_CB_split M (r + cap) _ _ junk B2s) as [B2' _].
          pose proof (buf_after_read M M' r cap Lc _ ltac:(lia) ltac:(lia) BLO ltac:(lia) B1 B2' (conj FM RD)) as X.
          replace (Z.to_nat Lc) with (length content) in X by (unfold Lc; lia). rewrite (pref_all Lc content) in X by (unfold Lc; lia).
          exact X.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Fixpoint SHF (n : nat) (j : Z) : TSet :=
      match n with
      | O => TREF
      | S n' => (if Lc <? cap_of (j + 1) then KT else SHF n' (j + 1))   (* [comment removed for export] *)
      end.

    Lemma grow_full : forall (n : nat) (j bufA : Z) (pb : bid) (s : ai_AS AI) (V : VmMaps) (R : bvmap 5 word) (M : word -> option byte),
      Z.of_nat n = 10 - j -> fullst j bufA pb s V R M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13614) M (seg_rom RSEGS)) (modelG (cap_of j) V)) (SHF n j).
    Proof.
      induction n as [|n IH]; intros j bufA pb s V R M Hn FS; destruct FS as [Fj Fcap R2 R3 R4 R19 R20 R21 R22 R23 INV TI AUX K0 BUF];
        pose proof SP0 as [SPR SPA]; pose proof alloc_ceiling_val as ACV; pose proof alloc_ceiling_sp as ACS.
      - (* [comment removed for export] *)
        assert (Ej : j = 10) by lia.
        assert (CAP : cap_of j = 67108864) by (rewrite Ej; reflexivity).
        rewrite CAP in *. cbn [SHF].
        apply realizes_to_mkR. unfold mkR_of. rewrite R2, R3, R4, R19, R20, R21, R22, R23.
        eapply (evt_realizes s0segs); [reflexivity | reflexivity | apply growR |].
        intros ms' ->. rewrite MS_mkst. apply ref_leaf; try reflexivity. exact K0.
      - (* [comment removed for export] *)
        pose proof (cap_of_pos j ltac:(lia)) as CP. pose proof (cap_of_succ j ltac:(lia)) as CS. pose proof (cap_of_le (j + 1) ltac:(lia)) as CL.
        set (cap := cap_of j) in *. set (cap' := cap_of (j + 1)) in *.
        change (SHF (S n) j) with (if Lc <? cap' then KT else SHF n (j + 1)).
        destruct (ai_inv_model AI INV) as [Hh Hl].
        pose proof (ai_inv_blocks AI INV (or_introl eq_refl)) as BOK. cbn [blk_addr blk_size fst snd] in BOK.
        cps_destruct BOK as (BK1 & BK2 & BK3 & BK4 & BK5). cbn [al_img_lo al_img_hi S0_layout] in BK5.
        assert (BLO : 0x66000 <= bufA) by lia.
        destruct (k_err M K0) as [e ERR].
        apply realizes_to_mkR. unfold mkR_of. rewrite R2, R3, R4, R19, R20, R21, R22, R23.
        eapply (evt_realizes s0segs); [reflexivity | reflexivity | apply growA; lia |].
        intros ms' ->. rewrite <- CS.
        (* [comment removed for export] *)
        eapply (at_malloc_big AT) with (s := s) (LB := [(pb, bufA, cap)]) (n := cap') (lo := spz - 8388608) (B := spz) (errv := e)
                                        (Tok := if Lc <? cap' then KT else SHF n (j + 1));
          [ exact INV | exact TI | reflexivity | unfold MMAP_THRESHOLD_Z, MAX_REQ; lia | exact AUX
          | rewrite u64_lit by lia; lia | rewrite u64_lit by lia; exact (k_stk M K0) | exact ACS
          | rewrite u64_lit by lia; cbn [al_stack S0_layout]; lia | exact ERR | exact (k_mi M K0) | reflexivity | reflexivity | ].
        + (* [comment removed for export] *)
          intros s' m' MD' rr p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' junk INV' TI' VMO MI' ST' ERR' AUX' HP Hr BOK' NIN RW.
          rewrite u64_lit in ST', HP by lia. rewrite ret_pc_lit by lia.
          destruct (ai_inv_model AI INV') as [Hh' Hl'].
          pose proof (modelG_canon path stdin0 fs0 tid cap V MD' VMO Hl' (at_mat AT TI')) as EMD. rewrite EMD in INV', TI', Hh', Hl'. rewrite EMD.
          cps_destruct BOK' as (RK1 & RK2 & RK3 & RK4 & RK5). cbn [al_img_lo al_img_hi S0_layout] in RK5.
          assert (RLO : 0x66000 <= rr) by lia.
          pose proof (kit_alloc _ _ _ _ K0 HP MI' ST' ERR') as K1.
          assert (BUF1 : rw_cells s0segs m' bufA [CB (Z.to_nat cap) (pref cap content)]).
          { eapply pres_rw_cells; [exact (pres_of_heap_pres _ _ _ _ _ HP) | exact BUF |]. cbn [cells_size csize Nat.add]. intros a Ha.
            right; right. exists (pb, bufA, cap). split; [left; reflexivity|]. cbn. lia. }
          assert (RW2 : rw_cells s0segs m' rr [CB (Z.to_nat cap + Z.to_nat cap) junk]).
          { replace (Z.to_nat cap + Z.to_nat cap)%nat with (Z.to_nat cap') by lia. exact RW. }
          destruct (rw_CB_split m' rr _ _ junk RW2) as [RWa RWb]. replace (rr + Z.of_nat (Z.to_nat cap)) with (rr + cap) in RWb by lia.
          assert (DISJ : bufA + cap <= rr \/ rr + cap' <= bufA).
          { assert (NE : (p, rr, cap') <> (pb, bufA, cap)) by (intros E; injection E as E1 _ _; apply NIN; rewrite E1; left; reflexivity).
            pose proof (ai_inv_disjoint AI INV' (or_introl eq_refl) (or_intror (or_introl eq_refl)) NE) as D.
            cbn [blk_addr blk_size fst snd] in D. lia. }
          assert (SRC1 : bytes_at s0segs m' bufA (pref cap content)).
          { pose proof (rw_cells_bytes_at _ _ _ BUF1) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. }
          (* [comment removed for export] *)
          eapply (evt_realizes s0segs); [exact Hh' | exact Hl' | apply growB; lia |].
          intros ms' ->.
          eapply memcpy_cps with (dst := rr) (src := bufA) (n := cap) (bs := pref cap content) (junk := firstn (Z.to_nat cap) junk);
            [ reflexivity | reflexivity | reflexivity
            | exists 0x13644; split; [reflexivity|]; split; [lia| reflexivity]
            | exact RWa | exact SRC1 | rewrite pref_length_le by lia; lia | lia | lia | lia
            | exact Hh' | exact Hl' | exact MI' |].
          intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m'' MU WM MI'' RWd SRC.
          rewrite ret_pc_lit by lia.
          pose proof (kit_munch _ _ _ K1 MU WM MI'' ltac:(apply Forall_cons; [cbn; lia| apply Forall_nil])) as K2.
          assert (INV2 : ai_inv AI s' ((p, rr, cap') :: [(pb, bufA, cap)]) m'' (modelG cap (m_vmmaps MD'))).
          { eapply (ai_inv_frame AI); [exact INV' | exact MU | exact WM |]. apply Forall_cons; [apply cwo_block; lia | apply Forall_nil]. }
          assert (AUX2 : ai_aux AI m'' spz).
          { eapply (ai_aux_frame AI); [exact AUX' | exact MU | exact WM |]. apply Forall_cons; [cbn; split; [lia| unfold S0_static; intros; lia] | apply Forall_nil]. }
          assert (RWb2 : rw_cells s0segs m'' (rr + cap) [CB (Z.to_nat cap) (skipn (Z.to_nat cap) junk)]).
          { eapply rw_cells_transport; [exact RWb | exact MU | exact WM |]. cbn. lia. }
          (* [comment removed for export] *)
          eapply (evt_realizes s0segs); [exact Hh' | exact Hl' | apply growC |].
          intros ms' ->.
          destruct (k_err m'' K2) as [e2 ERR2].
          eapply (at_free AT) with (s := s') (LB := (p, rr, cap') :: [(pb, bufA, cap)]) (p := pb) (A := bufA) (n := cap) (lo := spz - 8388608) (B := spz) (errv := e2);
            [ exact INV2 | exact TI' | reflexivity | right; left; reflexivity | exact AUX2
            | rewrite u64_lit by lia; lia | rewrite u64_lit by lia; exact (k_stk m'' K2) | exact ACS
            | rewrite u64_lit by lia; cbn [al_stack S0_layout]; lia | exact ERR2 | exact MI'' | reflexivity | reflexivity |].
          intros s3 m3 MD3 t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c INV3 TI3 VMO3 MI3 ST3 ERR3 AUX3 HP3.
          rewrite u64_lit in ST3, HP3 by lia. rewrite ret_pc_lit by lia.
          rewrite (lb_remove_pair p pb rr cap' bufA cap) in INV3, TI3, HP3 by (intros E; apply NIN; rewrite E; left; reflexivity).
          destruct (ai_inv_model AI INV3) as [Hh3 Hl3].
          pose proof (modelG_canon path stdin0 fs0 tid cap (m_vmmaps MD') MD3 VMO3 Hl3 (at_mat AT TI3)) as EMD3.
          rewrite EMD3 in INV3, TI3, Hh3, Hl3. rewrite EMD3.
          pose proof (kit_alloc _ _ _ _ K2 HP3 MI3 ST3 ERR3) as K3.
          assert (RWa3 : rw_cells s0segs m3 rr [CB (Z.to_nat cap) (pref cap content)]).
          { eapply pres_rw_cells; [exact (pres_of_heap_pres _ _ _ _ _ HP3) | exact RWd |]. cbn [cells_size csize Nat.add]. intros a Ha.
            right; right. exists (p, rr, cap'). split; [left; reflexivity|]. cbn. lia. }
          assert (RWb3 : rw_cells s0segs m3 (rr + cap) [CB (Z.to_nat cap) (skipn (Z.to_nat cap) junk)]).
          { eapply pres_rw_cells; [exact (pres_of_heap_pres _ _ _ _ _ HP3) | exact RWb2 |]. cbn [cells_size csize Nat.add]. intros a Ha.
            right; right. exists (p, rr, cap'). split; [left; reflexivity|]. cbn. lia. }
          (* [comment removed for export] *)
          rewrite MS_mkst.
          apply (mid_phase j rr p s3 (m_vmmaps MD3) _ m3 (skipn (Z.to_nat cap) junk)); try reflexivity.
          * lia. * exact Fcap. * exact INV3. * exact TI3. * exact AUX3. * exact K3. * exact RWa3. * exact RWb3.
          * intros HcL R' M' FS'. replace (Lc <? cap') with false by (symmetry; apply Z.ltb_ge; lia). apply (IH (j + 1) rr p s3); [lia | exact FS'].
          * intros HLc. replace (Lc <? cap') with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Definition FINAL : TSet := if Lc <? 2 ^ 26 then KT else TREF.

    Lemma SHF_norm : forall n j, Z.of_nat n = 10 - j -> 0 <= j -> cap_of j <= Lc -> (0 < n)%nat -> t_eq (SHF n j) FINAL.
    Proof.
      induction n as [|n IH]; intros j Hn Hj Hcap Hpos; [lia|]. cbn [SHF].
      pose proof (cap_of_le (j + 1) ltac:(lia)) as CL. pose proof (cap_of_succ j Hj) as CS.
      destruct (Z.ltb_spec Lc (cap_of (j + 1))) as [LT|GE].
      - unfold FINAL. replace (Lc <? 2 ^ 26) with true by (symmetry; apply Z.ltb_lt; lia). apply t_eq_refl.
      - destruct n as [|n'].
        + cbn [SHF]. assert (j = 9) by lia. subst j. change (cap_of (9 + 1)) with (2 ^ 26) in GE.
          unfold FINAL. replace (Lc <? 2 ^ 26) with false by (symmetry; apply Z.ltb_ge; lia). apply t_eq_refl.
        + apply (IH (j + 1)); lia.
    Qed.

    Lemma t_body_FINAL : t_body04 content fs0 = FINAL.
    Proof.
      unfold FINAL. destruct (Z.ltb_spec Lc (2 ^ 26)) as [LT|GE].
      - unfold KT. apply t_body_target; [unfold MAX_INPUT; unfold Lc in LT; lia|].
        pose proof (Z.mod_pos_bound (hdr_cfg content) 32768 ltac:(lia)). unfold Lc in HL. lia.
      - unfold t_body04, TREF, MAX_INPUT. replace (67108864 <=? Z.of_nat (length content)) with true by (symmetry; apply Z.leb_le; unfold Lc in GE; lia). reflexivity.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Lemma gw_mem_inv_of_pristine : forall m, img_pristine m 0x10000 0x32000 -> mem_inv s0segs m.
    Proof.
      intros m HP x b Hx. destruct (ro_addr s0segs x) eqn:E; [|reflexivity]. exfalso.
      pose proof (ro_addr_range x E) as R. pose proof (HP (bv_unsigned x) R) as N.
      unfold wa in N. rewrite Z_to_bv_bv_unsigned in N. congruence.
    Qed.

    Lemma gw_wr_at_img : forall m A (n : nat) bs,
      image_bytes s0segs A n = Some bs -> 0x32000 <= A -> A + Z.of_nat n <= 0x66000 -> wr_at s0segs m A (Z.of_nat n).
    Proof.
      intros m A n bs HI H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
      destruct (m (wa (A + i))) as [b|] eqn:E.
      - unfold wview. rewrite E. discriminate.
      - rewrite wview_rw_data_pristine; [| unfold rw_data; lia | exact E].
        replace (A + i) with (A + Z.of_nat (Z.to_nat i)) by lia.
        rewrite (image_bytes_nth n A bs (Z.to_nat i) HI) by lia.
        destruct (nth_error bs (Z.to_nat i)) eqn:N; [discriminate|].
        apply nth_error_None in N. pose proof (image_bytes_length s0segs n A bs HI). lia.
    Qed.

    Lemma gw_stk_all : forall M, stack_writable M sp0 -> stk s0segs M (spz - 8388608) spz.
    Proof.
      intros M SW. pose proof SP0 as [SPR _].
      pose proof (SW 0 (Z.to_nat 8388608) ltac:(lia) ltac:(lia)) as S. change (bv_unsigned sp0) with spz in S. rewrite Z.add_0_r in S.
      pose proof (stk_of_store_ok_off M (spz - 8388608) (Z.to_nat 8388608) ltac:(lia) ltac:(lia) ltac:(lia) S) as K.
      replace (spz - 8388608 + Z.of_nat (Z.to_nat 8388608)) with spz in K by lia. exact K.
    Qed.

    Lemma kit_of_world : forall (R : bvmap 5 word) M area brkv mas,
      read_pre sp0 p1 mb gm R M -> world0 area (bv_unsigned gm) brkv mas tidz hw M -> main_frame spz M -> kit M.
    Proof.
      intros R M area brkv mas RP W MF. pose proof SP0 as [SPR _].
      pose proof (gw_stk_all M (rp_stack _ _ _ _ _ _ RP)) as STALL.
      pose proof (w_img _ _ _ _ _ _ _ W) as IMG.
      assert (PR : forall lo hi, In (lo, hi) img_clear_ivs -> img_pristine M lo hi).
      { intros lo hi Hin a Ha. pose proof (proj1 (Forall_forall _ _) IMG _ Hin) as Cc. cbn in Cc. apply Cc. exact Ha. }
      assert (P1 : img_pristine M 0x10000 0x34090) by (apply PR; cbv; tauto).
      constructor.
      - exact (proj1 (stk_split s0segs M (spz - 8388608) (spz - 128) spz STALL ltac:(lia))).
      - eapply wr_at_of_stk; [exact STALL| lia| lia| lia].
      - apply gw_mem_inv_of_pristine. intros a Ha. apply P1. lia.
      - destruct (rp_errno _ _ _ _ _ _ RP) as [e He]. exists e. apply rw_cells_C4_of_rdn; [exact He|].
        change 4 with (Z.of_nat 4). eapply gw_wr_at_img; [solve_img| lia| lia].
      - constructor.
        + (* [comment removed for export] *)
          intros a Ha. cbn [in_ivs S_IVS] in Ha.
          assert (P2 : img_pristine M 0x34091 0x340d9) by (apply PR; cbv; tauto).
          assert (P2' : img_pristine M 0x440d9 0x44110) by (apply PR; cbv; tauto).
          assert (P3 : img_pristine M 0x441f8 0x641e8) by (apply PR; cbv; tauto).
          assert (P3' : img_pristine M 0x64220 0x64450) by (apply PR; cbv; tauto).
          assert (P4 : img_pristine M 0x64471 0x64478) by (apply PR; cbv; tauto).
          repeat (destruct Ha as [Ha|Ha];
            [first [apply P1; lia | apply P2; lia | apply P2'; lia | apply P3; lia | apply P3'; lia | apply P4; lia]|]).
          destruct Ha.
        + apply rw_cells_C4_of_rdn; [exact (w_tid _ _ _ _ _ _ _ W)|]. change 4 with (Z.of_nat 4). eapply gw_wr_at_img; [solve_img | lia | lia].
        + (* [comment removed for export] *)
          exists (Z_to_bv 64 run_guard). apply rw_cells_C8_of_rdn; [exact (w_canary _ _ _ _ _ _ _ W)|]. change 8 with (Z.of_nat 8). eapply gw_wr_at_img; [solve_img | lia | lia].
        + (* [comment removed for export] *)
          assert (P5 : img_pristine M 0x64890 0x66000) by (apply PR; cbv; tauto).
          unfold OFL.
          apply rw_cells_cons; [eapply rw_C4_pristine; [intros a Ha; apply P5; lia | lia | lia | solve_img | vm_compute; reflexivity] | cbn [csize]].
          replace (411792 + Z.of_nat 4) with 411796 by reflexivity.
          apply rw_cells_cons; [eapply rw_C4_pristine; [intros a Ha; apply P5; lia | lia | lia | solve_img | vm_compute; reflexivity] | cbn [csize]].
          replace (411796 + Z.of_nat 4) with 411800 by reflexivity.
          eapply rw_C8_pristine; [intros a Ha; apply P5; lia | lia | lia | solve_img | vm_compute; reflexivity].
        + (* [comment removed for export] *)
          destruct MF as [Mra Ms0 Ms1 Ms2 Ms3 Ms4 Ms5 Ms6 Ms7]. unfold S0World.cell in *.
          assert (WR : forall A, spz - 128 <= A -> A + 8 <= spz - 48 -> wr_at s0segs M A 8).
          { intros A HA HB. eapply wr_at_of_stk; [exact STALL | lia | lia | lia]. }
          destruct (stk_carve s0segs M (spz - 8388608) (spz - 120) 8
                      (proj1 (stk_split s0segs M (spz - 8388608) (spz - 120) spz STALL ltac:(lia))) ltac:(lia)) as [_ [junk8 JK]].
          replace (spz - 120 - Z.of_nat 8) with (spz - 128) in JK by lia.
          exists junk8.
          repeat match goal with
          | |- rw_cells _ _ ?A (?c :: ?rest) =>
              lazymatch rest with
              | [] => idtac
              | _ => change (c :: rest) with ([c] ++ rest); apply rw_cells_app; cbn [cells_size csize Nat.add]
              end
          end.
          1: exact JK.
          all: apply rw_cells_C8_of_rdn; [| apply WR; lia].
          all: first [ replace (spz - 128 + Z.of_nat 8) with (spz - 120) by lia; exact Ms7
                     | replace (spz - 128 + Z.of_nat 8 + Z.of_nat 8) with (spz - 112) by lia; exact Ms6
                     | replace (spz - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (spz - 104) by lia; exact Ms5
                     | replace (spz - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (spz - 96) by lia; exact Ms4
                     | replace (spz - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (spz - 88) by lia; exact Ms3
                     | replace (spz - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (spz - 80) by lia; exact Ms2
                     | replace (spz - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (spz - 72) by lia; exact Ms1
                     | replace (spz - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (spz - 64) by lia; exact Ms0
                     | replace (spz - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (spz - 56) by lia; exact Mra ].
      - intros a Ha. apply P1. unfold SO_FILE in Ha. lia.
      - split; [eapply incl_Forall; [apply gw_ivs_incl | exact IMG]|]. split; [exact (w_tid _ _ _ _ _ _ _ W)|]. split; [exact (w_self _ _ _ _ _ _ _ W)|].
        split; [exact (w_canary _ _ _ _ _ _ _ W)|]. split; [exact (w_pagesz _ _ _ _ _ _ _ W)| exact (w_lock80 _ _ _ _ _ _ _ W)].
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Lemma gw_target_vm : forall (VM : VmMaps) (area : Z),
      area = (bv_unsigned mb + 4096)%Z -> vm_pre VM mb gm -> vm_small6 VM gm -> target_vm (bv_unsigned gm) area VM.
    Proof.
      (intros VM area Harea; cps_intros (Pr & Pl & Ph & Pf & Pn & Plive & (q & Pin & Pne & Plo & Phi) & Pseps); cps_intros (Vr & Vl & Vn & Vin & Vf & Vs)).
      constructor.
      - exact Vr.
      - rewrite Z_to_bv_bv_unsigned. exact Vin.
      - exists (fst q), (snd q). destruct q as [lo sz]. cbn [fst snd] in *. split; [exact Pin|]. lia.
      - exact Vn.
      - exact Vf.
      - exact Vs.
      - exact Vl.
    Qed.

    Lemma big_file_run : forall (R : bvmap 5 word) (M : word -> option byte) (area brkv mas : Z) (VM : VmMaps),
      area = bv_unsigned mb + 4096 ->
      read_pre sp0 p1 mb gm R M -> world0 area (bv_unsigned gm) brkv mas tidz hw M -> main_frame spz M ->
      vm_pre VM mb gm -> vm_small6 VM gm -> target_vmx spz (bv_unsigned gm) area brkv mas VM -> auxv0 spz M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x135d4) M (seg_rom RSEGS)) (model_pre path VM stdin0 fs0 tid))
               (t_body04 content fs0).
    Proof.
      intros R M area brkv mas VM Harea RP W MF VP VS VX AX. pose proof SP0 as [SPR SPA]. pose proof alloc_ceiling_val as ACV.
      cps_pose (rp_gm _ _ _ _ _ _ RP) as (G1 & G2 & G3).
      set (gmz := bv_unsigned gm) in *.
      pose proof (kit_of_world R M area brkv mas RP W MF) as K0.
      cps_destruct (HE0W spz gmz area brkv mas tidz hw M VM (modelG 0 VM) W (conj (proj1 SPR) (proj2 SPR)) (gw_target_vm VM area Harea VP VS) VX AX
                  (atop_of_vmx _ _ _ _ _ _ VX ACV ltac:(lia)) eq_refl eq_refl eq_refl eq_refl) as (s & pb & INV & TI & AUX).
      (* [comment removed for export] *)
      rewrite t_body_FINAL. apply (rz_conseq RSEGS _ (SHF 10 0)); [| apply (SHF_norm 10 0); [reflexivity| lia| change (cap_of 0) with 65536; exact HL| lia]].
      (* [comment removed for export] *)
      apply realizes_to_mkR. unfold mkR_of.
      rewrite (rp_sp _ _ _ _ _ _ RP), (rp_gp _ _ _ _ _ _ RP), (rp_tp _ _ _ _ _ _ RP), (rp_a0 _ _ _ _ _ _ RP), (rp_s4 _ _ _ _ _ _ RP), (rp_s5 _ _ _ _ _ _ RP).
      change (bv_unsigned sp0) with spz. change (bv_unsigned gm) with gmz.
      change (model_pre path VM stdin0 fs0 tid) with (modelG 0 VM).
      eapply (evt_realizes s0segs); [reflexivity | reflexivity | apply grow0; lia |].
      intros ms' ->. rewrite MS_mkst.
      (* [comment removed for export] *)
      assert (GST : stk s0segs M (gmz + 32) (gmz + 32 + 65536)).
      { pose proof (rp_group _ _ _ _ _ _ RP 32 (Z.to_nat 65536) ltac:(lia) ltac:(lia)) as S. change (bv_unsigned gm) with gmz in S.
        pose proof (stk_of_store_ok_off M (gmz + 32) (Z.to_nat 65536) ltac:(lia) ltac:(lia) ltac:(lia) S) as X.
        replace (gmz + 32 + Z.of_nat (Z.to_nat 65536)) with (gmz + 32 + 65536) in X by lia. exact X. }
      cps_destruct (stk_bytes s0segs M (gmz + 32) (gmz + 32 + 65536) GST ltac:(lia)) as (junk & JL & JB).
      assert (B2 : rw_cells s0segs M (gmz + 32 + 0) [CB (Z.to_nat (65536 - 0)) junk]).
      { replace (gmz + 32 + 0) with (gmz + 32) by lia. split; [split; [cbn; split; [lia| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact JB]|].
        cbn [cells_size csize]. rewrite Nat.add_0_r. eapply wr_at_of_stk; [exact GST| lia| lia| lia]. }
      assert (B1 : rw_cells s0segs M (gmz + 32) [CB (Z.to_nat 0) (pref 0 content)]).
      { split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes pref Z.to_nat firstn app]; apply bytes_at_nil; lia]|].
        cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
      apply (chunk_loop_mid path content stdin0 fs0 tid VM Hfile (Z.to_nat 65536) _ M spz (gmz + 32) 0 65536 (SHF 10 0)); try lia.
      - repeat split; reflexivity.
      - apply (store_ok_of_stk M (spz - 8388608) (spz - 128)); [exact (k_stk M K0)| lia| cbn; lia].
      - apply (store_ok_of_stk M (gmz + 32) (gmz + 32 + 65536)); [exact GST| lia| lia].
      - (* [comment removed for export] *)
        (intros _ R' M'; cps_intros (P2 & P9 & P23 & P19 & PK); intros PM). destruct PM as [FM RD].
        assert (RS : Forall (fun q : Z * Z => 0 <= fst q < 2 ^ 64) [(spz - 136, 8); (gmz + 32 + 0, 65536 - 0); (READ_STAGE, 65536)]) by (unfold READ_STAGE; apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_nil).
        pose proof (munch_of_frame_mod _ M M' RS FM) as MU. cbn [ivs_of_regions] in MU. pose proof (wmono_of_frame_mod _ _ _ FM) as WM.
        apply (grow_full 10 0 (gmz + 32) pb s VM R' M'); [reflexivity|]. constructor; change (cap_of 0) with 65536.
        + lia.
        + exact HL.
        + exact P2.
        + rewrite (PK 3%bv) by (cbv; tauto). reflexivity.
        + rewrite (PK 4%bv) by (cbv; tauto). reflexivity.
        + exact P19.
        + rewrite (PK 20%bv) by (cbv; tauto). reflexivity.
        + rewrite (PK 21%bv) by (cbv; tauto). reflexivity.
        + rewrite (PK 22%bv) by (cbv; tauto). reflexivity.
        + exact P23.
        + eapply (ai_inv_model_frame AI (MD:=modelG 0 VM)); [| reflexivity| reflexivity].
          eapply (ai_inv_frame AI); [exact INV| exact MU| exact WM|].
          apply Forall_cons; [apply cwo_stack; pose proof alloc_ceiling_sp; lia|]. apply Forall_cons; [apply cwo_block; lia|]. apply Forall_cons; [apply cwo_stage| apply Forall_nil].
        + eapply (at_model_frame AT (MD:=modelG 0 VM)); [exact TI| reflexivity| reflexivity].
        + eapply (ai_aux_frame AI); [exact AUX| exact MU| exact WM|].
          apply Forall_cons; [cbn; split; [lia| unfold S0_static; intros; lia]|]. apply Forall_cons; [cbn; split; [lia| unfold S0_static; intros; lia]|]. apply Forall_cons; [unfold READ_STAGE; cbn; split; [lia| unfold S0_static; intros; lia]| apply Forall_nil].
        + eapply (kit_read M M' (gmz + 32 + 0) (65536 - 0)); [exact K0| exact FM| lia| lia| lia].
        + change (cap_of 0) with 65536. eapply (buf_after_read M M' (gmz + 32) 0 65536 junk); [lia| lia| lia| lia| exact B1| exact B2| split; [exact FM| exact RD]].
      (* [comment removed for export] *)
    Qed.
  End Run.

  Theorem big_file_cps : big_file_stmt.
  Proof.
    intros sp0 p1 mb gm R M area brkv mas hw VM path content stdin0 fs0 tid Hfile HL Harea RP W MF VP VS VX AX ACV.
    apply (big_file_run sp0 p1 mb gm tid path content stdin0 fs0 Hfile HL (rp_sp0 _ _ _ _ _ _ RP) (w_tidr _ _ _ _ _ _ _ W) hw (w_ghs _ _ _ _ _ _ _ W) ACV
             R M area brkv mas VM Harea RP W MF VP VS VX AX).
  Qed.
End Grow.

End ACeilS1.
