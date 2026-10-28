(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_membuffer_assign H_membuffer_destroy H_obj H_freelist H_httpheader_free H_ListAddTail HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition ListDestroy_entry := 0x16178%Z.
Ltac sstep := step; fix_lit_store.
Ltac lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.

Notation DFRc m q j s5 s4 s3 s2 s1 s0 ra := (rw_cells rsegs m q [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Notation FFc m L ffree fcmp := (rw_cells rsegs m (L + 80) [C8 (wz ffree); C8 (wz fcmp)]).

Notation LSTx L cur x1 q gp tp t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc pc mm :=
  (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz L) x9 a0 a1 a2 a3 a4 a5 a6 a7 (wz (L + 56)) s3 (wz (L + 24)) (wz cur) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (wz pc) fc None mm (seg_rom rsegs)).
Notation LST L cur x1 q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc pc mm :=
  (LSTx L cur x1 q gp tp t0 t1 t2 (wz 1) a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc pc mm).

Lemma dseg_entry : forall (lo L first last size : Z) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 64 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m L (lhead_cells first last size) -> (bv_unsigned sp <= L)%Z -> (L + 96 < 2^64)%Z -> (0 <= first < 2^64)%Z ->
  (L mod 8 = 0)%Z ->
  evt rsegs (fun ms' => exists m' j,
      ms' = LSTx L first ra (bv_unsigned sp + -64) gp tp t0 t1 t2 (if first =? L + 24 then s1 else wz 1) (wz 0) (wz 1) a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
              (if first =? L + 24 then 0x1623c else 0x161c4) m'
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -64) /\ DFRc m' (bv_unsigned sp + -64) j s5 s4 s3 s2 s1 s0 ra
      /\ rw_cells rsegs m' L (lhead_cells first last size))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz L) (wz 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ListDestroy_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI LC LLO LHI FR0 AL. unfold ListDestroy_entry, lhead_cells in *.
  pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 64%nat ST.
  uwalk_ub_to 0x161b4%Z. step. if_cases K1; zify_cond K1.
  - replace (first =? L + 24) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite land7_mod8, AL.
    apply evt_done. do 2 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact LC.
  - uwalk_ub_to 0x161c4%Z.
    replace (first =? L + 24) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite land7_mod8, AL.
    apply evt_done. do 2 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact LC.
Qed.

Definition unlink_post (lo L N next it last size : Z) (nextnode : option (Z * Z)) (q : Z) (gp tp : word)
    (t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (wz 0x16214) (wz q) gp tp t0 t1 t2 (wz L) (wz 1) (wz (L + 56)) (wz N) (wz next) (wz 0) a4 a5 a6 a7 (wz (L + 56)) (wz it) (wz (L + 24)) (wz next) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz FreeListFree_entry) fc None m' (seg_rom rsegs)
    /\ munch ((L, L + 56) :: match nextnode with None => [] | Some _ => [(next, next + 24)] end)%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' L (lhead_cells next (match nextnode with None => L | Some _ => last end) size)
    /\ rw_cells rsegs m' N (node_cells L next it)
    /\ match nextnode with None => True | Some (nx2, it2) => rw_cells rsegs m' next (node_cells L nx2 it2) end.

Lemma dseg_unlink : forall (lo L N next it last size : Z) (nextnode : option (Z * Z)) (q : Z) gp tp
    t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
  mem_inv rsegs m ->
  rw_cells rsegs m L (lhead_cells N last size) -> (lo <= L)%Z -> (L + 96 < 2^64)%Z -> (0 <= size < 2^63)%Z -> (0 <= last < 2^64)%Z ->
  rw_cells rsegs m N (node_cells L next it) -> (16 <= N)%Z -> (N + 24 <= lo)%Z -> (0 <= it < 2^64)%Z ->
  (L mod 8 = 0)%Z -> (N mod 8 = 0)%Z -> (next mod 8 = 0)%Z ->
  match nextnode with
  | None => next = L + 24
  | Some (nx2, it2) => rw_cells rsegs m next (node_cells N nx2 it2) /\ (16 <= next)%Z /\ (next + 24 <= lo)%Z
                      /\ (N + 24 <= next \/ next + 24 <= N)%Z /\ (0 <= nx2 < 2^64)%Z /\ (0 <= it2 < 2^64)%Z
  end ->
  evt rsegs (unlink_post lo L N next it last size nextnode q gp tp t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m)
    (LST L N x1 q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0x161c4 m).
Proof.
  intros until m. intros MI LC LLO LHI SZ LASTR NC N16 NHI ITR AL NAL XAL NXH. unfold lhead_cells, node_cells in *.
  pose proof (munch_refl ((L, L + 56) :: match nextnode with None => [] | Some _ => [(next, next + 24)] end)%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct nextnode as [[nx2 it2]|].
  - destruct NXH as (NXC & X16 & XHI & DJ & NX2R & IT2R). cbn [munch] in MU.
    uwalk_ub_to 0x16210%Z. step.
    rewrite land7_mod8, XAL.
    apply evt_done. unfold unlink_post, lhead_cells, node_cells. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  - subst next. cbn [munch] in MU.
    uwalk_ub_to 0x16210%Z. step.
    rewrite land7_mod8, XAL.
    apply evt_done. unfold unlink_post, lhead_cells, node_cells. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact I.
Qed.

Lemma dseg_callff : forall (L cur first last size ffree fcmp it : Z) (q : Z) gp tp
    t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
  mem_inv rsegs m ->
  rw_cells rsegs m L (lhead_cells first last size) -> FFc m L ffree fcmp -> (0 < L /\ L + 96 < 2^64)%Z -> (1 <= size < 2^63)%Z ->
  (0 < ffree < 2^63)%Z -> ffree mod 2 = 0 -> (0 <= it < 2^64)%Z ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (wz 0x16238) (wz q) gp tp t0 t1 t2 (wz L) (wz 1) (wz it) (wz ffree) a2 a3 a4 a5 a6 a7 (wz (L + 56)) (wz it) (wz (L + 24)) (wz cur) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz ffree) fc None m' (seg_rom rsegs)
      /\ munch [(L + 48, L + 56)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' L (lhead_cells first last (size - 1)) /\ FFc m' L ffree fcmp)
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz L) (wz 1) a0 a1 a2 a3 a4 a5 a6 a7 (wz (L + 56)) (wz it) (wz (L + 24)) (wz cur) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16214) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI LC FF LR SZ FR FEV ITR. unfold lhead_cells in *.
  pose proof (munch_refl [(L + 48, L + 56)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  uwalk_ub_to 0x1621c%Z. step. ubr_by ltac:(rewrite ?signed_lit in KU by lia; lia).
  uwalk_lia_to 0x16234%Z. step. rewrite ret_pc_even by lia.
  apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact FF.
Qed.

Lemma dseg_next : forall (L cur : Z) (q : Z) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
  (0 <= cur < 2^64)%Z -> (0 <= L /\ L + 96 < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = LST L cur x1 q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                                    (if cur =? L + 24 then 0x1623c else 0x161c4) m)
    (LST L cur x1 q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0x16238 m).
Proof.
  intros until m. intros CR LR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. if_cases K1; zify_cond K1.
  - replace (cur =? L + 24) with true by (symmetry; apply Z.eqb_eq; lia). apply evt_done. reflexivity.
  - replace (cur =? L + 24) with false by (symmetry; apply Z.eqb_neq; lia). apply evt_done. reflexivity.
Qed.

Lemma dseg_exit : forall (L first last size : Z) (q : Z) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x9 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
  mem_inv rsegs m -> rw_cells rsegs m L (lhead_cells first last size) -> (0 < L /\ L + 96 < 2^64)%Z ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (wz 0x16248) (wz q) gp tp t0 t1 t2 (wz L) x9 (wz (L + 56)) a1 a2 a3 a4 a5 a6 a7 (wz (L + 56)) s3 (wz (L + 24)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz FreeListDestroy_entry) fc None m' (seg_rom rsegs)
      /\ munch [(L + 48, L + 56)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' L (lhead_cells first last 0))
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz L) x9 a0 a1 a2 a3 a4 a5 a6 a7 (wz (L + 56)) s3 (wz (L + 24)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x1623c) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI LC LR. unfold lhead_cells, FreeListDestroy_entry in *.
  pose proof (munch_refl [(L + 48, L + 56)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  sstep. zstep. zstep. apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact LC.
Qed.

Lemma dseg_ret : forall (lo : Z) (j : list byte) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x8 x9 x18 x19 x20 x21
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -64) -> (lo + 64 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  DFRc m (bv_unsigned sp + -64) j s5 s4 s3 s2 s1 s0 ra ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom rsegs) /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16248) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR. pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. do 7 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
  apply evt_done. split; [reflexivity| exact ST].
Qed.

Section IDS.
Context {HCEIL : HasCeiling}.
  Context {K : Type}.
  Notation BLK := (block K).
  Definition idj (A B : list BLK) : Prop := forall a b, In a A -> In b B -> blk_id a <> blk_id b.
  #[using="Type"] Lemma idj_sym : forall A B, idj A B -> idj B A.
  Proof. intros A B H a b Ha Hb E. exact (H b a Hb Ha (eq_sym E)). Qed.
  #[using="Type"] Lemma idj_app_l : forall A B C, idj (A ++ B) C <-> idj A C /\ idj B C.
  Proof.
    intros A B C. unfold idj. split.
    - intros H. split; intros a b Ha Hb; apply H; auto; apply in_or_app; auto.
    - intros [H1 H2] a b Ha Hb. apply in_app_or in Ha. destruct Ha; [eapply H1| eapply H2]; eauto.
  Qed.
  #[using="Type"] Lemma idj_app_r : forall A B C, idj A (B ++ C) <-> idj A B /\ idj A C.
  Proof.
    intros A B C. split.
    - intros H. split; apply idj_sym; apply idj_sym in H; apply idj_app_l in H; LiaTuning.ctauto.
    - intros [H1 H2]. apply idj_sym. apply idj_app_l. split; apply idj_sym; assumption.
  Qed.
  #[using="Type"] Lemma idj_cons_l : forall a B C, idj (a :: B) C <-> idj [a] C /\ idj B C.
  Proof. intros a B C. change (a :: B) with ([a] ++ B). apply idj_app_l. Qed.
  #[using="Type"] Lemma idj_cons_r : forall A b C, idj A (b :: C) <-> idj A [b] /\ idj A C.
  Proof. intros A b C. change (b :: C) with ([b] ++ C). apply idj_app_r. Qed.
  #[using="Type"] Lemma idj_sub_l : forall A A' B, idj A B -> (forall x, In x A' -> In x A) -> idj A' B.
  Proof. intros A A' B H S a b Ha Hb. apply H; auto. Qed.
  #[using="Type"] Lemma idj_sub_r : forall A B B', idj A B -> (forall x, In x B' -> In x B) -> idj A B'.
  Proof. intros A B B' H S a b Ha Hb. apply H; auto. Qed.

  #[using="Type"] Lemma nd_app : forall (A B : list BLK), NoDup (map blk_id (A ++ B)) <-> NoDup (map blk_id A) /\ idj A B /\ NoDup (map blk_id B).
  Proof.
    intros A B. rewrite map_app, list.NoDup_app. unfold idj. split.
    - intros (N1 & D & N2). split; [exact N1|]. split; [| exact N2].
      intros a b Ha Hb E. apply (D (blk_id a)); [apply base.list_elem_of_In; apply in_map; exact Ha|].
      rewrite E. apply base.list_elem_of_In. apply in_map. exact Hb.
    - intros (N1 & D & N2). split; [exact N1|]. split; [| exact N2].
      intros x Hx Hx2. apply base.list_elem_of_In in Hx. apply base.list_elem_of_In in Hx2.
      apply in_map_iff in Hx. destruct Hx as (a & <- & Ha). apply in_map_iff in Hx2. destruct Hx2 as (b & E & Hb).
      exact (D a b Ha Hb (eq_sym E)).
  Qed.
  #[using="Type"] Lemma nd_cons : forall (a : BLK) B, NoDup (map blk_id (a :: B)) <-> idj [a] B /\ NoDup (map blk_id B).
  Proof.
    intros a B. change (a :: B) with ([a] ++ B). rewrite nd_app. split; [LiaTuning.ctauto|]. intros [H1 H2]. split; [| LiaTuning.ctauto].
    cbn. constructor; [| constructor]. intros X. apply base.list_elem_of_In in X. exact X.
  Qed.
  #[using="Type"] Lemma idj_neq : forall A B a b, idj A B -> In a A -> In b B -> a <> b.
  Proof. intros A B a b H Ha Hb ->. exact (H b b Ha Hb eq_refl). Qed.
End IDS.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation lbrm k LB := (lb_remove (ai_K_eqb rsegs AI) k LB).
  Hypothesis LOK : layout_ok AI.
  Hypothesis FREEPC : al_free_pc L_ = 0x17fb0.
  Notation bsub := (bsub AI).
  Notation dlseg := (dlseg AI).
  Notation flseg := (flseg AI).
  Notation hd_addr := (hd_addr AI).
  Notation last_addr := (last_addr AI).
  Notation hdrs_mem := (hdrs_mem AI).
  Notation hdrs_blocks := (hdrs_blocks AI).
  Notation hblocks := (hblocks AI).

  Definition ListDestroy_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LBK : list BLK) (L fcmp lo B : Z) (m : mem) : ai_PS rsegs AI -> list BLK -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp (wz (al_tp L_)) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ RENV rsegs AI m' B
      /\ (exists errv', rw_cells rsegs m' (al_errno L_) [C4 errv'])
      /\ hpx AI [(L, L + 80)] LBK (bv_unsigned sp) m m'
      /\ RHEAP rsegs AI s' LB' m' /\ bsub LBK LB'
      /\ rw_cells rsegs m' L (lhead_cells (L + 24) L 0) /\ rw_cells rsegs m' (L + 56) (fl_cells 0 0)
      /\ FFc m' L httpheader_free_entry fcmp.

  Section LOOP.
    Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (LBK : list BLK) (L fcmp lo B : Z) (m0 : mem).
    Hypothesis SPB : (bv_unsigned sp <= B)%Z.
    Hypothesis BHI : (B < 2^64)%Z.
    Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
    Hypothesis LO : (lo <= bv_unsigned sp - 96 - al_stack L_)%Z.
    Hypothesis STK : (0 <= al_stack L_)%Z.
    Hypothesis LLO : (bv_unsigned sp <= L)%Z.
    Hypothesis LB96 : (L + 96 <= B)%Z.
    Hypothesis FCMP : (0 <= fcmp < 2^64)%Z.
    Hypothesis LAL : (L mod 8 = 0)%Z.

    Notation q := (bv_unsigned sp + -64)%Z.
    Notation POST := (ListDestroy_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBK L fcmp lo B m0).

    #[using="AC LOK FREEPC SPB BHI CEIL LO STK LLO LB96 FCMP LAL"] Lemma ld_exit : forall (FB : list BLK) (flh fk size : Z) s LB m (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x9 x19 t3 t4 t5 t6 x1 : word) (j : list byte) (errv : word),
      rw_cells rsegs m L (lhead_cells (L + 24) L size) -> (0 <= size < 2^63)%Z ->
      rw_cells rsegs m (L + 56) (fl_cells flh fk) -> flseg m FB flh -> fk = zlength FB -> (fk <= 99)%Z ->
      FFc m L httpheader_free_entry fcmp ->
      bsub (FB ++ LBK) LB -> NoDup (map blk_id (FB ++ LBK)) ->
      RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> stk rsegs m lo q ->
      rw_cells rsegs m (al_errno L_) [C4 errv] -> mem_inv rsegs m ->
      DFRc m q j s5 s4 s3 s2 s1 s0 ra ->
      hpx AI [(L, L + 80)]%Z LBK (bv_unsigned sp) m0 m ->
      SREACH AI POST
        (MS (mkR x1 (wz q) gp (wz (al_tp L_)) t0 t1 t2 (wz L) x9 a0 a1 a2 a3 a4 a5 a6 a7 (wz (L + 56)) x19 (wz (L + 24)) (wz (L + 24)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz 0x1623c) fc None m (seg_rom rsegs)) s LB.
    Proof.
      intros until errv. intros LC SZ FLC FLS FK FK99 FF ASUB ND HR HE ST ERR MI FR HP0.
      pose proof (word_lt64 sp) as SPR. unfold zlength in *.
      destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
      pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
      apply (bsub_app AI) in ASUB. destruct ASUB as [FSUB KSUB].
      eapply sreach_evt. { eapply (dseg_exit L (L + 24) L size); try eassumption; lia. }
      intros ms' (m1 & -> & MU1 & WM1 & MI1 & LC1).
      assert (HR1 : RHEAP rsegs AI s LB m1).
      { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
      assert (HE1 : RENV rsegs AI m1 B).
      { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
      pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
      pose proof (rw_cells_transport rsegs _ m m1 _ _ FLC MU1 WM1 ltac:(cbn; lia)) as FLC1.
      pose proof (rw_cells_transport rsegs _ m m1 _ _ FF MU1 WM1 ltac:(cbn; lia)) as FF1.
      pose proof (rw_cells_transport rsegs _ m m1 _ _ FR MU1 WM1 ltac:(cbn; lia)) as FR1.
      assert (ST1 : stk rsegs m1 lo q) by (eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| cbn; lia]).
      assert (FLS1 : flseg m1 FB flh).
      { eapply (flseg_transport AI); [exact FLS| exact MU1| exact WM1|]. intros b Hb.
        destruct (flseg_shape AI _ _ _ _ FLS Hb) as [Eb _]. destruct (ai_block_range rsegs AI _ _ _ _ HR (FSUB b Hb)) as (Q1 & _ & _ & Q4 & _).
        rewrite Eb in Q4. cbn in Q1, Q4 |- *. lia. }
      assert (HP1 : hpx AI [(L, L + 80)]%Z LBK (bv_unsigned sp) m0 m1).
      { eapply (hpx_trans rsegs AI); [exact HP0|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact KSUB| exact MU1| exact WM1|].
        constructor; [| constructor]. right; right. cbn. lia. }
      eapply sreach_bind.
      { eapply (FreeListDestroy_spec AI AC LOK FREEPC) with (lo := lo) (B := B) (LBK := LBK) (FB := FB);
          try eassumption; rewrite ?unsigned_lit by lia; try lia; try eassumption; reflexivity. }
      intros s2' LB2 ms2 P. unfold FreeListDestroy_post in P. destruct_exs P.
      destruct P as (-> & MI2 & ST2 & HE2 & [e2 ERR2] & HP2 & HR2 & KSUB2 & FLC2).
      rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HP2 by lia.
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      replace (ret_pc (Z_to_bv 64 0x16248)) with (Z_to_bv 64 0x16248) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP2 FR1 ltac:(apply client_range_above; lia) ltac:(cbn; lia)) as FR2.
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP2 LC1 ltac:(apply client_range_above; lia) ltac:(cbn; lia)) as LC2.
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP2 FF1 ltac:(apply client_range_above; lia) ltac:(cbn; lia)) as FF2.
      eapply sreach_evt. { eapply (dseg_ret lo); try eassumption; lia. }
      intros ms' [-> ST3]. apply sreach_ret. unfold ListDestroy_post.
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST3|]. split; [exact HE2|]. split; [eexists; exact ERR2|]. split.
      { eapply (hpx_trans rsegs AI); [exact HP1|]. eapply (hpx_weaken rsegs AI); [exact HP2| | lia| auto].
        unfold sub_fp. cbn. intros y [Hy _]. lia. }
      split; [exact HR2|]. split; [exact KSUB2|]. split; [exact LC2|]. split; [exact FLC2| exact FF2].
    Qed.

    #[using="AC LOK FREEPC SPB BHI CEIL LO STK LLO LB96 FCMP LAL"] Lemma ld_loop : forall (ns : list (BLK * Z)) (hs : list (hdr AI)) (FB : list BLK) (flh fk : Z) s LB m
        (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 x1 : word) (j : list byte) (errv : word),
      ns <> [] -> dlseg m ns L (L + 24) -> hdrs_mem m hs -> map snd ns = map (hA AI) hs ->
      rw_cells rsegs m L (lhead_cells (hd_addr ns (L + 24)) (last_addr ns L) (zlength ns)) -> (zlength ns < 2^40)%Z ->
      rw_cells rsegs m (L + 56) (fl_cells flh fk) -> flseg m FB flh -> fk = zlength FB -> (fk <= 99)%Z ->
      FFc m L httpheader_free_entry fcmp ->
      bsub (map fst ns ++ hdrs_blocks hs ++ FB ++ LBK) LB -> NoDup (map blk_id (map fst ns ++ hdrs_blocks hs ++ FB ++ LBK)) ->
      RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> stk rsegs m lo q ->
      rw_cells rsegs m (al_errno L_) [C4 errv] -> mem_inv rsegs m ->
      DFRc m q j s5 s4 s3 s2 s1 s0 ra ->
      hpx AI [(L, L + 80)]%Z LBK (bv_unsigned sp) m0 m ->
      SREACH AI POST
        (LST L (hd_addr ns (L + 24)) x1 q gp (wz (al_tp L_)) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0x161c4 m) s LB.
    Proof.
      induction ns as [|[bN it] ns IH]; intros until errv; intros NNE DL HS ITEMS LC LEN FLC FLS FK FK99 FF ASUB ND HR HE ST ERR MI FR HP0; [congruence|].
      destruct hs as [|h hs]; [discriminate|]. cbn [map] in ITEMS. injection ITEMS as ITEM ITEMS'.
      pose proof (word_lt64 sp) as SPR. unfold zlength in *.
      change (length ((bN, it) :: ns)) with (S (length ns)) in *. rewrite !Nat2Z.inj_succ in *.
      destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
      pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
      cbn [H_obj.dlseg] in DL. destruct DL as (SZ & NZ & NT & ITR & NC & DL').
      pose proof HS as HS0. cbn [H_obj.hdrs_mem] in HS. destruct HS as (HM & HPU & HS').
      set (N := blk_addr bN) in *.

      change (map fst ((bN, it) :: ns)) with ([bN] ++ map fst ns) in ASUB, ND.
      change (hdrs_blocks (h :: hs)) with (hblocks h ++ hdrs_blocks hs) in ASUB, ND.
      rewrite <- !app_assoc in ND. rewrite <- !app_assoc in ASUB.
      apply (bsub_app AI) in ASUB. destruct ASUB as [NSUBb REST]. apply (bsub_app AI) in REST. destruct REST as [NSUB REST].
      apply (bsub_app AI) in REST. destruct REST as [HhSUB REST]. apply (bsub_app AI) in REST. destruct REST as [HsSUB REST].
      apply (bsub_app AI) in REST. destruct REST as [FSUB KSUB].
      pose proof (NSUBb bN (or_introl eq_refl)) as NIN.
      apply nd_app in ND. destruct ND as (_ & J0 & ND). apply nd_app in ND. destruct ND as (NDn & J1 & ND).
      apply nd_app in ND. destruct ND as (NDHh & J2 & ND). apply nd_app in ND. destruct ND as (NDhs & J3 & ND).
      apply nd_app in ND. destruct ND as (NDF & J4 & NDK).
      apply idj_app_r in J0. destruct J0 as [J0n J0]. apply idj_app_r in J0. destruct J0 as [J0Hh J0]. apply idj_app_r in J0. destruct J0 as [J0hs J0].
      apply idj_app_r in J0. destruct J0 as [J0F J0K].
      apply idj_app_r in J1. destruct J1 as [J1Hh J1]. apply idj_app_r in J1. destruct J1 as [J1hs J1]. apply idj_app_r in J1. destruct J1 as [J1F J1K].
      apply idj_app_r in J2. destruct J2 as [J2hs J2]. apply idj_app_r in J2. destruct J2 as [J2F J2K].
      apply idj_app_r in J3. destruct J3 as [J3F J3K].

      assert (BR : forall b, In b LB -> (0 < blk_addr b)%Z /\ blk_addr b mod 16 = 0 /\ (0 <= blk_size b)%Z /\ (blk_addr b + blk_size b <= alloc_ceiling)%Z).
      { intros b Hb. destruct (ai_block_range rsegs AI _ _ _ _ HR Hb) as (R1 & R2 & R3 & R4 & _). auto. }
      destruct (BR bN NIN) as (N0 & NAL & _ & NHI). fold N in N0, NAL, NHI. rewrite SZ in NHI.
      assert (N16 : (16 <= N)%Z) by (Z.div_mod_to_equations; lia).
      assert (NAL8 : (N mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
      assert (TAL : ((L + 24) mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
      assert (NK : bN = (blk_id bN, N, 24)) by (destruct bN as [[kk aa] zz]; cbn in SZ |- *; subst; reflexivity).
      cbn [H_obj.hd_addr] in LC |- *. fold N in LC |- *.
      assert (NODES : forall b0 it0, In (b0, it0) ns -> In b0 LB /\ blk_size b0 = 24 /\ (16 <= blk_addr b0)%Z /\ (blk_addr b0 + 24 <= alloc_ceiling)%Z /\ (N + 24 <= blk_addr b0 \/ blk_addr b0 + 24 <= N)%Z).
      { intros b0 it0 H0. destruct (dlseg_facts AI _ _ _ _ _ _ DL' H0) as (SZ0 & _). pose proof (in_map fst _ _ H0) as H0'. cbn [fst] in H0'.
        pose proof (NSUB _ H0') as B0IN. destruct (BR b0 B0IN) as (B0P & B0AL & _ & B0HI). rewrite SZ0 in B0HI.
        pose proof (idj_neq _ _ _ _ J0n (or_introl eq_refl) H0') as NE.
        destruct (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR NIN B0IN NE) as [D|D]; fold N in D; rewrite ?SZ, ?SZ0 in D;
          (split; [exact B0IN|]; split; [exact SZ0|]; split; [Z.div_mod_to_equations; lia|]; split; [lia| lia]). }
      assert (FBF : forall b, In b FB -> In b LB /\ blk_size b = 24 /\ (16 <= blk_addr b)%Z /\ (blk_addr b + 24 <= alloc_ceiling)%Z).
      { intros b Hb. destruct (flseg_shape AI _ _ _ _ FLS Hb) as [Eb _]. pose proof (FSUB b Hb) as HbL.
        destruct (BR b HbL) as (Q1 & Q2 & _ & Q4). assert (SZb : blk_size b = 24) by (rewrite Eb; reflexivity). rewrite SZb in Q4.
        split; [exact HbL|]. split; [exact SZb|]. split; [Z.div_mod_to_equations; lia| lia]. }
      assert (HREG : forall h0 A n, In h0 (h :: hs) -> In (A, n) (hregions AI h0) ->
                exists k, In (k, A, n) LB /\ In (k, A, n) (hblocks h ++ hdrs_blocks hs) /\ (16 <= A)%Z /\ (A + n <= alloc_ceiling)%Z /\ (0 <= n)%Z).
      { intros h0 A n Hh HA. destruct (hregion_block AI h0 A n HA) as [k Hk]. exists k.
        pose proof (in_hdrs_blocks AI _ _ _ Hh Hk) as HB. change (In (k, A, n) (hblocks h ++ hdrs_blocks hs)) in HB.
        assert (HbL : In (k, A, n) LB) by (apply in_app_or in HB; destruct HB as [HB|HB]; [apply HhSUB| apply HsSUB]; exact HB).
        destruct (BR _ HbL) as (Q1 & Q2 & Q3 & Q4). cbn in Q1, Q2, Q3, Q4.
        split; [exact HbL|]. split; [exact HB|]. split; [Z.div_mod_to_equations; lia| lia]. }
      assert (LASTR : (0 <= last_addr ns N < 2^64)%Z).
      { assert (G : forall nsx pv, (0 <= pv < 2^64)%Z -> (forall b it, In (b, it) nsx -> In (b, it) ns) -> (0 <= last_addr nsx pv < 2^64)%Z).
        { induction nsx as [|[b0 it0] nsx IHx]; intros pv Hpv Hsub; cbn; [exact Hpv|]. apply IHx.
          - destruct (NODES b0 it0 (Hsub _ _ (or_introl eq_refl))) as (_ & _ & ? & ? & _). lia.
          - intros b1 it1 H1. apply Hsub. right. exact H1. }
        apply G; [lia| auto]. }

      assert (CONT : forall m1 (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        dlseg m1 ns L (L + 24) -> hdrs_mem m1 (h :: hs) ->
        rw_cells rsegs m1 L (lhead_cells (hd_addr ns (L + 24)) (last_addr ns L) (Z.succ (Z.of_nat (length ns)))) ->
        rw_cells rsegs m1 (L + 56) (fl_cells flh fk) -> flseg m1 FB flh -> FFc m1 L httpheader_free_entry fcmp ->
        RHEAP rsegs AI s LB m1 -> RENV rsegs AI m1 B -> stk rsegs m1 lo q -> rw_cells rsegs m1 (al_errno L_) [C4 errv] -> mem_inv rsegs m1 ->
        DFRc m1 q j s5 s4 s3 s2 s1 s0 ra -> rw_cells rsegs m1 N (node_cells L (hd_addr ns (L + 24)) it) ->
        hpx AI [(L, L + 80)]%Z LBK (bv_unsigned sp) m0 m1 ->
        SREACH AI POST
          (MS (mkR (wz 0x16214) (wz q) gp (wz (al_tp L_)) t0' t1' t2' (wz L) (wz 1) (wz (L + 56)) (wz N) a2' a3' a4' a5' a6' a7' (wz (L + 56)) (wz it) (wz (L + 24)) (wz (hd_addr ns (L + 24))) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (wz FreeListFree_entry) fc None m1 (seg_rom rsegs)) s LB).
      { intros m1 t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' DL1 HS1 LC1 FLC1 FLS1 FF1 HR1 HE1 ST1 ERR1 MI1 FR1 NC1 HP1.
        set (k := blk_id bN) in *.

        assert (OURS : forall b0, In b0 (map fst ns ++ (hblocks h ++ hdrs_blocks hs) ++ FB) -> In b0 (lbrm k LB)).
        { intros b0 H0. apply (in_lb_remove AI).
          - rewrite !in_app_iff in H0. destruct H0 as [H0|[[H0|H0]|H0]]; [apply NSUB| apply HhSUB| apply HsSUB| apply FSUB]; exact H0.
          - apply not_eq_sym. unfold k. rewrite !in_app_iff in H0.
            destruct H0 as [H0|[[H0|H0]|H0]]; [eapply J0n| eapply J0Hh| eapply J0hs| eapply J0F]; try (left; reflexivity); exact H0. }
        assert (KEEPk : forall b0, In b0 LBK -> In b0 (lbrm k LB)).
        { intros b0 H0. apply (in_lb_remove AI); [apply KSUB; exact H0|]. apply not_eq_sym. eapply J0K; [left; reflexivity| exact H0]. }

        eapply sreach_bind.
        { rewrite NK in NIN. eapply (FreeListFree_spec AI AC LOK FREEPC) with (lo := lo) (B := B) (FB := FB) (k := k);
            try eassumption; rewrite ?unsigned_lit by lia; try lia; try eassumption; try reflexivity.
          apply nd_cons. split; [| exact NDF]. eapply idj_sub_l; [exact J0F|]. intros x [<-|[]]. rewrite <- NK. left. reflexivity. }
        intros s2' LB2 ms2 P. unfold FreeListFree_post in P. destruct_exs P.
        destruct P as (-> & MI2 & ST2 & HE2 & [e2 ERR2] & HP2 & HR2 & SUB2 & FLC2 & FLS2 & FK2 & FK2' & FSUB2 & NDF2 & CASES2).
        rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HP2 by lia.
        lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
        lazymatch type of FLC2 with rw_cells _ _ _ (fl_cells ?a ?b) => rename a into flh2; rename b into fk2 end.
        lazymatch type of FLS2 with H_obj.flseg _ _ ?fb _ => rename fb into FB2 end.
        replace (ret_pc (Z_to_bv 64 0x16214)) with (Z_to_bv 64 0x16214) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

        assert (FB2F : forall b, In b FB2 -> b = (k, N, 24) \/ In b FB).
        { intros b Hb. destruct CASES2 as [[-> ->]|[-> ->]]; [destruct Hb as [<-|Hb]; [left; reflexivity| right; exact Hb]| right; exact Hb]. }
        assert (JF2K : idj FB2 LBK).
        { intros a b Ha Hb. destruct (FB2F a Ha) as [->|Ha']; [cbn; unfold k; eapply J0K; [left; reflexivity| exact Hb]| exact (J4 a b Ha' Hb)]. }
        assert (JF2n : idj FB2 (map fst ns)).
        { intros a b Ha Hb. destruct (FB2F a Ha) as [->|Ha']; [cbn; unfold k; eapply J0n; [left; reflexivity| exact Hb]| exact (idj_sym _ _ J1F a b Ha' Hb)]. }
        assert (JF2Hh : idj FB2 (hblocks h)).
        { intros a b Ha Hb. destruct (FB2F a Ha) as [->|Ha']; [cbn; unfold k; eapply J0Hh; [left; reflexivity| exact Hb]| exact (idj_sym _ _ J2F a b Ha' Hb)]. }
        assert (JF2hs : idj FB2 (hdrs_blocks hs)).
        { intros a b Ha Hb. destruct (FB2F a Ha) as [->|Ha']; [cbn; unfold k; eapply J0hs; [left; reflexivity| exact Hb]| exact (idj_sym _ _ J3F a b Ha' Hb)]. }
        assert (FB2B : forall b, In b FB2 -> In b LB2 /\ blk_size b = 24 /\ (16 <= blk_addr b)%Z /\ (blk_addr b + 24 <= alloc_ceiling)%Z).
        { intros b Hb. split; [apply FSUB2; exact Hb|]. destruct (FB2F b Hb) as [->|Hb']; [cbn; lia|]. destruct (FBF b Hb') as (_ & ? & ? & ?). auto. }

        assert (HPh2 : heap_pres AI (map fst ns ++ (hblocks h ++ hdrs_blocks hs) ++ FB) (2^64) m1 m2).
        { eapply (heap_pres_of_hpx rsegs AI). { eapply (hpx_weaken rsegs AI); [exact HP2| intros y Hy; exact Hy| lia| exact OURS]. }
          intros a Ha [Hc|[(lo' & hi' & Hst & Hr)|(b & Hb & Hr)]]; cbn; [lia| |].
          - destruct (lo_static_img rsegs AI LOK lo' hi' Hst) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling rsegs AI LOK w Hw). split; [lia| exact I].
          - pose proof (OURS b Hb) as HbL. apply (lb_remove_sub rsegs AI) in HbL. destruct (BR b HbL) as (_ & _ & _ & R4). split; [lia| exact I]. }
        assert (DL2 : dlseg m2 ns L (L + 24)).
        { eapply (dlseg_heap_pres AI); [exact DL1| exact HPh2|]. intros b0 it0 H0. apply in_or_app. left. exact (in_map fst _ _ H0). }
        assert (HS2 : hdrs_mem m2 (h :: hs)).
        { eapply (hdrs_mem_heap_pres AI); [exact HS1| exact HPh2|]. intros b0 H0. apply in_or_app. right. apply in_or_app. left. exact H0. }
        pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP2 LC1 ltac:(apply client_range_above; lia) ltac:(cbn; lia)) as LC2.
        pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP2 FF1 ltac:(apply client_range_above; lia) ltac:(cbn; lia)) as FF2.
        pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP2 FR1 ltac:(apply client_range_above; lia) ltac:(cbn; lia)) as FR2.
        assert (HP02 : hpx AI [(L, L + 80)]%Z LBK (bv_unsigned sp) m0 m2).
        { eapply (hpx_trans rsegs AI); [exact HP1|]. eapply (hpx_weaken rsegs AI); [exact HP2| | lia| exact KEEPk]. unfold sub_fp. cbn. intros y [Hy _]. lia. }
        clear HP2 HP1 LC1 FF1 FR1 DL1 HS1 HPh2 NC1 ERR1 HE1 ST1 MI1 FLS1 FLC1.

        eapply sreach_evt.
        { eapply (dseg_callff L (hd_addr ns (L + 24)) (hd_addr ns (L + 24)) (last_addr ns L) (Z.succ (Z.of_nat (length ns))) httpheader_free_entry fcmp it);
            try eassumption; try LiaTuning.alia. all: unfold httpheader_free_entry; try reflexivity; lia. }
        intros ms' (m3 & -> & MU3 & WM3 & MI3 & LC3 & FF3).
        replace (Z.succ (Z.of_nat (length ns)) - 1)%Z with (Z.of_nat (length ns)) in LC3 by lia.
        assert (HR3 : RHEAP rsegs AI s2' LB2 m3).
        { eapply (ai_heap_frame rsegs AI); [exact HR2| exact MU3| exact WM3|]. constructor; [| constructor]. left. cbn. lia. }
        assert (HE3 : RENV rsegs AI m3 B).
        { eapply (ai_env_frame rsegs AI); [exact HR2| exact HE2| exact MU3| exact WM3|]. constructor; [| constructor]. left. cbn. lia. }
        pose proof (rw_cells_transport rsegs _ m2 m3 _ _ ERR2 MU3 WM3 ltac:(cbn; lia)) as ERR3.
        pose proof (rw_cells_transport rsegs _ m2 m3 _ _ FLC2 MU3 WM3 ltac:(cbn; lia)) as FLC3.
        pose proof (rw_cells_transport rsegs _ m2 m3 _ _ FR2 MU3 WM3 ltac:(cbn; lia)) as FR3.
        assert (ST3 : stk rsegs m3 lo q) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; lia]).
        assert (DL3 : dlseg m3 ns L (L + 24)).
        { eapply (dlseg_transport AI); [exact DL2| exact MU3| exact WM3|]. intros b0 it0 H0. destruct (NODES b0 it0 H0) as (_ & _ & ? & ? & _). cbn. lia. }
        assert (HS3 : hdrs_mem m3 (h :: hs)).
        { eapply (hdrs_mem_transport AI); [exact HS2| exact MU3| exact WM3|]. intros h0 A n Hh HA. destruct (HREG h0 A n Hh HA) as (kk & _ & _ & ? & ? & ?). cbn. lia. }
        assert (FLS3 : flseg m3 FB2 flh2).
        { eapply (flseg_transport AI); [exact FLS2| exact MU3| exact WM3|]. intros b Hb. destruct (FB2B b Hb) as (_ & _ & ? & ?). cbn. lia. }
        assert (HP03 : hpx AI [(L, L + 80)]%Z LBK (bv_unsigned sp) m0 m3).
        { eapply (hpx_trans rsegs AI); [exact HP02|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR2| intros b Hb; apply SUB2; apply KEEPk; exact Hb| exact MU3| exact WM3|].
          constructor; [| constructor]. right; right. cbn. lia. }
        clear MU3 WM3 HR2 HE2 ERR2 FLC2 FR2 ST2 DL2 HS2 FLS2 HP02 LC2 FF2 MI2.

        set (LBK' := map fst ns ++ hdrs_blocks hs ++ FB2 ++ LBK).
        assert (K'SUB : bsub LBK' LB2).
        { intros b0 H0. unfold LBK' in H0. rewrite !in_app_iff in H0. destruct H0 as [H0|[H0|[H0|H0]]].
          - apply SUB2. apply OURS. apply in_or_app. left. exact H0.
          - apply SUB2. apply OURS. apply in_or_app. right. apply in_or_app. left. apply in_or_app. right. exact H0.
          - apply FSUB2. exact H0.
          - apply SUB2. apply KEEPk. exact H0. }
        assert (NDK' : NoDup (map blk_id LBK')).
        { unfold LBK'. apply nd_app. split; [exact NDn|]. split.
          { apply idj_app_r. split; [exact J1hs|]. apply idj_app_r. split; [apply idj_sym; exact JF2n| exact J1K]. }
          apply nd_app. split; [exact NDhs|]. split.
          { apply idj_app_r. split; [apply idj_sym; exact JF2hs| exact J3K]. }
          apply nd_app. split; [exact NDF2|]. split; [exact JF2K| exact NDK]. }
        assert (JHK' : idj (hblocks h) LBK').
        { unfold LBK'. apply idj_app_r. split; [apply idj_sym; exact J1Hh|]. apply idj_app_r. split; [exact J2hs|].
          apply idj_app_r. split; [apply idj_sym; exact JF2Hh| exact J2K]. }
        cbn [H_obj.hdrs_mem] in HS3. destruct HS3 as (HM3 & _ & HS3').
        eapply sreach_bind.
        { rewrite ITEM. eapply (httpheader_free_spec AI AC LOK FREEPC) with (lo := lo) (B := B) (LBK := LBK') (h := h);
            try eassumption; rewrite ?unsigned_lit by lia; try lia; try eassumption; try reflexivity.
          - split; [exact HM3|]. split; [exact HPU|]. intros b0 H0. apply SUB2. apply OURS. apply in_or_app. right. apply in_or_app. left. apply in_or_app. left. exact H0.
          - apply nd_app. split; [exact NDHh|]. split; [exact JHK'| exact NDK']. }
        intros s4' LB4 ms4 P. unfold httpheader_free_post in P. destruct_exs P.
        destruct P as (-> & MI4 & ST4 & HE4 & [e4 ERR4] & HP4 & HR4 & K'SUB4).
        rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HP4 by lia.
        lazymatch type of MI4 with mem_inv _ ?mm => rename mm into m4 end.
        replace (ret_pc (Z_to_bv 64 0x16238)) with (Z_to_bv 64 0x16238) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (heap_pres_of_hpx rsegs AI _ _ _ _ _ HP4 ltac:(intros; exact I)) as HPh4.
        pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP4 LC3 ltac:(apply client_range_above; lia) ltac:(exact I)) as LC4.
        pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP4 FF3 ltac:(apply client_range_above; lia) ltac:(exact I)) as FF4.
        pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP4 FR3 ltac:(apply client_range_above; lia) ltac:(exact I)) as FR4.
        pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP4 FLC3 ltac:(apply client_range_above; lia) ltac:(exact I)) as FLC4.
        assert (DL4 : dlseg m4 ns L (L + 24)).
        { eapply (dlseg_heap_pres AI); [exact DL3| exact HPh4|]. intros b0 it0 H0. unfold LBK'. apply in_or_app. left. exact (in_map fst _ _ H0). }
        assert (HS4 : hdrs_mem m4 hs).
        { eapply (hdrs_mem_heap_pres AI); [exact HS3'| exact HPh4|]. intros b0 H0. unfold LBK'. apply in_or_app. right. apply in_or_app. left. exact H0. }
        assert (FLS4 : flseg m4 FB2 flh2).
        { eapply (flseg_heap_pres AI); [exact FLS3| exact HPh4|]. intros b0 H0. unfold LBK'. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact H0. }
        assert (HP04 : hpx AI [(L, L + 80)]%Z LBK (bv_unsigned sp) m0 m4).
        { eapply (hpx_trans rsegs AI); [exact HP03|]. eapply (hpx_weaken rsegs AI); [exact HP4| intros y Hy; cbn; exact I| lia|].
          intros b0 H0. unfold LBK'. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H0. }
        clear HP4 HPh4 LC3 FF3 FR3 FLC3 DL3 HS3' FLS3 HP03 HR3 HE3 ERR3 ST3 MI3 HM3.

        assert (CURR : (0 <= hd_addr ns (L + 24) < 2^64)%Z).
        { destruct ns as [|[b2 it2] ns2]; cbn; [lia|]. destruct (NODES b2 it2 (or_introl eq_refl)) as (_ & _ & ? & ? & _). lia. }
        eapply sreach_evt. { eapply (dseg_next L (hd_addr ns (L + 24))); lia. }
        intros ms' ->.
        destruct ns as [|[b2 it2] ns2].
        -
          cbn [H_obj.hd_addr H_obj.last_addr] in LC4 |- *. rewrite Z.eqb_refl.
          destruct hs as [|h' hs']; [| discriminate].
          eapply ld_exit; try eassumption; try (cbn; lia).
          all: first [intros b0 H0; apply K'SUB4; unfold LBK'; cbn; exact H0 | unfold LBK' in NDK'; cbn in NDK'; exact NDK'].
        -
          destruct hs as [|h' hs']; [discriminate|].
          destruct (NODES b2 it2 (or_introl eq_refl)) as (B2IN & B2SZ & B216 & B2HI & _).
          pose proof DL4 as DLx. cbn [H_obj.dlseg] in DLx. destruct DLx as (_ & _ & NT2 & _).
          cbn [H_obj.hd_addr]. replace (blk_addr b2 =? L + 24) with false by (symmetry; apply Z.eqb_neq; exact NT2).
          eapply (IH (h' :: hs') FB2 flh2 fk2); try eassumption; try LiaTuning.alia.
          all: first [discriminate | unfold LBK' in K'SUB4; exact K'SUB4 | unfold LBK' in NDK'; exact NDK']. }

      destruct ns as [|[b2 it2] ns2] eqn:ENS.
      - cbn [H_obj.last_addr H_obj.hd_addr] in LC, CONT |- *.
        eapply sreach_evt.
        { eapply (dseg_unlink lo L N (L + 24) it N (Z.succ (Z.of_nat (length ([] : list (BLK * Z))))) None); try eassumption; try (cbn; lia); try lia; try reflexivity. }
        intros ms' P. unfold unlink_post in P. destruct P as (m1 & -> & MU1 & WM1 & MI1 & LC1 & NC1 & _). cbn [munch app] in MU1.
        eapply CONT.
        + exact I.
        + eapply (hdrs_mem_transport AI); [exact HS0| exact MU1| exact WM1|]. intros h0 A n Hh HA. destruct (HREG h0 A n Hh HA) as (kk & _ & _ & ? & ? & ?). cbn. lia.
        + exact LC1.
        + eapply rw_cells_transport; [exact FLC| exact MU1| exact WM1| cbn; lia].
        + eapply (flseg_transport AI); [exact FLS| exact MU1| exact WM1|]. intros b Hb. destruct (FBF b Hb) as (_ & _ & ? & ?). cbn. lia.
        + eapply rw_cells_transport; [exact FF| exact MU1| exact WM1| cbn; lia].
        + eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia.
        + eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia.
        + eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| cbn; lia].
        + eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| cbn; lia].
        + exact MI1.
        + eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| cbn; lia].
        + exact NC1.
        + eapply (hpx_trans rsegs AI); [exact HP0|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact KSUB| exact MU1| exact WM1|].
          constructor; [| constructor]. right; right. cbn. lia.
      - pose proof DL' as DLn. cbn [H_obj.dlseg] in DLn. destruct DLn as (SZ2 & NZ2 & NT2 & ITR2 & NC2 & DL2).
        destruct (NODES b2 it2 ltac:(left; reflexivity)) as (B2IN & _ & B216 & B2HI & DJ2).
        assert (B2AL : (blk_addr b2 mod 8 = 0)%Z) by (destruct (BR b2 B2IN) as (_ & Q & _); Z.div_mod_to_equations; lia).
        cbn [H_obj.last_addr H_obj.hd_addr] in LC, LASTR, CONT |- *.
        eapply sreach_evt.
        { eapply (dseg_unlink lo L N (blk_addr b2) it (last_addr ns2 (blk_addr b2)) (Z.succ (Z.of_nat (length ((b2, it2) :: ns2)))) (Some (hd_addr ns2 (L + 24), it2)));
            try eassumption; try LiaTuning.alia.
          split; [exact NC2|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [| lia].
          destruct ns2 as [|[b3 it3] ?]; cbn; [lia|]. destruct (NODES b3 it3 ltac:(right; left; reflexivity)) as (_ & _ & ? & ? & _). lia. }
        intros ms' P. unfold unlink_post in P. destruct P as (m1 & -> & MU1 & WM1 & MI1 & LC1 & NC1 & NXC1). cbn [munch app] in MU1.
        pose proof (fresh_block_disjoint_errno rsegs AI _ _ _ _ LOK HR B2IN) as DE2. rewrite SZ2 in DE2. cbn in DE2.
        assert (B2NE : forall b0, In b0 LB -> b0 <> b2 -> (blk_addr b2 + 24 <= blk_addr b0 \/ blk_addr b0 + blk_size b0 <= blk_addr b2)%Z).
        { intros b0 H0 NE. destruct (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR B2IN H0 ltac:(congruence)) as [D|D]; rewrite ?SZ2 in D; lia. }

        pose proof NDn as NDn2. cbn [map] in NDn2. apply nd_cons in NDn2. destruct NDn2 as [J2r NDn2'].
        assert (ND2x : forall b0, In b0 (map fst ns2 ++ (hblocks h ++ hdrs_blocks hs) ++ FB ++ LBK) -> b0 <> b2).
        { intros b0 H0. apply not_eq_sym. rewrite !in_app_iff in H0. destruct H0 as [H0|[[H0|H0]|[H0|H0]]].
          - eapply (idj_neq _ _ _ _ J2r); [left; reflexivity| exact H0].
          - eapply (idj_neq _ _ _ _ J1Hh); [left; reflexivity| exact H0].
          - eapply (idj_neq _ _ _ _ J1hs); [left; reflexivity| exact H0].
          - eapply (idj_neq _ _ _ _ J1F); [left; reflexivity| exact H0].
          - eapply (idj_neq _ _ _ _ J1K); [left; reflexivity| exact H0]. }
        eapply CONT.
        + cbn [H_obj.dlseg]. split; [exact SZ2|]. split; [exact NZ2|]. split; [exact NT2|]. split; [exact ITR2|]. split; [exact NXC1|].
          eapply (dlseg_transport AI); [exact DL2| exact MU1| exact WM1|]. intros b0 it0 H0.
          destruct (NODES b0 it0 ltac:(right; exact H0)) as (B0IN & B0SZ & ? & ? & _).
          pose proof (B2NE b0 B0IN ltac:(apply ND2x; apply in_or_app; left; exact (in_map fst _ _ H0))) as D. rewrite B0SZ in D. cbn. lia.
        + eapply (hdrs_mem_transport AI); [exact HS0| exact MU1| exact WM1|]. intros h0 A n Hh HA. destruct (HREG h0 A n Hh HA) as (kk & KIN & KH & ? & ? & ?).
          pose proof (B2NE _ KIN ltac:(apply ND2x; apply in_or_app; right; apply in_or_app; left; exact KH)) as D. cbn in D. cbn. lia.
        + exact LC1.
        + eapply rw_cells_transport; [exact FLC| exact MU1| exact WM1| cbn; lia].
        + eapply (flseg_transport AI); [exact FLS| exact MU1| exact WM1|]. intros b Hb. destruct (FBF b Hb) as (BIN & BSZ & ? & ?).
          pose proof (B2NE _ BIN ltac:(apply ND2x; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb)) as D. rewrite BSZ in D. cbn. lia.
        + eapply rw_cells_transport; [exact FF| exact MU1| exact WM1| cbn; lia].
        + eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor. { left. cbn. lia. } constructor; [| constructor].
          right; right; right. exists b2. split; [exact B2IN|]. rewrite SZ2. cbn. lia.
        + eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor. { left. cbn. lia. } constructor; [| constructor].
          right; right; right. exists b2. split; [exact B2IN|]. rewrite SZ2. cbn. lia.
        + eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| cbn; lia].
        + eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| cbn; lia].
        + exact MI1.
        + eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| cbn; lia].
        + exact NC1.
        + eapply (hpx_trans rsegs AI); [exact HP0|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact KSUB| exact MU1| exact WM1|].
          constructor. { right; right. cbn. lia. } constructor; [| constructor].
          right; left. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI _ _ LBK b2); [exact LOK| exact HR| exact B2IN| | lia| rewrite SZ2; cbn; lia].
          intros b0 Hb0. split; [apply KSUB; exact Hb0|]. apply ND2x. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right. exact Hb0.
    Qed.
  End LOOP.

  #[using="AC LOK FREEPC"] Theorem ListDestroy_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (LBK : list BLK) (ns : list (BLK * Z)) (hs : list (hdr AI)) (L fcmp lo B : Z) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 96 - al_stack L_)%Z -> (0 <= al_stack L_)%Z ->
    rw_cells rsegs m (al_errno L_) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m L (lhead_cells (hd_addr ns (L + 24)) (last_addr ns L) (zlength ns)) ->
    rw_cells rsegs m (L + 56) (fl_cells 0 0) -> FFc m L httpheader_free_entry fcmp ->
    dlseg m ns L (L + 24) -> hdrs_mem m hs -> map snd ns = map (hA AI) hs ->
    (bv_unsigned sp <= L)%Z -> (L + 96 <= B)%Z -> (zlength ns < 2^40)%Z -> (0 <= fcmp < 2^64)%Z ->
    bsub (map fst ns ++ hdrs_blocks hs ++ LBK) LB -> NoDup (map blk_id (map fst ns ++ hdrs_blocks hs ++ LBK)) ->
    (L mod 8 = 0)%Z -> a0 = wz L -> a1 = wz 1 ->
    SREACH AI (ListDestroy_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBK L fcmp lo B m)
      (MS (mkR ra sp gp (wz (al_tp L_)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ListDestroy_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB BHI ST CEIL LO STK ERR MI LC FLC FF DL HS ITEMS LLO LB96 LEN FCMP ASUB ND AL -> ->.
    pose proof (word_lt64 sp) as SPR.
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    pose proof ASUB as ASUB0. apply (bsub_app AI) in ASUB. destruct ASUB as [NSUB REST]. apply (bsub_app AI) in REST. destruct REST as [HSUB KSUB].
    assert (NODES : forall b0 it0, In (b0, it0) ns -> (16 <= blk_addr b0)%Z /\ (blk_addr b0 + 24 <= alloc_ceiling)%Z).
    { intros b0 it0 H0. destruct (dlseg_facts AI _ _ _ _ _ _ DL H0) as (SZ0 & _).
      pose proof (in_map fst _ _ H0) as H0'. cbn [fst] in H0'.
      destruct (ai_block_range rsegs AI _ _ _ _ HR (NSUB _ H0')) as (R1 & R2 & _ & R4 & _). rewrite SZ0 in R4.
      split; [Z.div_mod_to_equations; lia| lia]. }
    assert (FIRSTR : (0 <= hd_addr ns (L + 24) < 2^64)%Z).
    { destruct ns as [|[b it] ns']; cbn; [lia|]. destruct (NODES b it (or_introl eq_refl)). lia. }
    eapply sreach_evt. { eapply (dseg_entry lo L (hd_addr ns (L + 24)) (last_addr ns L) (zlength ns)); try eassumption; lia. }
    intros ms' (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1 & LC1).
    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ FLC MU1 WM1 ltac:(cbn; lia)) as FLC1.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ FF MU1 WM1 ltac:(cbn; lia)) as FF1.
    assert (DL1 : dlseg m1 ns L (L + 24)).
    { eapply (dlseg_transport AI); [exact DL| exact MU1| exact WM1|]. intros b it H. destruct (NODES b it H). cbn. lia. }
    assert (HS1 : hdrs_mem m1 hs).
    { eapply (hdrs_mem_transport AI); [exact HS| exact MU1| exact WM1|]. intros h0 A n Hh HA.
      destruct (hregion_block AI h0 A n HA) as [k Hk]. pose proof (HSUB _ (in_hdrs_blocks AI _ _ _ Hh Hk)) as HbL.
      destruct (ai_block_range rsegs AI _ _ _ _ HR HbL) as (R1 & _ & R3 & R4 & _). cbn in R1, R3, R4. cbn. lia. }
    assert (HP1 : hpx AI [(L, L + 80)]%Z LBK (bv_unsigned sp) m m1).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact KSUB| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    destruct (Z.eqb_spec (hd_addr ns (L + 24)) (L + 24)) as [E|NE].
    -
      destruct ns as [|[b it] ns']. 2:{ exfalso. cbn in E. pose proof DL as DLx. cbn [H_obj.dlseg] in DLx. destruct DLx as (_ & _ & NT & _). exact (NT E). }
      destruct hs as [|h hs']; [| discriminate]. cbn [H_obj.hd_addr H_obj.last_addr zlength length Z.of_nat] in LC1 |- *.
      rewrite ?Z.eqb_refl.
      eapply (ld_exit ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBK L fcmp lo B m SPB BHI CEIL LO STK LLO LB96 FCMP AL [] 0 0 0);
        try eassumption; try (cbn; lia). cbn. reflexivity.
    - rewrite E in *|| idtac.
      replace (hd_addr ns (L + 24) =? L + 24) with false by (symmetry; apply Z.eqb_neq; exact NE).
      eapply (ld_loop ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBK L fcmp lo B m SPB BHI CEIL LO STK LLO LB96 FCMP AL ns hs [] 0 0);
        try eassumption; try (cbn; lia).
      + destruct ns; [cbn in NE; congruence| discriminate].
      + cbn. reflexivity.
  Qed.
End W.
