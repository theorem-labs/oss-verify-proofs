(** The pair loop of expect_of (fuzz_headamp.c:119-155) in the plain LLVMFuzzerTestOneInput, from the loop head
    0x142b4 to the store of x->rc at 0x14108, against Prog/HeadCheck/Cut.v's [expect_stmt] exit, with [key_stmt]
    (the pair with the prefix, 0x1433c -> 0x1465c / 0x14600) and strncmp_contract as Section hypotheses. The Section
    fixes the frame (sp, gp, tp and the callee-saved s1, s3-s6), the entry memory m, the record r at pp, cap, lo,
    the continuation Q and the answer E the continuation expects. Walked backwards: [exit_ok] (0x14108), [latch_ok]
    (0x14668: `bge s8,t0`), [fold_ok] (0x1465c: the first refusal is kept), the cap test and the cell write
    ([write_ok] 0x14600, [cellw_ok] 0x14618, [cellw2_ok] 0x14634), [pair_ok] (0x1433c: the key piece), the
    pod_next_pair scan by induction on the entries left ([key_ok] 0x142f4 with a key and strncmp, [nokey_ok] 0x142f4
    without, [scan_ok] 0x142c4), [head_ok] (0x142b4). The loop computes Pod/Headamp.v [ha_fold] over the pairs left
    ([pairs_by key_of] of the entries from the scan's index) step by step: at the exit the fold's (cells, keys,
    refusal) is what x holds past x->rc, and s0 its number of cells. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c strncmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require ParseSites.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts Cut PairFacts.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).
(* Register equations at a cut. *)
Ltac weq := first [ reflexivity
                  | (rewrite addiw1_small by lia; f_equal; lia)
                  | (f_equal; lia)
                  | (f_equal; rewrite ?unsigned_lit by lia; lia) ].

(** The binary32 bounds of the inlined pod_nearest in fs1 / fs2. *)
Definition FPinv (F : bvmap 5 word) : Prop :=
  Sem.reg_get F (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 F32_M1) /\
  Sem.reg_get F (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 F32_256).

Lemma FPinv_keep : forall F F', FPinv F ->
  (forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r) -> FPinv F'.
Proof.
  intros F F' (H9 & H18) H. split.
  - rewrite H; [exact H9 | vm_compute; intros E; discriminate E | vm_compute; intros E; discriminate E].
  - rewrite H; [exact H18 | vm_compute; intros E; discriminate E | vm_compute; intros E; discriminate E].
Qed.

Section Pairs.
Variables (sp gp tp s1 s3 s4 s5 s6 : word) (m : word -> option byte) (r : pod_rec) (cap pp lo : Z)
          (Q : machine_state -> Prop) (E : answer).

Local Abbreviation SP := (bv_unsigned sp).
Local Abbreviation es := (ents r).
Local Abbreviation n := (length (ents r)).

Hypothesis HWF : pod_rec_wf r.
Hypothesis HCAP : 0 <= cap <= 9.
Hypothesis HPP0 : 0 <= pp.
Hypothesis HPPLO : pp + POD_PROPS <= lo.
Hypothesis HST : stk rsegs m lo (SP + FRAME_LOCALS).
Hypothesis HLO : lo + NEAR_STACK <= SP.
Hypothesis HSPA : SP mod 16 = 0.
Hypothesis HROM : forall a, lo <= a < SP + FRAME_LOCALS -> seg_rom rsegs (wa a) = None.
Hypothesis KEY : key_stmt.
Hypothesis STRN : strncmp_contract.
Hypothesis HQ : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
                       (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
  frm0 fc' ->
  munch (EXPECT_W SP) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
  stk rsegs m' lo (SP + FRAME_LOCALS) ->
  bytes_at rsegs m' (SP + 0x94) (x_tail E) ->
  evt rsegs Q
    (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 (ans_rc E)) s1
             a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 cap) s3 s4 s5 s6 s7' s8' s9' s10' s11' t3' t4' t5' t6')
        F' (Z_to_bv 64 0x14108) fc' None m' (seg_rom rsegs)).

(** The numbers lia needs. *)
Lemma bnd : 0 <= pp /\ pp + 19744 <= lo /\ 0 <= lo /\ lo + 48 <= SP /\ SP + 432 <= 2^64 /\ 0 <= cap <= 9 /\
            (n <= 32)%nat.
Proof.
  pose proof HST as (H0 & H1 & _). pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof HPPLO as H2. pose proof HLO as H3. unfold POD_PROPS, NEAR_STACK, FRAME_LOCALS in *. lia.
Qed.

Lemma len_pp : Z.of_nat (length (pp_bytes r)) = 19744.
Proof. exact (length_pp_bytes r HWF). Qed.

(** ** The memory of the loop *)
(** The frame cells and facts every cut carries: changed only in EXPECT_W, the record at pp, the cells -0.5L's high
    word (over the cell that held &pp->len), 0.5L's high word, &pp->ent[0], 1000000 and the prefix's address. *)
Definition MemB (m1 : word -> option byte) : Prop :=
  munch (EXPECT_W SP) m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ MemNorm.task_mem rsegs m1 /\
  stk rsegs m1 lo (SP + FRAME_LOCALS) /\
  bytes_at rsegs m1 pp (pp_bytes r) /\
  bytes_at rsegs m1 (SP + 0x50) (le8 (Z_to_bv 64 MHALF_HI)) /\
  bytes_at rsegs m1 (SP + 0x60) (le8 (Z_to_bv 64 HALF_HI)) /\
  bytes_at rsegs m1 (SP + 0x68) (le8 (Z_to_bv 64 (pp + OFF_ENT))) /\
  bytes_at rsegs m1 (SP + 0x70) (le8 (Z_to_bv 64 RC_BIG)) /\
  bytes_at rsegs m1 (SP + 0x88) (le8 (Z_to_bv 64 PREFIX_AT)).

(** x past x->rc for the fold's state (cells, keys, refusal): the cells part, n, keys, refusal. *)
Definition MemX (m1 : word -> option byte) (cells : list cell) (keys rf : Z) : Prop :=
  bytes_at rsegs m1 (SP + 0x94) (x_cellz cells) /\
  bytes_at rsegs m1 (SP + 0x10c) (le4 (Z_to_bv 64 (Z.of_nat (length cells)))) /\
  bytes_at rsegs m1 (SP + 0x110) (le4 (Z_to_bv 64 keys)) /\
  bytes_at rsegs m1 (SP + 0x114) (le4 (Z_to_bv 64 rf)).

Definition MemL (m1 : word -> option byte) (cells : list cell) (keys rf : Z) : Prop :=
  MemB m1 /\ MemX m1 cells keys rf.

(** Inside a pair (after 0x14314): the saved &ent[0].body and n_ent too. *)
Definition MemP (m1 : word -> option byte) (cells : list cell) (keys rf : Z) : Prop :=
  MemL m1 cells keys rf /\ bytes_at rsegs m1 (SP + 0x78) (le8 (Z_to_bv 64 (pp + 16412))) /\
  bytes_at rsegs m1 (SP + 0x80) (le8 (Z_to_bv 64 (Z.of_nat n))).

(** The fold's state at index j: at most cap cells, at most j keys (each pair takes two entries), a refusal code. *)
Definition Linv (cells : list cell) (keys rf : Z) (j : nat) : Prop :=
  Z.of_nat (length cells) <= cap /\ 0 <= keys <= Z.of_nat j /\ 0 <= rf <= 5.

Lemma MemB_intro : forall m1,
  munch (EXPECT_W SP) m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> MemNorm.task_mem rsegs m1 ->
  stk rsegs m1 lo (SP + FRAME_LOCALS) -> bytes_at rsegs m1 pp (pp_bytes r) ->
  bytes_at rsegs m1 (SP + 0x50) (le8 (Z_to_bv 64 MHALF_HI)) -> bytes_at rsegs m1 (SP + 0x60) (le8 (Z_to_bv 64 HALF_HI)) ->
  bytes_at rsegs m1 (SP + 0x68) (le8 (Z_to_bv 64 (pp + OFF_ENT))) -> bytes_at rsegs m1 (SP + 0x70) (le8 (Z_to_bv 64 RC_BIG)) ->
  bytes_at rsegs m1 (SP + 0x88) (le8 (Z_to_bv 64 PREFIX_AT)) -> MemB m1.
Proof.
  intros m1 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 H11)))))))))).
Qed.

(** A store into EXPECT_W apart from the frame cells MemB keeps. *)
Lemma MemB_store : forall m1 a bs, MemB m1 -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP + 0x30 <= a -> a + Z.of_nat (length bs) <= SP + 0x118 ->
  disjoint_from [(SP + 0x50, SP + 0x60); (SP + 0x60, SP + 0x78); (SP + 0x88, SP + 0x90)] a (Z.of_nat (length bs)) ->
  MemB (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs (MU & WM & MI & TM & ST & HP & H50 & H60 & H68 & H70 & H88) HS HA1 HA2 HD.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _). pose proof len_pp as LP.
  cbn [disjoint_from] in HD. destruct HD as (D1 & D2 & D3 & _).
  assert (HIn : inside (EXPECT_W SP) a (Z.of_nat (length bs))).
  { unfold EXPECT_W. cbn [inside].
    destruct (Z_lt_le_dec a (SP + 0x58)) as [X|X]; [right; left; lia|].
    destruct (Z_lt_le_dec a (SP + 0x60)) as [X2|X2]; [destruct D1 as [D1|D1]; lia|].
    right; right; left; lia. }
  apply MemB_intro.
  - apply munch_write; [exact MU | lia | lia | exact HIn].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact HS].
  - apply task_mem_write; [exact TM | exact HS].
  - apply stk_write; [exact ST | lia | lia].
  - apply bytes_at_write_other; [exact HP | lia | lia | lia].
  - apply bytes_at_write_other; [exact H50 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H60 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H68 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H70 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H88 | lia | lia | rewrite length_le8; lia].
Qed.

(** The two saves of 0x14310 / 0x14314 into [sp + 0x78, sp + 0x88). *)
Lemma MemL_store78 : forall m1 cells keys rf a bs, MemL m1 cells keys rf ->
  store_ok rsegs m1 (wa a) (length bs) = true -> SP + 0x78 <= a -> a + Z.of_nat (length bs) <= SP + 0x88 ->
  MemL (write_to_mem m1 (wa a) bs) cells keys rf.
Proof.
  intros m1 cells keys rf a bs (MB & HX & HN & HK & HR) HS H1 H2.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _).
  split.
  - apply MemB_store; [exact MB | exact HS | lia | lia | cbn [disjoint_from]; repeat split; lia].
  - refine (conj _ (conj _ (conj _ _))).
    + apply bytes_at_write_other; [exact HX | lia | lia | lia].
    + apply bytes_at_write_other; [exact HN | lia | lia | lia].
    + apply bytes_at_write_other; [exact HK | lia | lia | lia].
    + apply bytes_at_write_other; [exact HR | lia | lia | lia].
Qed.

(** Across strncmp (no store). *)
Lemma MemP_none : forall m1 m2 cells keys rf, MemP m1 cells keys rf ->
  munch [] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> MemP m2 cells keys rf.
Proof.
  intros m1 m2 cells keys rf (((MU & WM & MI & TM & ST & HP & H50 & H60 & H68 & H70 & H88) & (HX & HN & HK & HR)) & H78 & H80)
    MU2 WM2 MI2.
  assert (T : forall A bs, bytes_at rsegs m1 A bs -> bytes_at rsegs m2 A bs)
    by (intros A bs H; exact (bytes_at_transport rsegs [] m1 m2 A bs H MU2 I)).
  split; [split|split; apply T; assumption].
  - apply MemB_intro; try (apply T; assumption).
    + exact (munch_trans _ m m1 m2 MU (munch_weaken [] _ m1 m2 (fun x _ => I) MU2)).
    + exact (wmono_trans rsegs m m1 m2 WM WM2).
    + exact MI2.
    + apply (task_mem_munch rsegs [] m1 m2 TM MU2). intros x Hx. exfalso. apply Hx. exact I.
    + exact (stk_transport_disjoint rsegs [] m1 m2 lo (SP + FRAME_LOCALS) ST MU2 WM2 I).
  - refine (conj _ (conj _ (conj _ _))); apply T; assumption.
Qed.

(** Across the key piece: its footprint KEY_W, keys + 1 at sp + 0x110. *)
Lemma MemP_key : forall m1 m2 cells keys rf, MemP m1 cells keys rf -> Z.of_nat (length cells) <= cap ->
  munch (KEY_W SP) m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> MemNorm.task_mem rsegs m2 ->
  stk rsegs m2 lo (SP + FRAME_LOCALS) -> bytes_at rsegs m2 (SP + 0x110) (le4 (Z_to_bv 64 (keys + 1))) ->
  MemP m2 cells (keys + 1) rf.
Proof.
  intros m1 m2 cells keys rf (((MU & WM & MI & TM & ST & HP & H50 & H60 & H68 & H70 & H88) & (HX & HN & HK & HR)) & H78 & H80)
    Hc MU2 WM2 MI2 TM2 ST2 HK2.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _). pose proof len_pp as LP.
  assert (LX : length (x_cellz cells) = 120%nat) by (apply length_x_cellz; unfold X_CELLS; lia).
  assert (T : forall A bs, bytes_at rsegs m1 A bs -> A + Z.of_nat (length bs) <= SP - 48 \/ SP <= A ->
                A + Z.of_nat (length bs) <= SP + 0x30 \/ SP + 0x50 <= A ->
                A + Z.of_nat (length bs) <= SP + 0x110 \/ SP + 0x114 <= A -> bytes_at rsegs m2 A bs).
  { intros A bs H D1 D2 D3. apply (bytes_at_transport rsegs _ m1 m2 A bs H MU2). unfold KEY_W, NEAR_STACK.
    cbn [disjoint_from]. repeat split; lia. }
  split; [split|split].
  - apply MemB_intro.
    + apply (munch_trans _ m m1 m2 MU). apply (munch_weaken (KEY_W SP) _ m1 m2); [|exact MU2].
      unfold sub_fp, KEY_W, EXPECT_W, NEAR_STACK. cbn [outside]. intros x (O1 & O2 & O3 & _).
      repeat split; try exact I; lia.
    + exact (wmono_trans rsegs m m1 m2 WM WM2).
    + exact MI2.
    + exact TM2.
    + exact ST2.
    + apply T; [exact HP | lia | lia | lia].
    + apply T; [exact H50 | rewrite length_le8; lia ..].
    + apply T; [exact H60 | rewrite length_le8; lia ..].
    + apply T; [exact H68 | rewrite length_le8; lia ..].
    + apply T; [exact H70 | rewrite length_le8; lia ..].
    + apply T; [exact H88 | rewrite length_le8; lia ..].
  - refine (conj _ (conj _ (conj _ _))).
    + apply T; [exact HX | rewrite LX; lia ..].
    + apply T; [exact HN | rewrite length_le4; lia ..].
    + exact HK2.
    + apply T; [exact HR | rewrite length_le4; lia ..].
  - apply T; [exact H78 | rewrite length_le8; lia ..].
  - apply T; [exact H80 | rewrite length_le8; lia ..].
Qed.

(** The refusal store 0x14664 `sw t3,0x114(sp)`. *)
Lemma MemP_rf : forall m1 cells keys rf bad, MemP m1 cells keys rf -> Z.of_nat (length cells) <= cap ->
  store_ok rsegs m1 (wa (SP + 0x114)) (length (le4 (Z_to_bv 64 bad))) = true ->
  MemP (write_to_mem m1 (wa (SP + 0x114)) (le4 (Z_to_bv 64 bad))) cells keys bad.
Proof.
  intros m1 cells keys rf bad ((MB & HX & HN & HK & HR) & H78 & H80) Hc HS.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _). rewrite length_le4 in HS.
  assert (LX : length (x_cellz cells) = 120%nat) by (apply length_x_cellz; unfold X_CELLS; lia).
  split; [split|split].
  - apply MemB_store; rewrite ?length_le4; [exact MB | exact HS | lia | lia | cbn [disjoint_from]; repeat split; lia].
  - refine (conj _ (conj _ (conj _ _))).
    + apply bytes_at_write_other; rewrite ?length_le4, ?LX; [exact HX | lia | lia | lia].
    + apply bytes_at_write_other; rewrite ?length_le4; [exact HN | lia | lia | lia].
    + apply bytes_at_write_other; rewrite ?length_le4; [exact HK | lia | lia | lia].
    + apply bytes_at_write_same; rewrite ?length_le4; lia.
  - apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H78 | lia | lia | lia].
  - apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H80 | lia | lia | lia].
Qed.

(** The memory of the cell write (0x14618-0x14644): MemB, the value and param cells, the two saves, n, keys,
    refusal; x's cells part apart. *)
Definition MemW (m1 : word -> option byte) (c keys rf p v : Z) : Prop :=
  MemB m1 /\ bytes_at rsegs m1 (SP + 0x40) (le8 (Z_to_bv 64 v)) /\ bytes_at rsegs m1 (SP + 0x48) (le8 (Z_to_bv 64 p)) /\
  bytes_at rsegs m1 (SP + 0x78) (le8 (Z_to_bv 64 (pp + 16412))) /\
  bytes_at rsegs m1 (SP + 0x80) (le8 (Z_to_bv 64 (Z.of_nat n))) /\
  bytes_at rsegs m1 (SP + 0x10c) (le4 (Z_to_bv 64 c)) /\ bytes_at rsegs m1 (SP + 0x110) (le4 (Z_to_bv 64 keys)) /\
  bytes_at rsegs m1 (SP + 0x114) (le4 (Z_to_bv 64 rf)).

(** A store into x's cells part. *)
Lemma MemW_store : forall m1 c keys rf p v a bs, MemW m1 c keys rf p v ->
  store_ok rsegs m1 (wa a) (length bs) = true -> SP + 0x94 <= a -> a + Z.of_nat (length bs) <= SP + 0x10c ->
  MemW (write_to_mem m1 (wa a) bs) c keys rf p v.
Proof.
  intros m1 c keys rf p v a bs (MB & H40 & H48 & H78 & H80 & HN & HK & HR) HS H1 H2.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _).
  split; [apply MemB_store; [exact MB | exact HS | lia | lia | cbn [disjoint_from]; repeat split; lia]|].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); apply bytes_at_write_other;
    rewrite ?length_le4, ?length_le8; first [eassumption | lia].
Qed.

(** The last store of the cell write, 0x14644 `sw s0,0x10c(sp)`: n + 1 cells. *)
Lemma MemW_fin : forall (m1 : word -> option byte) (cells : list cell) (keys rf p v : Z) (cl : list cell),
  MemW m1 (Z.of_nat (length cells)) keys rf p v ->
  bytes_at rsegs m1 (SP + 0x94) (x_cellz cl) -> (length cl = S (length cells))%nat -> Z.of_nat (length cl) <= cap ->
  store_ok rsegs m1 (wa (SP + 0x10c)) (length (le4 (Z_to_bv 64 (Z.of_nat (length cells) + 1)))) = true ->
  MemP (write_to_mem m1 (wa (SP + 0x10c)) (le4 (Z_to_bv 64 (Z.of_nat (length cells) + 1)))) cl keys rf.
Proof.
  intros m1 cells keys rf p v cl (MB & H40 & H48 & H78 & H80 & HN & HK & HR) HX Hl Hc HS.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _). rewrite length_le4 in HS.
  assert (LX : length (x_cellz cl) = 120%nat) by (apply length_x_cellz; unfold X_CELLS; lia).
  split; [split|split].
  - apply MemB_store; rewrite ?length_le4; [exact MB | exact HS | lia | lia | cbn [disjoint_from]; repeat split; lia].
  - refine (conj _ (conj _ (conj _ _))).
    + apply bytes_at_write_other; rewrite ?length_le4, ?LX; [exact HX | lia | lia | lia].
    + replace (Z.of_nat (length cl)) with (Z.of_nat (length cells) + 1) by lia.
      apply bytes_at_write_same; rewrite ?length_le4; lia.
    + apply bytes_at_write_other; rewrite ?length_le4; [exact HK | lia | lia | lia].
    + apply bytes_at_write_other; rewrite ?length_le4; [exact HR | lia | lia | lia].
  - apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H78 | lia | lia | lia].
  - apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H80 | lia | lia | lia].
Qed.

(** A store over one int of x's cells part. *)
Lemma bytes_at_write_at : forall m1 A X Y Y' Z a, bytes_at rsegs m1 A (X ++ Y ++ Z) -> length Y' = length Y ->
  a = A + Z.of_nat (length X) -> bytes_at rsegs (write_to_mem m1 (wa a) Y') A (X ++ Y' ++ Z).
Proof. intros m1 A X Y Y' Z a H L ->. exact (bytes_at_write_mid rsegs m1 A X Y Y' Z H L). Qed.

(** ** 0x14108: x->rc is not stored yet; s0 = the number of cells, x past x->rc the fold's state *)
Lemma exit_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (cells : list cell) (keys rf : Z),
  frm0 fc -> MemL m1 cells keys rf -> Z.of_nat (length cells) <= cap -> E = ha_result (cells, keys, rf) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length cells))) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14108) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 cells keys rf HF
    ((MU & WM & MI & TM & ST & _) & (HX & HN & HK & HR)) Hc HE.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _).
  assert (HT : bytes_at rsegs m1 (SP + 0x94) (x_tail E)).
  { rewrite HE, x_tail_res. apply bytes_at_app. split; [exact HX|].
    rewrite length_x_cellz by (unfold X_CELLS; lia). replace (SP + 0x94 + Z.of_nat 120) with (SP + 0x10c) by lia.
    apply bytes_at_app. split; [exact HN|]. rewrite length_le4. replace (SP + 0x10c + Z.of_nat 4) with (SP + 0x110) by lia.
    apply bytes_at_app. split; [exact HK|]. rewrite length_le4. replace (SP + 0x110 + Z.of_nat 4) with (SP + 0x114) by lia.
    exact HR. }
  replace (Z.of_nat (length cells)) with (ans_rc E) by (rewrite HE; reflexivity).
  apply HQ; assumption.
Qed.

(** ** The loop head 0x142b4 and the scan 0x142c4 *)
Definition head_P (j : nat) : Prop :=
  forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf : Z),
  frm0 fc -> FPinv F -> MemL m1 cells keys rf -> Linv cells keys rf j ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn j es) None) cells keys rf) -> (j < n)%nat ->
  s0 = Z_to_bv 64 (Z.of_nat (length cells)) -> s8 = Z_to_bv 64 (Z.of_nat j) ->
  t0 = Z_to_bv 64 (Z.of_nat n) -> t1 = Z_to_bv 64 104 -> t2 = Z_to_bv 64 8 -> a2 = Z_to_bv 64 (pp + 16412) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (-1)) s8 s9 s10 (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x142b4) fc None m1 (seg_rom rsegs)).

Definition scan_P (i : nat) : Prop :=
  forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf : Z),
  frm0 fc -> FPinv F -> MemL m1 cells keys rf -> Linv cells keys rf i ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn i es) None) cells keys rf) -> (i < n)%nat ->
  s0 = Z_to_bv 64 (Z.of_nat (length cells)) -> s8 = Z_to_bv 64 (Z.of_nat i + 1) -> s9 = Z_to_bv 64 (Z.of_nat i - 1) ->
  a0 = Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat i) ->
  t0 = Z_to_bv 64 (Z.of_nat n) -> t1 = Z_to_bv 64 104 -> t2 = Z_to_bv 64 8 -> a2 = Z_to_bv 64 (pp + 16412) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (-1)) s8 s9 s10 (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x142c4) fc None m1 (seg_rom rsegs)).

(** 0x142b4 .. 0x142c0: s9 := at - 1, a0 := &ent[at].body, s8 := at + 1. *)
Lemma head_ok : forall j, scan_P j -> head_P j.
Proof.
  intros j HS. unfold head_P.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 F fc m1 cells keys rf
    HF HFP ML HL HE Hj -> -> -> -> -> ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  (* 0x142b4 addi s9,s8,-1; mul a0,s8,t1; addi s8,s8,1; add a0,a2,a0 *)
  step. step. step. step.
  eapply HS; [exact HF | exact HFP | exact ML | exact HL | exact HE | exact Hj | weq ..].
Qed.

(** 0x14668 .. 0x14670: a2 := &ent[0].body again; `at < n_ent` back to the head, else no pair is left. *)
Lemma latch_ok : forall j, ((j < n)%nat -> head_P j) ->
  forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf : Z),
  frm0 fc -> FPinv F -> MemP m1 cells keys rf -> Linv cells keys rf j ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn j es) None) cells keys rf) -> (j <= n)%nat ->
  s0 = Z_to_bv 64 (Z.of_nat (length cells)) -> s8 = Z_to_bv 64 (Z.of_nat j) ->
  t0 = Z_to_bv 64 (Z.of_nat n) -> t1 = Z_to_bv 64 104 -> t2 = Z_to_bv 64 8 ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (-1)) s8 s9 s10 (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14668) fc None m1 (seg_rom rsegs)).
Proof.
  intros j HH ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 F fc m1 cells keys rf
    HF HFP (ML & H78 & H80) HL HE Hj -> -> -> -> ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  (* 0x14668 ld a2,0x78(sp) *)
  pose proof (read_le8 rsegs m1 (SP + 120) _ H78) as HR. step. clear HR.
  (* 0x1466c bge s8,t0 *)
  step. rewrite lts_s by lia.
  destruct (Z.ltb_spec (Z.of_nat j) (Z.of_nat n)) as [Hl|Hl]; cbn [negb]; cbv beta iota.
  - (* 0x14670 j 0x142b4 *)
    step. eapply (HH ltac:(lia)); [exact HF | exact HFP | exact ML | exact HL | exact HE | lia | reflexivity ..].
  - rewrite (pairs_end es j None) in HE by lia. rewrite ha_fold_nil in HE.
    eapply exit_ok; [exact HF | exact ML | exact (proj1 HL) | exact HE].
Qed.

(** 0x1465c .. 0x14664: the refusal t3 is stored when x->refusal is still NONE; then the latch. *)
Lemma fold_ok : forall j, ((j < n)%nat -> head_P j) ->
  forall (ra a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf bad : Z),
  frm0 fc -> FPinv F -> MemP m1 cells keys rf -> Linv cells keys rf j -> 0 <= bad <= 5 ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn j es) None) cells keys
                   (if rf =? REFUSE_NONE then bad else rf)) -> (j <= n)%nat ->
  s8 = Z_to_bv 64 (Z.of_nat j) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 104) (Z_to_bv 64 8)
             (Z_to_bv 64 (Z.of_nat (length cells))) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (-1)) s8 s9 s10 (Z_to_bv 64 (1 - Z.of_nat n)) (Z_to_bv 64 bad) t4 t5 t6)
        F (Z_to_bv 64 0x1465c) fc None m1 (seg_rom rsegs)).
Proof.
  intros j HH ra a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t4 t5 t6 F fc m1 cells keys rf bad
    HF HFP MP HL Hb HE Hj ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  pose proof MP as ((MB & HX & HN & HK & HR) & H78 & H80). pose proof MB as (MU & WM & MI & TM & ST & _).
  destruct HL as (HL1 & HL2 & HL3).
  (* 0x1465c lw a0,0x114(sp); bnez a0 *)
  pose proof (read_le4_cell rsegs m1 (SP + 276) _ HR) as HRd. step. clear HRd. rewrite sx32_small by lia.
  step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec rf 0) as [Er|Er]; cbn [negb]; cbv beta iota.
  - (* 0x14664 sw t3,0x114(sp) *)
    assert (HS : store_ok rsegs m1 (wa (SP + 276)) 4 = true)
      by (apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
    step.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
      change A with (wa (SP + 0x114));
      assert (MP2 : MemP (write_to_mem m1 (wa (SP + 0x114)) BS) cells keys bad)
        by (apply MemP_rf with (rf := rf); [exact MP | exact HL1 | rewrite length_le4; exact HS]);
      revert MP2; generalize (write_to_mem m1 (wa (SP + 0x114)) BS) as m2; intros m2 MP2
    end.
    subst rf. cbn [Z.eqb REFUSE_NONE] in HE.
    eapply latch_ok; [exact HH | exact HF | exact HFP | exact MP2 | split; [exact HL1 | split; lia] | exact HE
                     | exact Hj | reflexivity ..].
  - replace (if rf =? REFUSE_NONE then bad else rf) with rf in HE
      by (unfold REFUSE_NONE; rewrite (proj2 (Z.eqb_neq _ _) Er); reflexivity).
    eapply latch_ok; [exact HH | exact HF | exact HFP | exact MP | split; [exact HL1 | split; lia] | exact HE
                     | exact Hj | reflexivity ..].
Qed.

(** 0x14634 .. 0x14648: x->cell[n].param, x->cell[n].value, x->n = n + 1; then 0x1432c and the latch. *)
Lemma cellw2_ok : forall j, ((j < n)%nat -> head_P j) ->
  forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf ch p v : Z),
  frm0 fc -> FPinv F -> MemW m1 (Z.of_nat (length cells)) keys rf p v ->
  bytes_at rsegs m1 (SP + 0x94)
    (x_cells_bytes cells ++ le4 (Z_to_bv 64 ch) ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++
     repeat (Z_to_bv 8 0) (12 * (X_CELLS - S (length cells)))) ->
  Z.of_nat (length cells) < cap -> 0 <= keys <= Z.of_nat j -> 0 <= rf <= 5 ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn j es) None) (cells ++ [(ch, p, v)]) keys rf) ->
  (j <= n)%nat ->
  a1 = Z_to_bv 64 (SP + 148 + 12 * Z.of_nat (length cells)) -> s0 = Z_to_bv 64 (Z.of_nat (length cells) + 1) ->
  s8 = Z_to_bv 64 (Z.of_nat j) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (-1)) s8 s9 s10 (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14634) fc None m1 (seg_rom rsegs)).
Proof.
  intros j HH ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 F fc m1 cells keys rf ch p v
    HF HFP MW HX Hc HK HR HE Hj -> -> ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  assert (HL10 : (length cells < X_CELLS)%nat) by (unfold X_CELLS; lia).
  pose proof MW as ((MU & WM & MI & TM & ST & _) & H40 & H48 & _).
  (* 0x14634 ld a0,0x48(sp); sw a0,4(a1) *)
  pose proof (read_le8 rsegs m1 (SP + 72) _ H48) as HRd. step. clear HRd.
  assert (HS : store_ok rsegs m1 (wa (SP + 152 + 12 * Z.of_nat (length cells))) 4 = true)
    by (apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 152 + 12 * Z.of_nat (length cells)));
    assert (MW2 : MemW (write_to_mem m1 (wa (SP + 152 + 12 * Z.of_nat (length cells))) BS)
                    (Z.of_nat (length cells)) keys rf p v)
      by (apply MemW_store; rewrite ?length_le4; [exact MW | exact HS | lia | lia]);
    assert (HX2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 152 + 12 * Z.of_nat (length cells))) BS) (SP + 0x94)
                    ((x_cells_bytes cells ++ le4 (Z_to_bv 64 ch)) ++ BS ++ le4 (Z_to_bv 64 0) ++
                     repeat (Z_to_bv 8 0) (12 * (X_CELLS - S (length cells)))))
      by (apply bytes_at_write_at with (Y := le4 (Z_to_bv 64 0));
          [rewrite <- app_assoc; exact HX | rewrite !length_le4; reflexivity
          | rewrite length_app, length_x_cells_bytes, length_le4; lia]);
    revert MW2 HX2; generalize (write_to_mem m1 (wa (SP + 152 + 12 * Z.of_nat (length cells))) BS) as m2;
    intros m2 MW2 HX2
  end.
  clear MU WM MI TM ST H40 H48 HS MW HX.
  pose proof MW2 as ((MU & WM & MI & TM & ST & _) & H40 & H48 & _).
  (* 0x1463c ld a0,0x40(sp); sw a0,8(a1) *)
  pose proof (read_le8 rsegs m2 (SP + 64) _ H40) as HRd. step. clear HRd.
  assert (HS : store_ok rsegs m2 (wa (SP + 156 + 12 * Z.of_nat (length cells))) 4 = true)
    by (apply (stk_store_ok rsegs m2 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m2 ?A ?BS) _) =>
    change A with (wa (SP + 156 + 12 * Z.of_nat (length cells)));
    assert (MW3 : MemW (write_to_mem m2 (wa (SP + 156 + 12 * Z.of_nat (length cells))) BS)
                    (Z.of_nat (length cells)) keys rf p v)
      by (apply MemW_store; rewrite ?length_le4; [exact MW2 | exact HS | lia | lia]);
    assert (HX3 : bytes_at rsegs (write_to_mem m2 (wa (SP + 156 + 12 * Z.of_nat (length cells))) BS) (SP + 0x94)
                    (((x_cells_bytes cells ++ le4 (Z_to_bv 64 ch)) ++ le4 (Z_to_bv 64 p)) ++ BS ++
                     repeat (Z_to_bv 8 0) (12 * (X_CELLS - S (length cells)))))
      by (apply bytes_at_write_at with (Y := le4 (Z_to_bv 64 0));
          [rewrite <- (app_assoc (x_cells_bytes cells ++ le4 (Z_to_bv 64 ch))); exact HX2
          | rewrite !length_le4; reflexivity
          | rewrite !length_app, length_x_cells_bytes, !length_le4; lia]);
    revert MW3 HX3; generalize (write_to_mem m2 (wa (SP + 156 + 12 * Z.of_nat (length cells))) BS) as m3;
    intros m3 MW3 HX3
  end.
  clear MU WM MI TM ST H40 H48 HS MW2 HX2.
  rewrite <- !app_assoc in HX3. rewrite <- x_cellz_add in HX3 by exact HL10.
  pose proof MW3 as ((MU & WM & MI & TM & ST & _) & _).
  (* 0x14644 sw s0,0x10c(sp); j 0x1432c *)
  assert (HS : store_ok rsegs m3 (wa (SP + 268)) 4 = true)
    by (apply (stk_store_ok rsegs m3 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m3 ?A ?BS) _) =>
    change A with (wa (SP + 0x10c));
    assert (MP4 : MemP (write_to_mem m3 (wa (SP + 0x10c)) BS) (cells ++ [(ch, p, v)]) keys rf)
      by (apply MemW_fin with (p := p) (v := v);
          [exact MW3 | exact HX3 | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
          | rewrite length_le4; exact HS]);
    revert MP4; generalize (write_to_mem m3 (wa (SP + 0x10c)) BS) as m4; intros m4 MP4
  end.
  clear MU WM MI TM ST HS MW3 HX3.
  step.
  (* 0x1432c ld t0,0x80(sp); addi t1,zero,0x68; addi t2,zero,8; j 0x14668 *)
  pose proof MP4 as (_ & _ & H80).
  pose proof (read_le8 rsegs m4 (SP + 128) _ H80) as HRd. step. clear HRd. step. step. step.
  eapply latch_ok; [exact HH | exact HF | exact HFP | exact MP4 | | exact HE | exact Hj | | reflexivity ..].
  - split; [rewrite length_app; cbn [length]; lia | split; lia].
  - f_equal. rewrite length_app. cbn [length]. lia.
Qed.

(** 0x14618 .. 0x14630: x->cell[n].ch = ch; a1 := &x->cell[x->n], s0 := x->n + 1. *)
Lemma cellw_ok : forall j, ((j < n)%nat -> head_P j) ->
  forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf ch p v : Z),
  frm0 fc -> FPinv F -> MemP m1 cells keys rf -> Z.of_nat (length cells) < cap -> 0 <= keys <= Z.of_nat j ->
  0 <= rf <= 5 ->
  bytes_at rsegs m1 (SP + 0x40) (le8 (Z_to_bv 64 v)) -> bytes_at rsegs m1 (SP + 0x48) (le8 (Z_to_bv 64 p)) ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn j es) None) (cells ++ [(ch, p, v)]) keys rf) ->
  (j <= n)%nat ->
  s0 = Z_to_bv 64 (SP + 148 + 12 * Z.of_nat (length cells)) -> a2 = Z_to_bv 64 (SP + 148) ->
  s8 = Z_to_bv 64 (Z.of_nat j) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (-1)) s8 (Z_to_bv 64 ch) s10 (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14618) fc None m1 (seg_rom rsegs)).
Proof.
  intros j HH ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 t3 t4 t5 t6 F fc m1 cells keys rf ch p v
    HF HFP MP Hc HK HR H40 H48 HE Hj -> -> ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  assert (HL10 : (length cells < X_CELLS)%nat) by (unfold X_CELLS; lia).
  pose proof MP as ((MB & HX & HNc & HKc & HRc) & H78 & H80). pose proof MB as (MU & WM & MI & TM & ST & _).
  assert (MW : MemW m1 (Z.of_nat (length cells)) keys rf p v)
    by (exact (conj MB (conj H40 (conj H48 (conj H78 (conj H80 (conj HNc (conj HKc HRc)))))))).
  rewrite x_cellz_open in HX by exact HL10.
  (* 0x14618 sw s9,0(s0) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 148 + 12 * Z.of_nat (length cells))) 4 = true)
    by (apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 148 + 12 * Z.of_nat (length cells)));
    assert (MW2 : MemW (write_to_mem m1 (wa (SP + 148 + 12 * Z.of_nat (length cells))) BS)
                    (Z.of_nat (length cells)) keys rf p v)
      by (apply MemW_store; rewrite ?length_le4; [exact MW | exact HS | lia | lia]);
    assert (HX2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 148 + 12 * Z.of_nat (length cells))) BS) (SP + 0x94)
                    (x_cells_bytes cells ++ BS ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++
                     repeat (Z_to_bv 8 0) (12 * (X_CELLS - S (length cells)))))
      by (apply bytes_at_write_at with (Y := le4 (Z_to_bv 64 0));
          [exact HX | rewrite !length_le4; reflexivity | rewrite length_x_cells_bytes; lia]);
    revert MW2 HX2; generalize (write_to_mem m1 (wa (SP + 148 + 12 * Z.of_nat (length cells))) BS) as m2;
    intros m2 MW2 HX2
  end.
  clear MB MU WM MI TM ST HX HNc HKc HRc H78 H80 H40 H48 HS MW MP.
  pose proof MW2 as (_ & _ & _ & _ & _ & HN2 & _).
  (* 0x1461c lw s0,0x10c(sp); slli a0,s0,2; slli a1,s0,4; addiw s0,s0,1; sub a1,a1,a0; add a1,a2,a1 *)
  pose proof (read_le4_cell rsegs m2 (SP + 268) _ HN2) as HRd. step. clear HRd. rewrite sx32_small by lia.
  step. step. step. step. step.
  eapply cellw2_ok; [exact HH | exact HF | exact HFP | exact MW2 | exact HX2 | exact Hc | exact HK | exact HR | exact HE
                    | exact Hj | | | reflexivity].
  - apply Z_to_bv_eqm. rewrite ?unsigned_lit_wrap. rewrite ?Z.shiftl_mul_pow2 by lia. Z.div_mod_to_equations. lia.
  - weq.
Qed.

(** 0x14600 .. 0x14614: the cap test `bge s0,s2` (n >= cap: the loop stops), then &x->cell[n]. *)
Lemma write_ok : forall j k e, ((j < n)%nat -> head_P j) -> ha_prefix k = true ->
  forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf ch p v : Z),
  frm0 fc -> FPinv F -> MemP m1 cells (keys + 1) rf -> Linv cells (keys + 1) rf j ->
  bytes_at rsegs m1 (SP + 0x40) (le8 (Z_to_bv 64 v)) -> bytes_at rsegs m1 (SP + 0x48) (le8 (Z_to_bv 64 p)) ->
  expect_cell k e = inr (ch, p, v) ->
  E = ha_result (ha_fold expect_cell cap ((k, e) :: pairs_by key_of (skipn j es) None) cells keys rf) ->
  (j <= n)%nat ->
  s0 = Z_to_bv 64 (Z.of_nat (length cells)) -> s8 = Z_to_bv 64 (Z.of_nat j) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (-1)) s8 (Z_to_bv 64 ch) s10 (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14600) fc None m1 (seg_rom rsegs)).
Proof.
  intros j k e HH HP ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 t3 t4 t5 t6 F fc m1 cells keys rf ch p v
    HF HFP MP HL H40 H48 HC HE Hj -> ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn). destruct HL as (HL1 & HL2 & HL3).
  (* 0x14600 bge s0,s2 *)
  step. rewrite lts_s by lia.
  destruct (Z.ltb_spec (Z.of_nat (length cells)) cap) as [Hc|Hc]; cbn [negb]; cbv beta iota.
  2:{ rewrite (ha_fold_full expect_cell cap k e _ cells keys rf _ HP HC Hc) in HE.
      eapply exit_ok; [exact HF | exact (proj1 MP) | exact HL1 | exact HE]. }
  rewrite (ha_fold_add expect_cell cap k e _ cells keys rf _ HP HC Hc) in HE.
  (* 0x14604 slli a0,s0,2; slli s0,s0,4; sub s0,s0,a0; addi a2,sp,0x94; add s0,a2,s0 *)
  step. step. step. step. step.
  eapply cellw_ok; [exact HH | exact HF | exact HFP | exact MP | exact Hc | lia | lia | exact H40 | exact H48 | exact HE
                   | exact Hj | | | reflexivity].
  - apply Z_to_bv_eqm. rewrite ?unsigned_lit_wrap. rewrite ?Z.shiftl_mul_pow2 by lia. Z.div_mod_to_equations. lia.
  - weq.
Qed.

(** 0x1433c: the pair (k, ent[i + 1]) with the prefix: the key piece, then the refusal fold or the cap test. *)
Lemma pair_ok : forall i k, (S i < n)%nat -> ((S (S i) < n)%nat -> head_P (S (S i))) -> ha_prefix k = true ->
  forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf : Z),
  frm0 fc -> FPinv F -> MemP m1 cells keys rf -> Linv cells keys rf i ->
  E = ha_result (ha_fold expect_cell cap ((k, nth (S i) es (Ent 0 0 [])) :: pairs_by key_of (skipn (S (S i)) es) None)
                   cells keys rf) ->
  bytes_at rsegs m1 (pp + 16412 + 104 * Z.of_nat i) (k ++ [NUL]) -> ~ In NUL k -> (length k < 96)%nat ->
  a0 = Z_to_bv 64 0 -> s0 = Z_to_bv 64 (Z.of_nat (length cells)) -> s8 = Z_to_bv 64 (Z.of_nat i + 2) ->
  s9 = Z_to_bv 64 (Z.of_nat i) -> s10 = Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat i) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (-1)) s8 s9 s10 (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x1433c) fc None m1 (seg_rom rsegs)).
Proof.
  intros i k Hi HH HP ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 F fc m1 cells keys rf
    HF HFP MP HL HE HKB HNK HKL -> -> -> -> ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn). pose proof (proj1 HL) as HL1.
  pose proof MP as ((MB & HX & HN & HK & HR) & H78 & H80).
  pose proof MB as (MU & WM & MI & TM & ST & HPPB & H50 & H60 & H68 & H70 & H88).
  pose proof (ent_wf_nth r (S i) HWF Hi) as HEW.
  pose proof (bytes_at_ent rsegs m1 pp r (S i) HPPB HWF Hi) as HEB.
  pose proof HFP as (HF9 & HF18).
  apply (KEY Q ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length cells))) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 cap) s3 s4 s5 s6 (Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.of_nat i + 2)) (Z_to_bv 64 (Z.of_nat i))
           (Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat i)) (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6 F fc m1
           lo pp (pp + 16412 + 104 * Z.of_nat i) (Z.of_nat n) keys k (S i) (nth (S i) es (Ent 0 0 []))).
  - reflexivity.
  - reflexivity.
  - exact HKB.
  - exact HNK.
  - exact HP.
  - lia.
  - lia.
  - f_equal. lia.
  - lia.
  - exact HEB.
  - exact HEW.
  - exact HPP0.
  - exact HPPLO.
  - exact H68.
  - exact H70.
  - exact H80.
  - exact HK.
  - destruct HL as (_ & HL2 & _). lia.
  - exact HF9.
  - exact HF18.
  - exact H60.
  - exact H50.
  - exact ST.
  - exact HLO.
  - exact HSPA.
  - exact HROM.
  - exact HF.
  - exact MI.
  - exact TM.
  - (* a refusal: 0x1465c *)
    intros ra' a0' a1' a2' a3' a4' a5' a6' a7' s9' s10' t4' t5' t6' F' fc' m' bad HC HF' HFF MU' WM' MI' TM' ST' HK'.
    rewrite (ha_fold_bad expect_cell cap k _ _ cells keys rf bad HP HC) in HE.
    destruct HL as (_ & HL2 & HL3).
    eapply fold_ok; [exact HH | exact HF' | exact (FPinv_keep F F' HFP HFF)
                    | exact (MemP_key m1 m' cells keys rf MP HL1 MU' WM' MI' TM' ST' HK')
                    | split; [exact HL1 | split; lia]
                    | destruct (expect_cell_bad k _ bad HC) as [Eb|Eb]; rewrite Eb; unfold REFUSE_BAD_KEY, REFUSE_OUT_OF_RANGE; lia
                    | exact HE | lia | f_equal; lia].
  - (* a cell: 0x14600 *)
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' t5' t6' F' fc' m' ch p v HC HF' HFF MU' WM' MI'
      TM' ST' HK' H40 H48.
    destruct HL as (_ & HL2 & HL3).
    eapply write_ok; [exact HH | exact HP | exact HF' | exact (FPinv_keep F F' HFP HFF)
                     | exact (MemP_key m1 m' cells keys rf MP HL1 MU' WM' MI' TM' ST' HK')
                     | split; [exact HL1 | split; lia] | exact H40 | exact H48 | exact HC | exact HE | lia
                     | reflexivity | f_equal; lia].
Qed.

(** ** pod_next_pair's scan (0x142c4 .. 0x14328), by induction on the entries left *)
(** 0x142f4 .. 0x14308 with s10 = 0 (ent[i] is not a key): the next entry, or no pair is left. *)
Lemma nokey_ok : forall i, (i < n)%nat -> ((S i < n)%nat -> scan_P (S i)) ->
  forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf : Z),
  frm0 fc -> FPinv F -> MemL m1 cells keys rf -> Linv cells keys rf i ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn (S i) es) None) cells keys rf) ->
  s0 = Z_to_bv 64 (Z.of_nat (length cells)) -> s8 = Z_to_bv 64 (Z.of_nat i + 1) -> s9 = Z_to_bv 64 (Z.of_nat i - 1) ->
  a0 = Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat i) ->
  t0 = Z_to_bv 64 (Z.of_nat n) -> t1 = Z_to_bv 64 104 -> t2 = Z_to_bv 64 8 -> a2 = Z_to_bv 64 (pp + 16412) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (-1)) s8 s9 (Z_to_bv 64 0) (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x142f4) fc None m1 (seg_rom rsegs)).
Proof.
  intros i Hi HN ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 F fc m1 cells keys rf
    HF HFP ML HL HE -> -> -> -> -> -> -> ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  (* 0x142f4 add a1,s11,s9; beq a1,s7 *)
  step. step. rewrite eqb_s by lia.
  destruct (Z.eqb_spec (1 - Z.of_nat n + (Z.of_nat i - 1)) (-1)) as [Ee|Ee]; cbv beta iota.
  - rewrite (pairs_end es (S i) None) in HE by lia. rewrite ha_fold_nil in HE.
    eapply exit_ok; [exact HF | exact ML | exact (proj1 HL) | exact HE].
  - (* 0x142fc addi s9,s9,1; addiw s8,s8,1; addi a0,a0,0x68; beqz s10 *)
    step. step. step. step. if_true.
    destruct HL as (HL1 & HL2 & HL3).
    eapply (HN ltac:(lia)); [exact HF | exact HFP | exact ML | split; [exact HL1 | split; lia] | exact HE | lia
                            | weq ..].
Qed.

(** 0x142f4 .. 0x14328 with s10 = K (ent[i] is the key k): no value after it, or the saves, strncmp(k, prefix,
    13) and `beqz a0`. *)
Lemma key_ok : forall i k, (i < n)%nat -> ((S (S i) < n)%nat -> scan_P (S (S i))) ->
  forall (ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf : Z),
  frm0 fc -> FPinv F -> MemL m1 cells keys rf -> Linv cells keys rf i ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn (S i) es) (Some k)) cells keys rf) ->
  bytes_at rsegs m1 (pp + 16412 + 104 * Z.of_nat i) (k ++ [NUL]) -> ~ In NUL k -> (length k < 96)%nat ->
  s0 = Z_to_bv 64 (Z.of_nat (length cells)) -> s8 = Z_to_bv 64 (Z.of_nat i + 1) -> s9 = Z_to_bv 64 (Z.of_nat i - 1) ->
  t0 = Z_to_bv 64 (Z.of_nat n) -> t1 = Z_to_bv 64 104 -> t2 = Z_to_bv 64 8 -> a2 = Z_to_bv 64 (pp + 16412) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat i)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) s3 s4 s5 s6 (Z_to_bv 64 (-1)) s8 s9
             (Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat i)) (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x142f4) fc None m1 (seg_rom rsegs)).
Proof.
  intros i k Hi HN ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 F fc m1 cells keys rf
    HF HFP ML HL HE HKB HNK HKL -> -> -> -> -> -> ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  pose proof ML as ((MU & WM & MI & TM & ST & HPPB & H50 & H60 & H68 & H70 & H88) & HXm).
  (* 0x142f4 add a1,s11,s9; beq a1,s7 *)
  step. step. rewrite eqb_s by lia.
  destruct (Z.eqb_spec (1 - Z.of_nat n + (Z.of_nat i - 1)) (-1)) as [Ee|Ee]; cbv beta iota.
  { rewrite (pairs_end es (S i) (Some k)) in HE by lia. rewrite ha_fold_nil in HE.
    eapply exit_ok; [exact HF | exact ML | exact (proj1 HL) | exact HE]. }
  assert (HSi : (S i < n)%nat) by lia.
  (* 0x142fc addi s9,s9,1; addiw s8,s8,1; addi a0,a0,0x68; beqz s10 *)
  step. step. step. step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x1430c blt s9,s7 *)
  step. rewrite lts_s by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x14310 sd a2,0x78(sp) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 120)) 8 = true)
    by (apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 0x78));
    assert (ML2 : MemL (write_to_mem m1 (wa (SP + 0x78)) BS) cells keys rf)
      by (apply MemL_store78; rewrite ?length_le8; [exact ML | exact HS | lia | lia]);
    assert (H78 : bytes_at rsegs (write_to_mem m1 (wa (SP + 0x78)) BS) (SP + 0x78) (le8 (Z_to_bv 64 (pp + 16412))))
      by (apply bytes_at_write_same; rewrite ?length_le8; lia);
    assert (HKB2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 0x78)) BS) (pp + 16412 + 104 * Z.of_nat i) (k ++ [NUL]))
      by (apply bytes_at_write_other; rewrite ?length_le8, ?length_app; cbn [length]; [exact HKB | lia | lia | lia]);
    revert ML2 H78 HKB2; generalize (write_to_mem m1 (wa (SP + 0x78)) BS) as m2; intros m2 ML2 H78 HKB2
  end.
  clear MU WM MI TM ST HPPB H50 H60 H68 H70 H88 HXm HS ML HKB.
  pose proof ML2 as ((MU & WM & MI & TM & ST & _) & _).
  (* 0x14314 sd t0,0x80(sp) *)
  assert (HS : store_ok rsegs m2 (wa (SP + 128)) 8 = true)
    by (apply (stk_store_ok rsegs m2 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m2 ?A ?BS) _) =>
    change A with (wa (SP + 0x80));
    assert (MP3 : MemP (write_to_mem m2 (wa (SP + 0x80)) BS) cells keys rf);
    [ split; [apply MemL_store78; rewrite ?length_le8; [exact ML2 | exact HS | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le8; [exact H78 | lia | lia | lia]|];
      apply bytes_at_write_same; rewrite ?length_le8; lia
    | assert (HKB3 : bytes_at rsegs (write_to_mem m2 (wa (SP + 0x80)) BS) (pp + 16412 + 104 * Z.of_nat i) (k ++ [NUL]))
        by (apply bytes_at_write_other; rewrite ?length_le8, ?length_app; cbn [length]; [exact HKB2 | lia | lia | lia]);
      revert MP3 HKB3; generalize (write_to_mem m2 (wa (SP + 0x80)) BS) as m3; intros m3 MP3 HKB3 ]
  end.
  clear MU WM MI TM ST HS ML2 H78 HKB2.
  pose proof MP3 as (((_ & _ & MI & _ & _ & _ & _ & _ & _ & _ & H88) & _) & _).
  (* 0x14318 addi a2,zero,13; mv a0,s10; ld a1,0x88(sp); jal strncmp *)
  step. step.
  pose proof (read_le8 rsegs m3 (SP + 136) _ H88) as HRd. step. clear HRd.
  step.
  destruct (strncmp_prefix k HNK) as (v & HV & Hv & Hiff).
  eapply evt_cut.
  { eapply STRN with (ls := k ++ [NUL]) (rs := HA_PREFIX ++ [NUL]) (v := v).
    - rewrite unsigned_lit by lia. exact HKB3.
    - rewrite unsigned_lit by (unfold PREFIX_AT; lia). exact (proj1 (ParseSites.lits_at m3 MI)).
    - rewrite unsigned_lit by lia. exact HV.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4 & Ems & MU4 & WM4 &
              MI4 & HKB4 & _).
  subst ms'. ret_even. rewrite unsigned_lit in HKB4 by lia.
  pose proof (MemP_none m3 m4 cells keys rf MP3 MU4 WM4 MI4) as MP4.
  clear MP3 HKB3 MI H88.
  rewrite (pairs_value es i k HSi) in HE.
  (* 0x14328 beqz a0 *)
  step. rewrite eqb_s by lia.
  destruct (Z.eqb_spec v 0) as [Ev|Ev]; cbv beta iota.
  - (* the prefix: 0x1433c *)
    assert (HP : ha_prefix k = true) by (apply Hiff; exact Ev). subst v.
    eapply pair_ok; [exact HSi | intros Hl; apply head_ok; exact (HN Hl) | exact HP | exact HF | exact HFP | exact MP4
                    | exact HL | exact HE | exact HKB4 | exact HNK | exact HKL | weq ..].
  - (* no prefix: 0x1432c ld t0,0x80(sp); addi t1,zero,0x68; addi t2,zero,8; j 0x14668 *)
    assert (HP : ha_prefix k = false)
      by (destruct (ha_prefix k) eqn:X; [exfalso; apply Ev, Hiff; reflexivity | reflexivity]).
    rewrite (ha_fold_skip expect_cell cap k _ _ cells keys rf HP) in HE.
    pose proof MP4 as (_ & _ & H80).
    pose proof (read_le8 rsegs m4 (SP + 128) _ H80) as HRd. step. clear HRd. step. step. step.
    destruct HL as (HL1 & HL2 & HL3).
    eapply latch_ok; [intros Hl; apply head_ok; exact (HN Hl) | exact HF | exact HFP | exact MP4
                     | split; [exact HL1 | split; lia] | exact HE | lia | weq ..].
Qed.

(** 0x142c4 .. 0x142f0: pod_string(&pp->ent[i]) on an empty key slot. *)
Lemma scan_ok : forall K i, (n - i <= K)%nat -> scan_P i.
Proof.
  induction K as [|K IH]; intros i HK; unfold scan_P;
    intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 F fc m1 cells keys rf
      HF HFP ML HL HE Hi -> -> -> -> -> -> -> ->; [lia|].
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  assert (HN1 : (S i < n)%nat -> scan_P (S i)) by (intros _; apply IH; lia).
  assert (HN2 : (S (S i) < n)%nat -> scan_P (S (S i))) by (intros _; apply IH; lia).
  pose proof (ent_wf_nth r i HWF Hi) as (Ht0 & Hb & Hsz).
  pose proof ML as ((MU & WM & MI & TM & ST & HPPB & _) & _).
  pose proof (bytes_at_ent rsegs m1 pp r i HPPB HWF Hi) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat i) with (pp + 16404 + 104 * Z.of_nat i) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  (* 0x142c4 lw a1,-8(a0); bne a1,t2 *)
  pose proof (ent_type_read rsegs m1 _ _ HEB Ht0) as HR. step. clear HR.
  step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth i es (Ent 0 0 []))) 8) as [Et|Et]; cbn [negb]; cbv beta iota.
  2:{ assert (EK : key_of (nth i es (Ent 0 0 [])) = None)
        by (rewrite key_of_cases; unfold POD_STRING; rewrite (proj2 (Z.eqb_neq _ _) Et); reflexivity).
      rewrite (pairs_skip es i Hi EK) in HE.
      (* 0x142f0 mv s10,zero *)
      step. eapply nokey_ok; [exact Hi | exact HN1 | exact HF | exact HFP | exact ML | exact HL | exact HE | reflexivity ..]. }
  (* 0x142cc lw a1,-4(a0); beqz a1 *)
  pose proof (ent_size_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec (e_size (nth i es (Ent 0 0 []))) 0) as [Ez|Ez]; cbv beta iota.
  { assert (EK : key_of (nth i es (Ent 0 0 [])) = None)
      by (rewrite key_of_cases; rewrite Ez; cbn [Z.leb Z.compare]; rewrite andb_false_r; reflexivity).
    rewrite (pairs_skip es i Hi EK) in HE.
    step. eapply nokey_ok; [exact Hi | exact HN1 | exact HF | exact HFP | exact ML | exact HL | exact HE | reflexivity ..]. }
  (* 0x142d4 addi a1,a1,-1; slli a1,a1,32; srli a1,a1,32; add a1,a0,a1; lbu a1,0(a1) *)
  step. step. step. rewrite zext32_small by lia. step.
  pose proof (ent_byte_read rsegs m1 _ _ (Z.to_nat (e_size (nth i es (Ent 0 0 [])) - 1)) HEB ltac:(lia)) as HR.
  step. clear HR.
  (* 0x142e8 mv s10,a0; beqz a1 *)
  step. step. rewrite zxb_eqb0.
  destruct (Z.eqb_spec (bv_unsigned (nth (Z.to_nat (e_size (nth i es (Ent 0 0 [])) - 1))
                                         (e_body (nth i es (Ent 0 0 []))) NUL)) 0) as [Eb|Eb]; cbv beta iota.
  - (* a key: 0x142f4 *)
    assert (EK : key_of (nth i es (Ent 0 0 [])) = Some (cstr (e_body (nth i es (Ent 0 0 []))))).
    { rewrite key_of_cases. unfold POD_STRING, last_body_byte. rewrite (proj2 (Z.eqb_eq _ _) Et), Eb.
      rewrite (proj2 (Z.leb_le 1 _)) by lia. reflexivity. }
    rewrite (pairs_key es i _ Hi EK) in HE.
    assert (HNI : (nul_idx (e_body (nth i es (Ent 0 0 []))) < length (e_body (nth i es (Ent 0 0 []))))%nat).
    { pose proof (nul_idx_le_k (e_body (nth i es (Ent 0 0 []))) (Z.to_nat (e_size (nth i es (Ent 0 0 [])) - 1))
                    ltac:(lia) Eb). lia. }
    pose proof (ent_key_bytes rsegs m1 _ _ HEB HNI) as HKB.
    replace (pp + 16404 + 104 * Z.of_nat i + 8) with (pp + 16412 + 104 * Z.of_nat i) in HKB by lia.
    eapply key_ok; [exact Hi | exact HN2 | exact HF | exact HFP | exact ML | exact HL | exact HE | exact HKB
                   | apply cstr_no_nul | unfold cstr; rewrite length_firstn; lia | reflexivity ..].
  - (* not NUL-terminated: 0x142f0 *)
    assert (EK : key_of (nth i es (Ent 0 0 [])) = None).
    { rewrite key_of_cases. unfold last_body_byte. rewrite (proj2 (Z.eqb_neq _ _) Eb). rewrite andb_false_r. reflexivity. }
    rewrite (pairs_skip es i Hi EK) in HE.
    step. eapply nokey_ok; [exact Hi | exact HN1 | exact HF | exact HFP | exact ML | exact HL | exact HE | reflexivity ..].
Qed.

(** The loop from its first head (at = 0, no cell, no key, no refusal). *)
Theorem loop_start : forall (ra a0 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
                            (m1 : word -> option byte),
  frm0 fc -> FPinv F -> MemL m1 [] 0 REFUSE_NONE -> (0 < n)%nat ->
  E = ha_result (ha_fold expect_cell cap (pairs es) [] 0 REFUSE_NONE) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 104) (Z_to_bv 64 8) (Z_to_bv 64 0) s1 a0 a1
             (Z_to_bv 64 (pp + 16412)) a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s9 s10 (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x142b4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra a0 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 F fc m1 HF HFP ML Hn HE.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn32).
  pose proof (head_ok 0 (scan_ok n 0 ltac:(lia))) as H0. unfold head_P in H0.
  eapply H0; [exact HF | exact HFP | exact ML | | exact HE | exact Hn | reflexivity ..].
  unfold Linv, REFUSE_NONE. cbn [length Z.of_nat]. lia.
Qed.

End Pairs.

(** The loop with the frame and its facts stated in full: what the set-up of expect_of hands it. *)
Theorem pairs_loop : forall (sp gp tp s1 s3 s4 s5 s6 : word) (m : word -> option byte) (r : pod_rec) (cap pp lo : Z)
                            (Q : machine_state -> Prop) (E : answer),
  pod_rec_wf r -> 0 <= cap <= 9 -> 0 <= pp -> pp + POD_PROPS <= lo ->
  stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + NEAR_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
  (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
  key_stmt -> strncmp_contract ->
  (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
          (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
     frm0 fc' ->
     munch (EXPECT_W (bv_unsigned sp)) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
     stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS) ->
     bytes_at rsegs m' (bv_unsigned sp + 0x94) (x_tail E) ->
     evt rsegs Q
       (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 (ans_rc E)) s1
                a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 cap) s3 s4 s5 s6 s7' s8' s9' s10' s11' t3' t4' t5' t6')
           F' (Z_to_bv 64 0x14108) fc' None m' (seg_rom rsegs))) ->
  forall (ra a0 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte),
  frm0 fc -> FPinv F -> MemL sp m r pp lo m1 [] 0 REFUSE_NONE -> (0 < length (ents r))%nat ->
  E = ha_result (ha_fold expect_cell cap (pairs (ents r)) [] 0 REFUSE_NONE) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.of_nat (length (ents r)))) (Z_to_bv 64 104) (Z_to_bv 64 8) (Z_to_bv 64 0) s1
             a0 a1 (Z_to_bv 64 (pp + 16412)) a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s9 s10 (Z_to_bv 64 (1 - Z.of_nat (length (ents r)))) t3 t4 t5 t6)
        F (Z_to_bv 64 0x142b4) fc None m1 (seg_rom rsegs)).
Proof.
  intros sp gp tp s1 s3 s4 s5 s6 m r cap pp lo Q E HWF HCAP HPP0 HPPLO HST HLO HSPA HROM KEY STRN HQ
    ra a0 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 F fc m1 HF HFP ML Hn HE.
  eapply loop_start; eassumption.
Qed.
