(** The walk of the key piece of the checking segment of reac-pw/fuzz_headamp's LLVMFuzzerTestOneInput (plain,
    0x1433c -> 0x1465c / 0x14600: Prog/HeadCheck/Cut.v [key_stmt]), from strcmp's contract and [near_stmt] (the inlined
    pod_nearest, taken as a hypothesis). Section KeyWalk fixes key_stmt's frame (sp, gp, tp, the saved registers, the
    FP registers F, the entry memory m), the key k at K, the value e = ent[v] and the two continuations. Walked
    backwards: the exits (0x1465c, 0x14600, 0x1464c), the cap test 0x145e8, cell_value (0x144f4 pod_bool, 0x14514
    pod_int, 0x14538 pod_float with the nearest piece), &ent[v] and the type dispatch (0x144c0), big / ch > 47
    (0x144a8), the strcmp chain (0x14420), the used / '.' tests (0x14404), the digits loop (0x143d8, by induction on
    the bytes left), the first digit (0x143b4), the sign (0x14388), the blanks loop (0x1436c, by induction on the bytes
    left) and keys++ (0x1433c). The verdict agrees with Pod/Headamp.v [expect_cell] because each test the code makes
    decides one step of read_channel / expect_key / cell_value (Prog/HeadCheck/KeyFacts.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c strcmp_c
  ParseSites.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts Cut KeyFacts.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).
(* Register equations at a lemma's entry. *)
Ltac weq := first [ reflexivity
                  | (f_equal; lia)
                  | (f_equal; rewrite ?unsigned_lit by lia; lia) ].

(** ** Reads of byte runs *)
Lemma len_ent_mem : forall e, ent_wf e -> length (ent_mem e) = 104%nat.
Proof. intros e (_ & Hb & Hs). unfold ent_mem. rewrite !length_app, !length_le32, length_zeros. lia. Qed.

Lemma le8_le4 : forall w, le8 w = le4 w ++ skipn 4 (le8 w).
Proof. intros w. unfold le8, le4. rewrite <- store_bytes_8'. reflexivity. Qed.

Lemma read_le4_of_le8 : forall m A w, bytes_at rsegs m A (le8 w) -> ov_read_bytes rsegs m (wa A) 4 = Some (le4 w).
Proof. intros m A w H. rewrite le8_le4 in H. apply bytes_at_app in H as [H _]. exact (read_le4_cell rsegs m A w H). Qed.

Lemma bytes_at_suffix : forall m A l i, bytes_at rsegs m A l -> (i <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat i) (skipn i l).
Proof.
  intros m A l i H Hi. rewrite <- (firstn_skipn i l) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min i (length l)) with i in H by lia. exact H.
Qed.

Lemma byte_read : forall m A l i, bytes_at rsegs m A l -> (i < length l)%nat ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [nth i l NUL].
Proof.
  intros m A l i H Hi. rewrite (bytes_at_ov_read rsegs m A l i 1 H) by lia.
  rewrite (skipn_nth_cons l i NUL Hi). reflexivity.
Qed.

(** read_channel's `neg a0, a0; beq a0, a3` (used == 0, i.e. -d == k) never holds with k >= 1. *)
Lemma neg_ne_cnt : forall d kk, 0 <= d -> 1 <= kk -> d + kk < 2^64 ->
  bv_eqb (Z_to_bv 64 (0 - d)) (Z_to_bv 64 kk) = false.
Proof.
  intros d kk H1 H2 H3. unfold bv_eqb. rewrite !unsigned_lit_wrap. rewrite (Z.mod_small kk) by lia.
  apply Z.eqb_neq. destruct (Z.eq_dec d 0) as [->|Hd].
  - rewrite Z.sub_0_r, Zmod_0_l. lia.
  - replace ((0 - d) mod 2^64) with (2^64 - d) by (apply Z.mod_unique with (q := -1); lia). lia.
Qed.

Section KeyWalk.
Variables (Q : machine_state -> Prop) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s11 : word) (F : bvmap 5 word)
          (m : word -> option byte) (lo pp K nent keys : Z) (k : list byte) (v : nat) (e : ent).

Local Abbreviation SP := (bv_unsigned sp).
Local Abbreviation RS := (skipn 13 k).
Local Abbreviation EA := (pp + OFF_ENT + 104 * Z.of_nat v).

Hypothesis HKB : bytes_at rsegs m K (k ++ [NUL]).
Hypothesis HKN : ~ In NUL k.
Hypothesis HPF : ha_prefix k = true.
Hypothesis HK0 : 0 < K.
Hypothesis HKLO : K + Z.of_nat (length k) + 1 <= lo.
Hypothesis HV : (1 <= v < 32)%nat.
Hypothesis HEB : bytes_at rsegs m EA (ent_mem e).
Hypothesis HEW : ent_wf e.
Hypothesis HPP0 : 0 <= pp.
Hypothesis HPPLO : pp + POD_PROPS <= lo.
Hypothesis H68 : bytes_at rsegs m (SP + 0x68) (le8 (Z_to_bv 64 (pp + OFF_ENT))).
Hypothesis H70 : bytes_at rsegs m (SP + 0x70) (le8 (Z_to_bv 64 RC_BIG)).
Hypothesis H80 : bytes_at rsegs m (SP + 0x80) (le8 (Z_to_bv 64 nent)).
Hypothesis H110 : bytes_at rsegs m (SP + 0x110) (le4 (Z_to_bv 64 keys)).
Hypothesis HKEYS : 0 <= keys < 2^31 - 1.
Hypothesis HF9 : Sem.reg_get F (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 F32_M1).
Hypothesis HF18 : Sem.reg_get F (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 F32_256).
Hypothesis H60 : bytes_at rsegs m (SP + 0x60) (le8 (Z_to_bv 64 HALF_HI)).
Hypothesis H50 : bytes_at rsegs m (SP + 0x50) (le8 (Z_to_bv 64 MHALF_HI)).
Hypothesis HST : stk rsegs m lo (SP + FRAME_LOCALS).
Hypothesis HLO : lo + NEAR_STACK <= SP.
Hypothesis HSPA : SP mod 16 = 0.
Hypothesis HROM : forall a, lo <= a < SP + FRAME_LOCALS -> seg_rom rsegs (wa a) = None.
Hypothesis HMI : mem_inv rsegs m.
Hypothesis HTM : MemNorm.task_mem rsegs m.

(** The FP registers an exit may hold: F off f8 / f10. *)
Definition Fok (F' : bvmap 5 word) : Prop :=
  forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r.

Lemma Fok_refl : Fok F.
Proof. intros r _ _. reflexivity. Qed.

Hypothesis HBAD : forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' s9' s10' t4' t5' t6' : word) (F' : bvmap 5 word)
            (fc' : bv 32) (m' : word -> option byte) (bad : Z),
       expect_cell k e = inl bad ->
       frm0 fc' -> Fok F' ->
       munch (KEY_W SP) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (SP + FRAME_LOCALS) ->
       bytes_at rsegs m' (SP + 0x110) (le4 (Z_to_bv 64 (keys + 1))) ->
       evt rsegs Q
         (MS (mkR ra' sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9' s10' s11 (Z_to_bv 64 bad) t4' t5' t6')
             F' (Z_to_bv 64 0x1465c) fc' None m' (seg_rom rsegs)).

Hypothesis HCELL : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' t5' t6' : word)
            (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (ch p val : Z),
       expect_cell k e = inr (ch, p, val) ->
       frm0 fc' -> Fok F' ->
       munch (KEY_W SP) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (SP + FRAME_LOCALS) ->
       bytes_at rsegs m' (SP + 0x110) (le4 (Z_to_bv 64 (keys + 1))) ->
       bytes_at rsegs m' (SP + 0x40) (le8 (Z_to_bv 64 val)) ->
       bytes_at rsegs m' (SP + 0x48) (le8 (Z_to_bv 64 p)) ->
       evt rsegs Q
         (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 ch) s10' s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0x14600) fc' None m' (seg_rom rsegs)).

(** ** The memory the piece carries *)
(** Changed only in KEY_W; x->keys already incremented; the key, ent[v] and the frame cells it reads. *)
Definition MemK (m1 : word -> option byte) : Prop :=
  munch (KEY_W SP) m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ MemNorm.task_mem rsegs m1 /\
  stk rsegs m1 lo (SP + FRAME_LOCALS) /\ bytes_at rsegs m1 (SP + 0x110) (le4 (Z_to_bv 64 (keys + 1))) /\
  bytes_at rsegs m1 K (k ++ [NUL]) /\ bytes_at rsegs m1 EA (ent_mem e) /\
  bytes_at rsegs m1 (SP + 0x68) (le8 (Z_to_bv 64 (pp + OFF_ENT))) /\
  bytes_at rsegs m1 (SP + 0x70) (le8 (Z_to_bv 64 RC_BIG)) /\
  bytes_at rsegs m1 (SP + 0x80) (le8 (Z_to_bv 64 nent)) /\
  bytes_at rsegs m1 (SP + 0x60) (le8 (Z_to_bv 64 HALF_HI)) /\
  bytes_at rsegs m1 (SP + 0x50) (le8 (Z_to_bv 64 MHALF_HI)).

(** With the two cells sp + 0x40 and sp + 0x48 (from 0x14420 on). *)
Definition MemK2 (m1 : word -> option byte) (c40 c48 : Z) : Prop :=
  MemK m1 /\ bytes_at rsegs m1 (SP + 0x40) (le8 (Z_to_bv 64 c40)) /\ bytes_at rsegs m1 (SP + 0x48) (le8 (Z_to_bv 64 c48)).

Lemma kbounds : 0 <= lo /\ SP + FRAME_LOCALS <= 2^64 /\ EA + 104 <= lo /\ (13 <= length k)%nat /\
  lo + 48 <= SP /\ SP + 0x1b0 <= 2^64 /\ 0 <= EA.
Proof.
  pose proof HST as (ST0 & ST1 & _). pose proof (ha_prefix_len k HPF) as L.
  unfold POD_PROPS, OFF_ENT, NEAR_STACK, FRAME_LOCALS in *. lia.
Qed.

Lemma MemK_store_ok : forall m1 a n, MemK m1 -> SP + 0x30 <= a -> a + Z.of_nat n <= SP + 0x50 ->
  store_ok rsegs m1 (wa a) n = true.
Proof.
  intros m1 a n (_ & _ & _ & _ & ST & _) H1 H2. apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | |];
    unfold NEAR_STACK, FRAME_LOCALS in *; lia.
Qed.

Lemma MemK_store : forall m1 a bs, MemK m1 -> SP + 0x30 <= a -> a + Z.of_nat (length bs) <= SP + 0x50 ->
  MemK (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs MK H1 H2. pose proof (MemK_store_ok m1 a (length bs) MK H1 H2) as HS.
  destruct MK as (MU & WM & MI & TM & ST & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  pose proof kbounds as (B0 & B1 & B2 & B3). pose proof (len_ent_mem e HEW) as LE.
  unfold FRAME_LOCALS, NEAR_STACK in *.
  split; [apply munch_write; [exact MU | lia | lia | unfold KEY_W, NEAR_STACK; cbn [inside]; right; left; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI | exact HS]|].
  split; [apply task_mem_write; [exact TM | exact HS]|].
  split; [apply stk_write; [exact ST | lia | lia]|].
  split; [apply bytes_at_write_other; [exact C1 | lia | lia | rewrite length_le4; lia]|].
  split; [apply bytes_at_write_other; [exact C2 | lia | lia | rewrite length_app; cbn [length]; lia]|].
  split; [apply bytes_at_write_other; [exact C3 | lia | lia | rewrite LE; lia]|].
  split; [apply bytes_at_write_other; [exact C4 | lia | lia | rewrite length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact C5 | lia | lia | rewrite length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact C6 | lia | lia | rewrite length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact C7 | lia | lia | rewrite length_le8; lia]|].
  apply bytes_at_write_other; [exact C8 | lia | lia | rewrite length_le8; lia].
Qed.

Lemma MemK2_st40 : forall m1 c40 c48 x, MemK2 m1 c40 c48 ->
  MemK2 (write_to_mem m1 (wa (SP + 0x40)) (le8 (Z_to_bv 64 x))) x c48.
Proof.
  intros m1 c40 c48 x (MK & _ & C48). pose proof kbounds as (B0 & B1 & B2).
  split; [apply MemK_store; [exact MK | lia | rewrite length_le8; lia]|].
  split; [apply bytes_at_write_same; rewrite ?length_le8; lia|].
  apply bytes_at_write_other; [exact C48 | lia | rewrite length_le8; lia | rewrite !length_le8; lia].
Qed.

Lemma MemK2_st48 : forall m1 c40 c48 x, MemK2 m1 c40 c48 ->
  MemK2 (write_to_mem m1 (wa (SP + 0x48)) (le8 (Z_to_bv 64 x))) c40 x.
Proof.
  intros m1 c40 c48 x (MK & C40 & _). pose proof kbounds as (B0 & B1 & B2).
  split; [apply MemK_store; [exact MK | lia | rewrite length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact C40 | lia | rewrite length_le8; lia | rewrite !length_le8; lia]|].
  apply bytes_at_write_same; rewrite ?length_le8; lia.
Qed.

Lemma MemK2_init : forall m1 x y, MemK m1 ->
  MemK2 (write_to_mem (write_to_mem m1 (wa (SP + 0x40)) (le8 (Z_to_bv 64 x))) (wa (SP + 0x48)) (le8 (Z_to_bv 64 y))) x y.
Proof.
  intros m1 x y MK. pose proof kbounds as (B0 & B1 & B2).
  assert (MK1 : MemK (write_to_mem m1 (wa (SP + 0x40)) (le8 (Z_to_bv 64 x))))
    by (apply MemK_store; [exact MK | lia | rewrite length_le8; lia]).
  assert (C1 : bytes_at rsegs (write_to_mem m1 (wa (SP + 0x40)) (le8 (Z_to_bv 64 x))) (SP + 0x40) (le8 (Z_to_bv 64 x)))
    by (apply bytes_at_write_same; rewrite ?length_le8; lia).
  split; [apply MemK_store; [exact MK1 | lia | rewrite length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact C1 | lia | rewrite length_le8; lia | rewrite !length_le8; lia]|].
  apply bytes_at_write_same; rewrite ?length_le8; lia.
Qed.

(** pod_nearest's callees and stores: [(sp - 48, sp); (sp + 0x30, sp + 0x48)]. *)
Lemma MemK_near : forall m1 m2, MemK m1 ->
  munch [(SP - NEAR_STACK, SP); (SP + 0x30, SP + 0x48)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  MemNorm.task_mem rsegs m2 -> stk rsegs m2 lo (SP + FRAME_LOCALS) -> MemK m2.
Proof.
  intros m1 m2 (MU & WM & MI & TM & ST & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) MU2 WM2 MI2 TM2 ST2.
  pose proof kbounds as (B0 & B1 & B2 & B3). pose proof (len_ent_mem e HEW) as LE.
  unfold FRAME_LOCALS, NEAR_STACK in *.
  split.
  { apply (munch_trans _ m m1 m2 MU). eapply munch_weaken; [|exact MU2].
    unfold sub_fp, KEY_W, NEAR_STACK. cbn [outside]. intros x (O1 & O2 & O3 & _). split; [lia|]. split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
  split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2|].
  split; [apply (bytes_at_transport rsegs _ m1 m2 _ _ C1 MU2); cbn [disjoint_from]; rewrite length_le4; repeat split; lia|].
  split; [apply (bytes_at_transport rsegs _ m1 m2 _ _ C2 MU2); cbn [disjoint_from]; rewrite length_app; cbn [length];
          repeat split; lia|].
  split; [apply (bytes_at_transport rsegs _ m1 m2 _ _ C3 MU2); cbn [disjoint_from]; rewrite LE; repeat split; lia|].
  split; [apply (bytes_at_transport rsegs _ m1 m2 _ _ C4 MU2); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
  split; [apply (bytes_at_transport rsegs _ m1 m2 _ _ C5 MU2); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
  split; [apply (bytes_at_transport rsegs _ m1 m2 _ _ C6 MU2); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
  split; [apply (bytes_at_transport rsegs _ m1 m2 _ _ C7 MU2); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
  apply (bytes_at_transport rsegs _ m1 m2 _ _ C8 MU2); cbn [disjoint_from]; rewrite length_le8; repeat split; lia.
Qed.

(** The stored cell's memory, generalized (after `change` of the store's address to wa a). *)
Ltac kgen a mn MKn :=
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?A ?BS) _) =>
    change A with (wa a); revert MKn; generalize (write_to_mem m1 (wa a) BS); intros mn MKn
  end.

(** ** The exits *)
(** 0x1465c: the refusal fold. *)
Lemma bad_ok : forall (ra a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t4 t5 t6 : word) (F' : bvmap 5 word) (fc : bv 32)
    (m1 : word -> option byte) (bad : Z),
  expect_cell k e = inl bad -> frm0 fc -> Fok F' -> MemK m1 ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 bad) t4 t5 t6) F' (Z_to_bv 64 0x1465c) fc None m1
                  (seg_rom rsegs)).
Proof.
  intros ra a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t4 t5 t6 F' fc m1 bad HE HF HFk (MU & WM & MI & TM & ST & C1 & _).
  exact (HBAD ra a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t4 t5 t6 F' fc m1 bad HE HF HFk MU WM MI TM ST C1).
Qed.

(** 0x14600: the cap test, with the cell (ch, p, val). *)
Lemma cell_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc : bv 32)
    (m1 : word -> option byte) (ch p val : Z),
  expect_cell k e = inr (ch, p, val) -> frm0 fc -> Fok F' -> MemK2 m1 val p ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 ch) s10 s11
                  t3 t4 t5 t6) F' (Z_to_bv 64 0x14600) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 F' fc m1 ch p val HE HF HFk
    ((MU & WM & MI & TM & ST & C1 & _) & C40 & C48).
  exact (HCELL ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 F' fc m1 ch p val HE HF HFk MU WM MI TM ST C1 C40 C48).
Qed.

(** 0x1464c .. 0x14658: OUT_OF_RANGE, t0 .. t3 reloaded. *)
Lemma refuse5_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 : word) (F' : bvmap 5 word)
    (fc : bv 32) (m1 : word -> option byte),
  expect_cell k e = inl REFUSE_OUT_OF_RANGE -> frm0 fc -> Fok F' -> MemK m1 ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (Z_to_bv 64 0x1464c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 F' fc m1 HE HF HFk MK.
  pose proof MK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C80 & _).
  pose proof (read_le8 rsegs m1 _ _ C80) as HR. step. clear HR. step. step. step.
  exact (bad_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc m1 REFUSE_OUT_OF_RANGE HE HF HFk MK).
Qed.

(** 0x145e8 .. 0x145fc: value <= top (fuzz_headamp.c:141). *)
Lemma top_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc : bv 32)
    (m1 : word -> option byte) (ch p val : Z),
  frm0 fc -> Fok F' -> MemK2 m1 val p -> 0 <= val <= 255 ->
  expect_cell k e = (if ktop p <? val then inl REFUSE_OUT_OF_RANGE else inr (ch, p, val)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 ch)
                  (Z_to_bv 64 (ktop p)) s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x145e8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc m1 ch p val HF HFk MK2 Hv HE.
  pose proof MK2 as (MK & C40 & C48). pose proof MK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C80 & _).
  pose proof (ktop_range p) as Ht.
  (* 0x145e8 lw a0,0x40(sp) *)
  pose proof (read_le4_of_le8 m1 _ _ C40) as HR. step. clear HR. rewrite sx32_small by lia.
  (* 0x145ec ld t0,0x80(sp); addi t1,zero,0x68; addi t2,zero,8; addi t3,zero,5; bltu s10,a0 *)
  pose proof (read_le8 rsegs m1 _ _ C80) as HR. step. clear HR. step. step. step.
  step. rewrite ltu_u by lia.
  revert HE. destruct (Z.ltb_spec (ktop p) val) as [Hl|Hl]; cbv beta iota; intros HE.
  - exact (bad_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc m1 REFUSE_OUT_OF_RANGE HE HF HFk MK).
  - eapply cell_ok; [exact HE | exact HF | exact HFk | exact MK2].
Qed.

(** ** cell_value (fuzz_headamp.c:94-107) on ent[v] at a0 = EA, the cell p, ch and top known *)
(** 0x14514 .. 0x14534: pod_int, then 0 <= i < 256. *)
Lemma int_ok : forall (ra a1 a2 a4 a5 a6 a7 t4 t5 t6 : word) (fc : bv 32) (m1 : word -> option byte)
    (ch p c40 c48 : Z),
  frm0 fc -> MemK2 m1 c40 c48 -> e_type e = POD_INT ->
  expect_cell k e = (if (cell_value e <? 0) || (ktop p <? cell_value e) then inl REFUSE_OUT_OF_RANGE
                     else inr (ch, p, cell_value e)) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 (Z_to_bv 64 EA) a1 a2
                  (Z_to_bv 64 p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 ch) (Z_to_bv 64 (ktop p)) s11
                  (Z_to_bv 64 5) t4 t5 t6) F (Z_to_bv 64 0x14514) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra a1 a2 a4 a5 a6 a7 t4 t5 t6 fc m1 ch p c40 c48 HF MK2 Ht HE.
  pose proof kbounds as (B0 & B1 & B2). pose proof HEW as (Ht0 & Hb & Hsz).
  (* 0x14514 sd a3,0x48(sp) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 0x48)) 8 = true)
    by (apply (MemK_store_ok m1); [exact (proj1 MK2) | lia | lia]).
  step. clear HS. pose proof (MemK2_st48 m1 c40 c48 p MK2) as MK3. kgen (SP + 0x48) m2 MK3. clear MK2.
  pose proof MK3 as ((_ & _ & _ & _ & _ & _ & _ & C3 & _) & _ & _).
  (* 0x14518 lw a1,4(a0); addi a2,zero,4; bltu a1,a2 *)
  pose proof (ent_size_read rsegs m2 _ _ C3 ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size e) 4) as [Es|Es]; cbv beta iota.
  { assert (EB : expect_cell k e = inl REFUSE_OUT_OF_RANGE) by (rewrite HE, (cv_small e Es); reflexivity).
    exact (bad_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 _ EB HF Fok_refl (proj1 MK3)). }
  (* 0x14524 lw a1,8(a0); addi a0,zero,0x100; sd a1,0x40(sp); bltu a1,a0 *)
  pose proof (ent_word_read rsegs m2 _ _ C3 ltac:(lia)) as HR. step. clear HR.
  rewrite sext_rd32 by (rewrite length_firstn; lia). rewrite rd32_firstn.
  step.
  assert (HS : store_ok rsegs m2 (wa (SP + 0x40)) 8 = true)
    by (apply (MemK_store_ok m2); [exact (proj1 MK3) | lia | lia]).
  step. clear HS.
  pose proof (MemK2_st40 m2 c40 p (s32 (rd32 (e_body e))) MK3) as MK4. kgen (SP + 0x40) m3 MK4. clear MK3.
  pose proof (s32_range _ (rd32_range (e_body e))) as Hi.
  step. rewrite int_ltu256 by lia.
  pose proof (cv_int e Ht ltac:(lia)) as CV.
  destruct ((0 <=? s32 (rd32 (e_body e))) && (s32 (rd32 (e_body e)) <=? 255)) eqn:Ei; cbv beta iota in CV |- *.
  - apply andb_prop in Ei as [Ei1 Ei2]. apply Z.leb_le in Ei1. apply Z.leb_le in Ei2.
    eapply top_ok; [exact HF | exact Fok_refl | exact MK4 | lia |].
    rewrite HE, CV. rewrite (proj2 (Z.ltb_ge _ 0)) by lia. reflexivity.
  - (* 0x14534 j 0x1464c *)
    step. eapply refuse5_ok; [| exact HF | exact Fok_refl | exact (proj1 MK4)]. rewrite HE, CV. reflexivity.
Qed.

(** 0x144f4 .. 0x14510: pod_bool. *)
Lemma bool_ok : forall (ra a1 a2 a4 a5 a6 a7 t4 t5 t6 : word) (fc : bv 32) (m1 : word -> option byte)
    (ch p c40 c48 : Z),
  frm0 fc -> MemK2 m1 c40 c48 -> e_type e = POD_BOOL ->
  expect_cell k e = (if (cell_value e <? 0) || (ktop p <? cell_value e) then inl REFUSE_OUT_OF_RANGE
                     else inr (ch, p, cell_value e)) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 (Z_to_bv 64 EA) a1 a2
                  (Z_to_bv 64 p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 ch) (Z_to_bv 64 (ktop p)) s11
                  (Z_to_bv 64 5) t4 t5 t6) F (Z_to_bv 64 0x144f4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra a1 a2 a4 a5 a6 a7 t4 t5 t6 fc m1 ch p c40 c48 HF MK2 Ht HE.
  pose proof kbounds as (B0 & B1 & B2). pose proof HEW as (Ht0 & Hb & Hsz). pose proof (ktop_range p) as Htop.
  (* 0x144f4 sd a3,0x48(sp) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 0x48)) 8 = true)
    by (apply (MemK_store_ok m1); [exact (proj1 MK2) | lia | lia]).
  step. clear HS. pose proof (MemK2_st48 m1 c40 c48 p MK2) as MK3. kgen (SP + 0x48) m2 MK3. clear MK2.
  pose proof MK3 as ((_ & _ & _ & _ & _ & _ & _ & C3 & _) & _ & _).
  (* 0x144f8 lw a1,4(a0); addi a2,zero,4; bltu a1,a2 *)
  pose proof (ent_size_read rsegs m2 _ _ C3 ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size e) 4) as [Es|Es]; cbv beta iota.
  { assert (EB : expect_cell k e = inl REFUSE_OUT_OF_RANGE) by (rewrite HE, (cv_small e Es); reflexivity).
    exact (bad_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 _ EB HF Fok_refl (proj1 MK3)). }
  (* 0x14504 lw a0,8(a0); snez a0,a0; sd a0,0x40(sp); j 0x14600 *)
  pose proof (ent_word_read rsegs m2 _ _ C3 ltac:(lia)) as HR. step. clear HR.
  rewrite sext_rd32 by (rewrite length_firstn; lia). rewrite rd32_firstn.
  step. rewrite snez_s32 by (apply rd32_range).
  assert (HS : store_ok rsegs m2 (wa (SP + 0x40)) 8 = true)
    by (apply (MemK_store_ok m2); [exact (proj1 MK3) | lia | lia]).
  step. clear HS.
  pose proof (MemK2_st40 m2 c40 p (if negb (rd32 (e_body e) =? 0) then 1 else 0) MK3) as MK4.
  kgen (SP + 0x40) m3 MK4. clear MK3.
  step.
  pose proof (cv_bool e Ht ltac:(lia)) as CV.
  eapply cell_ok; [| exact HF | exact Fok_refl | exact MK4].
  rewrite HE, CV. destruct (negb (rd32 (e_body e) =? 0)); cbv beta iota.
  - replace (ktop p <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - replace (ktop p <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Hypothesis NEAR : near_stmt.

(** 0x14538 .. 0x14544: pod_float, then the nearest piece at 0x14548. *)
Lemma float_ok : forall (ra a1 a2 a4 a5 a6 a7 t4 t5 t6 : word) (fc : bv 32) (m1 : word -> option byte)
    (ch p c40 c48 : Z),
  frm0 fc -> MemK2 m1 c40 c48 -> e_type e = POD_FLOAT ->
  expect_cell k e = (if (cell_value e <? 0) || (ktop p <? cell_value e) then inl REFUSE_OUT_OF_RANGE
                     else inr (ch, p, cell_value e)) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 (Z_to_bv 64 EA) a1 a2
                  (Z_to_bv 64 p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 ch) (Z_to_bv 64 (ktop p)) s11
                  (Z_to_bv 64 5) t4 t5 t6) F (Z_to_bv 64 0x14538) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra a1 a2 a4 a5 a6 a7 t4 t5 t6 fc m1 ch p c40 c48 HF MK2 Ht HE.
  pose proof kbounds as (B0 & B1 & B2). pose proof HEW as (Ht0 & Hb & Hsz).
  (* 0x14538 sd a3,0x48(sp) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 0x48)) 8 = true)
    by (apply (MemK_store_ok m1); [exact (proj1 MK2) | lia | lia]).
  step. clear HS. pose proof (MemK2_st48 m1 c40 c48 p MK2) as MK3. kgen (SP + 0x48) m2 MK3. clear MK2.
  pose proof MK3 as ((MU & WM & MI & TM & ST & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) & C40 & C48).
  (* 0x1453c lw a1,4(a0); addi a2,zero,4; bltu a1,a2 *)
  pose proof (ent_size_read rsegs m2 _ _ C3 ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size e) 4) as [Es|Es]; cbv beta iota.
  { assert (EB : expect_cell k e = inl REFUSE_OUT_OF_RANGE) by (rewrite HE, (cv_small e Es); reflexivity).
    exact (bad_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 _ EB HF Fok_refl (proj1 MK3)). }
  (* 0x14548: pod_nearest(f, 0, 255) inlined *)
  apply NEAR with (lo := lo) (e := e).
  - rewrite unsigned_lit by lia. exact C3.
  - lia.
  - exact HF9.
  - exact HF18.
  - exact C7.
  - exact C8.
  - exact ST.
  - exact HLO.
  - exact HSPA.
  - exact HROM.
  - exact HF.
  - exact MI.
  - exact TM.
  - intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' HF' HFk MU' WM' MI' TM' ST'.
    pose proof (MemK_near m2 m' (proj1 MK3) MU' WM' MI' TM' ST') as MK'.
    assert (C48' : bytes_at rsegs m' (SP + 0x48) (le8 (Z_to_bv 64 p))).
    { apply (bytes_at_transport rsegs _ m2 m' _ _ C48 MU'). cbn [disjoint_from]. rewrite length_le8.
      unfold NEAR_STACK. repeat split; lia. }
    pose proof (cv_float e Ht ltac:(lia)) as CV.
    destruct (nearest (rd32 (e_body e)) 0 255) as [n|] eqn:EN; cbv beta iota.
    + intros C40'. pose proof (nearest_range _ _ _ _ EN) as Hn.
      eapply top_ok; [exact HF' | exact HFk | exact (conj MK' (conj C40' C48')) | lia |].
      rewrite HE, CV. rewrite (proj2 (Z.ltb_ge n 0)) by lia. reflexivity.
    + eapply refuse5_ok; [| exact HF' | exact HFk | exact MK']. rewrite HE, CV. reflexivity.
Qed.

(** 0x144c0 .. 0x144f0: &ent[v] (slli / mulhu with 104 << 32) and the type dispatch. *)
Lemma value_ok : forall (ra a0 a2 a4 a5 a6 a7 t4 t5 t6 : word) (fc : bv 32) (m1 : word -> option byte)
    (ch p c40 : Z),
  frm0 fc -> MemK2 m1 c40 (Z.of_nat v) ->
  expect_cell k e = (if (cell_value e <? 0) || (ktop p <? cell_value e) then inl REFUSE_OUT_OF_RANGE
                     else inr (ch, p, cell_value e)) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 a0
                  (Z_to_bv 64 (Z.of_nat v)) a2 (Z_to_bv 64 p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 ch)
                  (Z_to_bv 64 (ktop p)) s11 (Z_to_bv 64 5) t4 t5 t6) F (Z_to_bv 64 0x144c0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra a0 a2 a4 a5 a6 a7 t4 t5 t6 fc m1 ch p c40 HF MK2 HE.
  pose proof kbounds as (B0 & B1 & B2). pose proof HEW as (Ht0 & Hb & Hsz).
  pose proof MK2 as ((_ & _ & _ & _ & _ & _ & _ & C3 & C4 & _) & _ & _).
  (* 0x144c0 addi a0,zero,13; slli a0,a0,0x23; slli a1,a1,0x20; mulhu a0,a1,a0 *)
  step. step. step. step. rewrite mulhu_idx by lia.
  (* 0x144d0 ld a1,0x68(sp); add a0,a1,a0 *)
  pose proof (read_le8 rsegs m1 _ _ C4) as HR. step. clear HR. step.
  (* 0x144d8 lw a1,0(a0) *)
  pose proof (ent_type_read rsegs m1 _ _ C3 Ht0) as HR. step. clear HR.
  (* 0x144dc addi a2,zero,6; beq a1,a2 *)
  step. step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type e) 6) as [E6|E6]; cbv beta iota.
  { eapply float_ok; [exact HF | exact MK2 | exact E6 | exact HE]. }
  (* 0x144e4 addi a2,zero,4; beq a1,a2 *)
  step. step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type e) 4) as [E4|E4]; cbv beta iota.
  { eapply int_ok; [exact HF | exact MK2 | exact E4 | exact HE]. }
  (* 0x144ec addi a2,zero,2; bne a1,a2 *)
  step. step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type e) 2) as [E2|E2]; cbn [negb]; cbv beta iota.
  2:{ assert (EB : expect_cell k e = inl REFUSE_OUT_OF_RANGE)
        by (rewrite HE, (cv_other e) by (unfold POD_BOOL, POD_INT, POD_FLOAT; lia); reflexivity).
      exact (bad_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 _ EB HF Fok_refl (proj1 MK2)). }
  eapply bool_ok; [exact HF | exact MK2 | exact E2 | exact HE].
Qed.

(** 0x144a8 .. 0x144bc: big, then ch > 47 unsigned (fuzz_headamp.c:136). *)
Lemma range_ok : forall (ra a0 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (m1 : word -> option byte)
    (ch p : Z) (big : bool),
  frm0 fc -> MemK2 m1 (Z.b2z big) (Z.of_nat v) -> -2^63 <= ch < 2^63 ->
  expect_key RS = (if big || (ch <? 0) || (HA_CHANNELS <=? ch) then KRange else KCell ch p) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 a0 a1 a2 (Z_to_bv 64 p) a4
                  a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 ch) (Z_to_bv 64 (ktop p)) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x144a8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra a0 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 fc m1 ch p big HF MK2 Hch HK.
  pose proof MK2 as (MK & C40 & C48).
  (* 0x144a8 addi t3,zero,5; ld a1,0x48(sp); ld a0,0x40(sp); bnez a0 *)
  step. pose proof (read_le8 rsegs m1 _ _ C48) as HR. step. clear HR.
  pose proof (read_le8 rsegs m1 _ _ C40) as HR. step. clear HR.
  step. destruct big; cbn [orb] in HK.
  { if_true. assert (EB : expect_cell k e = inl REFUSE_OUT_OF_RANGE) by (rewrite expect_cell_key, HK; reflexivity).
    exact (bad_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 _ EB HF Fok_refl MK). }
  if_false.
  (* 0x144b8 addi a0,zero,0x2f; bltu a0,s9 *)
  step. step. rewrite range_gtu47 by lia.
  destruct ((ch <? 0) || (HA_CHANNELS <=? ch)) eqn:R; cbv beta iota.
  { assert (EB : expect_cell k e = inl REFUSE_OUT_OF_RANGE) by (rewrite expect_cell_key, HK; reflexivity).
    exact (bad_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 _ EB HF Fok_refl MK). }
  eapply value_ok; [exact HF | exact MK2 |]. rewrite expect_cell_key, HK. reflexivity.
Qed.

(** The C strings rest + j inside the key. *)
Lemma name_bytes : forall m1 j, bytes_at rsegs m1 K (k ++ [NUL]) -> (j <= length RS)%nat ->
  bytes_at rsegs m1 (K + 13 + Z.of_nat j) (skipn j RS ++ [NUL]).
Proof.
  intros m1 j H Hj. pose proof kbounds as (_ & _ & _ & L & _). rewrite length_skipn in Hj.
  pose proof (bytes_at_suffix m1 K (k ++ [NUL]) (13 + j) H ltac:(rewrite length_app; cbn [length]; lia)) as X.
  rewrite skipn_app in X. replace (13 + j - length k)%nat with 0%nat in X by lia. change (skipn 0 [NUL]) with [NUL] in X.
  rewrite skipn_skipn. replace (j + 13)%nat with (13 + j)%nat by lia.
  replace (K + 13 + Z.of_nat j) with (K + Z.of_nat (13 + j)) by lia. exact X.
Qed.

Lemma rest_byte : forall m1 i, MemK m1 -> (i <= length RS)%nat ->
  ov_read_bytes rsegs m1 (wa (K + 13 + Z.of_nat i)) 1 = Some [nth i RS NUL].
Proof.
  intros m1 i MK Hi. pose proof MK as (_ & _ & _ & _ & _ & _ & C2 & _).
  pose proof (name_bytes m1 0 C2 ltac:(lia)) as X. change (Z.of_nat 0) with 0 in X. change (skipn 0 RS) with RS in X.
  rewrite Z.add_0_r in X.
  rewrite (byte_read m1 (K + 13) (RS ++ [NUL]) i X) by (rewrite length_app; cbn [length]; lia).
  rewrite nth_app_nul. reflexivity.
Qed.

Hypothesis STRC : strcmp_contract.

(** 0x14420 .. 0x144a4: the cells big and v, name = rest + used + 1, strcmp against "phantom", "pad", "sens"
    (fuzz_headamp.c:132-133). *)
Lemma name_ok : forall (ra a1 a2 a4 a5 a6 a7 t6 : word) (fc : bv 32) (m1 : word -> option byte)
    (d kk : nat) (ch : Z) (big : bool),
  frm0 fc -> MemK m1 -> (d + kk < length RS)%nat -> -2^63 <= ch < 2^63 ->
  expect_key RS = (match param_of_name (skipn (S (d + kk)) RS) with
                   | None => KBad
                   | Some p => if big || (ch <? 0) || (HA_CHANNELS <=? ch) then KRange else KCell ch p
                   end) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 (Z_to_bv 64 46) a1 a2
                  (Z_to_bv 64 (Z.of_nat kk)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 ch)
                  (Z_to_bv 64 (K + Z.of_nat d)) s11 (Z_to_bv 64 4) (Z_to_bv 64 (Z.of_nat v)) (Z_to_bv 64 (Z.b2z big)) t6)
             F (Z_to_bv 64 0x14420) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra a1 a2 a4 a5 a6 a7 t6 fc m1 d kk ch big HF MK Hdk Hch HK.
  pose proof kbounds as (B0 & B1 & B2). pose proof (length_skipn 13 k) as LRS.
  (* 0x14420 sd t5,0x40(sp); sd t4,0x48(sp) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 0x40)) 8 = true) by (apply (MemK_store_ok m1); [exact MK | lia | lia]).
  step. clear HS.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A _) _) => change A with (wa (SP + 0x40)) end.
  assert (HS : store_ok rsegs (write_to_mem m1 (wa (SP + 0x40)) (le8 (Z_to_bv 64 (Z.b2z big)))) (wa (SP + 0x48)) 8 = true)
    by (apply MemK_store_ok; [apply MemK_store; [exact MK | lia | rewrite length_le8; lia] | lia | lia]).
  step. clear HS.
  pose proof (MemK2_init m1 (Z.b2z big) (Z.of_nat v) MK) as MK2. kgen (SP + 0x48) m2 MK2. clear MK.
  pose proof MK2 as ((_ & _ & MI2 & _ & _ & _ & C2 & _ & _ & _ & C80 & _) & _ & _).
  pose proof (name_bytes m2 (S (d + kk)) C2 ltac:(lia)) as HNB.
  pose proof (no_nul_skipn _ (S (d + kk)) (no_nul_skipn _ 13 HKN)) as HNN.
  pose proof (lits_at m2 MI2) as (_ & LPH & LPA & LSE). pose proof names_no_nul as (NPH & NPA & NSE).
  (* 0x14428 add a3,s10,a3; addi s10,a3,0xe; auipc a0; addi a1,a0,-0x101; mv a0,s10; jal strcmp *)
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply STRC with (sx := skipn (S (d + kk)) RS) (sy := NAME_PHANTOM).
    - match goal with |- bytes_at _ _ ?A _ => replace A with (K + 13 + Z.of_nat (S (d + kk))) by
        (rewrite ?unsigned_lit by lia; lia) end. exact HNB.
    - exact HNN.
    - match goal with |- bytes_at _ _ ?A _ => replace A with LIT_PHANTOM by (vm_compute; reflexivity) end. exact LPH.
    - exact NPH. }
  intros ms' (r1 & x11 & x12 & x13 & E & Hr). subst ms'. ret_even.
  (* 0x14440 beqz a0 *)
  step. destruct (bv_eqb r1 (Z_to_bv 64 0)) eqn:R1; cbv beta iota.
  { (* phantom: 0x14488 mv a3,zero; addi s10,zero,1; j 0x1449c; ld t0,0x80(sp); addi t1; addi t2 *)
    apply bv_eqb_true in R1. apply Hr in R1. rewrite (param_phantom _ R1) in HK. cbv beta iota in HK.
    step. step. step. pose proof (read_le8 rsegs m2 _ _ C80) as HR. step. clear HR. step. step.
    eapply range_ok with (p := HA_PHANTOM); [exact HF | exact MK2 | exact Hch | exact HK]. }
  assert (N1 : skipn (S (d + kk)) RS <> NAME_PHANTOM).
  { intros X. apply Hr in X. rewrite X in R1. unfold bv_eqb in R1. rewrite Z.eqb_refl in R1. discriminate R1. }
  (* 0x14444 auipc a0; addi a1,a0,0x1b; mv a0,s10; jal strcmp *)
  step. step. step. step.
  eapply evt_cut.
  { eapply STRC with (sx := skipn (S (d + kk)) RS) (sy := NAME_PAD).
    - match goal with |- bytes_at _ _ ?A _ => replace A with (K + 13 + Z.of_nat (S (d + kk))) by
        (rewrite ?unsigned_lit by lia; lia) end. exact HNB.
    - exact HNN.
    - match goal with |- bytes_at _ _ ?A _ => replace A with LIT_PAD by (vm_compute; reflexivity) end. exact LPA.
    - exact NPA. }
  intros ms' (r2 & y11 & y12 & y13 & E & Hr2). subst ms'. ret_even.
  (* 0x14454 beqz a0 *)
  step. destruct (bv_eqb r2 (Z_to_bv 64 0)) eqn:R2; cbv beta iota.
  { (* pad: 0x14494 addi s10,zero,1; addi a3,zero,1; ld t0,0x80(sp); addi t1; addi t2 *)
    apply bv_eqb_true in R2. apply Hr2 in R2. rewrite (param_pad _ N1 R2) in HK. cbv beta iota in HK.
    step. step. pose proof (read_le8 rsegs m2 _ _ C80) as HR. step. clear HR. step. step.
    eapply range_ok with (p := HA_PAD); [exact HF | exact MK2 | exact Hch | exact HK]. }
  assert (N2 : skipn (S (d + kk)) RS <> NAME_PAD).
  { intros X. apply Hr2 in X. rewrite X in R2. unfold bv_eqb in R2. rewrite Z.eqb_refl in R2. discriminate R2. }
  (* 0x14458 auipc a0; addi a1,a0,-0x1a0; mv a0,s10; jal strcmp *)
  step. step. step. step.
  eapply evt_cut.
  { eapply STRC with (sx := skipn (S (d + kk)) RS) (sy := NAME_SENS).
    - match goal with |- bytes_at _ _ ?A _ => replace A with (K + 13 + Z.of_nat (S (d + kk))) by
        (rewrite ?unsigned_lit by lia; lia) end. exact HNB.
    - exact HNN.
    - match goal with |- bytes_at _ _ ?A _ => replace A with LIT_SENS by (vm_compute; reflexivity) end. exact LSE.
    - exact NSE. }
  intros ms' (r3 & z11 & z12 & z13 & E & Hr3). subst ms'. ret_even.
  (* 0x14468 ld t0,0x80(sp); addi t1; addi t2; addi t3,zero,4; bnez a0 *)
  pose proof (read_le8 rsegs m2 _ _ C80) as HR. step. clear HR. step. step. step.
  step. destruct (bv_eqb r3 (Z_to_bv 64 0)) eqn:R3; cbn [negb]; cbv beta iota.
  { (* sens: 0x1447c addi a3,zero,2; addi s10,zero,0x37; j 0x144a8 *)
    apply bv_eqb_true in R3. apply Hr3 in R3. rewrite (param_sens _ N1 N2 R3) in HK. cbv beta iota in HK.
    step. step. step.
    eapply range_ok with (p := HA_SENS); [exact HF | exact MK2 | exact Hch | exact HK]. }
  assert (N3 : skipn (S (d + kk)) RS <> NAME_SENS).
  { intros X. apply Hr3 in X. rewrite X in R3. unfold bv_eqb in R3. rewrite Z.eqb_refl in R3. discriminate R3. }
  rewrite (param_none _ N1 N2 N3) in HK. cbv beta iota in HK.
  assert (EB : expect_cell k e = inl REFUSE_BAD_KEY) by (rewrite expect_cell_key, HK; reflexivity).
  exact (bad_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 _ EB HF Fok_refl (proj1 MK2)).
Qed.

(** 0x14404 .. 0x1441c: no digit (not here: kk >= 1), the sign, used = 0 (not here), rest[used] == '.'
    (fuzz_headamp.c:86-88, :128). *)
Lemma dot_ok : forall (ra a4 a5 a6 a7 t6 : word) (fc : bv 32) (m1 : word -> option byte)
    (d kk sn : nat) (acc : Z) (neg big : bool),
  frm0 fc -> MemK m1 ->
  rc_sign (skipn (rc_blanks RS) RS) = (neg, sn) -> d = (rc_blanks RS + sn)%nat ->
  rc_digits 0 false (skipn d RS) = (acc, big, kk) -> (1 <= kk)%nat -> (d + kk <= length RS)%nat ->
  0 <= acc <= 10000009 ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 (Z_to_bv 64 (Z.of_nat d))
                  (zxb (nth (d + kk) RS NUL)) (Z_to_bv 64 (if neg then 0 else 1)) (Z_to_bv 64 (Z.of_nat kk)) a4 a5 a6
                  a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 acc) (Z_to_bv 64 (K + Z.of_nat d)) s11 (Z_to_bv 64 4)
                  (Z_to_bv 64 (Z.of_nat v)) (Z_to_bv 64 (Z.b2z big)) t6) F (Z_to_bv 64 0x14404) fc None m1
                  (seg_rom rsegs)).
Proof.
  intros ra a4 a5 a6 a7 t6 fc m1 d kk sn acc neg big HF MK HSG Hd HD Hk Hdk Hacc.
  pose proof kbounds as (B0 & B1 & B2). pose proof (length_skipn 13 k) as LRS.
  assert (HRC : read_channel RS = ((d + kk)%nat, if neg then - acc else acc, big)).
  { rewrite Hd in HD. rewrite (read_channel_eq RS neg sn acc big kk HSG HD).
    destruct kk as [|kk']; [lia|]. cbn [Nat.eqb]. rewrite Hd. reflexivity. }
  pose proof (expect_key_read RS _ _ _ HRC) as HK.
  replace ((d + kk =? 0)%nat) with false in HK by (symmetry; apply Nat.eqb_neq; lia). cbn [orb] in HK.
  rewrite (cstr_id _ (no_nul_skipn _ _ (no_nul_skipn _ 13 HKN))) in HK.
  (* 0x14404 beqz a3 *)
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x14408 bnez a2 *)
  step. destruct neg; cbv beta iota in HK.
  - (* '-': 0x1440c neg s9,s9 *)
    if_false. step. rewrite (unsigned_lit acc) by lia. replace (0 - acc) with (- acc) by lia.
    (* 0x14410 neg a0,a0; beq a0,a3 *)
    step. step. rewrite (unsigned_lit (Z.of_nat d)) by lia.
    rewrite neg_ne_cnt by lia. cbv beta iota.
    (* 0x14418 addi a0,zero,0x2e; bne a1,a0 *)
    step. step. rewrite zxb_eqb by lia.
    destruct (Z.eqb_spec (bv_unsigned (nth (d + kk) RS NUL)) 46) as [E46|E46]; cbn [negb]; cbv beta iota.
    + cbn [negb] in HK. cbv beta iota in HK.
      eapply name_ok; [exact HF | exact MK | apply nth_nonnul_lt; lia | lia | exact HK].
    + cbn [negb] in HK. cbv beta iota in HK.
      assert (EB : expect_cell k e = inl REFUSE_BAD_KEY) by (rewrite expect_cell_key, HK; reflexivity).
      exact (bad_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 _ EB HF Fok_refl MK).
  - (* no '-': 0x14410 *)
    if_true.
    step. step. rewrite (unsigned_lit (Z.of_nat d)) by lia.
    rewrite neg_ne_cnt by lia. cbv beta iota.
    step. step. rewrite zxb_eqb by lia.
    destruct (Z.eqb_spec (bv_unsigned (nth (d + kk) RS NUL)) 46) as [E46|E46]; cbn [negb]; cbv beta iota.
    + cbn [negb] in HK. cbv beta iota in HK.
      eapply name_ok; [exact HF | exact MK | apply nth_nonnul_lt; lia | lia | exact HK].
    + cbn [negb] in HK. cbv beta iota in HK.
      assert (EB : expect_cell k e = inl REFUSE_BAD_KEY) by (rewrite expect_cell_key, HK; reflexivity).
      exact (bad_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 _ EB HF Fok_refl MK).
Qed.

(** The digits loop 0x143d8 .. 0x14400 (fuzz_headamp.c:79-85) at its digit j after d: the code's (acc, big) and
    rc_digits' fold agree. *)
Definition dig_P (d j : nat) : Prop :=
  forall (ra a0 a1 a4 a5 s9 s10 t6 : word) (fc : bv 32) (m1 : word -> option byte) (sn : nat) (acc : Z)
         (neg big : bool),
  frm0 fc -> MemK m1 ->
  rc_sign (skipn (rc_blanks RS) RS) = (neg, sn) -> d = (rc_blanks RS + sn)%nat ->
  rc_digit (nth (d + j) RS NUL) = true ->
  rc_digits 0 false (skipn d RS) =
    (fst (fst (rc_digits acc big (skipn (d + j) RS))), snd (fst (rc_digits acc big (skipn (d + j) RS))),
     (j + snd (rc_digits acc big (skipn (d + j) RS)))%nat) ->
  0 <= acc <= 10000009 ->
  a0 = Z_to_bv 64 (Z.of_nat d) -> a1 = zxb (nth (d + j) RS NUL) -> a4 = Z_to_bv 64 (K + Z.of_nat d + 14) ->
  s9 = Z_to_bv 64 acc -> s10 = Z_to_bv 64 (K + Z.of_nat d) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 a0 a1
                  (Z_to_bv 64 (if neg then 0 else 1)) (Z_to_bv 64 (Z.of_nat j)) a4 a5 (Z_to_bv 64 10)
                  (Z_to_bv 64 RC_BIG) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 4) (Z_to_bv 64 (Z.of_nat v))
                  (Z_to_bv 64 (Z.b2z big)) t6) F (Z_to_bv 64 0x143d8) fc None m1 (seg_rom rsegs)).

Lemma dig_ok : forall d L j, (length RS - (d + j) <= L)%nat -> dig_P d j.
Proof.
  intros d L. induction L as [|L IH]; intros j HL; unfold dig_P;
    intros ra a0 a1 a4 a5 s9 s10 t6 fc m1 sn acc neg big HF MK HSG Hd HDG HI Hacc -> -> -> -> ->;
    pose proof kbounds as (B0 & B1 & B2); pose proof (length_skipn 13 k) as LRS;
    pose proof HDG as Hc; unfold rc_digit in Hc; apply andb_prop in Hc as [Hc1 Hc2];
    apply Z.leb_le in Hc1; apply Z.leb_le in Hc2;
    assert (Hlt : (d + j < length RS)%nat) by (apply nth_nonnul_lt; lia).
  { lia. }
  unfold RC_BIG.
  pose proof (rc_digits_at RS (d + j) acc big) as RD. rewrite HDG in RD. cbv beta iota zeta in RD.
  (* 0x143d8 bge a7,s9 *)
  step. rewrite lts_s by lia.
  destruct (Z.ltb_spec 1000000 acc) as [Hb|Hb]; cbn [negb]; cbv beta iota in RD |- *.
  - (* acc > 1000000: 0x143dc addi t5,zero,1; 0x143e0 blt a7,s9 taken *)
    step. step. rewrite lts_s by lia. rewrite (proj2 (Z.ltb_lt _ _) Hb). cbv beta iota.
    (* 0x143f0 add a1,a4,a3; lbu a1,0(a1); addi a5,a1,-0x30; addi a3,a3,1; bltu a5,a6 *)
    step. pose proof (rest_byte m1 (S (d + j)) MK ltac:(lia)) as HR.
    replace (K + 13 + Z.of_nat (S (d + j))) with (K + Z.of_nat d + 14 + Z.of_nat j) in HR by lia.
    step. clear HR. step. step. step. rewrite digit_ltu10. replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia.
    pose proof (rc_digits_at RS (S (d + j)) acc true) as RD2.
    destruct (rc_digit (nth (S (d + j)) RS NUL)) eqn:HD2; cbv beta iota in RD2 |- *.
    + pose proof (IH (S j) ltac:(lia)) as IH1. unfold dig_P in IH1.
      eapply (IH1 _ _ _ _ _ _ _ _ fc m1 sn acc neg true); [exact HF | exact MK | exact HSG | exact Hd | | | lia | weq
        | (rewrite Nat.add_succ_r; reflexivity) | weq | weq | weq].
      * rewrite Nat.add_succ_r. exact HD2.
      * rewrite Nat.add_succ_r, HI, RD. cbn [fst snd]. f_equal. lia.
    + replace (S (d + j)) with (d + S j)%nat by lia.
      eapply (dot_ok _ _ _ _ _ _ fc m1 d (S j) sn acc neg true); [exact HF | exact MK | exact HSG | exact Hd | | lia | lia
        | lia].
      rewrite HI, RD, RD2. cbn [fst snd]. f_equal. lia.
  - (* acc <= 1000000: 0x143e0 blt a7,s9 not taken; mul s9,s9,a6; andi a1,a1,0xf; add s9,s9,a1 *)
    step. rewrite lts_s by lia. rewrite (proj2 (Z.ltb_ge _ _) Hb). cbv beta iota.
    step. step. step. rewrite (unsigned_lit acc) by lia. rewrite (digit_land _ HDG).
    step. pose proof (rest_byte m1 (S (d + j)) MK ltac:(lia)) as HR.
    replace (K + 13 + Z.of_nat (S (d + j))) with (K + Z.of_nat d + 14 + Z.of_nat j) in HR by lia.
    step. clear HR. step. step. step. rewrite digit_ltu10. replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia.
    pose proof (rc_digits_at RS (S (d + j)) (acc * 10 + (bv_unsigned (nth (d + j) RS NUL) - 48)) big) as RD2.
    destruct (rc_digit (nth (S (d + j)) RS NUL)) eqn:HD2; cbv beta iota in RD2 |- *.
    + pose proof (IH (S j) ltac:(lia)) as IH1. unfold dig_P in IH1.
      eapply (IH1 _ _ _ _ _ _ _ _ fc m1 sn (acc * 10 + (bv_unsigned (nth (d + j) RS NUL) - 48)) neg big);
        [exact HF | exact MK | exact HSG | exact Hd | | | lia | weq | (rewrite Nat.add_succ_r; reflexivity) | weq
        | weq | weq].
      * rewrite Nat.add_succ_r. exact HD2.
      * rewrite Nat.add_succ_r, HI, RD. cbn [fst snd]. f_equal. lia.
    + replace (S (d + j)) with (d + S j)%nat by lia.
      eapply (dot_ok _ _ _ _ _ _ fc m1 d (S j) sn (acc * 10 + (bv_unsigned (nth (d + j) RS NUL) - 48)) neg big);
        [exact HF | exact MK | exact HSG | exact Hd | | lia | lia | lia].
      rewrite HI, RD, RD2. cbn [fst snd]. f_equal. lia.
Qed.

(** 0x143b4 .. 0x143d4: the first digit test (fuzz_headamp.c:79, no digit: BAD_KEY) and the loop's set-up. *)
Lemma first_ok : forall (ra a0 a1 a2 a3 a4 a5 s9 s10 t3 t5 t6 : word) (fc : bv 32) (m1 : word -> option byte)
    (sn d : nat) (neg : bool),
  frm0 fc -> MemK m1 ->
  rc_sign (skipn (rc_blanks RS) RS) = (neg, sn) -> d = (rc_blanks RS + sn)%nat -> (d <= length RS)%nat ->
  a0 = Z_to_bv 64 (Z.of_nat d) -> a1 = zxb (nth d RS NUL) -> a2 = Z_to_bv 64 (if neg then 0 else 1) ->
  s10 = Z_to_bv 64 K ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 a0 a1 a2 a3 a4 a5
                  (Z_to_bv 64 10) (Z_to_bv 64 RC_BIG) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 (Z_to_bv 64 (Z.of_nat v)) t5
                  t6) F (Z_to_bv 64 0x143b4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra a0 a1 a2 a3 a4 a5 s9 s10 t3 t5 t6 fc m1 sn d neg HF MK HSG Hd Hdl -> -> -> ->.
  pose proof kbounds as (B0 & B1 & B2). pose proof (length_skipn 13 k) as LRS.
  (* 0x143b4 addi a3,a1,-0x30; addi t3,zero,4; addi a4,zero,9; bltu a4,a3 *)
  step. step. step. step. rewrite digit_gtu9.
  destruct (rc_digit (nth d RS NUL)) eqn:HDG; cbn [negb]; cbv beta iota.
  2:{ assert (HD : rc_digits 0 false (skipn d RS) = (0, false, O)) by (rewrite rc_digits_at, HDG; reflexivity).
      rewrite Hd in HD. pose proof (read_channel_eq RS neg sn 0 false O HSG HD) as HRC. cbn [Nat.eqb] in HRC.
      pose proof (expect_key_read RS _ _ _ HRC) as HK. cbn [Nat.eqb orb] in HK.
      assert (EB : expect_cell k e = inl REFUSE_BAD_KEY) by (rewrite expect_cell_key, HK; reflexivity).
      exact (bad_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 _ EB HF Fok_refl MK). }
  (* 0x143c4 mv a3,zero; mv t5,zero; mv s9,zero; add s10,s10,a0; addi a4,s10,0xe *)
  step. step. step. step. step.
  eapply (dig_ok d (length RS) 0 ltac:(lia) _ _ _ _ _ _ _ _ fc m1 sn 0 neg false);
    [exact HF | exact MK | exact HSG | exact Hd | rewrite Nat.add_0_r; exact HDG | | lia | weq
    | (rewrite Nat.add_0_r; reflexivity) | weq | weq | weq].
  rewrite Nat.add_0_r. destruct (rc_digits 0 false (skipn d RS)) as [[x y] z]. reflexivity.
Qed.

(** 0x14398 .. 0x143ac: after '+' or '-' at rc_blanks RS: the sign flag, the next byte, i + 1. *)
Lemma minus_ok : forall (ra a2 a3 a4 a5 s9 t3 t5 t6 : word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemK m1 ->
  bv_unsigned (nth (rc_blanks RS) RS NUL) = 43 \/ bv_unsigned (nth (rc_blanks RS) RS NUL) = 45 ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1
                  (Z_to_bv 64 (Z.of_nat (rc_blanks RS))) (zxb (nth (rc_blanks RS) RS NUL)) a2 a3 a4 a5
                  (Z_to_bv 64 10) (Z_to_bv 64 RC_BIG) s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 K) s11 t3
                  (Z_to_bv 64 (Z.of_nat v)) t5 t6) F (Z_to_bv 64 0x14398) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra a2 a3 a4 a5 s9 t3 t5 t6 fc m1 HF MK Hc.
  pose proof kbounds as (B0 & B1 & B2). pose proof (length_skipn 13 k) as LRS.
  assert (Hlt : (rc_blanks RS < length RS)%nat) by (apply nth_nonnul_lt; lia).
  (* 0x14398 addi a2,a1,-0x2d; add a1,s10,a0; lbu a1,0xe(a1); addi a0,a0,1; snez a2,a2; j 0x143b4 *)
  step. step.
  pose proof (rest_byte m1 (S (rc_blanks RS)) MK ltac:(lia)) as HR.
  replace (K + 13 + Z.of_nat (S (rc_blanks RS))) with (K + Z.of_nat (rc_blanks RS) + 14) in HR by lia.
  step. clear HR. step. step. rewrite (snez_sign _ Hc). step.
  pose proof (rc_sign_at RS (rc_blanks RS)) as HSG.
  replace ((bv_unsigned (nth (rc_blanks RS) RS NUL) =? 43) || (bv_unsigned (nth (rc_blanks RS) RS NUL) =? 45))
    with true in HSG by (destruct Hc as [Hc|Hc]; rewrite Hc; reflexivity).
  cbv beta iota in HSG.
  eapply (first_ok _ _ _ _ _ _ _ _ _ _ _ _ fc m1 1 (S (rc_blanks RS)) (bv_unsigned (nth (rc_blanks RS) RS NUL) =? 45));
    [exact HF | exact MK | exact HSG | lia | lia | weq | reflexivity | reflexivity | reflexivity].
Qed.

(** 0x14388 .. 0x143b0: the sign (fuzz_headamp.c:74-75). *)
Lemma sign_ok : forall (ra a2 a3 a4 a5 s9 t3 t5 t6 : word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemK m1 ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1
                  (Z_to_bv 64 (Z.of_nat (rc_blanks RS))) (zxb (nth (rc_blanks RS) RS NUL)) a2 a3 a4 a5
                  (Z_to_bv 64 10) (Z_to_bv 64 RC_BIG) s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 K) s11 t3
                  (Z_to_bv 64 (Z.of_nat v)) t5 t6) F (Z_to_bv 64 0x14388) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra a2 a3 a4 a5 s9 t3 t5 t6 fc m1 HF MK. pose proof (rc_blanks_le RS) as Hbl.
  (* 0x14388 addi a2,zero,0x2b; beq a1,a2 *)
  step. step. rewrite zxb_eqb by lia.
  destruct (Z.eqb_spec (bv_unsigned (nth (rc_blanks RS) RS NUL)) 43) as [E43|E43]; cbv beta iota.
  { eapply minus_ok; [exact HF | exact MK | left; exact E43]. }
  (* 0x14390 addi a2,zero,0x2d; bne a1,a2 *)
  step. step. rewrite zxb_eqb by lia.
  destruct (Z.eqb_spec (bv_unsigned (nth (rc_blanks RS) RS NUL)) 45) as [E45|E45]; cbn [negb]; cbv beta iota.
  { eapply minus_ok; [exact HF | exact MK | right; exact E45]. }
  (* 0x143b0 addi a2,zero,1 *)
  step.
  pose proof (rc_sign_at RS (rc_blanks RS)) as HSG.
  rewrite (proj2 (Z.eqb_neq _ _) E43), (proj2 (Z.eqb_neq _ _) E45) in HSG. cbn [orb] in HSG.
  eapply (first_ok _ _ _ _ _ _ _ _ _ _ _ _ fc m1 0 (rc_blanks RS) false);
    [exact HF | exact MK | exact HSG | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

(** The blanks loop 0x1436c .. 0x14384 (fuzz_headamp.c:70-72) at byte i <= rc_blanks RS. *)
Definition blank_P (i : nat) : Prop :=
  forall (ra a0 a1 a3 s9 t3 t5 t6 : word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemK m1 -> (i <= rc_blanks RS)%nat -> a0 = Z_to_bv 64 (Z.of_nat i) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 a0 a1
                  (Z_to_bv 64 (K + 13)) a3 (Z_to_bv 64 5) (Z_to_bv 64 32) (Z_to_bv 64 10) (Z_to_bv 64 RC_BIG)
                  s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 K) s11 t3 (Z_to_bv 64 (Z.of_nat v)) t5 t6)
             F (Z_to_bv 64 0x1436c) fc None m1 (seg_rom rsegs)).

Lemma blank_ok : forall L i, (length RS - i <= L)%nat -> blank_P i.
Proof.
  induction L as [|L IH]; intros i HL;
    assert (IHH : (S i <= rc_blanks RS)%nat -> blank_P (S i))
      by (intros Hs; pose proof (rc_blanks_le RS) as Hbl; first [exfalso; lia | apply IH; lia]);
    unfold blank_P; intros ra a0 a1 a3 s9 t3 t5 t6 fc m1 HF MK Hi ->;
    pose proof (rc_blanks_le RS) as Hbl; pose proof kbounds as (B0 & B1 & B2);
    pose proof (length_skipn 13 k) as LRS.
  all: (* 0x1436c add a1,a2,a0; lbu a1,0(a1); addi a3,a1,-9; bgeu a3,a4 *)
    step; pose proof (rest_byte m1 i MK ltac:(lia)) as HR; step; clear HR;
    step; step; rewrite zxb_add_ltu by lia;
    pose proof (rc_blank_code (nth i RS NUL)) as BC;
    destruct ((0 <=? bv_unsigned (nth i RS NUL) + -9) && (bv_unsigned (nth i RS NUL) + -9 <? 5)) eqn:BB1;
    cbn [negb orb] in BC |- *; cbv beta iota.
  all: try (step; step; eapply (IHH (rc_blanks_go RS i Hi BC)); [exact HF | exact MK | exact (rc_blanks_go RS i Hi BC)
              | weq]).
  all: (* 0x14384 beq a1,a5 *)
    step; rewrite zxb_eqb by lia;
    destruct (bv_unsigned (nth i RS NUL) =? 32) eqn:BB2; cbv beta iota.
  all: try (step; step; eapply (IHH (rc_blanks_go RS i Hi BC)); [exact HF | exact MK | exact (rc_blanks_go RS i Hi BC)
              | weq]).
  all: pose proof (rc_blanks_stop RS i Hi BC) as Ei; rewrite Ei; eapply sign_ok; [exact HF | exact MK].
Qed.

Lemma MemK_init : MemK (write_to_mem m (wa (SP + 0x110)) (le4 (Z_to_bv 64 (keys + 1)))).
Proof.
  pose proof kbounds as (B0 & B1 & B2 & B3). pose proof (len_ent_mem e HEW) as LE.
  assert (HS : store_ok rsegs m (wa (SP + 0x110)) (length (le4 (Z_to_bv 64 (keys + 1)))) = true)
    by (rewrite length_le4; apply (stk_store_ok rsegs m lo (SP + FRAME_LOCALS));
        [exact HST | unfold NEAR_STACK, FRAME_LOCALS in *; lia | unfold FRAME_LOCALS in *; lia]).
  unfold FRAME_LOCALS, NEAR_STACK in *.
  split; [apply munch_write; [apply munch_refl | lia | rewrite length_le4; lia
                             | unfold KEY_W, NEAR_STACK; cbn [inside]; rewrite length_le4; right; right; left; lia]|].
  split; [apply wmono_write; apply wmono_refl|].
  split; [apply mem_inv_store; [exact HMI | exact HS]|].
  split; [apply task_mem_write; [exact HTM | exact HS]|].
  split; [apply stk_write; [exact HST | lia | rewrite length_le4; lia]|].
  split; [apply bytes_at_write_same; rewrite ?length_le4; lia|].
  split; [apply bytes_at_write_other; [exact HKB | lia | rewrite length_le4; lia
                                      | rewrite length_le4, length_app; cbn [length]; lia]|].
  split; [apply bytes_at_write_other; [exact HEB | lia | rewrite length_le4; lia | rewrite length_le4, LE; lia]|].
  split; [apply bytes_at_write_other; [exact H68 | lia | rewrite length_le4; lia | rewrite length_le4, length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact H70 | lia | rewrite length_le4; lia | rewrite length_le4, length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact H80 | lia | rewrite length_le4; lia | rewrite length_le4, length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact H60 | lia | rewrite length_le4; lia | rewrite length_le4, length_le8; lia]|].
  apply bytes_at_write_other; [exact H50 | lia | rewrite length_le4; lia | rewrite length_le4, length_le8; lia].
Qed.

(** 0x1433c .. 0x14368: x->keys++ (fuzz_headamp.c:122), rest = K + 13, the constants of read_channel. *)
Lemma key_entry : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
  frm0 fc ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                  (Z_to_bv 64 (Z.of_nat v - 1)) (Z_to_bv 64 K) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1433c) fc None m
                  (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc HF.
  pose proof kbounds as (B0 & B1 & B2). pose proof (length_skipn 13 k) as LRS.
  (* 0x1433c lw a1,0x110(sp); addi t4,s9,1; addi a1,a1,1; sw a1,0x110(sp) *)
  pose proof (read_le4_cell rsegs m _ _ H110) as HR. step. clear HR. rewrite sx32_small by lia.
  step. step.
  assert (HS : store_ok rsegs m (wa (SP + 0x110)) 4 = true)
    by (apply (stk_store_ok rsegs m lo (SP + FRAME_LOCALS));
        [exact HST | unfold NEAR_STACK in *; lia | unfold FRAME_LOCALS in *; lia]).
  step. clear HS.
  pose proof MemK_init as MK. kgen (SP + 0x110) m1 MK.
  pose proof MK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & C70 & C80 & _).
  (* 0x1434c addi a2,s10,0xd; ld t0,0x80(sp); addi t1; addi t2; addi a4,zero,5; addi a5,zero,0x20; addi a6,zero,10;
     ld a7,0x70(sp) *)
  step. pose proof (read_le8 rsegs m1 _ _ C80) as HR. step. clear HR. step. step. step. step. step.
  pose proof (read_le8 rsegs m1 _ _ C70) as HR. step. clear HR.
  replace (Z.of_nat v - 1 + 1) with (Z.of_nat v) by lia.
  eapply (blank_ok (length RS) 0 ltac:(lia)); [exact HF | exact MK | lia | reflexivity].
Qed.

End KeyWalk.

(** [key_stmt] from strcmp's contract and the nearest piece's statement. *)
Theorem key_holds : strcmp_contract -> near_stmt -> key_stmt.
Proof.
  intros STRC NEAR. unfold key_stmt.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo pp K nent keys k v e -> -> HKB HKN HPF HK0 HKLO -> HV HEB HEW HPP0 HPPLO H68 H70 H80 H110 HKEYS HF9 HF18 H60 H50
    HST HLO HSPA HROM HFC HMI HTM HBAD HCELL.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat v) with (pp + OFF_ENT + 104 * Z.of_nat v) in HEB by (unfold ENT_SIZE; lia).
  eapply (key_entry Q sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s11 F m lo pp K nent keys k v e); eassumption.
Qed.
