(** The invariant of expect_of's pair loop (fuzz_headamp.c:119-155) in the UBSan LLVMFuzzerTestOneInput, at its head
    0x14268, and the statement [loop_stmt] that joins the head of expect_of (memset, the tests, the constants,
    0x14198 -> 0x14268) to the loop: from the head with no cell, no key and no refusal, every path reaches the store of
    x->rc and then 0x14784 with x the bytes of the fold's answer. [expect_cont] is U/Prog/HeadCheck/Cut.v
    [expect_stmt]'s continuation. The memory the loop carries: [MemB] the frame cells the constants made and the
    record, [MemX] x past x->rc (struct expect at sp + 0xb8: the cells, n, keys, refusal), [MemP] inside a pair the
    five saved registers at sp + 0x90 .. 0xb0. Statement text only: no function of a binary is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import PairFacts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadCheck Require Import Cut.
Import ListNotations.
Open Scope Z_scope.

(** The binary32 bounds of the inlined pod_nearest in fs1 / fs2 / fs3. *)
Definition FPinv (F : bvmap 5 word) : Prop :=
  Sem.reg_get F (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 F32_M1) /\
  Sem.reg_get F (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 F32_256) /\
  Sem.reg_get F (Z_to_bv 5 19) = Sem.nan_box (Z_to_bv 32 F32_2P63).

Lemma FPinv_keep : forall F F', FPinv F ->
  (forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r) -> FPinv F'.
Proof.
  intros F F' (H9 & H18 & H19) H. split; [|split].
  - rewrite H; [exact H9 | vm_compute; intros E; discriminate E | vm_compute; intros E; discriminate E].
  - rewrite H; [exact H18 | vm_compute; intros E; discriminate E | vm_compute; intros E; discriminate E].
  - rewrite H; [exact H19 | vm_compute; intros E; discriminate E | vm_compute; intros E; discriminate E].
Qed.

(** ~&pp->ent[0] and ~&pp->ent[0].body (s0 and ra of the loop), and the mulhu constant 104 << 32 (a6). *)
Definition NOT_ENT (pp : Z) : Z := 2^64 - 1 - (pp + OFF_ENT).
Definition NOT_BODY (pp : Z) : Z := 2^64 - 1 - (pp + OFF_ENT + 8).
Definition MULHU_104 : Z := 446676598784.

Section Inv.
Variables (sp : word) (m : word -> option byte) (r : pod_rec) (pp lo : Z).

Local Abbreviation SP := (bv_unsigned sp).

(** The frame cells and facts every cut of the loop carries: changed only in EXPECT_W, the record at pp, -0.5L's
    and 0.5L's high words, C2's words, &pp->n_ent, &pp->len, ~&x->cell[0] and 1000000. *)
Definition MemB (m1 : word -> option byte) : Prop :=
  munch (EXPECT_W SP) m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ MemNorm.task_mem rsegs m1 /\
  stk rsegs m1 lo (SP + FRAME_LOCALS) /\
  bytes_at rsegs m1 pp (pp_bytes r) /\
  bytes_at rsegs m1 (SP + 0x48) (le8 (Z_to_bv 64 MHALF_HI)) /\
  bytes_at rsegs m1 (SP + 0x50) (le8 (Z_to_bv 64 HALF_HI)) /\
  bytes_at rsegs m1 (SP + 0x58) (le8 (Z_to_bv 64 C2_HI)) /\
  bytes_at rsegs m1 (SP + 0x60) (le8 (Z_to_bv 64 C2_LO)) /\
  bytes_at rsegs m1 (SP + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
  bytes_at rsegs m1 (SP + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
  bytes_at rsegs m1 (SP + 0x80) (le8 (Z_to_bv 64 (2^64 - 1 - (SP + 0xbc)))) /\
  bytes_at rsegs m1 (SP + 0x88) (le8 (Z_to_bv 64 RC_BIG)).

(** x past x->rc for the fold's state (cells, keys, refusal): the cells part, n, keys, refusal. *)
Definition MemX (m1 : word -> option byte) (cells : list cell) (keys rf : Z) : Prop :=
  bytes_at rsegs m1 (SP + 0xbc) (x_cellz cells) /\
  bytes_at rsegs m1 (SP + 0x134) (le4 (Z_to_bv 64 (Z.of_nat (length cells)))) /\
  bytes_at rsegs m1 (SP + 0x138) (le4 (Z_to_bv 64 keys)) /\
  bytes_at rsegs m1 (SP + 0x13c) (le4 (Z_to_bv 64 rf)).

Definition MemL (m1 : word -> option byte) (cells : list cell) (keys rf : Z) : Prop :=
  MemB m1 /\ MemX m1 cells keys rf.

(** Inside the pair whose value is ent[v] (after 0x1431c): the next at = v + 1 and the saved ra, a7, a6, t6. *)
Definition MemP (m1 : word -> option byte) (cells : list cell) (keys rf : Z) (v : nat) : Prop :=
  MemL m1 cells keys rf /\
  bytes_at rsegs m1 (SP + 0x90) (le8 (Z_to_bv 64 (Z.of_nat v + 1))) /\
  bytes_at rsegs m1 (SP + 0x98) (le8 (Z_to_bv 64 MULHU_104)) /\
  bytes_at rsegs m1 (SP + 0xa0) (le8 (Z_to_bv 64 (pp + OFF_ENT + 8))) /\
  bytes_at rsegs m1 (SP + 0xa8) (le8 (Z_to_bv 64 (NOT_BODY pp))) /\
  bytes_at rsegs m1 (SP + 0xb0) (le8 (Z_to_bv 64 1)).

End Inv.

(** The fold's state at index j: at most cap cells, at most j keys (each pair takes two entries), a refusal code. *)
Definition Linv (cap : Z) (cells : list cell) (keys rf : Z) (j : nat) : Prop :=
  Z.of_nat (length cells) <= cap /\ 0 <= keys <= Z.of_nat j /\ 0 <= rf <= 5.

(** [expect_stmt]'s continuation at 0x14784 for the answer E. *)
Definition expect_cont (Q : machine_state -> Prop) (sp gp tp s1 s3 s4 s5 s6 : word) (m : word -> option byte)
    (cap lo : Z) (E : answer) : Prop :=
  forall (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    frm0 fc' ->
    munch (EXPECT_W (bv_unsigned sp)) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
    stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS) ->
    bytes_at rsegs m' (bv_unsigned sp + 0xb8) (x_bytes E) ->
    evt rsegs Q
      (MS (mkR ra' sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 cap) s3 s4 s5 s6 s7' s8' s9'
               s10' s11' t3' t4' t5' t6')
          F' (Z_to_bv 64 0x14784) fc' None m' (seg_rom rsegs)).

(** ** 0x14268 (at = 0, n = 0, no key, no refusal) -> 0x14784
    The loop's registers at its first head: ra = ~&pp->ent[0].body, s0 = ~&pp->ent[0], s8 = &pp->ent[0], a7 =
    &pp->ent[0].body, a6 = 104 << 32, a2 = &pp->n_ent, t5 = POD_STRING, t6 = pp->params_struct, a0 = at, s9 = n,
    s2 = cap; fs1 / fs2 / fs3 the nearest piece's bounds. *)
Definition loop_stmt : Prop :=
  forall (Q : machine_state -> Prop) (sp gp tp s1 s3 s4 s5 s6 : word) (m : word -> option byte) (r : pod_rec)
         (cap pp lo : Z),
    pod_rec_wf r -> 0 <= cap <= 9 -> 0 <= pp -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + NEAR_STACK <= bv_unsigned sp ->
    bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    params_struct r = true ->
    expect_cont Q sp gp tp s1 s3 s4 s5 s6 m cap lo (ha_result (ha_fold expect_cell cap (pairs (ents r)) [] 0 REFUSE_NONE)) ->
    forall (t0 t1 t2 a1 a3 a4 a5 s7 s10 s11 t3 t4 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
    frm0 fc -> FPinv F -> MemL sp m r pp lo m1 [] 0 REFUSE_NONE ->
    evt rsegs Q
      (MS (mkR (Z_to_bv 64 (NOT_BODY pp)) sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 (Z_to_bv 64 0) a1
               (Z_to_bv 64 (pp + POD_NENT_OFF)) a3 a4 a5 (Z_to_bv 64 MULHU_104) (Z_to_bv 64 (pp + OFF_ENT + 8))
               (Z_to_bv 64 cap) s3 s4 s5 s6 s7 (Z_to_bv 64 (pp + OFF_ENT)) (Z_to_bv 64 0) s10 s11 t3 t4
               (Z_to_bv 64 POD_STRING) (Z_to_bv 64 1))
          F (Z_to_bv 64 0x14268) fc None m1 (seg_rom rsegs)).
