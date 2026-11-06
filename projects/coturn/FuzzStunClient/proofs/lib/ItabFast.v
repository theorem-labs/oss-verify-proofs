(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From Stdlib Require Import Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2.

(* [comment removed for export] *)
Fixpoint pt_forall {A} (f : positive -> A -> bool) (t : ptree A) (path : positive -> positive) : bool :=
  match t with
  | PTLeaf => true
  | PTNode l o r =>
      if (match o with Some v => f (path xH) v | None => true end)
      then (if pt_forall f l (fun p => path (xO p)) then pt_forall f r (fun p => path (xI p)) else false)
      else false
  end.

Lemma pt_forall_sound {A} (f : positive -> A -> bool) : forall t path k v,
  pt_forall f t path = true -> pt_get t k = Some v -> f (path k) v = true.
Proof.
  induction t as [|l IHl o r IHr]; intros path k v H G; [rewrite pt_get_leaf in G; discriminate|].
  cbn [pt_forall] in H. destruct (match o with Some v => f (path xH) v | None => true end) eqn:Ho; [|discriminate].
  destruct (pt_forall f l (fun p => path (xO p))) eqn:Hl; [|discriminate].
  destruct k as [k|k|]; cbn [pt_get] in G.
  - exact (IHr (fun p => path (xI p)) k v H G).
  - exact (IHl (fun p => path (xO p)) k v Hl G).
  - subst o. exact Ho.
Qed.

Section Agree.
  Variable segs : list Segment.
  Definition instr_eqb (i j : instr) : bool := if instr_eq_dec i j then true else false.
  Definition itab_agrees (t : itab) : bool :=
    pt_forall (fun p i => match itab_entry segs (Zpos p) with Some i' => instr_eqb i' i | None => false end) t (fun p => p).
  Lemma itab_agrees_sound t : itab_agrees t = true -> itab_sound segs t.
  Proof.
    intros H pc i Hl. destruct pc as [|p|p]; cbn [itab_lookup] in Hl; try discriminate.
    pose proof (pt_forall_sound _ t (fun p => p) p i H Hl) as X. cbn beta in X.
    destruct (itab_entry segs (Zpos p)) as [i'|]; [|discriminate].
    unfold instr_eqb in X. destruct (instr_eq_dec i' i) as [->|]; [reflexivity|discriminate].
  Qed.
End Agree.

(* [comment removed for export] *)
Local Notation "a + b" := (PrimInt63.add a b).
Local Notation "a - b" := (PrimInt63.sub a b).

Definition c6 (s : string) (i : int) : int := PrimString.get s i - 35%uint63.

Fixpoint rd_var (f : nat) (s : string) (i sh acc : int) : int * int :=
  match f with
  | O => (acc, i)
  | S f' =>
      let d := c6 s i in
      if PrimInt63.ltb d 32%uint63 then (PrimInt63.lor acc (PrimInt63.lsl d sh), i + 1%uint63)
      else rd_var f' s (i + 1%uint63) (sh + 5%uint63) (PrimInt63.lor acc (PrimInt63.lsl (d - 32%uint63) sh))
  end.
Definition rdv (s : string) (i : int) : int * int := rd_var 13 s i 0%uint63 0%uint63.

(* [comment removed for export] *)
Fixpoint i2z (f : nat) (x : int) : Z :=
  match f with
  | O => 0%Z
  | S f' => if PrimInt63.eqb x 0%uint63 then 0%Z
            else if PrimInt63.eqb (PrimInt63.land x 1%uint63) 0%uint63 then Z.double (i2z f' (PrimInt63.lsr x 1%uint63))
            else Z.succ_double (i2z f' (PrimInt63.lsr x 1%uint63))
  end.
Definition bvf (n : N) (x : int) : bv n := Z_to_bv n (i2z 64 x).
Definition boolf (x : int) : bool := negb (PrimInt63.eqb x 0%uint63).

Definition aluop_of (k : int) : aluop := if PrimInt63.eqb k 0%uint63 then ALU_ADD else if PrimInt63.eqb k 1%uint63 then ALU_SUB else if PrimInt63.eqb k 2%uint63 then ALU_SLL else if PrimInt63.eqb k 3%uint63 then ALU_SLT else if PrimInt63.eqb k 4%uint63 then ALU_SLTU else if PrimInt63.eqb k 5%uint63 then ALU_XOR else if PrimInt63.eqb k 6%uint63 then ALU_SRL else if PrimInt63.eqb k 7%uint63 then ALU_SRA else if PrimInt63.eqb k 8%uint63 then ALU_OR else ALU_AND.
Definition mulop_of (k : int) : mulop := if PrimInt63.eqb k 0%uint63 then M_MUL else if PrimInt63.eqb k 1%uint63 then M_MULH else if PrimInt63.eqb k 2%uint63 then M_MULHSU else if PrimInt63.eqb k 3%uint63 then M_MULHU else if PrimInt63.eqb k 4%uint63 then M_DIV else if PrimInt63.eqb k 5%uint63 then M_DIVU else if PrimInt63.eqb k 6%uint63 then M_REM else M_REMU.
Definition branch_cond_of (k : int) : branch_cond := if PrimInt63.eqb k 0%uint63 then BC_EQ else if PrimInt63.eqb k 1%uint63 then BC_NE else if PrimInt63.eqb k 2%uint63 then BC_LT else if PrimInt63.eqb k 3%uint63 then BC_GE else if PrimInt63.eqb k 4%uint63 then BC_LTU else BC_GEU.
Definition msize_of (k : int) : msize := if PrimInt63.eqb k 0%uint63 then SZ1 else if PrimInt63.eqb k 1%uint63 then SZ2 else if PrimInt63.eqb k 2%uint63 then SZ4 else SZ8.
Definition amoop_of (k : int) : amoop := if PrimInt63.eqb k 0%uint63 then AMO_SWAP else if PrimInt63.eqb k 1%uint63 then AMO_ADD else if PrimInt63.eqb k 2%uint63 then AMO_XOR else if PrimInt63.eqb k 3%uint63 then AMO_AND else if PrimInt63.eqb k 4%uint63 then AMO_OR else if PrimInt63.eqb k 5%uint63 then AMO_MIN else if PrimInt63.eqb k 6%uint63 then AMO_MAX else if PrimInt63.eqb k 7%uint63 then AMO_MINU else AMO_MAXU.
Definition awidth_of (k : int) : awidth := if PrimInt63.eqb k 0%uint63 then AW else AD.
Definition csrop_of (k : int) : csrop := if PrimInt63.eqb k 0%uint63 then CSR_RW else if PrimInt63.eqb k 1%uint63 then CSR_RS else CSR_RC.
Definition ffmt_of (k : int) : ffmt := if PrimInt63.eqb k 0%uint63 then FMT_S else FMT_D.
Definition fariop_of (k : int) : fariop := if PrimInt63.eqb k 0%uint63 then F_ADD else if PrimInt63.eqb k 1%uint63 then F_SUB else if PrimInt63.eqb k 2%uint63 then F_MUL else F_DIV.
Definition fmaop_of (k : int) : fmaop := if PrimInt63.eqb k 0%uint63 then F_MADD else if PrimInt63.eqb k 1%uint63 then F_MSUB else if PrimInt63.eqb k 2%uint63 then F_NMSUB else F_NMADD.
Definition fsgnop_of (k : int) : fsgnop := if PrimInt63.eqb k 0%uint63 then F_SGNJ else if PrimInt63.eqb k 1%uint63 then F_SGNJN else F_SGNJX.
Definition fminmaxop_of (k : int) : fminmaxop := if PrimInt63.eqb k 0%uint63 then F_MIN else F_MAX.
Definition fcmpop_of (k : int) : fcmpop := if PrimInt63.eqb k 0%uint63 then F_EQ else if PrimInt63.eqb k 1%uint63 then F_LT else F_LE.
Definition fcvt_ty_of (k : int) : fcvt_ty := if PrimInt63.eqb k 0%uint63 then FC_W else if PrimInt63.eqb k 1%uint63 then FC_WU else if PrimInt63.eqb k 2%uint63 then FC_L else if PrimInt63.eqb k 3%uint63 then FC_LU else if PrimInt63.eqb k 4%uint63 then FC_S else FC_D.
Definition fmvdir_of (k : int) : fmvdir := if PrimInt63.eqb k 0%uint63 then FMV_X_F else FMV_F_X.

Definition dec_ins (s : string) (tag i : int) : option instr * int :=
  if PrimInt63.eqb tag 0%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in (Some (Lui (bvf 5 x0) (bvf 20 x1)), i1)
  else
  if PrimInt63.eqb tag 1%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in (Some (Auipc (bvf 5 x0) (bvf 20 x1)), i1)
  else
  if PrimInt63.eqb tag 2%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in (Some (Jal (bvf 5 x0) (bvf 21 x1)), i1)
  else
  if PrimInt63.eqb tag 3%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in (Some (Jalr (bvf 5 x0) (bvf 5 x1) (bvf 12 x2)), i2)
  else
  if PrimInt63.eqb tag 4%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (Branch (branch_cond_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 13 x3)), i3)
  else
  if PrimInt63.eqb tag 5%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in let '(x4, i4) := rdv s i3 in (Some (Load (msize_of x0) (boolf x1) (bvf 5 x2) (bvf 5 x3) (bvf 12 x4)), i4)
  else
  if PrimInt63.eqb tag 6%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (Store (msize_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 12 x3)), i3)
  else
  if PrimInt63.eqb tag 7%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (OpImm (aluop_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 12 x3)), i3)
  else
  if PrimInt63.eqb tag 8%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (ShiftImm (aluop_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 6 x3)), i3)
  else
  if PrimInt63.eqb tag 9%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (Op (aluop_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 5 x3)), i3)
  else
  if PrimInt63.eqb tag 10%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in (Some (OpImm32 (bvf 5 x0) (bvf 5 x1) (bvf 12 x2)), i2)
  else
  if PrimInt63.eqb tag 11%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (ShiftImm32 (aluop_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 5 x3)), i3)
  else
  if PrimInt63.eqb tag 12%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (Op32 (aluop_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 5 x3)), i3)
  else
  if PrimInt63.eqb tag 13%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in let '(x4, i4) := rdv s i3 in (Some (Fence (bvf 4 x0) (bvf 4 x1) (bvf 4 x2) (bvf 5 x3) (bvf 5 x4)), i4)
  else
  if PrimInt63.eqb tag 14%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in (Some (FenceI (bvf 5 x0) (bvf 5 x1) (bvf 12 x2)), i2)
  else
  if PrimInt63.eqb tag 15%uint63 then (Some Ecall, i)
  else
  if PrimInt63.eqb tag 16%uint63 then (Some Ebreak, i)
  else
  if PrimInt63.eqb tag 17%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (Mul (mulop_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 5 x3)), i3)
  else
  if PrimInt63.eqb tag 18%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (Mul32 (mulop_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 5 x3)), i3)
  else
  if PrimInt63.eqb tag 19%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in let '(x4, i4) := rdv s i3 in (Some (Lr (awidth_of x0) (boolf x1) (boolf x2) (bvf 5 x3) (bvf 5 x4)), i4)
  else
  if PrimInt63.eqb tag 20%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in let '(x4, i4) := rdv s i3 in let '(x5, i5) := rdv s i4 in (Some (Sc (awidth_of x0) (boolf x1) (boolf x2) (bvf 5 x3) (bvf 5 x4) (bvf 5 x5)), i5)
  else
  if PrimInt63.eqb tag 21%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in let '(x4, i4) := rdv s i3 in let '(x5, i5) := rdv s i4 in let '(x6, i6) := rdv s i5 in (Some (Amo (amoop_of x0) (awidth_of x1) (boolf x2) (boolf x3) (bvf 5 x4) (bvf 5 x5) (bvf 5 x6)), i6)
  else
  if PrimInt63.eqb tag 22%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (Csr (csrop_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 12 x3)), i3)
  else
  if PrimInt63.eqb tag 23%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (CsrI (csrop_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 12 x3)), i3)
  else
  if PrimInt63.eqb tag 24%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (FLoad (ffmt_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 12 x3)), i3)
  else
  if PrimInt63.eqb tag 25%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (FStore (ffmt_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 12 x3)), i3)
  else
  if PrimInt63.eqb tag 26%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in let '(x4, i4) := rdv s i3 in let '(x5, i5) := rdv s i4 in let '(x6, i6) := rdv s i5 in (Some (Fma (fmaop_of x0) (ffmt_of x1) (bvf 5 x2) (bvf 5 x3) (bvf 5 x4) (bvf 5 x5) (bvf 3 x6)), i6)
  else
  if PrimInt63.eqb tag 27%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in let '(x4, i4) := rdv s i3 in let '(x5, i5) := rdv s i4 in (Some (Fari (fariop_of x0) (ffmt_of x1) (bvf 5 x2) (bvf 5 x3) (bvf 5 x4) (bvf 3 x5)), i5)
  else
  if PrimInt63.eqb tag 28%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (Fsqrt (ffmt_of x0) (bvf 5 x1) (bvf 5 x2) (bvf 3 x3)), i3)
  else
  if PrimInt63.eqb tag 29%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in let '(x4, i4) := rdv s i3 in (Some (Fsgnj (fsgnop_of x0) (ffmt_of x1) (bvf 5 x2) (bvf 5 x3) (bvf 5 x4)), i4)
  else
  if PrimInt63.eqb tag 30%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in let '(x4, i4) := rdv s i3 in (Some (Fminmax (fminmaxop_of x0) (ffmt_of x1) (bvf 5 x2) (bvf 5 x3) (bvf 5 x4)), i4)
  else
  if PrimInt63.eqb tag 31%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in let '(x4, i4) := rdv s i3 in (Some (Fcmp (fcmpop_of x0) (ffmt_of x1) (bvf 5 x2) (bvf 5 x3) (bvf 5 x4)), i4)
  else
  if PrimInt63.eqb tag 32%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in let '(x4, i4) := rdv s i3 in (Some (Fcvt (fcvt_ty_of x0) (fcvt_ty_of x1) (bvf 5 x2) (bvf 5 x3) (bvf 3 x4)), i4)
  else
  if PrimInt63.eqb tag 33%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in let '(x3, i3) := rdv s i2 in (Some (Fmv (fmvdir_of x0) (ffmt_of x1) (bvf 5 x2) (bvf 5 x3)), i3)
  else
  if PrimInt63.eqb tag 34%uint63 then let '(x0, i0) := rdv s i in let '(x1, i1) := rdv s i0 in let '(x2, i2) := rdv s i1 in (Some (Fclass (ffmt_of x0) (bvf 5 x1) (bvf 5 x2)), i2)
  else
  (None, i).

(* [comment removed for export] *)
Definition itab_step (s : string) (st : itab * int * Z * int) : itab * int * Z * int :=
  let '(t, i, pc, n) := st in
  if PrimInt63.eqb n 0%uint63 then st else
  let '(d, i1) := rdv s i in
  let '(tag, i2) := rdv s i1 in
  let pc' := (pc + 4 * i2z 64 d)%Z in
  match dec_ins s tag i2 with
  | (Some ins, i3) => (pt_set (Z.to_pos pc') ins t, i3, pc', n - 1%uint63)
  | (None, i3) => (t, i3, pc', 0%uint63)          (* [comment removed for export] *)
  end.

Fixpoint itab_loopA (f : nat) (s : string) (st : itab * int * Z * int) : itab * int * Z * int :=
  match f with O => st | S f' => itab_loopA f' s (itab_step s st) end.
Fixpoint itab_loopB (f : nat) (s : string) (st : itab * int * Z * int) : itab * int * Z * int :=
  match f with
  | O => st
  | S f' => if PrimInt63.eqb (snd st) 0%uint63 then st else itab_loopB f' s (itab_loopA 1024 s st)
  end.

(* [comment removed for export] *)
Definition itab_of_string (s : string) (lo : Z) (n : int) : itab :=
  fst (fst (fst (itab_loopB 1024 s (PTLeaf, 0%uint63, lo, n)))).

