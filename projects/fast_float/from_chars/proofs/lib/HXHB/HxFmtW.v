(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation ASEGS := AsanUbsan.M.loaded_segments.
Definition af_table (k : Z) : Z := match k with 0 => 1 | 1 => 4 | _ => 4 end%Z.

Section FMT.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k : Z).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis HK : (0 <= k <= 2)%Z.
  Hypothesis PR : pristine m 0x259a0 0x259b8.

  #[local] Notation FST pc x22 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Zw (0x259a0 + 8 * k)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition fmt_post : machine_state -> Prop := fun ms' => ms' = FST 0x90220 (Zw (af_table k)).

  #[using="HK PR"] Lemma blockFMT : forall (x22 : word), evt ASEGS fmt_post (FST 0x9021c x22).
  Proof. LiaFast.lf_pins (fun (HK PR : LiaFast.U) => LiaFast.u0).
    intros x22. unfold fmt_post.
    assert (Hk3 : (k = 0 \/ k = 1 \/ k = 2)%Z) by lia.
    destruct Hk3 as [H | [H | H]]; rewrite H; cbn [Z.mul Z.add Pos.mul Pos.add af_table];
      step; (* [comment removed for export] *)
      apply evt_done; reflexivity.
  Qed.
End FMT.
