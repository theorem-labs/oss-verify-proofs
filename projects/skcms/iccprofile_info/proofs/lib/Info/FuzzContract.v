(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Record fuzz_abi : Type := FA {
  fa_entry : Z;        (* [comment removed for export] *)
  fa_gfool : Z;        (* [comment removed for export] *)
  fa_depth : Z;        (* [comment removed for export] *)
  fa_ro_lo : Z;        (* [comment removed for export] *)
  fa_ro_hi : Z
}.

Definition src1_abi : fuzz_abi := FA 0x12f28 0x30910 1824 0x103ec 0x1048c.
Definition infoub_abi : fuzz_abi := FA 0x12f88 0x31400 1824 0x103ec 0x10490.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fuzz_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition fuzz_contract (segs : list Segment) (A : fuzz_abi) : Prop :=
  forall (FP : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte)
         (ret sp data : word) (n : Z) (bs : list byte),
    (* [comment removed for export] *)
    getr regs 1 = ret -> ret_ok ret ->
    getr regs 2 = sp -> getr regs 10 = data -> getr regs 11 = Z_to_bv 64 n ->
    (* [comment removed for export] *)
    (0 <= n < 2 ^ 26)%Z -> Z.of_nat (length bs) = n ->
    (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned data mod 16 = 0)%Z ->
    (fa_depth A <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2 ^ 47)%Z ->
    (0 < bv_unsigned data)%Z -> (bv_unsigned data + n < 2 ^ 47)%Z ->
    (* [comment removed for export] *)
    (forall i, (0 <= i < n)%Z ->
       mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
    (* [comment removed for export] *)
    RiscvSemantics.store_ok segs mem (Z_to_bv 64 (bv_unsigned sp - fa_depth A)) (Z.to_nat (fa_depth A)) = true ->
    (forall i, (bv_unsigned sp - fa_depth A <= i < bv_unsigned sp)%Z ->
       Forall (fun seg => (i < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= i)%Z) segs) ->
    (* [comment removed for export] *)
    RiscvSemantics.store_ok segs mem (Z_to_bv 64 (fa_gfool A)) 4 = true ->
    (exists gb, rdn segs mem (Z_to_bv 64 (fa_gfool A)) 4 = Some gb) ->
    (* [comment removed for export] *)
    (forall i, (fa_ro_lo A <= i < fa_ro_hi A)%Z -> mem (Z_to_bv 64 i) = None) ->
    (* [comment removed for export] *)
    (bv_unsigned data + n <= bv_unsigned sp - fa_depth A \/ bv_unsigned sp <= bv_unsigned data)%Z ->
    (bv_unsigned data + n <= fa_gfool A \/ fa_gfool A + 4 <= bv_unsigned data)%Z ->
    (fa_gfool A + 4 <= bv_unsigned sp - fa_depth A \/ bv_unsigned sp <= fa_gfool A)%Z ->
    exists (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps segs (mkst (FP:=FP) regs (Z_to_bv 64 (fa_entry A)) mem rom)
                  (mkst (FP:=FP') regs' ret mem' rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ (forall r, In r fuzz_kept -> getr regs' r = getr regs r)
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - fa_depth A), fa_depth A); (Z_to_bv 64 (fa_gfool A), 4%Z)].
