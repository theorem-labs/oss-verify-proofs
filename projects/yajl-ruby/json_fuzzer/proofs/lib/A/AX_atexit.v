(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac xa := zstepA; try (first [if_true | if_false]).
Local Ltac xat_pc p := lazymatch goal with |- evtA _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Local Ltac xa_to p := repeat (tryif xat_pc p then fail else xa).

Notation AATX := 0x600b60%Z (only parsing).           (* [comment removed for export] *)
Notation AATX_BUILTIN := 0x600b78%Z (only parsing).   (* [comment removed for export] *)
Notation AATX_CALL := 0x91cbc%Z (only parsing).       (* [comment removed for export] *)
Notation AATX_HOOK := 0x71504%Z (only parsing).       (* [comment removed for export] *)
Notation AATXFLAG := 0x5e01d0%Z (only parsing).           (* [comment removed for export] *)
Notation AATXFLAG_GUARD := 0x81ecc%Z (only parsing).      (* [comment removed for export] *)
Notation AXLIBC := 0x600da0%Z (only parsing).         (* [comment removed for export] *)
Notation AXCOV := 0x13fa20%Z (only parsing).          (* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Definition atx_cells (reg : bool) (p3 p4 FJ AJ : list byte) : list cell :=
  [C1 (Z_to_bv 8 0); CB 3 p3; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (if reg then 2 else 1)); CB 4 p4;
   C8 (Z_to_bv 64 AATX_BUILTIN); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 AATX_CALL); C8 (Z_to_bv 64 (if reg then AATX_CALL else 0)); CB 240 FJ;
   C8 (Z_to_bv 64 AATX_HOOK); C8 (Z_to_bv 64 (if reg then AATXFLAG_GUARD else 0)); CB 240 AJ].

(* [comment removed for export] *)
Definition atx_ok_on (segs : list MemImageType.Segment) (m : mem) : Prop :=
  exists (reg : bool) (p3 p4 FJ AJ : list byte),
    rw_cells segs m AATX (atx_cells reg p3 p4 FJ AJ)
    /\ rw_cells segs m AATXFLAG [C1 (Z_to_bv 8 (if reg then 1 else 0))]
    /\ rw_cells segs m (AATXFLAG + 4) [C1 (Z_to_bv 8 0)].

Definition aatexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (p3 p4 FJ AJ : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AATX, AATX + 544)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' AATX (atx_cells true p3 p4 FJ AJ).

Lemma aatexit_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
         (p3 p4 FJ AJ : list byte) (cdt thr sec : byte) (tm1 : word) (P : acc -> Prop),
    (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
    (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
    stk asegs m lo (bv_unsigned sp) -> 0x603000 <= lo -> lo <= bv_unsigned sp - 48 ->
    mem_inv asegs m ->
    rw_cells asegs m AATX (atx_cells false p3 p4 FJ AJ) ->
    rw_cells asegs m AXLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
    a0 = Z_to_bv 64 AATXFLAG_GUARD ->
    bv_unsigned ra mod 2 = 0 ->
    evtA asegs P (aatexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x91bf8) fc None m (seg_rom asegs)).
Proof.
  intros until P; intros PSTK PIMG ST LOC LO MI ATX LIBC -> RA.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (AATX, AATX + 544)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold atx_cells in ATX.
  carve_frame 48%nat ST.
  xa_to 0x9e5ac%Z.
  (* [comment removed for export] *)
  xa. xa. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). xa. xa.
  (* [comment removed for export] *)
  xa_to 0x91c48%Z.
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity).
  xa_to 0x9e834%Z.
  (* [comment removed for export] *)
  xa_to 0x91c9c%Z.
  xa_to 0x91cb8%Z. release_frame FR ST (bv_unsigned sp). xa.
  apply evtA_done. unfold aatexit_post, atx_cells. do 19 eexists.
  split; [reflexivity|]. repeat (split; [assumption|]). exact ATX.
Time Qed.

(* [comment removed for export] *)
Definition afoe_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AATX, AATX + 544)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma afoe_spec :
  forall (reg : bool) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
         (p3 p4 FJ AJ : list byte) (cdt thr sec : byte) (tm1 : word) (P : acc -> Prop),
    (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
    (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
    stk asegs m lo (bv_unsigned sp) -> 0x603000 <= lo -> lo <= bv_unsigned sp - 48 ->
    mem_inv asegs m ->
    rw_cells asegs m AATX (atx_cells reg p3 p4 FJ AJ) ->
    rw_cells asegs m (AATXFLAG + 4) [C1 (Z_to_bv 8 0)] ->                            (* [comment removed for export] *)
    rw_cells asegs m AXCOV [C1 (Z_to_bv 8 0)] ->                                 (* [comment removed for export] *)
    rw_cells asegs m AXLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
    bv_unsigned ra mod 2 = 0 ->
    evtA asegs P (afoe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x91b2c) fc None m (seg_rom asegs)).
Proof.
  intros until P; intros PSTK PIMG ST LOC LO MI ATX FLG COV LIBC RA.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (AATX, AATX + 544)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold atx_cells in ATX. change (AATXFLAG + 4) with 0x5e01d4 in FLG.
  destruct reg; cbv iota in ATX.
  - (* [comment removed for export] *)
    carve_frame 48%nat ST.
    xa_to 0x9e5ac%Z.
    xa. xa. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). xa. xa.
    xa_to 0x91b64%Z.
    replace (sx32 (Z_to_bv 64 2)) with (Z_to_bv 64 2 : word) by (apply bv_eq; vm_compute; reflexivity).
    xa_to 0x9e834%Z.
    (* [comment removed for export] *)
    xa_to 0x91ba4%Z. xa_to 0x91cbc%Z. xa_to 0x81ecc%Z. xa_to 0x91bac%Z.
    (* [comment removed for export] *)
    xa_to 0x9e5ac%Z.
    xa. xa. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). xa. xa.
    xa.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity).
    xa_to 0x9e834%Z.
    xa_to 0x91ba4%Z. xa_to 0x91cbc%Z. xa_to 0x71504%Z. xa_to 0x91bac%Z.
    (* [comment removed for export] *)
    xa_to 0x9e5ac%Z.
    xa. xa. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). xa. xa.
    xa.
    replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity).
    xa_to 0x91bd8%Z.
    xa_to 0x9e834%Z. release_frame FR ST (bv_unsigned sp).
    xa_to 0x9e83c%Z. xa.
    apply evtA_done. unfold afoe_post. do 16 eexists.
    split; [reflexivity|]. repeat (split; [assumption|]). assumption.
  - (* [comment removed for export] *)
    carve_frame 48%nat ST.
    xa_to 0x9e5ac%Z.
    xa. xa. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). xa. xa.
    xa_to 0x91b64%Z.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity).
    xa_to 0x9e834%Z.
    xa_to 0x91ba4%Z. xa_to 0x91cbc%Z. xa_to 0x71504%Z. xa_to 0x91bac%Z.
    xa_to 0x9e5ac%Z.
    xa. xa. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). xa. xa.
    xa.
    replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity).
    xa_to 0x91bd8%Z.
    xa_to 0x9e834%Z. release_frame FR ST (bv_unsigned sp).
    xa_to 0x9e83c%Z. xa.
    apply evtA_done. unfold afoe_post. do 16 eexists.
    split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Time Qed.
End RC__1.
