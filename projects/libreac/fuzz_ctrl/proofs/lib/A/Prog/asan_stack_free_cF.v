(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1441 of its 1505 lines of code are new or changed and 947 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/YTail.v, with its module paths and module names changed; 534 of its 819 lines of code are new or changed and 1220 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/YTailF.v, with its module paths and module names changed; 59 of its 90 lines of code are new or changed and 788 lines of the source are left out. *)
(* Footprint form (D) of __asan_stack_free_6 of image A (fuzz_ctrl.asan, libreac v1.9.0) at
   ASAN_STACK_FREE_6 = 0x3dbf4, and the localized-shadow plain form its proof runs through.

   FORM, as lib/A/Prog/asan_set_shadow_cF.v states asan_set_shadow_contract_F: the binders, the premises and the
   post of asan_stack_free_contract (asan_stack_free_c.v) are repeated UNCHANGED, in the same order -- that file
   is frozen and this one does not touch it -- with
     - the footprint RNG universally quantified, FIRST among the binders;
     - `RngBytes.rng_bytes RNG` FIRST among the footprint premises: an access may straddle two adjacent rng
       ranges, and the route-1 proof needs the footprint byte-wise;
     - one `ExecF.rng` premise per region the call reads or writes, LAST, after every original premise;
     - the run an ExecF.evtF on RNG instead of an Exec.evt.
   asan_stack_free_6_contract_F RNG is WORD FOR WORD Seg/YTailF.v's `stack_free_6_F RNG` (its consumer, blob
   5439a6a24ed on the glue base and 81b7f401f87 on a working branch agree on the text), so that file's
   obligation is discharged by `exact asan_stack_freeF.asan_stack_free_6_holds_F`.

   THE REGIONS, and why each one is in the list (disassembly of 0x3dbf4, 18 instructions, 72 bytes, and of its
   one callee __asan::MemToShadow at 0x3dc3c):
     - [0x10000, 0x5fe000) = [IMG_LO, IMG_HI): every code fetch of the 18 instructions and of MemToShadow; the
       one constant load, the auipc+ld pair at 0x3dc14 / 0x3dc18 that reaches the 0xf5 pattern cell 0x10338 in
       .rodata; and MemToShadow's four GOT slots 0x9fad0 .. 0x9faf0 (0x3dc40, 0x3dc60, 0x3dc68, 0x3dc84) and the
       cells they point to, CELL_K 0xa8878 and HIEND / MIDBEG / MIDEND 0xa9560 .. 0xa9578 (0x3dc44, 0x3dc6c,
       0x3dc70, 0x3dc88), all inside [RT_LO, RT_HI) = [0x9fad0, 0xa9578), inside the image.
     - the helper's own stack window [sp - 32, sp) = [S0 - ASAN_STACK_FREE_K, S0): it saves and reloads ra and
       s0 in [sp - 16, sp) (0x3dbf8, 0x3dbfc, 0x3dc2c, 0x3dc30); ASAN_STACK_FREE_K = 32 is the frozen
       contract's bound and MemToShadow touches no stack.
     - the side stack [FS, FS + FS_SIZE): the frame's last word at fr + fs_B 6 - 8 = fr + 4088, which holds the
       flag's address and which it reads (0x3dc04 ld a1,2041(a1) with a1 = fr + 2047), and the flag byte
       fs_flag FS 6 j, which it writes 0 to (0x3dc0c sb zero,0(a1)).  Both lie in the FakeStack
       (fr + 4096 <= FS + 7376896 < FS + FS_SIZE for j < fs_M 6 = 256).
     - [shadow_addr fr, shadow_addr fr + fs_shadow_n 6 L): the fs_shadow_n 6 L = 512 shadow bytes of the frame,
       which the loop 0x3dc20 .. 0x3dc28 fills with the 0xf5 pattern word, 64 sd of 8 bytes, from the address
       MemToShadow returns.
   NOT in the list: no shadow cover of the stack window or of the side stack -- the run has no instrumented
   access, it reads no shadow byte outside the 512 it writes.

   The localized-shadow plain form (_L, below) is the SAME contract with the one premise that route 1 cannot
   carry into a restricted memory weakened: `shadow_rw m` (every shadow byte of the 64-bit space is readable and
   writable) becomes `stk rsegs m (shadow_addr fr) (shadow_addr fr + fs_shadow_n c L)`, the 512 bytes the run
   actually touches, and the post drops its `shadow_rw m'` conjunct.  A restricted memory that keeps only the
   four regions above does not satisfy shadow_rw, so the frozen contract cannot be the input of the route-1
   lift; the _L form can, and asan_stack_freeF.v re-establishes shadow_rw m' on the full memory afterwards.
   Tk/AW/Sf6L.v proves asan_stack_free_6_contract_L; that is a re-run of the proved walk Tk/AW/Sf6.stack_free_6
   with that one premise localized, not a second proof of the function. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c asan_stack_free_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Export ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the footprint contract *)

(* The image bounds are written as the literals 0x10000 and 0x5ee000 (= IMG_LO and IMG_HI - IMG_LO of
   ImgBounds.v) because Seg/YTailF.v's stack_free_6_F writes them that way and this definition must be its text. *)
Definition asan_stack_free_6_contract_F (RNG : ExecF.footprint) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS j : Z),
  let fr := bv_unsigned a0 in let L := bv_unsigned a1 in let S0 := bv_unsigned sp in
  0 <= j < fs_M 6 -> fr = fs_frame FS 6 j ->
  1 <= L <= fs_B 6 -> L mod 8 = 0 ->
  fs_place m FS ->
  bytes_at rsegs m (fs_flag FS 6 j) [Z_to_bv 8 1] ->
  bytes_at rsegs m (fr + fs_B 6 - 8) (le8 (Z_to_bv 64 (fs_flag FS 6 j))) ->
  asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
  stk rsegs m lo S0 -> lo + 32 <= S0 -> FS + FS_SIZE <= S0 - 32 ->
  HIGHMEM_BEG <= lo -> S0 <= APPMEM_END ->
  RngBytes.rng_bytes RNG ->
  ExecF.rng RNG 0x10000 0x5ee000 ->
  ExecF.rng RNG (S0 - 32) 32 ->
  ExecF.rng RNG FS FS_SIZE ->
  ExecF.rng RNG (shadow_addr fr) (fs_shadow_n 6 L) ->
  ExecF.evtF rsegs RNG (asan_stack_free_post 6 32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS j lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_STACK_FREE_6) fc None m (seg_rom rsegs)).

(* ---------------------------------------------------------------- the localized-shadow plain form *)

(* asan_stack_free_post without its last conjunct, shadow_rw m': a run that may read and write only the frame's
   own 512 shadow bytes says nothing about the rest of the shadow. *)
Definition asan_stack_free_post_L (c : nat) (K : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (L FS j lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    let fr := fs_frame FS c j in let n := fs_shadow_n c L in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(fs_flag FS c j, fs_flag FS c j + 1); (shadow_addr fr, shadow_addr fr + n);
              (bv_unsigned sp - K, bv_unsigned sp)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ fs_place m' FS
    /\ bytes_at rsegs m' (fs_flag FS c j) [Z_to_bv 8 0]
    /\ bytes_at rsegs m' (shadow_addr fr) (repeat (Z_to_bv 8 0xf5) (Z.to_nat n))
    /\ asan_cells m'.

Definition asan_stack_free_contract_L (c : nat) (entry K : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS j : Z),
  let fr := bv_unsigned a0 in let L := bv_unsigned a1 in let S0 := bv_unsigned sp in
  0 <= j < fs_M c -> fr = fs_frame FS c j ->
  1 <= L <= fs_B c -> L mod 8 = 0 ->
  fs_place m FS ->
  bytes_at rsegs m (fs_flag FS c j) [Z_to_bv 8 1] ->
  bytes_at rsegs m (fr + fs_B c - 8) (le8 (Z_to_bv 64 (fs_flag FS c j))) ->
  asan_cells m ->
  stk rsegs m (shadow_addr fr) (shadow_addr fr + fs_shadow_n c L) ->
  mem_inv rsegs m ->
  stk rsegs m lo S0 -> lo + K <= S0 -> FS + FS_SIZE <= S0 - K ->
  HIGHMEM_BEG <= lo -> S0 <= APPMEM_END ->
  evt rsegs (asan_stack_free_post_L c K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS j lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

Definition asan_stack_free_6_contract_L : Prop :=
  asan_stack_free_contract_L 6 ASAN_STACK_FREE_6 ASAN_STACK_FREE_K.

(* ---- the two forms are linked: the frozen contract is the footprint form at RNG_all ---- *)

Lemma asan_stack_free_6_contract_of_F :
  asan_stack_free_6_contract_F ExecF.RNG_all -> asan_stack_free_6_contract.
Proof.
  intros HF. unfold asan_stack_free_6_contract, asan_stack_free_contract, ASAN_STACK_FREE_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo FS j.
  cbv zeta. intros HJ EFR HL HL8 PL FLG FLW AC SRW MI ST LOK ROOM HLO HHI.
  pose proof PL as (FS0 & FS4K & FSGT & FAPP & FSTK).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in RSP.
  assert (EFA : bv_unsigned a0 = FS + 6328320 + j * 4096).
  { rewrite EFR. unfold fs_frame, fs_B.
    change (FS + 36864 + Z.of_nat 6 * 2 ^ 20 + j * (64 * 2 ^ Z.of_nat 6)) with (FS + 36864 + 6 * 1048576 + j * (64 * 64)).
    lia. }
  change (fs_M 6) with 256 in HJ.
  assert (EN : fs_shadow_n 6 (bv_unsigned a1) = 512) by reflexivity.
  unfold FS_SIZE, ASAN_GT, HIGHMEM_BEG, APPMEM_END in *.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
          F fc m lo FS j HJ EFR HL HL8 PL FLG FLW AC SRW MI ST LOK ROOM HLO HHI).
  - (* RNG_all is byte-wise; lib/Lib/RngBytes.v has no rng_bytes_all lemma, so its one-line proof is here *)
    intros ? ? _ _ _. exact I.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - unfold FS_SIZE. apply ExecF.rng_all; lia.
  - rewrite EN. apply ExecF.rng_all.
    + unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
    + unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
Qed.
