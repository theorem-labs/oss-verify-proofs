(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Definition a8_poison_entry : Z := poison_entry.   (* [comment removed for export] *)
Definition mmap_ecall_pc : Z := 0x6a974.
Definition mmap_after_pc : Z := 0x6a978.
Definition mmapnamed_resume : Z := 0x6c198.       (* [comment removed for export] *)
Definition MFNR_RET : Z := 0x746bc.               (* [comment removed for export] *)
Definition MFSNR_RET : Z := 0x74780.              (* [comment removed for export] *)
Definition RSMR_RET : Z := 0x726ec.               (* [comment removed for export] *)
Definition a8_die_spin : Z := 0x746f4.
Definition CF : Z := 0x1466e8.                    (* [comment removed for export] *)
Definition PSC : Z := 0x144660.                   (* [comment removed for export] *)
Definition SSP_GOT : Z := 0xa9818.               (* [comment removed for export] *)
Definition SSP_CELL : Z := 0x607c18.              (* [comment removed for export] *)
Definition LIBC_PAGESIZE : Z := 0x607e98.         (* [comment removed for export] *)
Definition SEALED_GOT : Z := 0xa8bb0.            (* [comment removed for export] *)
Definition DYING_GOT : Z := 0xa8bb8.             (* [comment removed for export] *)
Definition DYING : Z := 0x1466dc.

Definition unmap_entry : Z := 0x6c1c0.            (* [comment removed for export] *)
Definition munmap_ecall_pc : Z := 0x6a980.
Definition munmap_after_pc : Z := 0x6a984.
Definition unmap_resume : Z := 0x6c1f0.
Definition unmap_die_spin : Z := 0x662bc.

(* [comment removed for export] *)
Definition pg_up (x : Z) : Z := (x + 4095) / 4096 * 4096.
Definition pg_dn (x : Z) : Z := x / 4096 * 4096.
(* [comment removed for export] *)
Definition a8_pbeg (addr : Z) : Z := pg_up (sh addr).
Definition a8_pend (addr size : Z) : Z := pg_dn (sh addr + size / 8).
Definition a8_len (addr size : Z) : Z := a8_pend addr size - a8_pbeg addr.
Definition A8_STACK : Z := 592.        (* [comment removed for export] *)
Definition A8_FRAMES : Z := 176.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition a8_consts (m : word -> option byte) (canary : word) : Prop :=
     ro_cells rsegs m (CF + 144) [C8 (wz 0)]                 (* [comment removed for export] *)
  /\ ro_cells rsegs m (CF + 219) [C1 (Z_to_bv 8 1)]          (* [comment removed for export] *)
  /\ ro_cells rsegs m (CF + 244) [C1 (Z_to_bv 8 1)]          (* [comment removed for export] *)
  /\ ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)]          (* [comment removed for export] *)
  /\ ro_cells rsegs m SSP_GOT [C8 (wz SSP_CELL)] /\ ro_cells rsegs m SSP_CELL [C8 canary]
  /\ ro_cells rsegs m LIBC_PAGESIZE [C8 (wz 4096)]
  /\ ro_cells rsegs m SEALED_GOT [C8 (wz 1)] /\ ro_cells rsegs m DYING_GOT [C8 (wz DYING)] /\ ro_cells rsegs m DYING [C4 (wz 0)].

(* [comment removed for export] *)
Definition a8_frames (pbeg len : Z) (scr12 scr8 : list byte) (s4v s3v s2v s1v s0v ra0 : word) : list cell :=
  [ CB 12 scr12; C4 (wz 0x4032); C8 (wz pbeg); C8 (wz 0); C8 (wz len); C8 (wz MFNR_RET);
    CB 8 scr8; C8 (wz 1); C8 (wz 0); C8 (wz pbeg); C8 (wz len); C8 (wz MFSNR_RET);
    C8 (wz 0); C8 (wz len); C8 (wz pbeg); C8 (wz RSMR_RET);
    C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0 ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition poisonbig_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (addr size lo : Z) (canary : word) (old : list byte)
         (Q : machine_state -> Prop),
    let usp := bv_unsigned sp in let q := sh addr in let n := size / 8 in
    let pbeg := a8_pbeg addr in let pend := a8_pend addr size in let len := a8_len addr size in
    mem_inv rsegs m -> stk rsegs m lo usp -> lo <= usp - A8_STACK -> alloc_ceiling <= lo -> usp <= 2^47 ->
    usp mod 16 = 0 ->
    a0 = wz addr -> a1 = wz size -> a2 = wz 0 ->
    addr mod 8 = 0 -> size mod 8 = 0 -> pz_in addr size -> addr + size <= 2^47 -> 0x10000 <= n ->     (* [comment removed for export] *)
    poison_consts m -> a8_consts m canary ->
    rw_cells rsegs m q [CB (Z.to_nat n) old] ->
    (forall (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scr12 scr8 : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (usp + -176) (a8_frames pbeg len scr12 scr8 s4 s3 s2 s1 s0 ra) ->
        rw_cells rsegs m' q [CB (Z.to_nat (pbeg - q)) (repeat (Z_to_bv 8 0) (Z.to_nat (pbeg - q)));
                              CB (Z.to_nat len) (firstn (Z.to_nat len) (skipn (Z.to_nat (pbeg - q)) old));
                              CB (Z.to_nat (q + n - pend)) (repeat (Z_to_bv 8 0) (Z.to_nat (q + n - pend)))] ->
        munch [(usp - A8_STACK, usp); (q, q + n)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (usp + -176) ->
        Q (MSsvc (mkR (wz mmapnamed_resume) (wz (usp + -176)) gp tp t0' t1' t2' (wz 3) (wz len)
                      (wz pbeg) (wz len) (wz 3) (wz 0x4032) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz pbeg) (wz PSC) (wz pend) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz a8_poison_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition poisonbig_post_stmt : Prop :=
  forall (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo pbeg len : Z) (canary : word) (scr12 scr8 : list byte)
         (s4v s3v s2v s1v s0v ra0 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp + -176) -> lo <= usp - 176 -> alloc_ceiling <= lo -> usp <= 2^47 ->
    0 <= pbeg -> pbeg + len < 2^47 -> 0 <= len ->
    rw_cells rsegs m (usp + -176) (a8_frames pbeg len scr12 scr8 s4v s3v s2v s1v s0v ra0) -> bv_unsigned ra0 mod 2 = 0 ->
    ro_cells rsegs m 0xa8b60 [C8 (wz CF)] -> a8_consts m canary ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        munch [(usp - 176, usp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        Q (MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7'
                   s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz mmapnamed_resume) (wz (usp + -176)) gp tp t0 t1 t2 s0 s1 (wz pbeg) a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz mmap_after_pc) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition poisonbig_die_stmt : Prop :=
  forall (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo pbeg len : Z) (canary : word) (scr12 scr8 : list byte)
         (s4v s3v s2v s1v s0v ra0 : word),
    mem_inv rsegs m -> stk rsegs m lo (usp + -176) -> lo <= usp - 176 -> alloc_ceiling <= lo -> usp <= 2^47 ->
    0 <= pbeg -> pbeg + len < 2^47 -> 0 <= len ->
    bv_unsigned a0 = 2^64 - 12 ->
    rw_cells rsegs m (usp + -176) (a8_frames pbeg len scr12 scr8 s4v s3v s2v s1v s0v ra0) ->
    a8_consts m canary ->
    evt rsegs (fun ms' => exists R' m', ms' = MS R' F (wz a8_die_spin) fc None m' (seg_rom rsegs)
                                   /\ munch [(usp - 176, usp)] m m')
        (MS (mkR (wz mmapnamed_resume) (wz (usp + -176)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz mmap_after_pc) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unmap_frame (scr : list byte) (s2v s1v s0v ra0 : word) : list cell :=
  [CB 16 scr; C8 s2v; C8 s1v; C8 s0v; C8 ra0].
Definition UNMAP_STACK : Z := 64.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition unmap_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (addr size rr lo : Z) (Q : machine_state -> Prop),
    let usp := bv_unsigned sp in
    mem_inv rsegs m -> stk rsegs m lo usp -> lo <= usp - 48 -> alloc_ceiling <= lo -> usp <= 2^47 ->
    a0 = wz addr -> a1 = wz size -> a2 = wz rr -> 1 <= addr < 2^64 -> 1 <= size < 2^64 -> 0 <= rr < 2^64 ->
    (forall (scr : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (usp + -48) (unmap_frame scr s2 s1 s0 ra) ->
        munch [(usp - 48, usp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (usp + -48) ->
        Q (MSsvc (mkR (wz unmap_resume) (wz (usp + -48)) gp tp t0 t1 t2 (wz size) (wz rr)
                      (wz addr) (wz size) a2 a3 a4 a5 a6 (wz 215)
                      (wz addr) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz munmap_ecall_pc) (wz 215) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz unmap_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition unmap_post_stmt : Prop :=
  forall (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo : Z) (scr : list byte)
         (s2v s1v s0v ra0 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp + -48) -> lo <= usp - 48 -> alloc_ceiling <= lo -> usp <= 2^47 ->
    rw_cells rsegs m (usp + -48) (unmap_frame scr s2v s1v s0v ra0) -> bv_unsigned ra0 mod 2 = 0 ->
    ro_cells rsegs m 0xa8b60 [C8 (wz CF)] -> ro_cells rsegs m (CF + 144) [C8 (wz 0)] ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        munch [(usp - 48, usp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        Q (MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7'
                   s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz unmap_resume) (wz (usp + -48)) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz munmap_after_pc) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition unmap_die_stmt : Prop :=
  forall (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo : Z) (scr : list byte) (s2v s1v s0v ra0 : word),
    mem_inv rsegs m -> stk rsegs m lo (usp + -48) -> lo <= usp - UNMAP_STACK -> alloc_ceiling <= lo -> usp <= 2^47 ->
    2^64 - 4095 <= bv_unsigned a0 < 2^64 ->
    rw_cells rsegs m (usp + -48) (unmap_frame scr s2v s1v s0v ra0) ->
    ro_cells rsegs m SEALED_GOT [C8 (wz 1)] -> ro_cells rsegs m DYING [C4 (wz 0)] ->
    evt rsegs (fun ms' => exists R' m', ms' = MS R' F (wz unmap_die_spin) fc None m' (seg_rom rsegs)
                                   /\ munch [(usp - UNMAP_STACK, usp)] m m')
        (MS (mkR (wz unmap_resume) (wz (usp + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz munmap_after_pc) fc None m (seg_rom rsegs)).

End CEIL.
