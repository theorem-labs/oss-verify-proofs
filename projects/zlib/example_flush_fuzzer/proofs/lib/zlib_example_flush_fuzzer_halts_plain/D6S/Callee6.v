(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel MemFill.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface AdlerModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

End FXG.
Abbreviation A6_MEMCPY := 0x27800%Z.
Abbreviation A6_MEMSET := 0x27c04%Z.
Abbreviation A6_ADLER32 := 0x1a3d4%Z.
Abbreviation A6_CRC32 := 0x1aa44%Z.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Definition IMG6_LO : Z := 0x10000.
Definition IMG6_HI : Z := 0x5c000.


Definition memcpy_clob : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Definition memcpy_run6 : Prop :=
  forall (mem : word -> option byte) (regs : bvmap 5 word) (dst src : Z) (n : nat) (bs : list byte) (ra : word),
    rdn s6_segs mem (zw src) n = Some bs ->
    0 <= dst -> dst + Z.of_nat n < 2 ^ 64 -> 0 <= src -> src + Z.of_nat n < 2 ^ 64 ->
    (dst + Z.of_nat n <= src \/ src + Z.of_nat n <= dst) ->
    mapped mem dst (Z.of_nat n) ->
    ret_ok ra ->
    reg_get regs 1 = ra -> reg_get regs 10 = zw dst -> reg_get regs 11 = zw src ->
    reg_get regs 12 = zw (Z.of_nat n) ->
    exists regs',
      msteps s6_segs (mkst regs (zw A6_MEMCPY) mem s6_rom) (mkst regs' ra (wbytes mem (zw dst) bs) s6_rom)
      /\ reg_get regs' 10 = zw dst
      /\ (forall r : reg, reg_in r memcpy_clob = false -> getr regs' r = getr regs r).


Definition memset_clob : list reg := [5; 6; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Definition memset_run6 : Prop :=
  forall (mem : word -> option byte) (regs : bvmap 5 word) (dst c n : Z) (ra : word),
    0 <= dst -> 0 <= n -> dst + n < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
    mapped mem dst n -> ret_ok ra ->
    reg_get regs 1 = ra -> reg_get regs 10 = zw dst -> reg_get regs 11 = zw c -> reg_get regs 12 = zw n ->
    exists regs' mem',
      msteps s6_segs (mkst regs (zw A6_MEMSET) mem s6_rom) (mkst regs' ra mem' s6_rom)
      /\ reg_get regs' 10 = zw dst
      /\ (forall r : reg, reg_in r memset_clob = false -> getr regs' r = getr regs r)
      /\ filled mem' dst (dst + n) (ms_bb c)
      /\ same_outside mem mem' dst (dst + n)
      /\ (forall x, mem x <> None -> mem' x <> None).


Definition c_clob : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition ADLER_FR6 : Z := 32.

Definition rom_local6 (ROM : (word -> option byte) -> Prop) : Prop :=
  forall m m' : word -> option byte,
    ROM m -> (forall x : word, IMG6_LO <= bv_unsigned x < IMG6_HI -> m' x = m x) -> ROM m'.

Definition adler32_run6 (ROM : (word -> option byte) -> Prop) : Prop :=
  forall (mem : word -> option byte) (regs : bvmap 5 word) (adler P : Z) (d : list byte) (usp : Z) (ra : word),
    rdn s6_segs mem (zw P) (length d) = Some d ->
    0 <= adler < 2 ^ 64 -> adler_canon adler -> 1 <= P -> P + Z.of_nat (length d) < 2 ^ 64 -> Z.of_nat (length d) < 2 ^ 32 ->
    ADLER_FR6 <= usp -> usp < 2 ^ 63 -> mapped mem (usp - ADLER_FR6) ADLER_FR6 ->
    (1 <= Z.of_nat (length d) -> P + Z.of_nat (length d) <= usp - ADLER_FR6 \/ usp <= P) ->
    ROM mem -> ret_ok ra ->
    reg_get regs 1 = ra -> reg_get regs 2 = zw usp ->
    reg_get regs 10 = zw adler -> reg_get regs 11 = zw P -> reg_get regs 12 = zw (Z.of_nat (length d)) ->
    exists regs' mem',
      msteps s6_segs (mkst regs (zw A6_ADLER32) mem s6_rom) (mkst regs' ra mem' s6_rom)
      /\ reg_get regs' 10 = zw (adler32_z_spec adler P d)
      /\ reg_get regs' 2 = zw usp
      /\ (forall r : reg, reg_in r c_clob = false -> getr regs' r = getr regs r)
      /\ agree_out [(usp - ADLER_FR6, ADLER_FR6)] mem mem'
      /\ (forall x, mem x <> None -> mem' x <> None).
End FXG.
