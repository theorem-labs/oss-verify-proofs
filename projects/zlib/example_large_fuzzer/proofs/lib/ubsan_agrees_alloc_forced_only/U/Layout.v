(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation RLIBC := 0x5da58%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0x5d7d8%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0x3d708%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0x3d7d0%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0x5da40%Z (only parsing).
Notation RDEFSTACK := 0x2d660%Z (only parsing).  (* [comment removed for export] *)
Notation RGOT_DYNAMIC := 0x2c3c0%Z (only parsing). (* [comment removed for export] *)
Notation RGOT_SSP := 0x2c440%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0x5da38%Z (only parsing).     (* [comment removed for export] *)
Notation RENVIRON := 0x3d700%Z (only parsing).
Notation RPROGNAME := 0x5da48%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0x5dac0%Z (only parsing).
Notation RGOT3 := 0x2c418%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x25c44);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x25e00); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x2d570%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x5dea0%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x2d480%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x25e08%Z (only parsing).
Notation F_STDIO_WRITE := 0x25c70%Z (only parsing).

(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0x5f000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x2c000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x2c440%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0x5da38%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].
