(* musl vsnprintf 0x91f0c (fm.asan) in the donor's proof form, from the contracts of __wrap_memset and
   __interceptor_vfprintf: entry at sp0 + 0x160 (s = D, n = N, fmt, ap = P), frame 0x130 with the stack protector,
   memset (sp, 0, 0xe8) through __wrap_memset 0x51a60 (ra 0x91f70), the FILE fields, the cookie {D, N - 1}, *D = 0,
   __wrap_vfprintf 0x41308 = j 0x457ec (ra 0x91fac) with the FILE at sp0 + FO, the canary check and the epilogue.
   New file. *)
(* Modified by Theorem Labs, 2026-10: the image-bearing half of origin/cold/port-fm-rtprintf-param 7e395de08f5
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGvsn.v for the snprintf chain restated over ARx (route (a),
   c-omx-hpreset 10:51Z), re-pinned at preset image A (fuzz_preset.asan d83eb25d; symbols from its unstripped twin
   f0d2e8d4): only the items of the four roots' closure that carry image numerals, gv_got / gv_can (:32-35), GVTO /
   GVRUN (:39-40, over lib/A/PSnpGk.v's tbl_g) and c3_lk / c3_ec / c3_dec (:118-120); the image-free ones are
   lib/Reusable/PSnpGvsnkit.v. The canary cells are preset A's own names A/AE2p.v A_GOT_canary / A_canary
   (= AImgCells' A_GOT_STACK_CHK_GUARD / A_STACK_CHK_GUARD: 0xa2758 / 0x5fd910 at d83eb25d, 0xa2c98 / 0x5fdf30 at #102 A' (lib/A/AImgCells.v:24 / :23)), for
   fm's FMH_Base FM_GOT_canary 0x9a638 / FM_canary 0x5f4db0; the internal file reloc.py derives the same pair BY SYMBOL + OFFSET (__stack_chk_guard + 0; its
   .got slot through the auipc / ld pair at printf_core + 0x64 in both images). Relocation of c3_lk from fm.asan 0ba7e169 (unstripped
   fc92e86b): vsnprintf + 0x8c, fm 0x91f98 -> preset A 0x9a6c8; the word there is 622627 in both images. *)
(* Modified by Theorem Labs, 2026-10: image B twin (fuzz_preset.asan-ubsan f8f98a95; symbols from its unstripped twin
   3b5e1a09) of lib/A/PSnpGvsn.v, by the unit's image-B convention (lib/AU/FCxA.v's generator rule, as lib/AU/PSnpK.v): module
   names A<x> -> image B's Y<x> (lib/Reusable), the chain's lib/A files -> their lib/AU twins, and every image numeral
   relocated BY SYMBOL + OFFSET from preset A d83eb25d to B by the internal file reloc.py (equal function size
   and opcodes, equal instruction words). The relocation table above is image A's; image B's:
     A symbol + off                                   preset A   preset B
     vsnprintf + 0x8c (c3_lk; word 622627 in both)     0x9a6c8    0x9af64
   The canary cells are B's YE2p.A_GOT_canary / A_canary (YImgCellsB B_GOT_0XCE8 0xa2ff8 / B_STACK_CHK_GUARD_CELL). *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset, checked equal to the B -> B' map of record (preset-F reloc102-maps bmap_b2bp.py 27b4c628bef6 over this file); B''s derived bounds from that map: the read-only top / writable start 0xa1000 -> 0xa2000, the image top 0x600000 -> 0x601000; kept as written: the IImg record keys, the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/AU/PSnpGvsn.v.reloc.tsv. Comment numerals are as written. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YE34 YF0l YF0m YF0x YE20 YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import PSnpGkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PSnpGk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YE2p.
Import ListNotations.
Open Scope Z_scope.

(* ---- the canary cells (the stack protector's .got slot and __stack_chk_guard; atom 32 the canary value), the runs
   over the code table and the store at vsnprintf + 0x8c (`sb zero, 0(s3)`, s3 = D) ---- *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition gv_got : YP09.region :=
  YP09.mkRegion None A_GOT_canary (A_GOT_canary + 8) 0 0 [YP09.mkChunk A_GOT_canary (CVal 8 (SLit A_canary))].
Definition gv_can : YP09.region :=
  YP09.mkRegion None A_canary (A_canary + 8) 0 0 [YP09.mkChunk A_canary (CVal 8 (SOff 32 0))].
Definition GVTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_g FUEL stop s.
Definition GVRUN (s : sstate) := sym_runN tfibsegs tbl_g FUEL s.
Lemma c3_lk : clookup tbl_g 0x9b454 = Some 622627. Proof. vm_compute. reflexivity. Qed.
Lemma c3_ec : is_ecall (Z_to_bv 32 622627) = false. Proof. vm_compute. reflexivity. Qed.
Lemma c3_dec : decode_any (Z_to_bv 32 622627) = Some (Store SZ1 19%bv 0%bv 0%bv, 4%Z). Proof. vm_refl_bv. Qed.
End r.
