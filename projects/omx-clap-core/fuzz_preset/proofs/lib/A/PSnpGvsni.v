(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: a new walk of fm.asan's __interceptor_vsnprintf 0x458a0; the entry-state tactics
   (pairwise_disjoint_of_extents, facts_ok), the return-address step and the epilogue state built from the saved slots
   are adapted from A/AE35.v (tfib_vprintf_icpt_A / tfib_vprintf_icpt_E). *)
(* fm's snprintf glue, the vsnprintf interceptor level: avsni_realizes (FMsnprintfGI.v) for fm.asan's
   __interceptor_vsnprintf 0x458a0, from printf_common's contract (apcommon_realizesU), musl vsnprintf's (avsn_realizes)
   and the WRITE_RANGE (str, res + 1) check (FMsnprintfGwrc.v vsn_wr_check_srrU).
   The walk (MEASURED: the symbolic runs below; disassembly, the internal file 0x458a0.s):
     entry sp = sp0 + 0x9d0 (atom 2); the prologue saves ra, s0..s7 at entry - 8 .. entry - 0x48 and the va pointer P at
       entry - 0x58 and entry - 0x60, sp = entry - 0x870 = sp0 + 0x160; TryAsanInitFromRtl 0x59a78 returns 1 (it reads
       asan_inited 0xa2a58 = 1); check_printf (0x999a0 -> 0x1338a8, byte 0x1338fc) = 1;
     printf_common (ctx 0x17890, format, P) returns to 0x45918: a kcall, its band [sp - STK_PCOM, sp);
     REAL (vsnprintf) = 0x91f0c from 0x9b748, entered with (D, N, format, P), returns to 0x45934: a kcall, its band
       [sp0 - SNK_STK, sp0 + 0x160) and the destination [D, D + M);
     res >= 0 (bltz not taken), size >= res + 1 (bgeu taken): 0x45a14 mv s1, a1, then the check at 0x45a18 with
       s1 = res + 1, s2 = str, s3 = size, a0 = res; it returns at 0x4599c;
     the epilogue reloads ra, s0..s7 from the saved slots (a symbolic state built from them, as A/AE35.v builds its
       ss_epi) and returns. *)
(* Modified by Theorem Labs, 2026-10: the image-bearing half of origin/cold/port-fm-rtprintf-param 7e395de08f5
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGvsni.v for the snprintf chain restated over ARx (route (a),
   c-omx-hpreset 10:51Z), re-pinned at preset image A (fuzz_preset.asan d83eb25d; symbols from its unstripped twin
   f0d2e8d4): only the items of the four roots' closure that carry image numerals or run the code, vsni_rodata
   and its check vsni_rodata_chk (:49-53; the REAL (vsnprintf) cell is a row of AF0m.v since h-pre-b3's blob
   1d01cd9b0fcd), vsni_rodata0 / vsni_rodata_split / vsni_rodata0_chk (the three other cells, kept for the roots'
   Svsni), RUNTO / RUN (:56-57, over lib/A/PSnpGk.v's tbl_g), ss_epi / epi_e / r_epi (:83-87) and
   ro_low (:158-165); the image-free ones are lib/Reusable/PSnpGvsnikit.v. ss_epi starts at PSnpGwrc.RC_END, which
   is FMsnprintfGI's WRC_END (both 0x4599c at fm); ro_low's bound 0x140000 is a bound, not an address (preset A's
   highest cell ends at 0x13c43d, below it). Relocation BY SYMBOL + OFFSET from fm.asan 0ba7e169 (unstripped
   fc92e86b) by the internal file reloc.py:
     cell / pc                                         fm.asan    preset A
     __asan::asan_inited + 0                           0xa2a58    0xab598  (.bss, value 1 at run time)
     .got slot of __sanitizer::common_flags_dont_use   0x999a0    0xa1ac0  (no symbol: the auipc / ld pair at
         ___interceptor_vfprintf + 0x30 in both images; the slot holds common_flags_dont_use + 0 in both)
     __sanitizer::common_flags_dont_use + 0 (value)    0x1338a8   0x13c3e8
     __sanitizer::common_flags_dont_use + 0x54         0x1338fc   0x13c43c (check_printf)
     __interception::real_vsnprintf + 0                0x9b748    0xa3850
     vsnprintf + 0 (value)                             0x91f0c    0x9a63c
     ___interceptor_vsnprintf + 0xfc (ss_epi's pc)     0x4599c    0x46284 *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset by c-asan's alreloc of record (frame/alreloc.py.frozen-c4338d099cfb8025, --src omx-clap-core/fuzz_preset --src-pin d83eb25d --assume-source; the chain's code is equal old -> #102); kept as written: the IImg record keys (fm addresses), the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/A/PSnpGvsni.v.reloc.tsv. Comment numerals are as written (sentences above that name preset A's addresses describe the old pin). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import PSnpGkit PSnpGvsnikit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PSnpGk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PSnpGwrc.
Import ListNotations.
Open Scope Z_scope.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the image cells the walk reads: asan_inited, the common_flags pointer, check_printf, REAL (vsnprintf) *)
Definition vsni_rodata : list (Z * Z * list (Z * N * Z)) :=
  [(0xabb98, 1, [(0, 1%N, 1)]); (0xa2000, 8, [(0, 8%N, 0x13c9e8)]); (0x13ca3c, 1, [(0, 1%N, 1)]);
   (0xa3d90, 8, [(0, 8%N, 0x9ab78)])].
(* The three cells other than REAL (vsnprintf), and the split (the roots' Svsni uses them). Every cell of vsni_rodata
   is a row of preset A's constant table (AF0m.v Tfib_const): the REAL (vsnprintf) row `z8 (ANum 0xa3850) 0x9a63c` is
   h-pre-b3's generated blob 1d01cd9b0fcd (origin/cold/h-pre-b3-af0m-vsnp d4c54f298e8); fm's AF0m has its twin
   (7e395de08f5 lib/A/AF0m.v:341). *)
Definition vsni_rodata0 : list (Z * Z * list (Z * N * Z)) :=
  [(0xabb98, 1, [(0, 1%N, 1)]); (0xa2000, 8, [(0, 8%N, 0x13c9e8)]); (0x13ca3c, 1, [(0, 1%N, 1)])].
Lemma vsni_rodata_split : vsni_rodata = vsni_rodata0 ++ [(0xa3d90, 8, [(0, 8%N, 0x9ab78)])].
Proof. reflexivity. Qed.
Lemma vsni_rodata0_chk : forall ly, rodata_chk ly vsni_rodata0 = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Lemma vsni_rodata_chk : forall ly, rodata_chk ly vsni_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_g FUEL stop s.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_g FUEL s.
(* the epilogue from the check's return (PSnpGwrc.RC_END = ___interceptor_vsnprintf + 0xfc, the value of fm's
   FMsnprintfGI.WRC_END): the saved ra, s0..s7 as atoms 32..40, at sp + 0x868 - 8 j (sp = sp0 + 0x160) *)
Definition ss_epi : sstate :=
  mkSS PSnpGwrc.RC_END sr_atoms [YP09.mkRegion (Some 2%nat) 0x828 0x870 0x828 0x828 epi_chunks] None
    (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Lemma ro_low : forall r, In r (map ro_region vsni_rodata) ->
  region_wf r = true /\ YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 0x140600 /\
  YP09.r_wlo r = YP09.r_whi r.
Proof.
intros r Hr. unfold vsni_rodata in Hr. cbn [map] in Hr.
repeat destruct Hr as [<-|Hr]; try destruct Hr;
repeat split; vm_compute; first [reflexivity | intros Hc; discriminate].
Qed.
End v.
