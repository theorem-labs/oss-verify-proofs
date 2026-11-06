(* fm's snprintf glue, kit: the code table of the walks above printf_core, their run and return steps, dropping and
   adding a region of a symbolic state, and the frame bookkeeping of FMsnprintfI's snk_frame across runs and calls.
   New file. *)
(* Modified by Theorem Labs, 2026-10: the image-bearing half of origin/cold/port-fm-rtprintf-param 7e395de08f5
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGk.v (:25-71: g_ranges, tbl_g, tbl_g_eq, tbl_g_ok, g_phase,
   g_phase_to, g_ret) for the snprintf chain restated over ARx (route (a), c-omx-hpreset 10:51Z), re-pinned at preset
   image A (fuzz_preset.asan d83eb25d; symbols from its unstripped twin f0d2e8d4). The image-free half (register /
   slot reads, region kit) is lib/Reusable/PSnpGkit.v; the ARU-form frame lemmas (:157-228) are not reached by the
   four roots and are not ported. Relocation, BY SYMBOL + OFFSET from fm.asan 0ba7e169 (unstripped fc92e86b), checked
   equal size and equal opcodes (pc-relative immediates masked) by the internal file reloc.py:
     fm symbol + off                              fm.asan            preset A
     __interceptor_trampoline_strlen + 0          0x412c8, 39 words  0x42c84, 36 words  (the whole __wrap_* trampoline
                                                  block, up to ___interceptor_strlen: fm has 39 trampolines, preset
                                                  36 - strncmp / strncasecmp / strstr are absent; every one is one j)
     ___interceptor_vfprintf + 0                  0x457ec, 45        0x460d4, 45
     ___interceptor_vsnprintf + 0                 0x458a0, 198       0x46188, 198
     ___interceptor_snprintf + 0                  0x45c90, 28        0x46578, 28
     __asan::TryAsanInitFromRtl + 0               0x59a78, 40        0x5a6a8, 40 *)
(* Modified by Theorem Labs, 2026-10: image B twin (fuzz_preset.asan-ubsan f8f98a95; symbols from its unstripped twin
   3b5e1a09) of lib/A/PSnpGk.v, by the unit's image-B convention (lib/AU/FCxA.v's generator rule, as lib/AU/PSnpK.v): module
   names A<x> -> image B's Y<x> (lib/Reusable), the chain's lib/A files -> their lib/AU twins, and every image numeral
   relocated BY SYMBOL + OFFSET from preset A d83eb25d to B by the internal file reloc.py (equal function size
   and opcodes, equal instruction words). The relocation table above is image A's; image B's:
     A symbol + off                                   preset A   preset B
     __interceptor_trampoline_strlen + 0 (36 words)     0x42c84    0x42d08 (36 words: B has the same trampolines)
     ___interceptor_vfprintf + 0                      0x460d4    0x46158
     ___interceptor_vsnprintf + 0                     0x46188    0x4620c
     ___interceptor_snprintf + 0                      0x46578    0x465fc
     __asan::TryAsanInitFromRtl + 0                   0x5a6a8    0x5a72c *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset, checked equal to the B -> B' map of record (preset-F reloc102-maps bmap_b2bp.py 27b4c628bef6 over this file); B''s derived bounds from that map: the read-only top / writable start 0xa1000 -> 0xa2000, the image top 0x600000 -> 0x601000; kept as written: the IImg record keys, the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/AU/PSnpGk.v.reloc.tsv. Comment numerals are as written. *)
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
Import ListNotations.
Open Scope Z_scope.

(* ---- the code: the __wrap_* trampolines, the vfprintf / vsnprintf / snprintf interceptors and TryAsanInitFromRtl
   (MEASURED word counts: the next function starts right after each range, except the snprintf interceptor's, which
   the walk needs only its first 28 words of, as at fm); musl comes from tfibmusl_tbl ---- *)
Definition g_ranges : list (Z * nat) :=
  [(0x42e04, 36%nat); (0x46254, 45%nat); (0x46308, 198%nat); (0x466f8, 28%nat); (0x5a828, 40%nat)].
Definition tbl_g : ctable := Eval vm_compute in build_ranges g_ranges tfibmusl_tbl.
Lemma tbl_g_eq : tbl_g = build_ranges g_ranges tfibmusl_tbl.
Proof. vm_cast_no_check (eq_refl tbl_g). Qed.
Lemma tbl_g_ok : table_ok tfibsegs tbl_g.
Proof.
rewrite tbl_g_eq. apply build_ranges_ok; [unfold g_ranges; repeat constructor; cbn; discriminate | exact tfibmusl_tbl_ok].
Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma g_phase : forall (W : world tfibsegs) E ss ss' st ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_g FUEL ss = (ss', st) ->
  SRr tfibsegs W (mkCfg ms md)
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
       match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
       | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_g tbl_g_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF _. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1 | exact HF].
Qed.
Lemma g_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs tbl_g FUEL stop ss = (ss', st) ->
  SRr tfibsegs W (mkCfg ms md)
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
       match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
       | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_g tbl_g_ok YF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF _. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1 | exact HF].
Qed.
(* the return `ret` at the end of a walk *)
Lemma g_ret : forall (W : world tfibsegs) E ss ms md Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  clookup tbl_g (ss_pc ss) = Some RET_WORD_r ->
  (forall mat', Q W (mkCfg (mkst (ms_regs ms) (v_jalr (getr (ms_regs ms) 1) 0) (ms_mem ms) (seg_rom tfibsegs))
     (with_vm_backing (m_vm_lazy md) mat' md))) ->
  SRr tfibsegs W (mkCfg ms md) Q.
Proof. intros. eapply (SRr_ret_at tfibsegs tbl_g tbl_g_ok YF0x.Hwx_tfa); eassumption. Qed.
End g.
