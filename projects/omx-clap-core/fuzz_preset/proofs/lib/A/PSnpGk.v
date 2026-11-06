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
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset by c-asan's alreloc of record (frame/alreloc.py.frozen-c4338d099cfb8025, --src omx-clap-core/fuzz_preset --src-pin d83eb25d --assume-source; the chain's code is equal old -> #102); kept as written: the IImg record keys (fm addresses), the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/A/PSnpGk.v.reloc.tsv. Comment numerals are as written (sentences above that name preset A's addresses describe the old pin). *)
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
Import ListNotations.
Open Scope Z_scope.

(* ---- the code: the __wrap_* trampolines, the vfprintf / vsnprintf / snprintf interceptors and TryAsanInitFromRtl
   (MEASURED word counts: the next function starts right after each range, except the snprintf interceptor's, which
   the walk needs only its first 28 words of, as at fm); musl comes from tfibmusl_tbl ---- *)
Definition g_ranges : list (Z * nat) :=
  [(0x42d18, 36%nat); (0x46168, 45%nat); (0x4621c, 198%nat); (0x4660c, 28%nat); (0x5a73c, 40%nat)].
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
eapply (SRr_run_gen tfibsegs tbl_g tbl_g_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
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
eapply (SRr_run_to_gen tfibsegs tbl_g tbl_g_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
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
Proof. intros. eapply (SRr_ret_at tfibsegs tbl_g tbl_g_ok AF0x.Hwx_tfa); eassumption. Qed.
End g.
