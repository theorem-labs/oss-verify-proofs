(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_manifest.asan (module paths). kcall generalizes A/AE3h.v vf_icpt_xcall (callee post handed in, regions after the
   stack region constrained by what they must avoid); kentry, kenv, st_ok_pc_mem_out and kstore0 are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSnpK.v, with its module paths changed; 741 of its 850 lines of code are new or changed and 228 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/FMsnprintfSk.v, with its module paths and module names changed; 97 of its 190 lines of code are new or changed and 757 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Rt/RtFSprintfK.v, with its module paths and module names changed; 26 of its 49 lines of code are new or changed and 167 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGt0.v (cold/port-fm-rtprintf-param 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMsnprintfGt0.table). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMsnprintfGt0.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* fm's snprintf glue, transport without any stack window (split out of FMsnprintfGt.v, which re-exports it): a
   world-hidden byte's writability kept with its presence, and ecall_preU from ARU, the registers and the ESTACK window.
   New file. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YI00 YI16 YK06.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import FMH_Base FMsnprintfK.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import FMsnprintfImg FMsnprintfGk0.
Import ListNotations.
Open Scope Z_scope.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
#[local] Abbreviation H W := (w_H W).

(* a byte the world may hide stays writable when its presence is kept *)
Lemma writable_xfer : forall (Hd : word -> bool) (m m' : word -> option byte) a,
  writable_at tfibsegs (mrestrict Hd m) a -> (apresent Hd m a -> apresent Hd m' a) ->
  writable_at tfibsegs (mrestrict Hd m') a.
Proof.
intros Hd m m' a Hw Hp. unfold writable_at, wview, mrestrict in *.
destruct (Hd (Z_to_bv 64 a)) eqn:Eh; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj Eh (ex_intro _ b Em))) as [_ [b' Hb']]. rewrite Hb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* ecall_preU from ARU, the registers and the ESTACK window *)
Lemma g_ecall_preU : forall ly S U W regs mem md,
  ARU tfibsegs B ly S U W mem md -> YK0s.ret_ok (getr regs 1) -> spZ regs mod 16 = 0 ->
  ly_stk_lo ly + ESTACK <= spZ regs -> spZ regs <= ly_stk_hi ly ->
  (forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (H W) mem a) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  ecall_preU tfibsegs B ly S U W regs mem md.
Proof.
intros ly S U W regs mem md HA Hra H16 Hlo Hhi Hp Hgp Htp.
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA)) as [K1 K2].
split; [|split; [exact (ARU_ok tfibsegs B ly S U W mem md HA) | exact (ARU_poisoned tfibsegs B ly S U W mem md HA)]].
split; [exact (ARU_AR tfibsegs B ly S U W mem md HA)|]. do 4 (split; [assumption|]). split; [|split; assumption].
intros a Ha. destruct (Hp a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
unfold ESTACK in *.
rewrite unpoison_out; [exact Hb|]. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [|reflexivity].
exfalso. pose proof (ush_facts tfibsegs B ly S U W mem md _ HA Ei) as (_ & L1 & L2).
rewrite unsigned_lit_small in L2 by (unfold kHighMemEnd, kHighMemBeg in *; lia). lia.
Qed.

End t.
