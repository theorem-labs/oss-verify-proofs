(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_scene/lib/Reusable/YI5cSat.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YI5cSat.v, with its module paths and addresses changed; 2 of its 55 lines of code are new or changed and 2 lines of the source are left out. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e YN35 YN3f YN3g YN34 YN3d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL02 YL0a YL00 YL04 YL0c YL09 YL05 YL0g YL0k YL0m YL0u YL0r YL0o YL0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YL0t.
Local Open Scope Z_scope.

Section sat.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma sat_sk_file_none : @sk_file src0_sink = None.
Proof. reflexivity. Qed.

Lemma sat_sink_at_none : forall mem md f S, ~ sink_at src0_msyms mem md f S.
Proof. intros mem md f S H. exact H. Qed.

Lemma sat_fopen_spec : forall MR pc, fopen_spec src0_msyms MR pc.
Proof. intros MR pc F EF. discriminate EF. Qed.

Lemma sat_unlink_spec : forall MR pc, unlink_spec src0_msyms MR pc.
Proof. intros MR pc F EF. discriminate EF. Qed.

Lemma sat_stdio_env_rom : forall mem : word -> option byte,
  (forall a, env_addr a -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a)) ->
  stdio_env src0_msyms mem.
Proof.
  intros mem Hrom. destruct (src0_env_rom mem Hrom) as ((H1 & H2) & _).
  assert (R : forall a, env_addr a -> forall v, seg_rom src0segs (Z_to_bv 64 a) = v -> mbyte src0segs mem a = v)
    by (intros a Ha v <-; apply Hrom; exact Ha).
  refine (conj H1 (conj H2 (conj I (conj _ _)))).
  all: intros j Hj; cbn in Hj;
    do 8 (destruct j as [|j]; [split; [intros k Hk; destruct k as [|k];
      [apply R; [unfold env_addr; cbn; lia | vm_compute; reflexivity] | cbn in Hk; lia] | cbn; lia] |]); lia.
Qed.

Lemma sat_sink_none_rom : forall (mem : word -> option byte) md,
  (forall a, env_addr a -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a)) ->
  Namei.fd_names_path (m_fds md) sink_path = false ->
  sink_none src0_msyms mem md.
Proof.
  intros mem md Hrom Hn. destruct (src0_env_rom mem Hrom) as (HC & HH). exact (conj HC (conj HH Hn)).
Qed.

Lemma cs_sink_laws : sink_laws src0_msyms.
Proof. exact src0_sink_laws. Qed.

Lemma cs_env_addr_img : forall a, env_addr a ->
  in_img src0_msyms a /\ ~ static_owned src0_msyms a /\ ~ (ms_ctx src0_msyms <= a < ms_ctx src0_msyms + CTX_SIZE) /\
  ~ (errno_addr src0_msyms <= a < errno_addr src0_msyms + 4).
Proof. intros a Ha. exact (skl_env src0_msyms a Ha). Qed.

Lemma cs_env_addr_range : forall a, env_addr a -> 0x10000 <= a < 0x56000.
Proof. exact src0_env_addr_range. Qed.
End sat.
