(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, route R1 (h-hpreset-7) at main, image B (asan-ubsan, pin sha256
   f8f98a95bc52...): the twin of lib/A/AjMemnormMainA.v over image B's names. The walk's own mem at main is the
   UNRESTRICTED overlay FULL: tfib_AR_init (YD1f.v:257-269) concludes `AR TSEGS B ly init_state (YD2i.W1 ...) FULL model`,
   and every program text's fpre / afn_pre_x (YCbqG.v:182) takes ARx ... W regs mem at that position. The hidden set
   w_H W is applied only when a walk READS (YG0n.aview segs (w_H W) mem := mbyte segs (mrestrict (w_H W) mem),
   YG0n.v:18-19); it is never part of mem. So the fact here is memnorm of FULL itself: the walks' aj_memnorm entry law
   (aj_memnorm m := Lib.Mem.mem_inv segs m /\ MemNorm.task_mem segs m, the body of YAjMemnorm.memnorm). It is
   YA0j.ho_memnorm, from the start-up invariant YA02.SINV0 through YA02.SINV0_mn, converted by YAkMemnormJ.memnorm_kit_j.
   The restricted form, where a runner segment needs it, follows by YAkMemnorm.memnorm_mrestrict at that segment
   (YSRrMemnorm), not here. A leaf: it requires YAjMemnorm.v (and so lib/Lib/LiaTwx2.v), which no kit file may.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YP09 YK00 YK04 YA0i YA0n YK0g
YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j
YB12 YB1h YB13 YB01
YG00 YG01 YG0f YG0v YG0n YG0r YG0b YF0m YM05 YD1h YD1g YD2i
YD1d YD1e YD1f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YAjMemnorm YAkMemnormJ.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState}.
Theorem tfib_memnorm_at_main_B : forall (B : asyms) (HB : TfibSyms B) (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput)
(Hsp : valid_sp sp) (Hva : valid_argv (in_argv inp)),
valid_envp (in_envp inp) -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
forall (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
HS_tfib h = Some ch ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 TSEGS TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
(forall a, YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
FULL a = wrap_mem TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
forall {rc : YM05.RunCeil}, YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
YAjMemnorm.memnorm TSEGS FULL.
Proof.
intros B HB sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM rc Hceil.
apply YAkMemnormJ.memnorm_kit_j.
eapply ho_memnorm; [exact (YA02.SINV0_mn TSEGS TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) | exact HC].
Qed.
End c.
