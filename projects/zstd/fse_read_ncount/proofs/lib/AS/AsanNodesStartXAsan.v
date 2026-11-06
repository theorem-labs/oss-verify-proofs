(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.zstd.fse_read_ncount.images Require Import Asan.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanPlanImages.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Asan_code_startx.
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Section AsanInstance.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variable stdin : InputStream.
Variable FS0 : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Variable uid : word.
Variable hw : word.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variable LIMIT : Z.
Section AnySINV.
Variable SINV : env -> (word -> option byte) -> Prop.
Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Variable nx0 : nat.
Hypothesis Hnx0 : (NX0 <= nx0)%nat.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
#[using="brk0 Hsp Hva Hve Hfit SINV_SINV0 SINV_frame Hnx0"] Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS ASAN nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
Proof.
eapply (init_x_sound_envscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
W_88908 W_8890c W_88910
ltac:(cbn [x_envscan x_envscan_k ASAN]; lia)
(fetch_lit _ _ _ _ eq_refl F_88908) (fetch_lit _ _ _ _ eq_refl F_8890c) (fetch_lit _ _ _ _ eq_refl F_88910)
ltac:(repeat split; reflexivity)
D_88908 D_8890c D_88910
sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame nx0 Hnx0).
Qed.
#[using="brk0 Hsp Hva Hve Hfit SINV_SINV0 SINV_frame Hnx0 SINV_agree"] Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS ASAN nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
Proof.
eapply (init_x_sound_pnscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
W_889c4 W_889c8 W_889cc W_889d0 W_889d4
ltac:(cbn [x_pnscan x_pnscan_k ASAN]; lia)
(fetch_lit _ _ _ _ eq_refl F_889c4) (fetch_lit _ _ _ _ eq_refl F_889c8) (fetch_lit _ _ _ _ eq_refl F_889cc)
(fetch_lit _ _ _ _ eq_refl F_889d0) (fetch_lit _ _ _ _ eq_refl F_889d4)
ltac:(repeat split; reflexivity)
D_889c4 D_889c8 D_889cc D_889d0 D_889d4
sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
Qed.
End AnySINV.
End AsanInstance.
