(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ja0PlanImagesK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanNodesAuxK AsanStartLoops AsanNodesStartXK AsanNodesStartXInitK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanNodesStartXAsanK () := ([""; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DefsK."], [["0FS0"; "1LIMIT"; "1SINV0"; "1argH0"; "2NX0"; "2XEnvScan"; "2XLayout"; "2XPnScan"; "3x_stmt"; "4APH0"; "4ASAN0"; "4ASEGS0"; "0SINV"; "0argv"; "0brk0"; "0envp"]; ["0hw"; "0rdraw"; "0scfg"; "0sp"; "0uid"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.
Section AsanInstance.
Variable scfg : SpuriousCfg.
Variable sp brk0 mbase : word.
Variable rdraw : EntryDraw.
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
Section AnySINV.
Variable SINV : env -> (word -> option byte) -> Prop.
Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH0 sp rdraw brk0 argv envp uid hw E M.
Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH0 sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
Theorem node_x_sound_XEnvScan_asan_gen : ltac2:(TCodec.tc2 tcn__AsanNodesStartXAsanK "C&8&;vB&:&4&1v<&3&9vCvAv=v?vDv@%877654321v0(5%B9A@?>=<321").
Proof.
eapply (init_x_sound_envscan ASEGS0 scfg ASAN0 APH0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok
(ltac:(oW' 0x112e78%Z)) (ltac:(oW' 0x112e7c%Z)) (ltac:(oW' 0x112e80%Z))
ltac:(cbn [x_envscan x_envscan_k ASAN0]; lia)
(fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x112e78%Z))) (fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x112e7c%Z))) (fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x112e80%Z)))
ltac:(repeat split; reflexivity)
(ltac:(oD' 0x112e78%Z)) (ltac:(oD' 0x112e7c%Z)) (ltac:(oD' 0x112e80%Z))
sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame).
Qed.
Theorem node_x_sound_XPnScan_asan_gen : ltac2:(TCodec.tc2 tcn__AsanNodesStartXAsanK "C&8&;vB&:&4&1v<&3&9vCvAv=v?vDv@%877654321v0(7%B9A@?>=<321").
Proof.
eapply (init_x_sound_pnscan ASEGS0 scfg ASAN0 APH0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok
(ltac:(oW' 0x112f34%Z)) (ltac:(oW' 0x112f38%Z)) (ltac:(oW' 0x112f3c%Z)) (ltac:(oW' 0x112f40%Z)) (ltac:(oW' 0x112f44%Z))
ltac:(cbn [x_pnscan x_pnscan_k ASAN0]; lia)
(fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x112f34%Z))) (fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x112f38%Z))) (fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x112f3c%Z)))
(fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x112f40%Z))) (fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x112f44%Z)))
ltac:(repeat split; reflexivity)
(ltac:(oD' 0x112f34%Z)) (ltac:(oD' 0x112f38%Z)) (ltac:(oD' 0x112f3c%Z)) (ltac:(oD' 0x112f40%Z)) (ltac:(oD' 0x112f44%Z))
sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame SINV_agree).
Qed.
Theorem node_x_sound_XLayout_asan_gen : ltac2:(TCodec.tc2 tcn__AsanNodesStartXAsanK "C&8&;vB&:&4&1v<&3&9vCvAv=v?vDv@%877654321v0(6%B9A@?>=<321").
Proof. apply x_sound_layout. Qed.
End AnySINV.
Theorem node_x_sound_XEnvScan_asan : ltac2:(TCodec.tc2 tcn__AsanNodesStartXAsanK "E&8&;vB&:&4&1&2&9vCvAv>v=v?vDv@%9887654321&3%17:986543v0(5%D9CBA@?5321").
Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame]. Qed.
Theorem node_x_sound_XPnScan_asan : ltac2:(TCodec.tc2 tcn__AsanNodesStartXAsanK "E&8&;vB&:&4&1&2&9vCvAv>v=v?vDv@%9887654321&3%17:986543v0(7%D9CBA@?5321").
Proof. apply node_x_sound_XPnScan_asan_gen; [auto | apply SINV0_frame | apply SINV0_agree]. Qed.
Theorem node_x_sound_XLayout_asan : ltac2:(TCodec.tc2 tcn__AsanNodesStartXAsanK "E&8&;vB&:&4&1&2&9vCvAv>v=v?vDv@%9887654321&3%17:986543v0(6%D9CBA@?5321").
Proof. apply x_sound_layout. Qed.
End AsanInstance.
