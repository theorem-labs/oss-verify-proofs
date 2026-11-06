(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Test file (a Theorem Labs lane; a build target of every glue green). Gate 6h probe for the asan-ubsan glue in the WIDEST
   context (a Theorem Labs lane 07:16Z): every module lib/AU/G_Close.v Requires, the four G files (G_Sink, G_Drv, G_Top, G_Close),
   lib/SceneAsanBase.v and lib/AU/SceneAsanTop.v are Required AND Imported, and SinkGuard is in effect. Each `Fail`
   line elaborates one sink-taking statement with a bare sink head (no SK given): it must fail, and the build log
   prints "The command has indeed failed with message: ..." for it. The Definition after each one is the same text
   with SK given by name (asan_ubsan_sink_head), and it must compile, so each Fail fails only for the missing sink head. Control:
   lib/A/G_SinkCtl.v, where the released src0 instances resolve the same bare classes without SinkGuard. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_scene Require Statements.
From OSSVerify.libreac.fuzz_scene.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require SceneAsanTop.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require SinkGuard.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YG0f YG00 YG01 YG0n YG0d YG05 YG0q YG0t YK04 YA0i YA0n YI16 YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YE00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz StackFreeDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym SceneSyms SceneList SceneCode ScenePa SceneImg ScenePaLib SceneBase SceneRo SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import P_kind_of_link1 P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_frame P_check_step_cut P_check_step.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import G_Sink.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_reac_ctrl_build_scene_step P_reac_ctrl_scene_build P_reac_ctrl_scene_set_mac P_cksum_stamp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Rt Require Import StackMalloc8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require YF0m SceneBCertU.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require YD2l.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require CtrlParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP09 YP0m YI04 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import G_Drv G_Top.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import G_Close.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import SceneAsanBase.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import SceneAsanTop.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import SinkGuard YI14.
(* 1. The two sink classes themselves: no instance of either is in scope. *)
Fail Definition gp_sk : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head := _.
Definition gp_sk_named : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head := asan_ubsan_sink_head.
Fail Definition gp_ss : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI14.sink_syms := _.
(* 2. Every statement the glue passes a sink head to, with the head left bare, then given by name. *)
Fail Definition gp_ro (rc : YM05.RunCeil) (fx : YK11.FPState) : Prop :=
  ro_below_ofl (@pa_segs rc scene_listing (@PI_scene rc)) 0%Z 0%Z.
Definition gp_ro_named (rc : YM05.RunCeil) (fx : YK11.FPState) : Prop :=
  ro_below_ofl (SK:=asan_ubsan_sink_head) (@pa_segs rc scene_listing (@PI_scene rc)) 0%Z 0%Z.
Fail Definition gp_img_laws (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  asink_img_laws (@pa_segs rc scene_listing (@PI_scene rc)) B scene_K.
Definition gp_img_laws_named (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  asink_img_laws (SK:=asan_ubsan_sink_head) (@pa_segs rc scene_listing (@PI_scene rc)) B scene_K.
Fail Definition gp_kl1 (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  tkind_of_link1_spec (PI:=@PI_scene rc) B.
Definition gp_kl1_named (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  tkind_of_link1_spec (SK:=asan_ubsan_sink_head) (PI:=@PI_scene rc) B.
Fail Definition gp_ckv (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  tctrl_checksum_verify_spec (PI:=@PI_scene rc) B.
Definition gp_ckv_named (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  tctrl_checksum_verify_spec (SK:=asan_ubsan_sink_head) (PI:=@PI_scene rc) B.
Fail Definition gp_parse_spec (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  tctrl_parse_spec (PI:=@PI_scene rc) B.
Definition gp_parse_spec_named (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  tctrl_parse_spec (SK:=asan_ubsan_sink_head) (PI:=@PI_scene rc) B.
Fail Definition gp_bss (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  treac_ctrl_build_scene_step_spec (PI:=@PI_scene rc) B.
Definition gp_bss_named (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  treac_ctrl_build_scene_step_spec (SK:=asan_ubsan_sink_head) (PI:=@PI_scene rc) B.
Fail Definition gp_sb (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  treac_ctrl_scene_build_spec (PI:=@PI_scene rc) B.
Definition gp_sb_named (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  treac_ctrl_scene_build_spec (SK:=asan_ubsan_sink_head) (PI:=@PI_scene rc) B.
Fail Definition gp_ssm (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  treac_ctrl_scene_set_mac_spec (PI:=@PI_scene rc) B.
Definition gp_ssm_named (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  treac_ctrl_scene_set_mac_spec (SK:=asan_ubsan_sink_head) (PI:=@PI_scene rc) B.
Fail Definition gp_stamp (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  treac_ctrl_block_cksum_stamp_spec (PI:=@PI_scene rc) B.
Definition gp_stamp_named (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) : Prop :=
  treac_ctrl_block_cksum_stamp_spec (SK:=asan_ubsan_sink_head) (PI:=@PI_scene rc) B.
(* 3. A Theorem Labs lane's proved parse walk, as G_Close.v applies it. *)
Fail Definition gp_parse_walk (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) :=
  CtrlParse.pb_ctrl_parse (fx:=fx) (rc:=rc) (PI:=@PI_scene rc) B.
Definition gp_parse_walk_named (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) :=
  CtrlParse.pb_ctrl_parse (fx:=fx) (rc:=rc) (SK:=asan_ubsan_sink_head) (PI:=@PI_scene rc) B.
(* 4. The same bare-head elaborations, for the build log: rocq c does not print a Fail line's message, so each one
   below is caught with Ltac2 Control.case and its message is printed as "gate6h <name>: the command has indeed
   failed with message: ...". If any of them elaborated, gate6h throws and this file does not compile. *)
From Ltac2 Require Import Ltac2.
Ltac2 gate6h (name : string) (f : unit -> constr) :=
  match Control.case f with
  | Val _ => Control.throw (Invalid_argument (Some (Message.concat (Message.of_string name)
               (Message.of_string ": a bare sink head elaborated; gate 6h broken"))))
  | Err e => Message.print (Message.concat (Message.of_string "gate6h ") (Message.concat (Message.of_string name)
               (Message.concat (Message.of_string ": the command has indeed failed with message: ") (Message.of_exn e))))
  end.
Ltac2 Eval gate6h "AU sk (YI16.sink_head)" (fun () => constr:((_ : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head))).
Ltac2 Eval gate6h "AU ss (YI14.sink_syms)" (fun () => constr:((_ : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI14.sink_syms))).
Ltac2 Eval gate6h "AU ro" (fun () => constr:(fun (rc : YM05.RunCeil) (fx : YK11.FPState) => ro_below_ofl (@pa_segs rc scene_listing (@PI_scene rc)) 0%Z 0%Z)).
Ltac2 Eval gate6h "AU img_laws" (fun () => constr:(fun (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) => asink_img_laws (@pa_segs rc scene_listing (@PI_scene rc)) B scene_K)).
Ltac2 Eval gate6h "AU kl1" (fun () => constr:(fun (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) => tkind_of_link1_spec (PI:=@PI_scene rc) B)).
Ltac2 Eval gate6h "AU ckv" (fun () => constr:(fun (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) => tctrl_checksum_verify_spec (PI:=@PI_scene rc) B)).
Ltac2 Eval gate6h "AU parse_spec" (fun () => constr:(fun (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) => tctrl_parse_spec (PI:=@PI_scene rc) B)).
Ltac2 Eval gate6h "AU bss" (fun () => constr:(fun (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) => treac_ctrl_build_scene_step_spec (PI:=@PI_scene rc) B)).
Ltac2 Eval gate6h "AU sb" (fun () => constr:(fun (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) => treac_ctrl_scene_build_spec (PI:=@PI_scene rc) B)).
Ltac2 Eval gate6h "AU ssm" (fun () => constr:(fun (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) => treac_ctrl_scene_set_mac_spec (PI:=@PI_scene rc) B)).
Ltac2 Eval gate6h "AU stamp" (fun () => constr:(fun (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) => treac_ctrl_block_cksum_stamp_spec (PI:=@PI_scene rc) B)).
Ltac2 Eval gate6h "AU parse_walk" (fun () => constr:(fun (rc : YM05.RunCeil) (fx : YK11.FPState) (B : asyms) => CtrlParse.pb_ctrl_parse (fx:=fx) (rc:=rc) (PI:=@PI_scene rc) B)).
