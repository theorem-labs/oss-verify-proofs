(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanPlanImages.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import Asan_code_startx.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanNodesStartXAsan () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.env"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.argH0"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPlanImages.APH"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.None"].


Section AsanInstance.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.           (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)

  #[local] Notation SINV0a := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH0a := (argH0 APH sp rdraw argv envp uid hw).

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0a E M.
    Hypothesis SINV_frame : ltac2:(CDefT.buildp (gd_tbl_AsanNodesStartXAsan ()) "PE,$0.PM,Px,(1.&40.)(2.(1.&8.))PM',Px,(1.&40.)(2.(1.&8.))P,Pa,(1.&40.)P,(3.$4.(5.$6.Vsp,Vrdraw,Vargv,Venvp,Vuid,Vhw,R4.R1.)$7.)(3.(2.(1.&8.))A1.R3.R2.A1.R4.R2.)P,Pa,(1.&40.)P,(8.(9.&40.Vsp,)(9.&40.R1.))P,(:.(3.(2.(1.&8.))A1.R5.R2.(;.(1.&8.))))(:.(3.(2.(1.&8.))A1.R5.R3.(;.(1.&8.))))P,A2.VSINV,R5.R4.A2.VSINV,R6.R4.")
(* [comment removed for export] *).   (* [comment removed for export] *)
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    (* [comment removed for export] *)
    #[using="brk0 Hsp Hva Hve Hfit SINV_SINV0 SINV_frame"] Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS BOTH NX0 LIMIT (bv_unsigned sp) SINV argH0a FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS BOTH APH asan_wx asan_in_hull asan_hull_ok
                W_dd408 W_dd40c W_dd410
                ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_dd408) (fetch_lit _ _ _ _ eq_refl F_dd40c) (fetch_lit _ _ _ _ eq_refl F_dd410)
                ltac:(repeat split; reflexivity)
                D_dd408 D_dd40c D_dd410
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame).
    Qed.

    #[using="brk0 Hsp Hva Hve Hfit SINV_SINV0 SINV_frame SINV_agree"] Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS BOTH NX0 LIMIT (bv_unsigned sp) SINV argH0a FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS BOTH APH asan_wx asan_in_hull asan_hull_ok
                W_dd4c4 W_dd4c8 W_dd4cc W_dd4d0 W_dd4d4
                ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_dd4c4) (fetch_lit _ _ _ _ eq_refl F_dd4c8) (fetch_lit _ _ _ _ eq_refl F_dd4cc)
                (fetch_lit _ _ _ _ eq_refl F_dd4d0) (fetch_lit _ _ _ _ eq_refl F_dd4d4)
                ltac:(repeat split; reflexivity)
                D_dd4c4 D_dd4c8 D_dd4cc D_dd4d0 D_dd4d4
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame SINV_agree).
    Qed.

    #[using="Type"] Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS BOTH NX0 LIMIT (bv_unsigned sp) SINV argH0a FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit"] Theorem node_x_sound_XEnvScan_asan : x_stmt ASEGS BOTH NX0 LIMIT (bv_unsigned sp) SINV0a argH0a FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame]. Qed.

  #[using="Hsp Hva Hve Hfit"] Theorem node_x_sound_XPnScan_asan : x_stmt ASEGS BOTH NX0 LIMIT (bv_unsigned sp) SINV0a argH0a FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen; [auto | apply SINV0_frame | apply SINV0_agree]. Qed.

  #[using="Type"] Theorem node_x_sound_XLayout_asan : x_stmt ASEGS BOTH NX0 LIMIT (bv_unsigned sp) SINV0a argH0a FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
