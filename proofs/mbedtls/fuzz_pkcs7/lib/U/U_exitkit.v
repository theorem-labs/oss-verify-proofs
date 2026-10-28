(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac SymExec2 SymExec2Sound SymDriveX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_img U_stdio_defs U_exit_base U_exit U_exit_main U_fwrite_err U_printf1.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_exitkit () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.U.U_exit_base.file_clean"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.exit_common"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.exit_pre"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.U_printf1.stdout_buffered"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"].


(* [comment removed for export] *)
Record exit_mem (sp0 : word) (tid : Z) (M : word -> option byte) : Prop := EXIT_MEM {
  xm_win : forall a : word, (bv_unsigned sp0 - 8388608 <= bv_unsigned a < bv_unsigned sp0)%Z -> wview RSEGS M a <> None;
  xm_ro  : forall a : Z, (0x10000 <= a < 0x4bcd8)%Z -> M (Z_to_bv 64 a) = None;
  xm_got : rdn RSEGS M (Z_to_bv 64 0x4bcd8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7d330));
  xm_rest : forall a : Z, (0x4bce0 <= a < 0x4cd30)%Z -> M (Z_to_bv 64 a) = None;
  xm_used2 : forall a : Z, (0x4ce18 <= a < 0x4ce20)%Z -> M (Z_to_bv 64 a) = None;     (* [comment removed for export] *)
  xm_used1 : forall a : Z, (0x4cf08 <= a < 0x4cf10)%Z -> M (Z_to_bv 64 a) = None;     (* [comment removed for export] *)
  xm_comp : rdn RSEGS M (Z_to_bv 64 0x4cf68) 1 = Some [Z_to_bv 8 0];
  xm_tid  : rdn RSEGS M (Z_to_bv 64 0x5d020) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  xm_tidr : (0 < tid < 2 ^ 22)%Z;
  xm_lock : rdn RSEGS M (Z_to_bv 64 0x7d328) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  xm_canary : exists canw : word, rdn RSEGS M (Z_to_bv 64 0x7d330) 8 = Some (word_to_le_bytes 8 canw);   (* [comment removed for export] *)
  xm_needlocks : rdn RSEGS M (Z_to_bv 64 0x7d353) 1 = Some [Z_to_bv 8 0];
  xm_stdin : rdn RSEGS M (Z_to_bv 64 0x7d770) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  xm_ofl  : rdn RSEGS M (Z_to_bv 64 0x7d780) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  xm_err  : exists wp2 rp2, file_clean M 0x4cd30 wp2 rp2;
  xm_atexit : exists b : bool, atexit_st b M                                          (* [comment removed for export] *)
}.

Lemma rdn_none_img : ltac2:(CDefT.buildp (gd_tbl_P_exitkit ()) "PM,Px,(0.&40.)(1.(0.&8.))Pa,$2.Pn,$3.P,Pi,$2.P,(4.(5.R3.R1.)(6.R1.(7.R3.(8.R2.))))(9.(1.(0.&8.))A1.R5.(:.&40.R2.)(;.(0.&8.)))P,(5.=R3.)P,(5.(7.R4.(8.R3.))(<.+2.+40.))(9.(1.(=.(0.&8.)))(>.$?.R6.(:.&40.R5.)R4.)(>.$?.L,(0.&40.)(;.(0.&8.))(:.&40.R5.)R4.))")
(* [comment removed for export] *).
Proof.
  intros M a n H Ha Hn. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac img_cell H lem a n :=
  rewrite (rdn_none_img _ a n); [exact lem | intros i Hi; apply H; lia | lia | lia].

Lemma stderr_pristine_clean : ltac2:(CDefT.buildp (gd_tbl_P_exitkit ()) "PM,Px,(0.&40.)(1.(0.&8.))P,Pa,$2.P,(4.(5.+4<=30.R1.)(6.R1.+4<>18.))(9.(1.(0.&8.))A1.R3.(:.&40.R2.)(;.(0.&8.)))(10.R2.+4<=30.(:.&40.=)(:.&40.=))")
(* [comment removed for export] *).
Proof.
  intros M H. unfold file_clean.
  change (0x4cd30 + 140)%Z with 0x4cdbc%Z. change (0x4cd30 + 40)%Z with 0x4cd58%Z. change (0x4cd30 + 56)%Z with 0x4cd68%Z.
  change (0x4cd30 + 8)%Z with 0x4cd38%Z. change (0x4cd30 + 16)%Z with 0x4cd40%Z.
  split; [img_cell H img_49674_4 0x4cdbc%Z 4%nat|]. split; [img_cell H img_49610_8 0x4cd58%Z 8%nat|].
  split; [img_cell H img_49620_8 0x4cd68%Z 8%nat|]. split; [img_cell H img_495f0_8 0x4cd38%Z 8%nat|].
  img_cell H img_495f8_8 0x4cd40%Z 8%nat.
Qed.

(* [comment removed for export] *)
Lemma stdout_pristine_clean : ltac2:(CDefT.buildp (gd_tbl_P_exitkit ()) "PM,Px,(0.&40.)(1.(0.&8.))P,Pa,$2.P,(4.(5.+4<>20.R1.)(6.R1.+4<?08.))(9.(1.(0.&8.))A1.R3.(:.&40.R2.)(;.(0.&8.)))(10.R2.+4<>20.(:.&40.=)(:.&40.=))")
(* [comment removed for export] *).
Proof.
  intros M H. unfold file_clean.
  change (0x4ce20 + 140)%Z with 0x4ceac%Z. change (0x4ce20 + 40)%Z with 0x4ce48%Z. change (0x4ce20 + 56)%Z with 0x4ce58%Z.
  change (0x4ce20 + 8)%Z with 0x4ce28%Z. change (0x4ce20 + 16)%Z with 0x4ce30%Z.
  split; [img_cell H img_49764_4 0x4ceac%Z 4%nat|]. split; [img_cell H img_49700_8 0x4ce48%Z 8%nat|].
  split; [img_cell H img_49710_8 0x4ce58%Z 8%nat|]. split; [img_cell H img_496e0_8 0x4ce28%Z 8%nat|].
  img_cell H img_496e8_8 0x4ce30%Z 8%nat.
Qed.

(* [comment removed for export] *)
Lemma stdout_buffered_clean : forall M,
  stdout_buffered M 0x7d798 -> file_clean M 0x4ce20 (Z_to_bv 64 0x7d798) (Z_to_bv 64 0).
Proof.
  intros M SB. destruct SB. unfold file_clean.
  split; [exact sob_lock|]. split; [exact sob_wpos|]. split; [exact sob_wbase|]. split; [exact sob_rpos| exact sob_rend].
Qed.

Section XK.
  Variable sp0 : word.
  Variable model : Model.
  Variable tid : Z.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Variables (R : bvmap 5 word) (M : word -> option byte) (code : word).
  Hypothesis G2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 48).
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x5d0c8.
  Hypothesis G10 : getr R 10 = code.
  Hypothesis XM : exit_mem sp0 tid M.

  #[using="Hvsp SPlo SPhi G2 G4 G10 XM"] Lemma exit_common_of : ltac2:(CDefT.buildp (gd_tbl_P_exitkit ()) "Pwp2,(0.&40.)Prp2,(0.&40.)P,(10.VM,+4<=30.R2.R1.)(11.VR,VM,(:.&40.(12.(13.&40.Vsp0,)+30.))(:.&40.+5=0<8.)Vcode,Vtid,R3.R2.)")
(* [comment removed for export] *).
  Proof.
    intros wp2 rp2 FC. pose proof SPlo. pose proof SPhi. destruct XM as [Wn RO GOT RE U2 U1 CO TI TR LO [canw CA] NL SI OF _ AT].
    split.
    - exact G2.
    - exact G4.
    - exact G10.
    - rewrite u_small by lia. lia.
    - rewrite u_small by lia. lia.
    - rewrite u_small by lia. apply store_ok_of_all; rewrite u_small by lia; [lia|]. intros x Hx. apply Wn. lia.
    - rewrite u_small by lia. lia.
    - rewrite u_small by lia. lia.
    - lia.
    - rewrite u_small by lia. change (0x5d0c8 - 168)%Z with 0x5d020%Z. exact TI.
    - exact LO.
    - img_cell RE img_48598_8 0x4bce0%Z 8%nat.
    - img_cell RE img_485a0_8 0x4bce8%Z 8%nat.
    - img_cell RO img_44c10_8 0x48358%Z 8%nat.
    - exact CO.
    - img_cell RO img_48538_8 0x4bc80%Z 8%nat.
    - img_cell RO img_48540_8 0x4bc88%Z 8%nat.
    - unfold stdio_globals. split; [exact NL|]. split; [exact OF|]. split; [exact SI|].
      split; [img_cell U1 img_497c0_8 0x4cf08%Z 8%nat | img_cell U2 img_496d0_8 0x4ce18%Z 8%nat].
    - exact FC.
    - img_cell RE img_495a8_8 0x4ccf0%Z 8%nat.
    - exact AT.
  Qed.

  (* [comment removed for export] *)
  #[using="sp0 tid Hvsp Hh Hlazy SPlo SPhi G2 G4 G10 XM"] Theorem exit_pre_nostdout : ltac2:(CDefT.buildp (gd_tbl_P_exitkit ()) "P,Pa,$2.P,(4.(5.+4<>20.R1.)(6.R1.+4<?08.))(9.(1.(0.&8.))A1.VM,(:.&40.R2.)(;.(0.&8.)))(14.VR,VM,Vmodel,Vcode,(15.(0.&8.)))")
(* [comment removed for export] *).
  Proof.
    intros ST. destruct (xm_err _ _ _ XM) as (wp2 & rp2 & FC).
    dexists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0x5d0c8), tid, wp2, rp2.
    split; [apply exit_common_of; exact FC|]. split; [exact Hh|]. split; [exact Hlazy|].
    left. split; [reflexivity|]. dexists (Z_to_bv 64 0), (Z_to_bv 64 0). apply stdout_pristine_clean. exact ST.
  Qed.

  (* [comment removed for export] *)
  #[using="sp0 tid Hvsp Hh Hlazy SPlo SPhi G2 G4 G10 XM"] Theorem exit_pre_flushed :
    stdout_buffered M 0x7d798 -> exit_pre R M model code [].
  Proof.
    intros SB. destruct (xm_err _ _ _ XM) as (wp2 & rp2 & FC).
    dexists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0x5d0c8), tid, wp2, rp2.
    split; [apply exit_common_of; exact FC|]. split; [exact Hh|]. split; [exact Hlazy|].
    left. split; [reflexivity|]. dexists (Z_to_bv 64 0x7d798), (Z_to_bv 64 0). apply stdout_buffered_clean. exact SB.
  Qed.

  (* [comment removed for export] *)
  #[using="sp0 tid Hvsp Hh Hlazy SPlo SPhi G2 G4 G10 XM"] Theorem exit_pre_pending : ltac2:(CDefT.buildp (gd_tbl_P_exitkit ()) "Pwp,$2.Ppending,(=.(0.&8.))P,(16.VM,R2.)P,(4.(6.+7=798.R3.)(5.R3.+7=;98.))P,(9.$2.(12.R4.+7=798.)(8.(17.(0.&8.)R3.)))P,(9.(1.(=.(0.&8.)))(>.$?.VM,(:.&40.+7=798.)(17.(0.&8.)R4.))(18.(=.(0.&8.))R4.))P,(9.(1.$19.)(1:.(1;.Vmodel,)(:.&40.+1.))(18.$19.(1<.(:.&40.+1.))))(14.VR,VM,Vmodel,Vcode,R6.)")
(* [comment removed for export] *).
  Proof.
    intros wp pending SB Hwp Hlen Hrd Hfd1. destruct (xm_err _ _ _ XM) as (wp2 & rp2 & FC).
    pose proof XM as [Wn RO GOT RE U2 U1 CO TI TR LO [canw CA] NL SI OF _ _]. destruct SB.
    dexists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0x5d0c8), tid, wp2, rp2.
    split; [apply exit_common_of; exact FC|]. split; [exact Hh|]. split; [exact Hlazy|].
    right. dexists 0x7d798%Z, wp, (Z_to_bv 64 0x7d798), (Z_to_bv 64 1024), (Z_to_bv 64 0), canw.
    split; [|exact Hfd1].
    split.
    - exact sob_lock.
    - exact sob_wpos.
    - exact sob_wbase.
    - exact sob_write.
    - exact sob_buf.
    - exact sob_bsz.
    - exact sob_fd.
    - exact sob_rpos.
    - exact sob_rend.
    - lia.
    - exact Hlen.
    - unfold rw_bytes_max. lia.
    - exact Hrd.
    - split; [exact GOT | exact CA].
  Qed.
End XK.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
