(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ShapeX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Export SumWalkTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Export SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_exit_base () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.None"; "atexit_st"; "Corelib.Init.Datatypes.false"; "atexit_none"; "atexit_fp"; "atexit_reg"].


Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_wseg_1c : wseg_ok RSEGS (0x4c000 : word) 204800%nat = true.  (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.

Lemma store_ok_data : ltac2:(CDefT.buildp (gd_tbl_P_exit_base ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)Pn,$2.P,(3.+4<000.(4.&40.R2.))P,(3.(5.(4.&40.R3.)(6.R2.))+7>000.)(7.$8.(9.$:.R5.R4.R3.)$;.)")
(* [comment removed for export] *).
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window RSEGS m (0x4c000 : word) a 204800%nat n 0x4c000 0x7e000);
    [reflexivity | reflexivity | lia | exact ref_wseg_1c | exact Hlo | exact Hhi].
Qed.

(* [comment removed for export] *)
Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_clean (mem : word -> option byte) (f : Z) (wp rp : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_exit_base ()) "(<.(7.(1.(=.(0.&8.)))(>.$:.O4.(?.&40.(5.O3.+8<.))#4.)(10.(=.(0.&8.))(11.#4.(?.&40.+????????.))))(<.(7.(1.(=.(0.&8.)))(>.$:.O4.(?.&40.(5.O3.+28.))#8.)(10.(=.(0.&8.))(11.#8.O2.)))(<.(7.(1.(=.(0.&8.)))(>.$:.O4.(?.&40.(5.O3.+38.))#8.)(10.(=.(0.&8.))(11.#8.O2.)))(<.(7.(1.(=.(0.&8.)))(>.$:.O4.(?.&40.(5.O3.+8.))#8.)(10.(=.(0.&8.))(11.#8.O1.)))(7.(1.(=.(0.&8.)))(>.$:.O4.(?.&40.(5.O3.+10.))#8.)(10.(=.(0.&8.))(11.#8.O1.)))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition stdio_globals (mem : word -> option byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_exit_base ()) "(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+7=353.)#1.)(10.(=.(0.&8.))(12.(0.&8.)(?.&8.=)(13.(0.&8.)))))(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+7=780.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.=))))(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+7=770.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.=))))(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+4<?08.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.+4<>20.))))(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+4<>18.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.+4<=30.))))))))")
(* [comment removed for export] *). (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition atexit_none (mem : word -> option byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_exit_base ()) "(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+7=118.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.=))))(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+7=10<.)#4.)(10.(=.(0.&8.))(11.#4.(?.&40.=)))))")
(* [comment removed for export] *).       (* [comment removed for export] *)

Definition atexit_reg (mem : word -> option byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_exit_base ()) "(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+7=118.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.+7=120.))))(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+7=10<.)#4.)(10.(=.(0.&8.))(11.#4.(?.&40.=))))(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+7=110.)#4.)(10.(=.(0.&8.))(11.#4.(?.&40.+1.))))(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+7=120.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.=))))(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+7=128.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.+3?6?8.))))(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+7=228.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.+1=674.))))(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+5<?74.)#1.)(10.(=.(0.&8.))(12.(0.&8.)(?.&8.=)(13.(0.&8.)))))))))))")
(* [comment removed for export] *).                             (* [comment removed for export] *)

Definition atexit_st (reg : bool) (M : word -> option byte) : Prop := if reg then atexit_reg M else atexit_none M.

(* [comment removed for export] *)
Definition atexit_fp (x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_exit_base ()) "(14.(<.(3.+5<?74.O1.)(15.O1.+5<?75.))(14.(<.(3.+7=10<.O1.)(15.O1.+7=114.))(14.(<.(3.+7=118.O1.)(15.O1.+7=130.))(<.(3.+7=228.O1.)(15.O1.+7=230.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma atx_img_head : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x7d118) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma atx_img_lock : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x7d10c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma atx_rdn_agree : ltac2:(CDefT.buildp (gd_tbl_P_exit_base ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Pa,$16.Pn,$2.P,(3.=R2.)P,(3.(5.R3.(6.R2.))(17.+2.+40.))P,Px,$16.P,(<.(3.R5.R1.)(15.R1.(5.R5.(6.R4.))))(7.(1.(0.&8.))A1.R7.(?.&40.R2.)A1.R8.(?.&40.R2.))(7.(1.(=.(0.&8.)))(>.$:.R6.(?.&40.R5.)R4.)(>.$:.R7.(?.&40.R5.)R4.))")
(* [comment removed for export] *).
Proof.
  intros m m' a n Ha Hn AG. destruct n as [|n]; [reflexivity|].
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. specialize (AG (bv_unsigned x) Hx). rewrite Z_to_bv_bv_unsigned in AG. exact AG.
Qed.

(* [comment removed for export] *)
Lemma atexit_st_none_of_pristine : ltac2:(CDefT.buildp (gd_tbl_P_exit_base ()) "Pm,P,(0.&40.)(1.(0.&8.))P,Pa,$16.P,(<.(3.+7=108.R1.)(15.R1.+7=120.))(7.(1.(0.&8.))A1.R3.(?.&40.R2.)(18.(0.&8.)))(19.$1:.R2.)")
(* [comment removed for export] *).
Proof.
  intros m H. change (atexit_none m). split.
  - rewrite (atx_rdn_agree (fun _ => None) m 0x7d118 8); [exact atx_img_head | lia | lia | intros x Hx; apply H; lia].
  - rewrite (atx_rdn_agree (fun _ => None) m 0x7d10c 4); [exact atx_img_lock | lia | lia | intros x Hx; apply H; lia].
Qed.

(* [comment removed for export] *)
Lemma atexit_none_agree : ltac2:(CDefT.buildp (gd_tbl_P_exit_base ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))P,(1;.R2.)P,Px,$16.P,(1<.R1.)(7.(1.(0.&8.))A1.R4.(?.&40.R2.)A1.R5.(?.&40.R2.))(1;.R3.)")
(* [comment removed for export] *).
Proof.
  intros m m' (A & B) AG. unfold atexit_fp in AG. split.
  - rewrite (atx_rdn_agree m m') by (first [lia | intros x Hx; apply AG; lia]). exact A.
  - rewrite (atx_rdn_agree m m') by (first [lia | intros x Hx; apply AG; lia]). exact B.
Qed.

Lemma atexit_reg_agree : ltac2:(CDefT.buildp (gd_tbl_P_exit_base ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))P,(1=.R2.)P,Px,$16.P,(1<.R1.)(7.(1.(0.&8.))A1.R4.(?.&40.R2.)A1.R5.(?.&40.R2.))(1=.R3.)")
(* [comment removed for export] *).
Proof.
  (intros m m' dd_H; ddestruct dd_H as (A & B & C & D & E & F & G); intros AG). unfold atexit_fp in AG.
  repeat split; rewrite (atx_rdn_agree m m') by (first [lia | intros x Hx; apply AG; lia]); assumption.
Qed.

Lemma atexit_st_agree : ltac2:(CDefT.buildp (gd_tbl_P_exit_base ()) "Pb,$8.Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))P,(19.R3.R2.)P,Px,$16.P,(1<.R1.)(7.(1.(0.&8.))A1.R4.(?.&40.R2.)A1.R5.(?.&40.R2.))(19.R5.R3.)")
(* [comment removed for export] *).
Proof.
  intros [|] m m' H AG; unfold atexit_st in H |- *; [eapply atexit_reg_agree | eapply atexit_none_agree]; eauto.
Qed.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
