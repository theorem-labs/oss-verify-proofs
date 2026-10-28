(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import RepEcp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_ecp_grp_id_list () : Init.string Init.list := ["Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "ecp_ids_bytes"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "ecp_ids_state"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "ecp_grp_id_list_post"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"].


Definition U_ECP_GRP_ID_LIST : Z := 0x38310.
Definition U_ECP_IDS_DONE : Z := 0x5cfa0.   (* [comment removed for export] *)
Definition U_ECP_IDS : Z := 0x5cfc0.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ecp_ids : list Z := [5; 8; 4; 7; 3; 12; 6; 2; 11; 1; 10; 9; 13; 0].
Definition ecp_ids_bytes : list byte := Eval vm_compute in flat_map (fun i => le4 (Z_to_bv 64 i)) ecp_ids.

(* [comment removed for export] *)
Definition ecp_ids_state (segs : list Segment) (IDONE IDS : Z) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_grp_id_list ()) "(0.(1.&8.)Lb,(1.&8.)(0.(2.(1.&8.))Lbs,(2.(1.&8.))(3.(4.O4.O1.O3.(5.$6.(7.#1.(5.(1.&8.)R2.(8.(1.&8.))))(8.$6.)))(3.(4.O4.O1.O2.(5.$6.(7.#38.R1.)(8.$6.)))P,(9.(:.$;.(<.&8.R2.)=))(:.(2.(1.&8.))R2.$=.)))))")
(* [comment removed for export] *).

Definition ecp_grp_id_list_post (segs : list Segment) (IDONE IDS : Z)
    (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_grp_id_list ()) "Lms',$>.(0.(1.&40.)Lt0,(1.&40.)(0.(1.&40.)Lt1,(1.&40.)(0.(1.&40.)La1,(1.&40.)(0.(1.&40.)La2,(1.&40.)(0.(1.&40.)La3,(1.&40.)(0.(1.&40.)La4,(1.&40.)(0.(1.&40.)La5,(1.&40.)(0.(1.&40.)La6,(1.&40.)(0.(1.&40.)La7,(1.&40.)(0.P,(1.&40.)(?.(1.&8.))Lm',P,(1.&40.)(?.(1.&8.))(0.(1.&8.)Lb,(1.&8.)(3.(:.$>.R<.(10.(11.O18.O17.O16.O15.R;.R:.O14.O13.O12.(12.&40.O19.)R9.R8.R7.R6.R5.R4.R3.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.)O3.(13.O18.)O2.(14.(1.&40.))R2.(15.O1;.)))(3.(16.(5.(17.$;.$;.)(18.$;.$;.O1:.(19.O1:.+1.))(5.(17.$;.$;.)(18.$;.$;.O19.(19.O19.+38.))(8.(17.$;.$;.))))O1.R2.)(3.(1:.O1;.O1.R2.)(3.(1;.O1;.R2.)(3.(4.O1;.R2.O1:.(5.$6.(7.#1.(5.(1.&8.)R1.(8.(1.&8.))))(8.$6.)))(3.(9.(:.$;.(<.&8.R1.)=))(4.O1;.R2.O19.(5.$6.(7.#38.$=.)(8.$6.))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_grp_id_list_stmt (segs : list Segment) (ENTRY IDONE IDS : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_grp_id_list ()) "Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(1<.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(?.(1.&8.))P,(1=.O4.O2.O1.R1.)P,(1;.O4.R2.)P,(:.$;.(1>.(<.&40.R24.)+2.)=)(1?.O4.(20.O4.O2.O1.R25.R24.R23.R22.R1?.R1>.R1=.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)(10.(11.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R6.(12.&40.O3.)R5.(14.(1.&40.))R4.(15.O4.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Lemma ecp_ids_state_done : ltac2:(CDefT.buildp (gd_tbl_P_ecp_grp_id_list ()) "Psegs,(2.$21.)PIDONE,$;.PIDS,$;.Pm,P,(1.&40.)(?.(1.&8.))Pb,(1.&8.)P,(4.R5.R2.R4.(5.$6.(7.#1.(5.(1.&8.)R1.(8.(1.&8.))))(8.$6.)))P,(9.(:.$;.(<.&8.R2.)=))P,(4.R7.R4.R5.(5.$6.(7.#38.$=.)(8.$6.)))(1=.R8.R7.R6.R5.)")
(* [comment removed for export] *).
Proof. intros. dexists b, ecp_ids_bytes. auto. Qed.

Lemma U_ecp_grp_id_list_spec : ecp_grp_id_list_stmt usegs U_ECP_GRP_ID_LIST U_ECP_IDS_DONE U_ECP_IDS.
Proof.
  unfold ecp_grp_id_list_stmt, U_ECP_GRP_ID_LIST, U_ECP_IDS_DONE, U_ECP_IDS. intros until m. (intros dd_H; ddestruct dd_H as (b & bs & HF & HA & HINV); intros MI RA).
  pose proof HA as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [LBS _].
  pose proof (munch_refl [(0x5cfa0, 0x5cfa0 + 1); (0x5cfc0, 0x5cfc0 + 56)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. zstep. zstep. zstep.
  if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    zstep. zstep. finish; [exact HF| exact K0| rewrite (HINV K0) in HA; exact HA].
  - (* [comment removed for export] *)
    do 27 zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
    do 4 zstep.
    finish.
    + match goal with H : rw_cells usegs ?mx 0x5cfa0 _ |- _ => eapply rw_cells_reshape; [exact H| cbn; tauto| reflexivity] end.
    + vm_compute. discriminate.
    + match goal with H : rw_cells usegs ?mx 0x5cfc0 ?cs |- _ =>
        pose proof (rw_cells_merge usegs mx 0x5cfc0 [] cs []) as R; cbn [app] in R; rewrite ?app_nil_r in R; specialize (R H) end.
      match type of R with rw_cells _ _ _ [CB ?n ?bs] => change n with 56%nat in R;
        replace bs with ecp_ids_bytes in R by (apply bytes_eq_of_unsigned; vm_compute; reflexivity) end.
      exact R.
Qed.
