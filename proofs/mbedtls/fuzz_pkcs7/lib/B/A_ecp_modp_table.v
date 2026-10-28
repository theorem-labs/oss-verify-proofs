(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpCurves.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_mpi_grow A_mpi_core_mul A_amemmove_stmt A_ecp_red_lib A_ecp_defs
  A_ecp_mod_p192 A_ecp_mod_p224 A_ecp_mod_p256 A_ecp_mod_p384 A_ecp_mod_p521 A_ecp_mod_p255 A_ecp_mod_p192k1 A_ecp_mod_p224k1 A_ecp_mod_p256k1 A_ecp_mod_p448.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_A_ecp_modp_table () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"].


Section TBL.
  Variable R : art_layout.
  Variable HIA : artA asegs R.
  Hypothesis IMG : asan_img_ok (arl_AL R).
  Hypothesis UARG : arl_uar_got R = 0x0f5ea8.
  Hypothesis SM1 : arl_smalloc R 1 = 0x5306c.
  Hypothesis SM2 : arl_smalloc R 2 = 0x531fc.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis GROW : mpi_grow_stmtA_sz asegs R HIA A_MPI_GROW.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_EC.
  Hypothesis AMC : arl_amemcpy R = 0x67dbc.
  Hypothesis CMUL : mpi_core_mul_stmtA asegs R HIA A_MPI_CORE_MUL.
  Hypothesis AMM : amemmove_stmtA asegs R HIA A_ASAN_MEMMOVE.
  Hypothesis RTC : forall m, arl_rtc R m -> asan_rtc m.
  Hypothesis PRIMG : forall a, rtc_prist a -> hl_img_lo (arl_L R) <= a < hl_img_hi (arl_L R).
  Hypothesis DIMG : hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R).
  Hypothesis ROIMG : ltac2:(CDefT.buildp (gd_tbl_A_ecp_modp_table ()) "Pa,$0.P,(1.$2.(3.$4.(5.R1.))$6.)P,(7.(8.=R2.)(9.R2.(:.+2.+40.)))(7.(8.(;.(<.VR,))R3.)(9.R3.(=.(<.VR,))))")
(* [comment removed for export] *).
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L15454560991.18L1702057183.18 L24728057055.18L3497718271.18 L47380624607.18L49943550975.18L55576763007.18L55828726271.18L56809643135.18L62977909471.18L65010947199.1800000100200300400500600700800900:00;SSSSSSSSSSS". (* [comment removed for export] *)
  #[using="IMG UARG SM1 SM2 NS1 NEEDR GROW AMS AMC CMUL AMM RTC PRIMG DIMG ROIMG HND"] Lemma A_modp_table_ok : modp_table_okA asegs R HIA A_MT.
  Proof.
    unfold modp_table_okA, A_MT. intros e lp ws IN.
    repeat (destruct IN as [E|IN];
      [ injection E as <- <- <-; split; [reflexivity|]; eexists _, _;
        split; [| split; [|
          first [ exact (A_ecp_mod_p192_spec R HIA IMG GROW AMS NEEDR HND DIMG ROIMG)
                | exact (A_ecp_mod_p224_spec R HIA IMG GROW AMS NEEDR HND DIMG ROIMG)
                | exact (A_ecp_mod_p256_spec R HIA IMG GROW AMS NEEDR HND DIMG ROIMG)
                | exact (A_ecp_mod_p384_spec R HIA IMG GROW AMS NEEDR HND DIMG ROIMG)
                | exact (A_ecp_mod_p521_spec R HIA IMG GROW AMS NEEDR HND DIMG ROIMG)
                | exact (A_ecp_mod_p255_spec R HIA IMG UARG SM1 NS1 NEEDR GROW AMS DIMG HND)
                | exact (A_ecp_mod_p192k1_spec R HIA IMG UARG SM2 NS1 NEEDR GROW AMS AMC CMUL RTC PRIMG DIMG ROIMG HND)
                | exact (A_ecp_mod_p224k1_spec R HIA IMG UARG SM2 NS1 NEEDR GROW AMS AMC CMUL RTC PRIMG DIMG ROIMG HND)
                | exact (A_ecp_mod_p256k1_spec R HIA IMG UARG SM2 NS1 NEEDR GROW AMS AMC CMUL RTC PRIMG DIMG ROIMG HND)
                | exact (A_ecp_mod_p448_spec R HIA IMG UARG SM2 NS1 NEEDR GROW AMS AMC AMM DIMG HND) ]]];
        [cbn; lia| lia] |]).
    destruct IN.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End TBL.
