(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_divmod_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_mpi_add_abs_W A_mpi_add_sub A_mpi_add_sub_ng_sz A_mpi_add_sub_stmtSZ
     A_mpi_div_stmtA A_mpi_div_mpi_c24 A_mpi_mod_stmtA A_mpi_mod_mpi_C A_mpi_mod_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AEvtS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_mod_mpi_sz () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_div_stmtA.mpi_div_mpi_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_div_stmtA.A_MPI_DIV_MPI_E"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_div_mpi_c24.div_mpi_PHI"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_div_mpi_c24.div_mpi_FR"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_ng_sz.add_sub_mpi_ng_stmtA_oz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ADD_SUB_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_stmtSZ.add_sub_mpi_stmtA_osz"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mod_stmtA.mpi_mod_mpi_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mod_stmtA.A_MPI_MOD_MPI_E"; "mod_mpi_PHI"; "mod_mpi_FR"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_binop_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.C24_MOD_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mod_mpi_Rsz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_mod_mpi_stmtA_sz"].


Definition mod_mpi_PHI (dX dA dB : mpd) : Z := mod_mpi_PHIg (fun _ dA dB => div_mpi_PHI dA dB) dX dA dB.
Definition mod_mpi_FR (dX dA dB : mpd) (d : Z) : Z := mod_mpi_FRg (fun _ dA _ d => div_mpi_FR dA d) dX dA dB d.

Lemma mod_mpi_PHI_val : forall dX dA dB, mod_mpi_PHI dX dA dB = 1200136 * md_n dA + 48 * md_n dB + 80088.
Proof. intros. unfold mod_mpi_PHI, mod_mpi_PHIg. rewrite div_mpi_PHI_val. lia. Qed.
Lemma mod_mpi_FR_val : forall dX dA dB d, mod_mpi_FR dX dA dB d = md_n dA * (20 * d + 118) + 17 * d + 105.
Proof. intros. unfold mod_mpi_FR, mod_mpi_FRg. rewrite div_mpi_FR_val. unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge. lia. Qed.

(* [comment removed for export] *)
Theorem A_mpi_mod_mpi_spec : forall (R : art_layout) (HIA : artA asegs R),
    asan_img_ok (arl_AL R) ->
    arl_uar_got R = A_UAR_GOT_MD ->
    arl_smalloc R 0 = A_SMALLOC_0_MD ->
    0 <= arl_need_smalloc R ->
    mpi_div_mpi_stmtA asegs R HIA A_MPI_DIV_MPI_E (fun (_ : mpd) (dA dB : mpd) => div_mpi_PHI dA dB)
      (fun (_ : mpd) (dA : mpd) (_ : mpd) (d : Z) => div_mpi_FR dA d) ->
    (forall flip : Z, flip = 1 \/ flip = -1 -> add_sub_mpi_ng_stmtA_oz flip asegs R HIA A_ADD_SUB_MPI) ->
    add_sub_mpi_stmtA_osz 1 asegs R HIA A_ADD_SUB_MPI ->
    0 <= arl_need_rt R ->
    (forall (h : HST asegs R HIA) (LB LF : list blk) (m : mem), HM asegs R HIA h LB LF m -> List.NoDup (map fst LB)) ->
    hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R) ->
    (forall a : Z, ro_addr asegs (wa a) = true -> 0 <= a < 2 ^ 64 -> hl_img_lo (arl_L R) <= a < hl_img_hi (arl_L R)) ->
    mpi_mod_mpi_stmtA asegs R HIA A_MPI_MOD_MPI_E mod_mpi_PHI mod_mpi_FR
(* [comment removed for export] *).
Proof.
  intros R HIA IMG UARG SM0 NS1 HDIV HASN HADD NEEDR HND DIMG ROIMG.
  eapply (A_mpi_mod_mpi_spec_g R HIA (fun _ dA dB => div_mpi_PHI dA dB) (fun _ dA _ d => div_mpi_FR dA d)); try eassumption.
  - intros dX dA dB NA NB. rewrite div_mpi_PHI_val. lia.
  - intros dX dA dB d NA D0. rewrite div_mpi_FR_val. nia.
Qed.

(* [comment removed for export] *)
Lemma mpi_mod_mpi_stmtA_sz_gen : forall (R : art_layout) (HIA : artA asegs R) (ENTRY : Z)
    (PHI : mpd -> mpd -> mpd -> Z) (FRC : mpd -> mpd -> mpd -> Z -> Z)
    (PHIt : mpd -> mpd -> mpd -> Z) (FRt : mpd -> mpd -> mpd -> Z -> Z),
    mpi_mod_mpi_stmtA asegs R HIA ENTRY PHI FRC ->
    (forall dX dA dB : mpd, 0 <= md_n dA <= 10000 -> 0 <= md_n dB <= 10000 -> PHI dX dA dB <= PHIt dX dA dB) ->
    (forall (dX dA dB : mpd) (d : Z), 0 <= md_n dA <= 10000 -> 0 <= md_n dB <= 10000 -> 0 <= d ->
       FRC dX dA dB d <= FRt dX dA dB d) ->
    mpi_binop_stmtA_sz asegs R HIA ENTRY 864 2%nat C24_MOD_MPI true true PHIt FRt mod_mpi_Rsz
(* [comment removed for export] *).
Proof.
  intros R HIA ENTRY PHI FRC PHIt FRt H HP HF. unfold mpi_binop_stmtA_sz. intros until slo.
  intros HH HK LFB MX MA MB SXA SXB SAB NST NEB OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO SS TOP SPA TPV MI RAE OXA OAA OBA IA IB BUD UW UWX _ UWB BUDF C24 E0 E1 E2.
  pose proof (arl_need_ecp_rt R) as NER. pose proof (arl_need_ecp_smalloc R) as NES.
  ddestruct (SS eq_refl) as (SSH & SLOS & SLOL).
  pose proof MA as [(_ & _ & _ & _ & NRA & _) _]. pose proof MB as [(_ & _ & _ & _ & NRB & _) _]. unfold MPI_MAX_LIMBS in NRA, NRB.
  pose proof (uw_obj_nonneg _ _ _ _ UWX) as D0.
  pose proof (HP dX dA dB NRA NRB) as LEP. pose proof (HF dX dA dB d NRA NRB D0) as LEF.
  eapply aevtS_mono.
  - unfold mpi_mod_mpi_stmtA in H.
    eapply H with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (slo := slo) (d := d);
      first [ eassumption | reflexivity | exact (NEB eq_refl)
            | (clear - LFB; lia) | (clear - SLO NER; lia) | (clear - SLO NES; lia)
            | (intros ES _; first [exact (IA ES) | exact (IB ES)])
            | (clear - BUD LEP; lia) | (clear - BUDF LEF; lia)
            | (unfold C24_MOD_MPI in C24; unfold C24_DIV_MPI; exact C24)
            | match goal with |- ?g => idtac "MODSZ-LEFT:" g end ].
  - cbv beta. intros c PO. unfold mpi_binop_postA in *.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & mo' & h' & LB' & dX' & r & PO).
    dexists y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m', mo', h', LB', dX', r.
    ddestruct PO as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16).
    split; [exact P0|]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|].
    split; [exact P8|]. split; [exact P9|]. split; [clear - P10 LEP; lia|]. split; [clear - P11 LEF; lia|].
    split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|].
    exact P16.
Qed.

(* [comment removed for export] *)
Theorem A_mpi_mod_mpi_sz_spec : forall (R : art_layout) (HIA : artA asegs R),
    asan_img_ok (arl_AL R) ->
    arl_uar_got R = A_UAR_GOT_MD ->
    arl_smalloc R 0 = A_SMALLOC_0_MD ->
    0 <= arl_need_smalloc R ->
    mpi_div_mpi_stmtA asegs R HIA A_MPI_DIV_MPI_E (fun (_ : mpd) (dA dB : mpd) => div_mpi_PHI dA dB)
      (fun (_ : mpd) (dA : mpd) (_ : mpd) (d : Z) => div_mpi_FR dA d) ->
    (forall flip : Z, flip = 1 \/ flip = -1 -> add_sub_mpi_ng_stmtA_oz flip asegs R HIA A_ADD_SUB_MPI) ->
    add_sub_mpi_stmtA_osz 1 asegs R HIA A_ADD_SUB_MPI ->
    0 <= arl_need_rt R ->
    (forall (h : HST asegs R HIA) (LB LF : list blk) (m : mem), HM asegs R HIA h LB LF m -> List.NoDup (map fst LB)) ->
    hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R) ->
    (forall a : Z, ro_addr asegs (wa a) = true -> 0 <= a < 2 ^ 64 -> hl_img_lo (arl_L R) <= a < hl_img_hi (arl_L R)) ->
    mpi_mod_mpi_stmtA_sz asegs R HIA A_MPI_MOD_MPI_E
(* [comment removed for export] *).
Proof.
  intros R HIA IMG UARG SM0 NS1 HDIV HASN HADD NEEDR HND DIMG ROIMG. unfold mpi_mod_mpi_stmtA_sz.
  eapply mpi_mod_mpi_stmtA_sz_gen; [eapply A_mpi_mod_mpi_spec; eassumption| |].
  - intros dX dA dB NA NB. rewrite mod_mpi_PHI_val. unfold mod_mpi_PHIn. lia.
  - intros dX dA dB d NA NB D0. rewrite mod_mpi_FR_val. unfold mod_mpi_FRn, calls_FR, fr_charge. nia.
Qed.
