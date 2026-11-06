(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiOpnd.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_divmod_stmt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_mpi_add_abs_W A_mpi_add_sub A_mpi_add_sub_ng_sz A_mpi_add_sub_stmtSZ
     A_mpi_div_stmtA A_mpi_div_mpi_c24 A_mpi_mod_stmtA A_mpi_mod_mpi.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AEvtS TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_mod_mpi_sz () : Init.string Init.list := ["OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.A.A_mpi_div_stmtA.mpi_div_mpi_stmtA"; "OSSVerify.KrLib.A.A_mpi_div_stmtA.A_MPI_DIV_MPI_E"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.A.A_mpi_div_mpi_c24.div_mpi_PHI"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.A.A_mpi_div_mpi_c24.div_mpi_FR"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.A.A_mpi_add_sub_ng_sz.add_sub_mpi_ng_stmtA_oz"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_ADD_SUB_MPI"; "OSSVerify.KrLib.A.A_mpi_add_sub_stmtSZ.add_sub_mpi_stmtA_osz"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.LibA.ARt.HM"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.A.A_mpi_mod_stmtA.mpi_mod_mpi_stmtA"; "OSSVerify.KrLib.A.A_mpi_mod_stmtA.A_MPI_MOD_MPI_E"; "mod_mpi_PHI"; "mod_mpi_FR"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.mpi_binop_stmtA_sz"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.C24_MOD_MPI"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.mod_mpi_Rsz"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.mpi_mod_mpi_stmtA_sz"].


Definition mod_mpi_PHI (dX dA dB : mpd) : Z := mod_mpi_PHIg (fun _ dA dB => div_mpi_PHI dA dB) dX dA dB.
Definition mod_mpi_FR (dX dA dB : mpd) (d : Z) : Z := mod_mpi_FRg (fun _ dA _ d => div_mpi_FR dA d) dX dA dB d.

Lemma mod_mpi_PHI_val : forall dX dA dB, mod_mpi_PHI dX dA dB = 1200136 * md_n dA + 48 * md_n dB + 80088.
Proof. intros. unfold mod_mpi_PHI, mod_mpi_PHIg. rewrite div_mpi_PHI_val. lia. Qed.
Lemma mod_mpi_FR_val : forall dX dA dB d, mod_mpi_FR dX dA dB d = md_n dA * (20 * d + 98) + 17 * d + 88.
Proof. intros. unfold mod_mpi_FR, mod_mpi_FRg. rewrite div_mpi_FR_val. unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge. lia. Qed.

(* [comment removed for export] *)
Theorem A_mpi_mod_mpi_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_sz ()) "PR,$0.PHIA,(1.$2.R1.)P,(3.(4.R2.))P,(5.$2.R3.R2.$6.L,$7.LdA,$7.LdB,$7.(8.R2.R1.)L,$7.LdA,$7.L,$7.Ld,$9.(:.R3.R1.))P,Pflip,$9.P,(;.(<.$9.R1.+1.)(<.$9.R1.-1.))(=.R2.$2.R6.R5.$>.)P,(?.+1.$2.R5.R4.$>.)P,(10.=(11.R6.))P,Ph,(12.$2.R7.R6.)PLB,(13.$14.)PLF,(13.$14.)Pm,P,(15.&40.)(16.(15.&8.))P,(17.$2.R;.R:.R4.R3.R2.R1.)(18.$9.(19.(1:.$9.$9.)$9.(1;.$9.$9.)R4.))P,(1<.(10.(1=.(1>.R8.))(1?.(1>.R8.)))(10.(20.(1>.R8.))(21.(1>.R8.))))P,Pa,$9.P,(<.$22.(23.$2.(24.R1.))$25.)P,(1<.(10.=R2.)(26.R2.(27.+2.+40.)))(1<.(10.(1=.(1>.R<.))R3.)(26.R3.(21.(1>.R<.))))(28.$2.R:.R9.$29.$2:.$2;.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG HDIV HASN HADD NEEDR HND DIMG ROIMG.
  eapply (A_mpi_mod_mpi_spec_g R HIA (fun _ dA dB => div_mpi_PHI dA dB) (fun _ dA _ d => div_mpi_FR dA d)); try eassumption.
  - intros dX dA dB NA NB. rewrite div_mpi_PHI_val. lia.
  - intros dX dA dB d NA D0. rewrite div_mpi_FR_val. nia.
Qed.

(* [comment removed for export] *)
Lemma mpi_mod_mpi_stmtA_sz_gen : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_sz ()) "PR,$0.PHIA,(1.$2.R1.)PENTRY,$9.PPHI,P,$7.P,$7.P,$7.$9.PFRC,P,$7.P,$7.P,$7.P,$9.$9.PPHIt,P,$7.P,$7.P,$7.$9.PFRt,P,$7.P,$7.P,$7.P,$9.$9.P,(28.$2.R7.R6.R5.R4.R3.)P,PdX,$7.PdA,$7.PdB,$7.P,(1<.(10.=(2<.R2.))(10.(2<.R2.)+2710.))P,(1<.(10.=(2<.R2.))(10.(2<.R2.)+2710.))(10.A3.R:.R5.R4.R3.A3.R8.R5.R4.R3.)P,PdX,$7.PdA,$7.PdB,$7.Pd,$9.P,(1<.(10.=(2<.R3.))(10.(2<.R3.)+2710.))P,(1<.(10.=(2<.R3.))(10.(2<.R3.)+2710.))P,(10.=R3.)(10.A4.R<.R7.R6.R5.R4.A4.R:.R7.R6.R5.R4.)(2=.$2.R:.R9.R8.+2=0.#2.$2>.$25.$25.R5.R4.$2?.)")
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
Theorem A_mpi_mod_mpi_sz_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_sz ()) "PR,$0.PHIA,(1.$2.R1.)P,(3.(4.R2.))P,(5.$2.R3.R2.$6.L,$7.LdA,$7.LdB,$7.(8.R2.R1.)L,$7.LdA,$7.L,$7.Ld,$9.(:.R3.R1.))P,Pflip,$9.P,(;.(<.$9.R1.+1.)(<.$9.R1.-1.))(=.R2.$2.R6.R5.$>.)P,(?.+1.$2.R5.R4.$>.)P,(10.=(11.R6.))P,Ph,(12.$2.R7.R6.)PLB,(13.$14.)PLF,(13.$14.)Pm,P,(15.&40.)(16.(15.&8.))P,(17.$2.R;.R:.R4.R3.R2.R1.)(18.$9.(19.(1:.$9.$9.)$9.(1;.$9.$9.)R4.))P,(1<.(10.(1=.(1>.R8.))(1?.(1>.R8.)))(10.(20.(1>.R8.))(21.(1>.R8.))))P,Pa,$9.P,(<.$22.(23.$2.(24.R1.))$25.)P,(1<.(10.=R2.)(26.R2.(27.+2.+40.)))(1<.(10.(1=.(1>.R<.))R3.)(26.R3.(21.(1>.R<.))))(30.$2.R:.R9.$29.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG HDIV HASN HADD NEEDR HND DIMG ROIMG. unfold mpi_mod_mpi_stmtA_sz.
  eapply mpi_mod_mpi_stmtA_sz_gen; [eapply A_mpi_mod_mpi_spec; eassumption| |].
  - intros dX dA dB NA NB. rewrite mod_mpi_PHI_val. unfold mod_mpi_PHIn. lia.
  - intros dX dA dB d NA NB D0. rewrite mod_mpi_FR_val. unfold mod_mpi_FRn, calls_FR, fr_charge. nia.
Qed.
