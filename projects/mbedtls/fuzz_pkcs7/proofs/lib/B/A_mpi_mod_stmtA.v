(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_divmod_stmt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals A_alloc_lib A_mpi_stmtA A_mpi_div_stmtA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw AEvtS. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_mod_stmtA () : Init.string Init.list := ["OSSVerify.KrLib.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibB.ARt.HM"; "OSSVerify.KrLib.LibB.ARt.HK"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.P.P_mpi_addsub.opnd_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibB.ARt.fdata"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.B.A_mpi_stmtA.mpd_writableA"; "OSSVerify.KrLib.LibB.ARt.htop"; "OSSVerify.KrLib.Spec.Rep.LNull"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.B.A_mpi_read_binary_stmt.arl_need_rt"; "OSSVerify.KrLib.LibB.ARt.arl_need_smalloc"; "OSSVerify.KrLib.LibB.ARt.sshad"; "OSSVerify.KrLib.LibB.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.LibB.ARt.arl_tp"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.B.A_mpi_stmtA.mpd_aobjA"; "OSSVerify.KrLib.LibB.ARt.hcs"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.B.AImgGlobals.img_norz"; "OSSVerify.KrLib.LibB.ARt.havol"; "OSSVerify.KrLib.LibB.ARt.AVOL_MAX"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.LibB.ARt.hstkhi"; "OSSVerify.KrLib.B.A_alloc_lib.uw_obj"; "OSSVerify.KrLib.LibB.ARt.hfr"; "OSSVerify.KrLib.LibB.ARt.FR_MAX"; "OSSVerify.KrLib.LibA.ACnt24.cnt24"; "OSSVerify.KrLib.B.A_mpi_div_stmtA.C24_DIV_MPI"; "OSSVerify.KrLib.LibA.ACnt24.C24MAX"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "OSSVerify.KrLib.B.A_mpi_stmtA.mpi_binop_postA"; "mod_mpi_Rs"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].


Definition A_MPI_MOD_MPI_E : Z := 0x0a04b0.        (* [comment removed for export] *)

Definition mod_mpi_Rs (LBr : list blk) (dXr dAr dBr : mpd) (r : Z) (dX' : mpd) : Prop :=
  mod_mpi_R LBr dXr dAr dBr r dX' /\ md_n dX' <= div_mpi_nz (md_n dXr) (md_n dAr) (md_n dBr).

(* [comment removed for export] *)
Definition mpi_mod_mpi_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z)
    (PHI : mpd -> mpd -> mpd -> Z) (FRC : mpd -> mpd -> mpd -> Z -> Z) : Prop :=
  forall (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (dX dA dB : mpd) (lo slo d : Z),
    HM segs R HIA h LB LF m ->
    HK segs R HIA h mo ->
    (length LF < 511)%nat ->
    mpd_at segs m LB dX ->
    mpd_at segs m LB dA ->
    mpd_at segs m LB dB ->
    mpd_sep dX dA ->
    mpd_sep dX dB ->
    mpd_sep dA dB ->
    md_own dX <> LStatic ->
    md_addr dX <> md_addr dB ->
    opnd_sep dX dA lo (bv_unsigned sp) ->
    opnd_sep dX dB lo (bv_unsigned sp) ->
    client_range (arl_L R) (LB ++ fdata LF) lo (md_addr dA) 16 ->
    (md_own dA = LHeap -> client_range (arl_L R) (LB ++ fdata LF) lo (md_p dA) (4 * md_n dA)) ->
    client_range (arl_L R) (LB ++ fdata LF) lo (md_addr dB) 16 ->
    (md_own dB = LHeap -> client_range (arl_L R) (LB ++ fdata LF) lo (md_p dB) (4 * md_n dB)) ->
    mpd_writableA R LB LF (bv_unsigned sp) (htop segs R HIA h) dX ->
    (md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX) ->
    stk segs m lo (bv_unsigned sp) ->
    arl_stklo R <= lo ->
    lo <= bv_unsigned sp - 864 - arl_need_rt R ->
    lo <= bv_unsigned sp - 496 - arl_need_smalloc R ->
    sshad segs (arl_AL R) m slo (bv_unsigned sp) ->
    arl_stklo R <= slo ->
    slo <= lo ->
    bv_unsigned sp <= htop segs R HIA h ->
    bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 (arl_tp R) ->
    mem_inv segs m ->
    bv_unsigned ra mod 2 = 0 ->
    mpd_aobjA segs (arl_AL R) (hcs segs R HIA h) m dX ->
    mpd_aobjA segs (arl_AL R) (hcs segs R HIA h) m dA ->
    mpd_aobjA segs (arl_AL R) (hcs segs R HIA h) m dB ->
    (md_own dA = LStatic -> (forall i : Z, 0 <= i < 4 * md_n dA -> ro_addr segs (wa (md_p dA + i)) = true) ->
       img_norz (md_p dA) (4 * md_n dA) = true) ->
    (md_own dB = LStatic -> (forall i : Z, 0 <= i < 4 * md_n dB -> ro_addr segs (wa (md_p dB + i)) = true) ->
       img_norz (md_p dB) (4 * md_n dB) = true) ->
    havol segs R HIA h + PHI dX dA dB <= AVOL_MAX ->
    uwc segs m (arl_stklo R) (hstkhi segs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    uw_obj R (md_addr dX) 16 d ->
    uw_obj R (md_addr dB) 16 d ->
    hfr segs R HIA h + FRC dX dA dB d <= FR_MAX ->
    cnt24 LB + C24_DIV_MPI <= C24MAX ->
    a0 = Z_to_bv 64 (md_addr dX) ->
    a1 = Z_to_bv 64 (md_addr dA) ->
    a2 = Z_to_bv 64 (md_addr dB) ->
    aevtS segs
      (mpi_binop_postA segs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX
         (mod_mpi_Rs LB dX dA dB) (PHI dX dA dB) (FRC dX dA dB d) lo m mo)
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)) mo).

