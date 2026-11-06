(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjStage1 SjOd SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim SjModel AtpModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsA Od_cpsA Od_hkit0A Od_hkit3A Od_setcapA Od_beginA Od_topA Od_setup_defsA Od_setupw2A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition od_parserC (IMPL L SB : Z) (jp : list byte) : list cell :=
  [C1 (Z_to_bv 8 0); CB 7 jp; C8 (wz IMPL); C8 (wz L); C8 (wz 0xffffffff); C8 (wz 1024); C8 (wz L); C8 (wz SB)].

Definition od_implC (IDX OC IA BUF L nidx : Z) (p12 p28 p50 docj : list byte) (nxt : word) : list cell :=
  [C8 (wz OD_DPI_VPTR); C4 (wz nidx); CB 4 p12; C8 (wz IDX); C4 nxt;
   CB 44 (mid16 p28 (wz L) (wz 1024) (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (wz OC) (wz IA)); C8 (wz BUF); C8 (wz L); CB 8 docj].

Section SetupDefs2.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Record od_cutC (Σ0 ΣC : rts RT) (m0 mC : mem) (usp S1 F lo : Z) (dz : list Z) (A cap size COPY BUF SB IMPL IDX OC IA code : Z) (out : list Z)
    (els : list (Z * Z)) (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) : Prop := mkOdCutC {
  cc_0 : od_cut0 RT LIB Σ0 ΣC m0 mC usp S1 F lo A cap size els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11;
  cc_dz : bytes_ok dz /\ zlength dz < 2^26;
  cc_live : rt_live RT ΣC = (IA, 1024) :: (OC, 8192) :: (IDX, sc_idx (zlength (od_doc dz))) :: (IMPL, 96) :: (SB, OD_SBUF (zlength (od_doc dz)))
                            :: (if od_copied dz then [(COPY, zlength (od_s0 dz) + 64)] else []) ++ vblockA A cap size ++ rt_live RT Σ0;
  cc_copy : if od_copied dz
            then 0 < COPY /\ COPY mod 16 = 0 /\ COPY <= BUF <= COPY + 3 /\ BUF - COPY + zlength (od_doc dz) = zlength (od_s0 dz)
                 /\ bytes_at asegs mC BUF (padded_bytes (od_doc dz))
            else COPY = 0 /\ BUF = 0;
  cc_chunks : (0 < SB /\ SB mod 16 = 0) /\ (0 < IMPL /\ IMPL mod 16 = 0) /\ (0 < IDX /\ IDX mod 16 = 0) /\ (0 < OC /\ OC mod 16 = 0) /\ (0 < IA /\ IA mod 16 = 0);
  cc_credit : rt_credit RT Σ0 - OD_VEC_COST - OD_PAD_COST - mcost (OD_SBUF (zlength (od_doc dz)))
              - mcost 96 - mcost (sc_idx (zlength (od_doc dz))) - mcost 8192 - mcost 1024 <= rt_credit RT ΣC;
  cc_low : exists j0 j192 j224 j248, rw_cells asegs mC S1 (od_lowB F (od_action dz) j0 j192 j224 j248);
  cc_par : exists jp, rw_cells asegs mC (F + 96) (od_parserC IMPL (zlength (od_doc dz)) SB jp);
  cc_sh : rw_cells asegs mC (F / 8 + 2147450880) (od_shadow 0 0);
  cc_sb : wr_at asegs mC SB (OD_SBUF (zlength (od_doc dz)));
  cc_code : (od_copied dz = true /\ (code, out) = stage1 (od_doc dz)) \/ (od_copied dz = false /\ code = 13 /\ out = []);
  cc_impl : exists p12 p28 p50 docj nxt, rw_cells asegs mC IMPL (od_implC IDX OC IA BUF (zlength (od_doc dz)) (Z.of_nat (length out)) p12 p28 p50 docj nxt);
  cc_idx : exists ws, u32arr asegs mC IDX ws /\ 4 * Z.of_nat (length ws) = sc_idx (zlength (od_doc dz))
                      /\ firstn (length out + 3) ws = map wz (out ++ [zlength (od_doc dz); zlength (od_doc dz); 0])
}.

Definition od_cutC_k (K : config -> Prop) (Σ0 : rts RT) (m0 : mem) (usp lo : Z) (dz : list Z)
    (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) : Prop :=
  forall (ΣC : rts RT) (S1 F A cap size COPY BUF SB IMPL IDX OC IA code : Z) (out : list Z) (els : list (Z * Z))
         (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 : word) xF xfc (mC : mem),
    frm0 xfc ->
    od_cutC Σ0 ΣC m0 mC usp S1 F lo dz A cap size COPY BUF SB IMPL IDX OC IA code out els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
    aevt ΣC K (lh_regs 0x96e40 (wz 0x96e40) S1 gp (wz 0x6488f0) xt0 xt1 xt2 usp (wz code) xa1 xa2 xa3 xa4 xa5 xa6 xa7 F
                 (wz (F + 96)) (wz COPY) (wz (zlength (od_doc dz))) (wz BUF) xs10 xt3 xt4 xt5 xt6 xF xfc mC).

Definition od_phaseC1_stmt : Prop :=
  forall (K : config -> Prop) (Σ0 : rts RT) (m0 : mem) (usp lo : Z) (dz : list Z)
         (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word),
  fdfs_only PMc -> mat_stable PMc ->
  od_cutC_k K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  od_cutB_k RT LIB PMc K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11.

Definition od_phaseC2_stmt : Prop :=
  forall (K : config -> Prop) (Σ0 : rts RT) (m0 : mem) (usp lo : Z) (dz : list Z)
         (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word),
  fdfs_only PMc -> mat_stable PMc ->
  od_iter_k RT LIB PMc K Σ0 m0 usp lo gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  od_fin_k RT LIB PMc K Σ0 usp lo cra gp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 (rt_credit RT Σ0 - FUZZ_COST) ->
  od_cutC_k K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11.

Theorem od_phaseC_of : od_phaseC1_stmt -> od_phaseC2_stmt -> od_phaseC_stmt RT LIB PMc.
Proof using.
  intros C1 C2 K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 FDO MST KI KF.
  apply (C1 K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 FDO MST).
  exact (C2 K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 FDO MST KI KF).
Qed.

End SetupDefs2.
