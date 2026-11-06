(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Pm_iface Pm_iface2 Cf_iface RT_fk RT_fk_iface Bi_iface Bi_iface2 Bi_fktw D_iface D_defs Po_rows Po_iface Po_addbg_defs Po_addbg0 Po_addbg16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_addbg () := "C69OSSVerify5KrLib2K53B239Po_addbg0GpixAddBorderGeneral32_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Po_addbg16HpixAddBorderGeneral32_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=Po_addbg_defsKpixAddBorderGeneral32_of_alC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section ADDBG.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis RERRP : returnError_cpsF RT e_returnErrorPtr.
Hypothesis PCW : pixCreate_cpsF RT.
Hypothesis PC1 : pixCreate1_sure_cps RT.
Hypothesis PCOPYRES : pixCopyResolution_po_cps RT.
Hypothesis PCOPYCMAP : pixCopyColormap_cpsF RT.
Hypothesis PROP : pixRasterop_po_cps RT.

Theorem pixAddBorderGeneral32_rows_ok :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (rcs : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 32 -> a2 = Z_to_bv 64 32 -> a3 = Z_to_bv 64 32 -> a4 = Z_to_bv 64 32 -> a5 = Z_to_bv 64 0 ->
  pix1rc (rt_live RT Σ) m pixs vs cvs rcs -> 1 <= rcs <= 2 ->
  uctx m sp s0 ras -> In (PMCOPY_CALLOC1 :: RA_ABG_CMAP :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 9 4 (RC1 + 8) -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixAddBorderGeneral_po m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix1rc (rt_live RT Σ') m' pixs vs cvs rcs
          /\ (pixd = 0 <-> (20000 < p_w vs + 64 \/ 20000 < p_h vs + 64))
          /\ (pixd <> 0 -> pix1c (rt_live RT Σ') m' pixd vd cvd /\ p_w vd = p_w vs + 64 /\ p_h vd = p_h vs + 64
                          /\ (p_cmap vs = 0 -> p_cmap vd = 0) /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs)
                          /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs))) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_copy_live pixd vd cvd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RC1 + 8) <= rt_credit RT Σ').
Proof using AF GP FKC RERRP PCW PC1 PCOPYRES PCOPYCMAP PROP.
ltac2:(KReplay.run1 (kr_t_Po_addbg ()) ["ADDBG"] "p;:p;3g0000l:2Tg001=l:1Tg002Lj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,5RERRPR4p,3PCWR5p,3PC1R6p,8PCOPYRESR7p,9PCOPYCMAPR8p,4PROPR9M:2P0P1P2P3P4P5P6P7P8P9M:130o"). Qed.
End ADDBG.
