(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the ledger invariant's entries_nonzero conjunct; recorded proofs re-encoded or written as text where the change reaches them). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HImage HZBridge HSysStep HSFModel CellsX HArr TacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsanAllocModel HAllocSim HMmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HStrFun.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv AllocWalkKit F_memset.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AW_Leaves AW_PoisonShadow AW_AllocBase AW_LargeAlloc1 AW_SysconfPg AW_PoisonRemap1 SecLazy SecLazy2 AW_GetBlockBegin AW_SecRecycle1 AW_LargeDealloc1 AW_LargeDealloc2 AW_LargeDealloc3 AS_SecRecycle1 AS_SecRecycle2 AllocTacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_AS_SecRecycle () := "C69OSSVerify5KrLib3bpA2Rt8AsShadow4aappC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib3bpA2Rt8AsShadow5aceilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib3bpA2Rt8AllocRep8aapp_envC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega6VarMap1t01C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel@kPtrArrayReserveC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I69OSSVerify5KrLib3bpA2HF6SReach6sreach00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF6LazySR;lzok_rangesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF9LazyNodesFlazy_ranges_okb_nowrapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF:LazyLedger>entries_nowrapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AS_SecRecycle1?recycle_sec_midC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AS_SecRecycle2@recycle_sec_mid2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AS_SecRecycle2Arecycle_sec_unmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AS_SecRecycle2Brecycle_sec_poisonC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AS_SecRecycle1@recycle_sec_headC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib3bpA2Rt5ASegs5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF4Scfg=hunspell_scfgC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section SecRecycle.
  Context {HCEIL : HeapCeil}.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo a msz sz idx pa nres nch lst lidx TSD CTX TH sb n actx : Z) (chunks : list Z) (ob0 ob1 : byte) (sbs : list byte) (g : word) (b244 : byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 800 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ 0x11000 <= msz < 2^40.
  Hypothesis SBX : hidden (a + msz <= sb \/ sb + kSpaceSize <= a).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil).
  Hypothesis TPR : hidden (6755912 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (6755824 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).

  Hypothesis PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (pa + kPtrArrayReserve <= TH \/ TH + 4096 <= pa) /\ (pa + kPtrArrayReserve <= CTX \/ CTX + 160 <= pa)
                        /\ (a + msz <= TH \/ TH + 4096 <= a) /\ (a + msz <= CTX \/ CTX + 160 <= a) /\ (a + msz <= pa \/ pa + kPtrArrayReserve <= a)).
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil /\ pa mod 4096 = 0.
  Hypothesis NCH : zlen chunks = nch /\ 0 <= idx < nch /\ nch <= nres <= 2^20.
  Hypothesis IDX : nth_error chunks (Z.to_nat idx) = Some a.
  Hypothesis LNTH : nth_error chunks (Z.to_nat (nch - 1)) = Some lst.
  Hypothesis LR : aapp lst 4096 /\ lst + 4096 <= aceil.
  Hypothesis PLCL : idx < nch - 1 -> hidden ((a + msz <= lst \/ lst + 4096 <= a) /\ (lst + 4096 <= pa \/ pa + kPtrArrayReserve <= lst) /\ (lst + 4096 <= TH \/ TH + 4096 <= lst) /\ (lst + 4096 <= CTX \/ CTX + 160 <= lst)).
  Hypothesis LSTA : idx = nch - 1 -> lst = a.

  Hypothesis DISJ : Forall (fun c => 0 <= c < 2^47 /\ (c <= a + 6128 -> c <= a)) chunks.
  Hypothesis NR : 0 <= n < 2^32.

  Hypothesis SEN : SENV tp TSD CTX TH m.
  Hypothesis REN : RENV g b244 m.
  Hypothesis SB32 : rw_cells asegs m 1622200 [C8 (wz sb)].
  Hypothesis INST64 : rw_cells asegs m 1622232 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells asegs m 1622280 [C8 (wz nres); C8 (wz nch); C8 (wz 0)].
  Hypothesis SST : stk asegs m 1622304 1622848.
  Hypothesis MTX : rw_cells asegs m 1622848 [C8 (wz 0)].
  Hypothesis GST : stk asegs m 1622856 1622896.
  Hypothesis PA : u64arr asegs m pa (wlist chunks).
  Hypothesis HDR : rw_cells asegs m a [C8 (wz a); C8 (wz msz); C8 (wz sz); C8 (wz idx)].
  Hypothesis LSTC : idx < nch - 1 -> rw_cells asegs m (lst + 24) [C8 (wz lidx)].
  Hypothesis CHDR : rw_cells asegs m (a + 6128) [C1 ob0; C1 ob1; C2 (wz 0); C4 (wz n); C8 (wz actx)].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis SHD : u8arr asegs m (sh a) sbs. Hypothesis SHDL : Z.of_nat (length sbs) = msz / 8.
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (a + 6128)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x948a4) fc None m (seg_rom asegs).

  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  Hypothesis NZM : entries_nonzero (vm_maps (m_vmmaps mo)).

  Hypothesis ZRSH : forall x : word, (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x Zr = true.
  Hypothesis HSRF : forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      region_free (vm_reserved (m_vmmaps mo)) a n = true.
  Hypothesis HSMC : forall a n : word, 0 < bv_unsigned n -> (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      map_contains (vm_maps (m_vmmaps mo)) a n = true.

  Hypothesis HSNA : forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      region_free (vm_noaccess (m_vmmaps mo)) a n = true.

  Hypothesis WIN : forall x : word, sh a <= bv_unsigned x < sh a + msz / 8 -> in_rangesb x S = true.
  Hypothesis HAS : map_has (vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true.
  Hypothesis NOL : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x L = false.
  Hypothesis NOACC : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (vm_noaccess (m_vmmaps mo)) = false.

  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.

  Let ARE : 7233536 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(lia)). Qed.
  Let PAE : 7233536 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.
  Let LRE : 7233536 <= lst /\ lst + 4096 <= aceil. Proof. exact (aapp_env _ _ (proj1 LR) ltac:(clear; lia)). Qed.
  Let POST := recycle_sec_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a msz nres nch idx pa lst TSD CTX TH chunks g b244.

  Theorem recycle_sec_sreach :
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
Proof.
ltac2:(KReplay.run1 (kr_t_AS_SecRecycle ()) ["SecRecycle"] "p%0p'0p%1p'1p%2p'2p%3p'3p%4p'4p%5p'5p%6p'6p%7p'7p%8p'8p%9p'9p%:p':p%;p';p%<p'<p%=p'=p%>p'>p%?p'?p%@p'@p%Ap'Ap%Bp'Bp%Cp'Cp%Dp'Dp%Ep'Ep%Fp'Fp%Gp'Gp%Hp'Hp%Ip'Ip%Jp'Jp%Kp'Kp%Lp'Lp%Mp'Mp%Np'Np%Op'Op%Pp'Pp%Qp'Qp%Rp'Rp%Sp'Sp%Tp'Tp%Up'Up%Vp'Vp%Wp'Wp%Xp'Xp%Yp'Yp%Zp'Zp%[p'[p%\p'\p%]p']p%^p'^p%_p'_p%`p'`p%ap'ap%bp'bp%cp'cp%dp'dp%ep'ep%fp'fp%gp'gp%hp'hp%ip'ip%jp'jp%kp'kp%lp'lp%mp'mp%np'np%op'op%pp'pp%qp'qp%rp'rp%sp'sp%tp'tp%up'up%vp'vp%wp'wp%xp'xp%yp'yp%zp'zp%{p'{p%|p'|p%}p'}p%~p'~g00\?g00]Fp,4POSTf1f0O2g00R<g00^<g00_3p,1Qg00QGf2f1O2O4pB1000i003mo'pB1100i004msF'pB1100g00T5g00^<p,1Lg00S7g00^<p,1Lp,1Sp,2Zrg00QGp,3msFp,2moO2p,2OKO6O3g00UAp,1LO1g00[4p,5HCEILp,1Lp,1Sp,2Zrp,3msFp,2mop,1Qp,2rap,2spp,2gpp,2tpp,2t0p,2t1p,2t2p,2s0p,2s1p,2a0p,2a2p,2a3p,2a4p,2a5p,2a6p,2a7p,2s2p,2s3p,2s4p,2s5p,2s6p,2s7p,2s8p,2s9p,3s10p,3s11p,2t3p,2t4p,2t5p,2t6p,1Fp,2fcp,1mp,2lop,1ap,3mszp,2szp,3idxp,2pap,4nresp,3nchp,3lstp,4lidxp,3TSDp,3CTXp,2THp,2sbp,1np,4actxp,6chunksp,3ob0p,3ob1p,3sbsp,1gp,4b244p,2MIp,2STp,2LOp,2HIp,2ARp,3SBXp,3SBRp,3TPRp,3RNGp,3PLCp,3PARp,3NCHp,3IDXp,4LNTHp,2LRp,4PLCLp,4LSTAp,4DISJp,3SENp,3RENp,4SB32p,6INST64p,4NRESp,3SSTp,3MTXp,3GSTp,2PAp,3HDRp,4LSTCp,4CHDRp,3TSTp,3SHDp,4SHDLp,2OKp,4VISEg00\?g00]Fg00VFp,1Lp,1Sp,2Zrp,2mop,2rap,2spp,2gpp,2tpp,2s0p,2s1p,2s2p,2s3p,2s4p,2s5p,2s6p,2s7p,2s8p,2s9p,3s10p,3s11p,1Fp,2fcp,1mp,2lop,1ap,3mszp,4nresp,3nchp,3idxp,2pap,3lstp,3TSDp,3CTXp,2THp,6chunksp,3sbsp,1gp,4b244f1f0OXg00Ygp,5HCEILp,1Lp,1Sp,2Zrp,2mop,1Qp,2rap,2spp,2gpp,2tpp,2s0p,2s1p,2s2p,2s3p,2s4p,2s5p,2s6p,2s7p,2s8p,2s9p,3s10p,3s11p,1Fp,2fcp,1mp,2lop,1ap,3mszp,3idxp,2pap,4nresp,3nchp,3lstp,3TSDp,3CTXp,2THp,6chunksp,1gp,4b244p,2LOp,2HIp,2ARp,3TPRp,3RNGp,3PLCp,3PARp,3NCHp,2LRp,4PLCLp,4LSTAp,3sbsf2f1f0p,4SHDLg00\?g00]Fg00WPp,1Lp,1Sp,2Zrp,2mop,2rap,2spp,2gpp,2tpp,2s0p,2s1p,2s2p,2s3p,2s4p,2s5p,2s6p,2s7p,2s8p,2s9p,3s10p,3s11p,1Fp,2fcp,1mp,2lop,1ap,3mszp,4nresp,3nchp,3idxp,2pap,3lstp,3TSDp,3CTXp,2THp,6chunksp,1gp,4b244f1f0OWg00X[p,5HCEILp,1Lp,1Sp,2Zrp,2mop,1Qp,2rap,2spp,2gpp,2tpp,2s0p,2s1p,2s2p,2s3p,2s4p,2s5p,2s6p,2s7p,2s8p,2s9p,3s10p,3s11p,1Fp,2fcp,1mp,2lop,1ap,3mszp,3idxp,2pap,4nresp,3nchp,3lstp,3TSDp,3CTXp,2THp,6chunksp,1gp,4b244p,2LOp,2HIp,3SPAp,2ARp,3TPRp,3RNGp,3PLCp,3PARp,3NCHp,2LRp,4PLCLp,4LSTAp,2NWp,3NWAp,3NOVp,3NZMp,4ZRSHp,4HSRFp,4HSMCp,4HSNAp,3WINp,3HASp,3NOLp,5NOACCf2f1f0f7Osi002M4pB0100i003mo4pB0100i004msF4pB0100Ohi002M3pB0100i003mo3pB0100i004msF3pB0100p$1Ri003NWLpB2100i001KpB0100o"). Qed.
End SecRecycle.
