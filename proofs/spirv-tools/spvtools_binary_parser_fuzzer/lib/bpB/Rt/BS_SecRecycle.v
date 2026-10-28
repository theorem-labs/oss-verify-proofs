(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BAllocSim BMmapSim BReach BazyRestrict BazyLedger BazySR BazyNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BsDepotInv BllocWalkKit B_memset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BW_Leaves BW_PoisonShadow BW_AllocBase BW_LargeAlloc1 BW_SysconfPg BW_PoisonRemap1 BecLazy BecLazy2 BW_GetBlockBegin BW_SecRecycle1 BW_LargeDealloc1 BW_LargeDealloc2 BW_LargeDealloc3 BS_SecRecycle1 BS_SecRecycle2 BllocTacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BS_SecRecycle () := "C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep8aapp_envK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega6VarMap1t01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel@kPtrArrayReserveK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I6ARocqVerifyHarness?AgentSubmission3bpB2HF6BReach6sreach00C6ARocqVerifyHarness?AgentSubmission3bpB2HF6BazySR;lzok_rangesC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BazyNodesFlazy_ranges_okb_nowrapC6ARocqVerifyHarness?AgentSubmission3bpB2HF:BazyLedger>entries_nowrapC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BS_SecRecycle1?recycle_sec_midC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BS_SecRecycle2@recycle_sec_mid2C6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BS_SecRecycle2Arecycle_sec_unmapC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BS_SecRecycle2Brecycle_sec_poisonC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BS_SecRecycle1@recycle_sec_headI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsC6ARocqVerifyHarness?AgentSubmission3bpB2HF4Bcfg=hunspell_scfg".
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
  Hypothesis TPR : hidden (6762376 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (6762288 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).

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
  Hypothesis SB32 : rw_cells asegs m 1628664 [C8 (wz sb)].
  Hypothesis INST64 : rw_cells asegs m 1628696 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells asegs m 1628744 [C8 (wz nres); C8 (wz nch); C8 (wz 0)].
  Hypothesis SST : stk asegs m 1628768 1629312.
  Hypothesis MTX : rw_cells asegs m 1629312 [C8 (wz 0)].
  Hypothesis GST : stk asegs m 1629320 1629360.
  Hypothesis PA : u64arr asegs m pa (wlist chunks).
  Hypothesis HDR : rw_cells asegs m a [C8 (wz a); C8 (wz msz); C8 (wz sz); C8 (wz idx)].
  Hypothesis LSTC : idx < nch - 1 -> rw_cells asegs m (lst + 24) [C8 (wz lidx)].
  Hypothesis CHDR : rw_cells asegs m (a + 6128) [C1 ob0; C1 ob1; C2 (wz 0); C4 (wz n); C8 (wz actx)].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis SHD : u8arr asegs m (sh a) sbs. Hypothesis SHDL : Z.of_nat (length sbs) = msz / 8.
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (a + 6128)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x947ac) fc None m (seg_rom asegs).

  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).

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

  Let ARE : 7241728 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(lia)). Qed.
  Let PAE : 7241728 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.
  Let LRE : 7241728 <= lst /\ lst + 4096 <= aceil. Proof. exact (aapp_env _ _ (proj1 LR) ltac:(clear; lia)). Qed.
  Let POST := recycle_sec_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a msz nres nch idx pa lst TSD CTX TH chunks g b244.

  Theorem recycle_sec_sreach :
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
Proof.
ltac2:(KReplay.run1 (kr_t_BS_SecRecycle ()) ["SecRecycle"] "h01Kh12M3h22M4h33NWLh43mo'h53mo3h63mo4h74msF'h84msF3h94msF4p&0p;2p;4p;6p;3p;1p;Xp;Wp;rp;hg00QGj20Tg00R<j48Tg00S7j62Tg00T5j31Tg00UAj17Tg00VFlX6Tg00WPlW3Tg00X[lr4Tg00Yglh5Tg00[4p<1R00Tg00\?R0g00]FR1p,4POSTf1R2f0R3O2g00^<R4g00_3p,1QR5f2R6/02C8[]4]7p,1LR7P4P7p,1SR8p,2ZrR9p,3msFR:p,2moR;'0p,2OKR<E2514%77p,5HCEILR4P7P8P9P:P;P5p,2raR:p,2spR=p,2gpR>p,2tpR?p,2t0p,2t1p,2t2p,2s0R@p,2s1RAp,2a0p,2a2p,2a3p,2a4p,2a5p,2a6p,2a7p,2s2RBp,2s3RCp,2s4RDp,2s5REp,2s6RFp,2s7RGp,2s8RHp,2s9RIp,3s10RJp,3s11RKp,2t3p,2t4p,2t5p,2t6p,1FRLp,2fcRMp,1mRNp,2loROp,1aRPp,3mszRQp,2szp,3idxRRp,2paRSp,4nresRTp,3nchRUp,3lstRVp,4lidxp,3TSDRWp,3CTXRXp,2THRYp,2sbp,1np,4actxp,6chunksRZp,3ob0p,3ob1p,3sbsR[p,1gR\p,4b244R]p,2MIp,2STp,2LOR^p,2HIR_p,2ARR`p,3SBXp,3SBRp,3TPRRap,3RNGRbp,3PLCRcp,3PARRdp,3NCHRep,3IDXp,4LNTHp,2LRRfp,4PLCLRgp,4LSTARhp,4DISJp,3SENp,3RENp,4SB32p,6INST64p,4NRESp,3SSTp,3MTXp,3GSTp,2PAp,3HDRp,4LSTCp,4CHDRp,3TSTp,3SHDp,4SHDLRiP<p,4VISEP7P8P9P;P:P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPTPUPRPSPVPWPXPYPZP[P\P]P2P3MX6P4P7P8P9P;P5P:P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP\P]P^P_P`PaPbPcPdPePfPgPhP[P6P2P3PiP7P8P9P;P:P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPTPUPRPSPVPWPXPYPZP\P]P2P3MW3P4P7P8P9P;P5P:P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP\P]P^P_p,3SPAP`PaPbPcPdPePfPgPhp,2NWp,3NWAp,3NOVp,4ZRSHp,4HSRFp,4HSMCp,4HSNAp,3WINp,3HASp,3NOLp,5NOACCP6P2P3f7Mr4W2X61X90Mh5W1X51X80p#1R00b3W0o"). Qed.
End SecRecycle.
