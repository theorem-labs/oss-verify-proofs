(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 RtB_Iface RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_TablStmt LbB_SnStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DPdK LbB_SnK LbB_SnFind LbB_SnXZ.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_SnV LbB_SnTA.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 33) (ELit k).

Definition RT5 : list (reg * expr) := (10%bv, EVar 58) :: RTK4.

Lemma sn_ret_ok : forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0xf9b20) fc None m (seg_rom asegs)).
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  step. apply evt_done. exact HQ.
Qed.

Lemma scF_lit : forall segs base E a n, 0 <= n < 2 ^ 64 -> flat E a n -> sc_denot segs base E (SCFlat a (ELit n)).
Proof. intros segs base E a n Hn HF. cbn [sc_denot]. unfold elenZ. cbn [edenot]. rewrite unsigned_lit by exact Hn. exact HF. Qed.

Lemma sh_word : forall x, 0 <= x < 2 ^ 47 ->
  alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 SHBASE) = Z_to_bv 64 (sh x).
Proof.
  intros x Hx.
  assert (E1 : bv_unsigned (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) = x / 8).
  { cbn [alu64 alu]. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite (Z.mod_small x) by lia.
    replace (bv_unsigned (bv_and (Z_to_bv 64 3) (Z_to_bv 64 63))) with 3 by (vm_compute; reflexivity).
    rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite <- (Z_to_bv_bv_unsigned (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3))), E1.
  assert (D8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite w_add by (unfold SHBASE; lia). unfold sh, SHBASE, ASHADOW_BASE. f_equal. lia.
Qed.

Section SnF.
  Local Notation PD_SHB := LbB_DPdK.PD_SHB (only parsing).

  Local Notation PO_SIZE := LbB_SnK.PO_SIZE (only parsing).
  Local Notation kst_sn := LbB_SnK.kst_sn (only parsing).
  Local Notation dj2 := LbB_SnK.dj2 (only parsing).
  Local Notation rg := LbB_SnK.rg (only parsing).
  Local Notation shT := LbB_SnK.shT (only parsing).
  Local Notation kT := LbB_SnK.kT (only parsing).
  Local Notation kwin := LbB_SnK.kwin (only parsing).
  Local Notation shN := LbB_SnK.shN (only parsing).
  Local Notation shP := LbB_SnK.shP (only parsing).
  Local Notation POA := LbB_SnK.POA (only parsing).
  Local Notation kP := LbB_SnK.kP (only parsing).
  Local Notation kN := LbB_SnK.kN (only parsing).
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m1 : mem) (this po tid pcons icount lo ff fp : Z) (LF : list fframe).

  Variables (bl bc nd nk bw enc : Z).
  Variables (LBl : list (Z * Z)) (ents : list (Z * (Z * (Z * Z * Z)))).

  Hypothesis DSA : addressable m1 po PO_SIZE.
  Hypothesis DSW : wr_at asegs m1 po PO_SIZE.
  Hypothesis DSO : app_obj po PO_SIZE.
  Hypothesis DS8 : po mod 8 = 0.
  Hypothesis DSV : shvis m1 po (po + PO_SIZE).
  Hypothesis DSH : po + PO_SIZE + 64 <= AAPP_HI.
  Hypothesis DSM : po + PO_SIZE <= aceil.
  Hypothesis DSin : obj_inframe LF po PO_SIZE.

  Hypothesis PCA : addressable m1 pcons 48.
  Hypothesis PCO : app_obj pcons 48.
  Hypothesis PC8 : pcons mod 8 = 0.
  Hypothesis PCC : rw_cells asegs m1 (pcons + 32) [C8 (Z_to_bv 64 0)].
  Hypothesis DISJ : forall a, po <= a < po + PO_SIZE -> ~ (pcons <= a < pcons + 48).
  Hypothesis ICN : 0 <= icount < 2 ^ 63.

  Hypothesis STK : stk asegs m1 lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ADS_STACK.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPHI : bv_unsigned sp <= AAPP_HI.
  Hypothesis SPOBJ : forall O n, O = po /\ n = PO_SIZE \/ O = pcons /\ n = 48 ->
                     O + n <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= O.

  Hypothesis FFR : aframe_range H 4 ff fp.
  Hypothesis FSB_OK : afsb_ok H.
  Hypothesis FFDS : ff + 1024 <= po \/ po + PO_SIZE <= ff.
  Hypothesis FFPC : ff + 1024 <= pcons \/ pcons + 48 <= ff.
  Hypothesis FPPC : fp + 1 <= pcons \/ pcons + 48 <= fp.
  Hypothesis FPDS : fp + 1 <= po \/ po + PO_SIZE <= fp.
  Hypothesis HULL : hull_hi (po + PO_SIZE) <= ff \/ ff + 1024 <= hull_lo po.
  Hypothesis FRW : wr_at asegs m1 ff 1024.
  Hypothesis FSV : shvis m1 ff (ff + 1024).
  Hypothesis FSW : wr_at asegs m1 (sh ff) 128.
  Hypothesis FLW : wr_at asegs m1 fp 1.

  Hypothesis MI1 : mem_inv asegs m1.
  Hypothesis AC1 : ACONST m1.
  Hypothesis LV1 : LINV_P5 m1.

  Hypothesis THA : addressable m1 this 288.
  Hypothesis THO : app_obj this 288.
  Hypothesis TH8 : this mod 8 = 0.
  Hypothesis THS : dj2 (this + 288) (bv_unsigned sp - ADS_STACK) (bv_unsigned sp) this.
  Hypothesis THF : dj2 (ff + 1024) this (this + 288) ff.
  Hypothesis THP : dj2 (fp + 1) this (this + 288) fp.

  Hypothesis THD : dj2 (this + 272) po (po + PO_SIZE) this.
  Hypothesis THC1 : rw_cells asegs m1 (this + 8) [C8 (Z_to_bv 64 pcons)].
  Hypothesis THC2 : rw_cells asegs m1 (this + 80) [C8 (Z_to_bv 64 icount)].
  Hypothesis TIDR : rg 0 tid (2 ^ 32).
  Hypothesis BLR : rg 0 bl (2 ^ 64).
  Hypothesis BCR : rg 0 bc (2 ^ 64).
  Hypothesis NDR : rg 0 nd (2 ^ 64) /\ rg 0 nk (2 ^ 32) /\ rg 0 bw (2 ^ 32) /\ rg 0 enc (2 ^ 32).

  Hypothesis UM1 : umapx MI_A 32 (nval32 ASEGS) LBl m1 (this + 136) bl bc ents.
  Hypothesis UG1 : gz m1 (this + 136) 40.
  Hypothesis UG2 : bc <> 0 -> gz m1 bl (8 * bc).
  Hypothesis UG3 : forall p k v, In (p, (k, v)) ents -> gz m1 p 32.
  Hypothesis UFO : forall a, umap_foot 32 (this + 136) bl bc ents a ->
    outside [(bv_unsigned sp - 16384, bv_unsigned sp); (po, po + PO_SIZE); (ff, ff + 1024); (sh ff, sh ff + 128); (fp, fp + 1)] a
    /\ outside [(bv_unsigned sp - 16384, bv_unsigned sp); (po, po + PO_SIZE); (ff, ff + 1024); (sh ff, sh ff + 128); (fp, fp + 1)] (a / 8 + SHBASE)
    /\ 0 <= a < 2 ^ 47.

  Local Notation Wp := (@LbB_SnK.Wp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc) (only parsing).
  Local Notation PW := (@LbB_SnK.PW sp po ff fp) (only parsing).
  Local Notation PWF := (@LbB_SnK.PWF sp po ff fp) (only parsing).
  Local Notation Pw := (@LbB_SnK.Pw sp m1 po ff fp) (only parsing).
  Local Notation Pw_cz := (@LbB_SnK.Pw_cz sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation Pw_m1 := (@LbB_SnK.Pw_m1 sp m1 po ff fp) (only parsing).
  Local Notation sn_ranges := (@LbB_SnK.sn_ranges HCEIL H sp m1 this po pcons icount lo ff fp ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation sh_mono8 := (@LbB_SnK.sh_mono8 sp this po pcons icount ICN) (only parsing).
  Local Notation pw_aconst := (@LbB_SnK.pw_aconst HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pw_out_img := (@LbB_SnK.pw_out_img HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pw_sh_apart := (@LbB_SnK.pw_sh_apart HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pw_hull_apart := (@LbB_SnK.pw_hull_apart HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation sn_keep := (@LbB_SnK.sn_keep HCEIL H sp m1 this po pcons icount lo ff fp DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation sn_keepT := (@LbB_SnK.sn_keepT HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK THA THO TH8 THS THF THP THD THC1 THC2) (only parsing).
  Local Notation evWp := (@LbB_SnK.evWp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc ICN) (only parsing).
  Local Notation sn_vals := (@LbB_SnK.sn_vals HCEIL H sp m1 this po pcons icount lo ff fp DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation kst_pd_ok := (@LbB_SnK.kst_pd_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation sn_keepU := (@LbB_SnK.sn_keepU sp m1 this po pcons icount ff fp bl bc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation evT := (@LbB_SnK.evT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc THO) (only parsing).
  Local Notation shT_start := (@LbB_SnK.shT_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc THO) (only parsing).
  Local Notation shT_apart := (@LbB_SnK.shT_apart HCEIL H sp m1 this po pcons icount lo ff fp ICN STK CEIL LO SPHI FFR FSB_OK TH8 THF) (only parsing).
  Local Notation kT_ok := (@LbB_SnK.kT_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK THA THO TH8 THS THF THP THD THC1 THC2) (only parsing).
  Local Notation scT_flat := (@LbB_SnK.scT_flat ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc THO) (only parsing).
  Local Notation tS := (@LbB_SnK.tS sp) (only parsing).
  Local Notation tF := (@LbB_SnK.tF ff) (only parsing).
  Local Notation tH := (@LbB_SnK.tH ff) (only parsing).
  Local Notation tL := (@LbB_SnK.tL fp) (only parsing).
  Local Notation sn_wins := (@LbB_SnK.sn_wins HCEIL H sp m1 this po pcons icount lo ff fp ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tab_vals := (@LbB_SnK.tab_vals HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_wf3 := (@LbB_SnK.tabs_wf3 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_wf4 := (@LbB_SnK.tabs_wf4 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation wk_stk := (@LbB_SnK.wk_stk sp this po pcons icount lo ICN LO) (only parsing).
  Local Notation wk_win := (@LbB_SnK.wk_win sp this po pcons icount ICN) (only parsing).
  Local Notation inPW := (@LbB_SnK.inPW sp po ff fp) (only parsing).
  Local Notation Pw_ext := (@LbB_SnK.Pw_ext sp m1 po ff fp) (only parsing).
  Local Notation in_stk := (@LbB_SnK.in_stk sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_p2 := (@LbB_SnK.in_p2 sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_p8 := (@LbB_SnK.in_p8 sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_fr := (@LbB_SnK.in_fr sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_sh := (@LbB_SnK.in_sh sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_fl := (@LbB_SnK.in_fl sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation shb_eq := (@LbB_SnK.shb_eq sp this po pcons icount ff ICN) (only parsing).
  Local Notation W3 := (@LbB_SnK.W3 sp ff) (only parsing).
  Local Notation winsT3_eq := (@LbB_SnK.winsT3_eq sp ff) (only parsing).
  Local Notation Pw_step3 := (@LbB_SnK.Pw_step3 sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation Pw_step4 := (@LbB_SnK.Pw_step4 sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation HHb := (@LbB_SnK.HHb HCEIL H HHbp) (only parsing).
  Local Notation afs_ok_frame := (@LbB_SnK.afs_ok_frame H sp this po pcons icount ff fp LF ICN) (only parsing).
  Local Notation afs_ok_stack := (@LbB_SnK.afs_ok_stack HCEIL H sp m1 this po pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation afs_ok_shadow := (@LbB_SnK.afs_ok_shadow HCEIL H sp m1 this po pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_ok3 := (@LbB_SnK.tabs_ok3 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation tabs_ok4 := (@LbB_SnK.tabs_ok4 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation tP2 := (@LbB_SnK.tP2 po) (only parsing).
  Local Notation tP8 := (@LbB_SnK.tP8 po) (only parsing).
  Local Notation po_wins := (@LbB_SnK.po_wins sp po pcons SPOBJ) (only parsing).
  Local Notation po_sh_wins := (@LbB_SnK.po_sh_wins HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_wf5p := (@LbB_SnK.tabs_wf5p HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO DSH PCO ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS) (only parsing).
  Local Notation Pw_step5p := (@LbB_SnK.Pw_step5p sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation tabs_ok5p := (@LbB_SnK.tabs_ok5p HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation afs_ok_po := (@LbB_SnK.afs_ok_po H po ff fp LF DSin) (only parsing).
  Local Notation RFS_step5p := (@LbB_SnK.RFS_step5p HCEIL H HHbp sp m1 this po pcons icount lo ff fp LF DSin ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation RFS_step3 := (@LbB_SnK.RFS_step3 HCEIL H HHbp sp m1 this po pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation po_rng := (@LbB_SnK.po_rng po DSO) (only parsing).
  Local Notation evP := (@LbB_SnK.evP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation shP_start := (@LbB_SnK.shP_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation POA_start := (@LbB_SnK.POA_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation po_sh_self := (@LbB_SnK.po_sh_self po DSO DS8) (only parsing).
  Local Notation flatP := (@LbB_SnK.flatP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation flat_shP := (@LbB_SnK.flat_shP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation kP_ok := (@LbB_SnK.kP_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation nd_facts := (@LbB_SnK.nd_facts sp m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation nd_out := (@LbB_SnK.nd_out sp this po tid ff fp bl bc nd nk bw enc ents UFO) (only parsing).
  Local Notation evN := (@LbB_SnK.evN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation ndA_start := (@LbB_SnK.ndA_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation shN_start := (@LbB_SnK.shN_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation flatN := (@LbB_SnK.flatN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation flat_shN := (@LbB_SnK.flat_shN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation kN_ok := (@LbB_SnK.kN_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents DSO ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation SF5 := (@LbB_SnK.SF5 HCEIL H HHbp ra sp gp tp) (only parsing).
  Local Notation tabs_wf1 := (@LbB_SnK.tabs_wf1 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation Pw_step1 := (@LbB_SnK.Pw_step1 sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation tabs_ok1 := (@LbB_SnK.tabs_ok1 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation RFS_L_step1 := (@LbB_SnK.RFS_L_step1 HCEIL H HHbp sp m1 this po pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation nopo := (@LbB_SnK.nopo sp ff fp) (only parsing).
  Local Notation po_cells_keep := (@LbB_SnK.po_cells_keep HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FPDS) (only parsing).
  Local Notation po4 := (@LbB_SnK.po4 po nk bw enc) (only parsing).
  Local Notation po4_keep := (@LbB_SnK.po4_keep HCEIL H sp m1 this po pcons icount lo ff fp nk bw enc DSO ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FPDS) (only parsing).
  Local Notation nopo_w3 := (@LbB_SnK.nopo_w3 sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation nopo_w1 := (@LbB_SnK.nopo_w1 sp ff fp) (only parsing).
  Local Notation nopo_sf := (@LbB_SnK.nopo_sf sp ff fp) (only parsing).
  Local Notation inPW_sf := (@LbB_SnK.inPW_sf sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation sf_stack_keep := (@LbB_SnK.sf_stack_keep HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation sn_Pok := (@LbB_SnK.sn_Pok H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 po ff fp LF nk bw enc) (only parsing).
  Local Notation sn_fin_ok := (@LbB_SnK.sn_fin_ok H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 po ff fp LF nk bw enc) (only parsing).

  Notation spz := (bv_unsigned sp) (only parsing).

  Ltac evwp := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wp;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Ltac tnormp H :=
    lazymatch type of H with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    end.

  Ltac dkrunP3 HRT HSF HFT HHT HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) (kst_sn ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] ((kst_sn ++ kf) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3]
                    (tabs_wf3 SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step3 SF FT HT ks1 ks2 ks3)
                    Q R F pc fc m ro RT [] (kst_sn ++ kf) fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok3; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end
    end.

  Ltac dkrunP4 HRT HSF HFT HHT HLT HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HLT with ftbl _ _ _ ?LT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []; tL LT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) (kst_sn ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] ((kst_sn ++ kf) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          let ks4 := eval vm_compute in (nkeys (EVar 53) (s_log SSr) LT) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3; tL LT ks4]
                    (tabs_wf4 SF FT HT LT ks1 ks2 ks3 ks4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step4 SF FT HT LT ks1 ks2 ks3 ks4)
                    Q R F pc fc m ro RT [] (kst_sn ++ kf) fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok4; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | exact HLT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end
    end.

  Ltac tcomp HTS :=
    lazymatch type of HTS with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS; clear E
    end.
  Ltac tsplit HTS H1 H2 H3 :=
    tcomp HTS;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; clear HTS; cbn [fst snd] in H1, H2, H3.
  Ltac tsplit4 HTS H1 H2 H3 H4 :=
    tcomp HTS;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; apply Forall_cons_iff in HTS as [H4 HTS]; clear HTS; cbn [fst snd] in H1, H2, H3, H4.

  Ltac rgetp HRT r H :=
    lazymatch type of HRT with
    | rtbl ?W ?R ?RT =>
        let e := eval vm_compute in (match List.find (fun re => bv_eqb (fst re) r) RT with Some re => snd re | None => ELit 0 end) in
        assert (H : PropExec.getr R r = edenot (wenv W) e)
          by (apply (rtbl_In W R RT r e HRT); apply LbB_DCtorK.inb_In'; vm_compute; reflexivity);
        unfold wenv in H; cbn [edenot] in H; unfold HLib.Eseed, reg_ev, Wp in H;
        lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
              Init.Nat.add Nat.sub nth app] in H;
        rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z in H by (pose proof sn_vals; lia)
    end.
  Ltac dkrunP1 HRT HSF HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] (kst_sn ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          eapply (dk_runN Wp [tS SF ks1] (tabs_wf1 SF ks1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step1 SF ks1) Q R F pc fc m ro RT [] kst_sn fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok1; [exact HP | exact HMI | exact HSF | vm_compute; reflexivity]
          | exact HP | exact HMI | apply kst_pd_ok; [exact HP | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end
    end.
  Ltac dkrunP5p HRT HSF HFT HHT HP2 HP8 HP HMI fuel stops kx scr0 :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HP2 with ftbl _ _ _ ?P2 =>
      lazymatch type of HP8 with ftbl _ _ _ ?P8 =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []; tP2 P2 []; tP8 P8 []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops scr0 (SS pc (HLib.srs sr_id RT) [] ((kst_sn ++ kx) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          let ks4 := eval vm_compute in (kwin 2 4 (nkeys (EVar 35) (s_log SSr) P2)) in
          let ks5 := eval vm_compute in (kwin 8 20 (nkeys (EVar 35) (s_log SSr) P8)) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3; tP2 P2 ks4; tP8 P8 ks5]
                    (tabs_wf5p SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step5p SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5)
                    Q R F pc fc m ro RT [] (kst_sn ++ kx) fuel stops scr0 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok5p; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | exact HP2 | exact HP8 | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end end
    end.
  Ltac tsplit5 HTS H1 H2 H3 H4 H5 :=
    tcomp HTS;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; apply Forall_cons_iff in HTS as [H4 HTS]; apply Forall_cons_iff in HTS as [H5 HTS];
    clear HTS; cbn [fst snd] in H1, H2, H3, H4, H5.

  Ltac fget HT k w e C :=
    lazymatch type of HT with ftbl ?W ?B ?m ?T =>
      assert (C : rw_cells asegs m (B + k) [CB w (word_to_le_bytes w (edenot (wenv W) e))])
        by (apply (ftbl_In W B m T k w e HT); apply fent_in_In; vm_compute; reflexivity)
    end.

  Ltac nx := apply Forall_cons; [cbn [sc_denot]; unfold elenZ; cbn [edenot]; rewrite ?unsigned_lit by (clear; lia)|].

  Lemma sn_found : In (nd, (tid, (nk, bw, enc))) ents -> nk <> 0 -> nk < 4 -> enc < 16 ->
    forall R m, rfull R -> rtbl Wp R RT5 -> ftbl Wp spz m SF4 -> ftbl Wp ff m FT4 -> ftbl Wp (ff / 8) m HT4 ->
    Pw m -> mem_inv asegs m -> as_RFS H ((4, ff, fp) :: LF) m ->
    evt asegs sn_Pok (MS R F (Z_to_bv 64 LbB_SnFind.SNF_FOUND) fc None m (seg_rom asegs)).
  Proof.
    intros IN NZ NK4 EN16 R m RF HRT HSF HFT HHT HP HMI HRF.
    pose proof NDR as (NDR1 & NDR2 & NDR3 & NDR4). unfold rg in NDR1, NDR2, NDR3, NDR4.
    assert (HP2 : ftbl Wp po m []) by constructor.
    assert (HP8 : ftbl Wp po m []) by constructor.
    dkrunP5p HRT HSF HFT HHT HP2 HP8 HP HMI 600%nat [ASET_SHADOW_F5] (kN ++ kP) (SCR [false; false; false] [] []).
    - apply Forall_app; split; [exact (kN_ok IN R [] m HP HMI) | exact (kP_ok R [] m HP HMI)].
    - unfold scs_denot. repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with
        | |- sc_denot _ _ _ (SCFlat (SA (EVar 35) _) (ELit _)) =>
            apply scF_lit; [clear; lia | apply flatP; clear; lia]
        | |- sc_denot _ _ _ (SCFlat (SA (EVar 58) _) (ELit _)) =>
            apply scF_lit; [clear; lia | apply (flatN IN); clear; lia]
        | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) _) _) _) (ELit _)) =>
            apply scF_lit; [clear; lia | apply flat_shP; clear; lia]
        | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 58) _) _) _) (ELit _)) =>
            apply scF_lit; [clear; lia | apply (flat_shN IN); clear; lia]
        | |- sc_denot _ _ _ (SCBr false BC_LTU _ _) =>
            cbn [sc_denot edenot]; change (ev (HLib.Eseed R (Wp ++ [])) 61) with (Z_to_bv 64 enc);
            apply sn_br_e16; clear - NDR4 EN16; lia
        | |- sc_denot _ _ _ (SCBr false BC_EQ _ _) =>
            cbn [sc_denot edenot]; change (ev (HLib.Eseed R (Wp ++ [])) 59) with (Z_to_bv 64 nk);
            apply sn_br; clear - NDR2 NZ; lia
        | |- sc_denot _ _ _ (SCBr false BC_GEU _ _) =>
            cbn [sc_denot edenot]; change (ev (HLib.Eseed R (Wp ++ [])) 59) with (Z_to_bv 64 nk);
            apply sn_br_k4; clear - NDR2 NK4; lia
        end.
    - intros R2 m2 RF2 HRT2 HTS2 HPm2 HMI2 MU2 WM2.
      tsplit5 HTS2 HSF2 HFT2 HHT2 HP22 HP82.
      cbn [s_pc].
      pose proof sn_ranges as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
      pose proof sn_wins as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
      pose proof shb_eq as SHB.
      assert (FFB : 0 <= ff /\ ff + 1024 <= 2 ^ 47) by (clear - G4 G5 G8 G9 G12; unfold AIMG_TOP, AFS_HDR in *; lia).
      assert (FPB : 0 <= fp /\ fp + 1 <= 2 ^ 47) by (clear - G4 G7 G8 FFB; unfold AIMG_TOP, AFS_FLAGS in *; lia).
      assert (SPB : 2 ^ 45 <= spz - 96 /\ spz <= 2 ^ 47) by (clear - G2 G3 G12; unfold ADS_STACK, AAPP_HI in *; lia).
      pose proof (proj2 HPm2) as WM12.
      assert (AC2 : ACONST m2) by exact (ACONST_frame _ _ _ AC1 (proj1 (Pw_cz m2 HPm2)) WM12 pw_aconst).
      assert (RF2' : as_RFS H ((4, ff, fp) :: LF) m2) by (eapply RFS_step5p; [exact HRF | exact MU2 | exact WM2]).
      assert (PO2 : po4 m2).
      { assert (C1 : rw_cells asegs m2 (po + 8) [CB 4 (word_to_le_bytes 4 (ext_val true 0 4 (Z_to_bv 64 nk)))])
          by (apply (ftbl_In Wp po m2 _ 8 4%nat (EExt true 0 4 (EVar 59)) HP82); apply fent_in_In; vm_compute; reflexivity).
        assert (C2 : rw_cells asegs m2 (po + 12) [CB 4 (word_to_le_bytes 4 (ext_val true 0 4 (Z_to_bv 64 bw)))])
          by (apply (ftbl_In Wp po m2 _ 12 4%nat (EExt true 0 4 (EVar 60)) HP82); apply fent_in_In; vm_compute; reflexivity).
        assert (C3 : rw_cells asegs m2 (po + 16) [CB 4 (word_to_le_bytes 4 (ext_val true 0 4 (Z_to_bv 64 enc)))])
          by (apply (ftbl_In Wp po m2 _ 16 4%nat (EExt true 0 4 (EVar 61)) HP82); apply fent_in_In; vm_compute; reflexivity).
        assert (C4 : rw_cells asegs m2 (po + 2)
                       [CB 2 (word_to_le_bytes 2 (sext 64 (alu32 ALU_SRL (low32 (alu64 ALU_ADD (ext_val true 0 4 (Z_to_bv 64 bw))
                                                                                    (Z_to_bv 64 31)))
                                                                 (low32 (Z_to_bv 64 5)))))])
          by (apply (ftbl_In Wp po m2 _ 2 2%nat (EAluw ALU_SRL (EAlu ALU_ADD (EExt true 0 4 (EVar 60)) (ELit 31)) (ELit 5)) HP22);
              apply fent_in_In; vm_compute; reflexivity).
        rewrite (sn_w4 nk NDR2) in C1. rewrite (sn_w4 bw NDR3) in C2. rewrite (sn_w4 enc NDR4) in C3. rewrite (sn_w2 bw NDR3) in C4.
        split; [exact (rw_C4_of_CB _ _ _ C1)|]. split; [exact (rw_C4_of_CB _ _ _ C2)|].
        split; [exact (rw_C4_of_CB _ _ _ C3) | exact (rw_C2_of_CB _ _ _ C4)]. }
      assert (SV2 : rw_cells asegs m2 (spz - 80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { replace (spz - 80) with (spz + -80) by (clear; lia).
        eapply (rw_C8s_of_ftbl Wp spz m2 _ [EVar 45; EVar 44; EVar 43; EVar 42; EVar 41; EVar 40; EVar 39; EVar 38; EVar 34]
                  (EVar 46) (-80)); [| exact HSF2].
        intros i e Hi; do 10 (destruct i as [|i]; [injection Hi as <-; vm_compute; reflexivity|]); destruct i; discriminate Hi. }
      assert (CF2 : rw_cells asegs m2 (ff + 1016) [C8 (Z_to_bv 64 fp)]).
      { apply rw_C8_of_CB.
        apply (ftbl_In Wp ff m2 _ 1016 8%nat (EVar 53) HFT2); apply fent_in_In; vm_compute; reflexivity. }
      rgetp HRT2 (1%bv : bv 5) A1. rgetp HRT2 (3%bv : bv 5) A3. rgetp HRT2 (4%bv : bv 5) A4. rgetp HRT2 (8%bv : bv 5) A8.
      rgetp HRT2 (11%bv : bv 5) A11. rgetp HRT2 (18%bv : bv 5) A18. rgetp HRT2 (20%bv : bv 5) A20.
      rgetp HRT2 (25%bv : bv 5) A25. rgetp HRT2 (26%bv : bv 5) A26. rgetp HRT2 (27%bv : bv 5) A27.
      assert (A1' : PropExec.getr R2 1 = Z_to_bv 64 LbB_SnXZ.SX_SF_RA) by exact A1.
      assert (A8' : PropExec.getr R2 8 = Z_to_bv 64 spz) by (rewrite A8; symmetry; apply Z_to_bv_bv_unsigned).
      assert (A10 : PropExec.getr R2 10 = Z_to_bv 64 (sh ff)).
      { rewrite (rtbl_In _ R2 _ 10%bv (EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit SHBASE)) HRT2
                   ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)).
        change (edenot (wenv Wp) (EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit SHBASE)))
          with (alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 ff) (Z_to_bv 64 3)) (Z_to_bv 64 SHBASE)).
        apply sh_word. clear - FFB; lia. }
      rewrite (MS_full_eq R2 F _ fc m2 _ RF2).
      destruct (rw_cells_of_wr_hi m2 (sh ff) 128 (wr_at_wmono _ _ _ _ FSW WM12)
                  ltac:(clear - FFB; unfold sh, AIMG_TOP, ASHADOW_BASE; Z.div_mod_to_equations; lia) ltac:(clear; lia))
        as (junk & CSH).
      eapply evt_cut.
      { eapply (ah_setf5 H HHb) with (sa := sh ff) (n := 128); [exact A10 | exact A11 | clear; lia | exact CSH | exact HMI2 | exact AC2]. }
      intros ms3 (v0 & v1 & v2 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m3 & EQ3 & MU3 & WM3 & MI3 & SH3).
      subst ms3.
      rewrite A1', (ret_pc_even LbB_SnXZ.SX_SF_RA ltac:(unfold LbB_SnXZ.SX_SF_RA; lia) eq_refl), A8', A18, A20.
      assert (SV3 : rw_cells asegs m3 (spz - 80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rw_cells_transport; [exact SV2 | exact MU3 | exact WM3 |]. clear - V3 SHB. cbn. lia. }
      assert (CF3 : rw_cells asegs m3 (ff + 1016) [C8 (Z_to_bv 64 fp)]).
      { eapply rw_cells_transport; [exact CF2 | exact MU3 | exact WM3 |]. clear - V5 SHB. cbn. lia. }
      pose proof (wr_at_wmono _ _ _ _ FLW (wmono_trans asegs _ _ _ WM12 WM3)) as WP3.
      assert (B7 : fp + 1 <= spz - 80 \/ spz <= fp) by (clear - V4; lia).
      destruct (LbB_SnXZ.sn_xe2 (Z_to_bv 64 LbB_SnXZ.SX_SF_RA) (PropExec.getr R2 2) v0 v1 v2 (PropExec.getr R2 9)
                  v10 v11 v12 v13 v14 v15 v16 v17 (PropExec.getr R2 19) (PropExec.getr R2 21) (PropExec.getr R2 22)
                  (PropExec.getr R2 23) (PropExec.getr R2 24) (PropExec.getr R2 25) (PropExec.getr R2 26) (PropExec.getr R2 27)
                  v28 v29 v30 v31 (PropExec.getr R2 3) (PropExec.getr R2 4) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 F fc m3 (seg_rom asegs)
                  ff fp spz 0 (proj1 FFB) (proj2 FFB) (proj1 FPB) (proj2 FPB) (proj1 SPB) (proj2 SPB) B7 SV3 CF3 WP3 MI3)
        as (R4 & m4 & RUN4 & HR4 & MU4 & WM4 & MI4 & ST4 & FL4).
      eapply evt_of_msteps; [exact RUN4|]. subst R4.
      apply sn_ret_ok.
      assert (PW4 : Pw m4).
      { apply (Pw_ext m3 m4 [(fp, fp + 1)]); [| exact MU4 | exact WM4 | apply Forall_cons; [apply in_fl; clear; lia | apply Forall_nil]].
        apply (Pw_ext m2 m3 [(sh ff, sh ff + 128)]); [exact HPm2 | exact MU3 | exact WM3 |].
        apply Forall_cons; [apply in_sh; clear; lia | apply Forall_nil]. }
      pose proof (munch_app _ _ _ _ _ MU3 MU4) as MU24. cbn [app] in MU24.
      pose proof (wmono_trans asegs _ _ _ WM3 WM4) as WM24.
      assert (RF4 : as_RFS H LF m4).
      { pose proof (ah_release H HHb ((4, ff, fp) :: LF) m2 m4 _ 4 ff fp RF2' (or_introl eq_refl) MU24 WM24) as K.
        rewrite lf_remove_head in K. apply K; [| exact FL4].
        apply Forall_cons; [left; exact afs_ok_shadow|]. apply Forall_cons; [right; split; reflexivity | apply Forall_nil]. }
      assert (NP : Forall nopo [(sh ff, sh ff + 128); (fp, fp + 1)]).
      { apply Forall_cons; [right; right; left; cbn [fst snd]; clear; lia|].
        apply Forall_cons; [right; right; right; cbn [fst snd]; clear; lia | apply Forall_nil]. }
      destruct (po4_keep _ m2 m4 MU24 WM24 NP PO2) as (P1 & P2 & P3 & P4).
      rewrite A3, A4, A25, A26, A27, Z_to_bv_bv_unsigned.
      exists v0, v1, v2, v11, v12, v13, v14, v15, v16, v17, v28, v29, v30, v31, m4.
      split; [reflexivity|]. split; [exact MI4|]. split; [exact PW4|]. split; [exact RF4|].
      split; [exact P1|]. split; [exact P2|]. split; [exact P3 | exact P4].
  Qed.

  Ltac dkrunP3ks HRT HSF HFT HHT HP HMI fuel stops kx scr0 :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops scr0 (SS pc (HLib.srs sr_id RT) [] ((kst_sn ++ kx) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3]
                    (tabs_wf3 SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step3 SF FT HT ks1 ks2 ks3)
                    Q R F pc fc m ro RT [] (kst_sn ++ kx) fuel stops scr0 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok3; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end
    end.

  Lemma sn_found0 : In (nd, (tid, (nk, bw, enc))) ents -> nk = 0 ->
    forall Q R m, rfull R -> rtbl Wp R RT5 -> ftbl Wp spz m SF4 -> ftbl Wp ff m FT4 -> ftbl Wp (ff / 8) m HT4 ->
    Pw m -> mem_inv asegs m -> as_RFS H ((4, ff, fp) :: LF) m ->
    (forall R' m', rfull R' -> rtbl Wp R' RTK4 -> ftbl Wp spz m' SF4 -> ftbl Wp ff m' FT4 -> ftbl Wp (ff / 8) m' HT4 ->
       Pw m' -> mem_inv asegs m' -> as_RFS H ((4, ff, fp) :: LF) m' -> munch W3 m m' ->
       evt asegs Q (MS R' F (Z_to_bv 64 0xf9bf8) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS R F (Z_to_bv 64 LbB_SnFind.SNF_FOUND) fc None m (seg_rom asegs)).
Proof.
    intros IN NZ Q R m RF HRT HSF HFT HHT HP HMI HRF K.
    dkrunP3ks HRT HSF HFT HHT HP HMI 600%nat [0xf9bf8] kN (SCR [false; true] [] []).
    - exact (kN_ok IN R [] m HP HMI).
    - unfold scs_denot. repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with
        | |- sc_denot _ _ _ (SCFlat (SA (EVar 58) _) (ELit _)) =>
            apply scF_lit; [clear; lia | apply (flatN IN); clear; lia]
        | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 58) _) _) _) (ELit _)) =>
            apply scF_lit; [clear; lia | apply (flat_shN IN); clear; lia]
        | |- sc_denot _ _ _ (SCBr true BC_EQ _ _) =>
            cbn [sc_denot edenot]; change (ev (HLib.Eseed R (Wp ++ [])) 59) with (Z_to_bv 64 nk);
            rewrite NZ; exact sn_br0
        | |- sc_denot _ _ _ (SCBr false BC_GEU _ _) =>
            cbn [sc_denot edenot]; change (ev (HLib.Eseed R (Wp ++ [])) 59) with (Z_to_bv 64 nk);
            apply sn_br_k4; clear - NZ; lia
        end.
    - intros R2 m2 RF2 HRT2 HTS2 HPm2 HMI2 MU2 WM2.
      tsplit HTS2 HSF2 HFT2 HHT2.
      cbn [s_pc].
      apply (K R2 m2 RF2).
      + apply (rtbl_sub _ R2 _ RTK4 HRT2); vm_compute; reflexivity.
      + apply (ftbl_sub _ _ _ _ _ HSF2); vm_compute; reflexivity.
      + apply (ftbl_sub _ _ _ _ _ HFT2); vm_compute; reflexivity.
      + apply (ftbl_sub _ _ _ _ _ HHT2); vm_compute; reflexivity.
      + exact HPm2.
      + exact HMI2.
      + eapply RFS_step3; [exact HRF | exact MU2 | exact WM2].
      + rewrite winsT3_eq in MU2. exact MU2.
  Qed.
End SnF.
