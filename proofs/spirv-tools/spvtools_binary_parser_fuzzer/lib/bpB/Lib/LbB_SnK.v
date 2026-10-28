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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DPdK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_TablStmt LbB_SnStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_SnV.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition PO_SIZE : Z := 20.
Notation PD_SHB := LbB_DPdK.PD_SHB (only parsing).

Definition kst_sn : list kentry :=
  [ KImg 0x17e000 0x186000; KWord (SA (ELit 0) SHCELL) 8 (ELit SHBASE); KWord (SA (ELit 0) AUAR_CELL) 4 (ELit 1);
    KWr (SA (EVar 33) (-8192)) (ELit 8192); KRange (EVar 33) (2 ^ 45) (2 ^ 47);
    KWr (SA (EVar 52) 0) (ELit 1024); KRange (EVar 52) 0x6e8000 (2 ^ 47 - 1024);
    KWr (SA PD_SHB SHBASE) (ELit 128); KWr (SA (EVar 53) 0) (ELit 1); KRange (EVar 53) 0x6e8000 (2 ^ 47);
    KDisj (SA (EVar 52) 0) (ELit 1024) (SA (EVar 33) (-8192)) (ELit 8192);
    KDisj (SA PD_SHB SHBASE) (ELit 128) (SA (EVar 33) (-8192)) (ELit 8192);
    KDisj (SA PD_SHB SHBASE) (ELit 128) (SA (EVar 52) 0) (ELit 1024);
    KDisj (SA (EVar 53) 0) (ELit 1) (SA (EVar 33) (-8192)) (ELit 8192);
    KDisj (SA (EVar 53) 0) (ELit 1) (SA (EVar 52) 0) (ELit 1024);
    KDisj (SA (EVar 53) 0) (ELit 1) (SA PD_SHB SHBASE) (ELit 128) ].

Definition dj2 (xa xb xc xd : Z) : Prop := xa <= xb \/ xc <= xd.
Definition rg (xa xx xb : Z) : Prop := xa <= xx < xb.

Section Sn.
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

  Notation spz := (bv_unsigned sp) (only parsing).

  Definition Wp : list word :=
    [Z_to_bv 64 this; sp; ra; Z_to_bv 64 po; Z_to_bv 64 (sx32A tid); aw; s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; gp; tp;
     Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 pcons; Z_to_bv 64 icount;
     Z_to_bv 64 bl; Z_to_bv 64 bc; Z_to_bv 64 nd; Z_to_bv 64 nk; Z_to_bv 64 bw; Z_to_bv 64 enc].

  Definition PW : list (Z * Z) := [(spz - 16384, spz); (po, po + PO_SIZE); (ff, ff + 1024); (sh ff, sh ff + 128); (fp, fp + 1)].

  Definition PWF : list (Z * Z) :=
    [(spz - 16384, spz); (po + 2, po + 4); (po + 8, po + 20); (ff, ff + 1024); (sh ff, sh ff + 128); (fp, fp + 1)].
  Definition Pw (m : mem) : Prop := munch PWF m1 m /\ wmono asegs m1 m.
  Lemma Pw_cz : forall m, Pw m -> munch PW m1 m /\ wmono asegs m1 m.
  Proof.
    intros m [MU WM]. split; [| exact WM]. eapply munch_weaken; [| exact MU]. apply sub_fp_of. unfold PWF, PW, PO_SIZE.
    apply Forall_cons; [eexists; split; [left; reflexivity | cbn; lia]|].
    apply Forall_cons; [eexists; split; [right; left; reflexivity | cbn; lia]|].
    apply Forall_cons; [eexists; split; [right; left; reflexivity | cbn; lia]|].
    apply Forall_cons; [eexists; split; [right; right; left; reflexivity | cbn; lia]|].
    apply Forall_cons; [eexists; split; [right; right; right; left; reflexivity | cbn; lia]|].
    apply Forall_cons; [eexists; split; [right; right; right; right; left; reflexivity | cbn; lia] | apply Forall_nil].
  Qed.

  Lemma Pw_m1 : Pw m1.
  Proof. split; [apply munch_refl | apply wmono_refl]. Qed.

  Lemma sn_ranges :
    0 <= spz < 2 ^ 64 /\ aceil + ADS_STACK <= spz /\ spz <= AAPP_HI
    /\ as_FSB H + AFS_HDR <= ff /\ ff + 1024 <= as_FSB H + AFS_SIZE /\ ff mod 64 = 0
    /\ as_FSB H + AFS_FLAGS <= fp < as_FSB H + AFS_HDR
    /\ AIMG_TOP <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ as_FSB H mod 4096 = 0
    /\ (as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H)
    /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000.
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof STK as (S0 & S1 & _). pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    destruct FFR as (K1 & K2 & K3 & (K4 & K5) & K6). destruct FSB_OK as (B1 & B2 & B3 & B4).
    unfold fsz in K3. change (64 * 2 ^ 4) with 1024 in K3.
    split; [lia|]. split; [unfold ADS_STACK in *; lia|]. split; [exact SPHI|].
    split; [lia|]. split; [lia|]. split; [exact K4|]. split; [lia|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
    split; [|lia]. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in *. destruct B4; [left | right]; lia.
  Qed.

  Lemma sh_mono8 : forall a b, 0 <= a -> a <= b -> a mod 8 = 0 -> b mod 8 = 0 -> sh b - sh a = (b - a) / 8.
  Proof. intros a b H0 H1 H2 H3. unfold sh. Z.div_mod_to_equations. nia. Qed.

  Lemma pw_aconst : Forall aconst_ok PW.
  Proof.
    pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof DSO as (O1 & O2 & O3).
    assert (SH : 0x800d5000 <= sh ff) by (unfold sh, ASHADOW_BASE, AIMG_TOP, AFS_HDR in *; Z.div_mod_to_equations; lia).
    clear - R1 R2 R3 R4 R5 R7 R8 R9 R11 R12 O1 O2 O3 SH.
    unfold PW, ADS_STACK, AFS_HDR, AFS_SIZE, AFS_FLAGS, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, PO_SIZE in *.
    apply Forall_cons; [apply LbB_DPdK.aconst_ok_hi; lia|].
    apply Forall_cons; [destruct O2; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP; lia|].
    apply Forall_cons; [destruct R11; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP; lia|].
    apply Forall_cons; [apply LbB_DPdK.aconst_ok_hi; lia|].
    apply Forall_cons; [destruct R11; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP; lia|].
    apply Forall_nil.
  Qed.

  Lemma pw_out_img : forall a, aimg_client a -> outside PW a.
  Proof.
    intros a Ha. pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof DSO as (O1 & O2 & O3).
    assert (SH : 0x800d5000 <= sh ff) by (unfold sh, ASHADOW_BASE, AIMG_TOP, AFS_HDR in *; Z.div_mod_to_equations; lia).
    clear - Ha R1 R2 R4 R7 R8 R12 O1 SH.
    unfold aimg_client in Ha. unfold PW, ADS_STACK, AFS_HDR, AFS_FLAGS, AIMG_TOP, PO_SIZE in *.
    apply LbB_DPdK.outside_of. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
  Qed.

  Lemma pw_sh_apart : forall A n, AIMG_TOP <= A -> A mod 8 = 0 -> 0 <= n -> A + n <= AAPP_HI ->
    (A + n <= ff \/ ff + 1024 <= A) -> (A + n <= bv_unsigned sp - 16384 \/ bv_unsigned sp <= A) ->
    disjoint_from PW (sh A) (nsh n).
  Proof.
    intros A n H1 H2 H3 H5 H6 H7. pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof DSO as (O1 & O2 & O3).
    assert (N8 : (nsh n = n / 8 /\ n = n / 8 * 8) \/ (nsh n = n / 8 + 1 /\ n / 8 * 8 < n < n / 8 * 8 + 8))
      by (clear - H3; unfold nsh; Z.div_mod_to_equations; lia).
    unfold PW. cbn [disjoint_from]. unfold sh.
    assert (EA : A = A / 8 * 8) by (clear - H2; Z.div_mod_to_equations; lia).
    assert (EN : 0 <= n / 8) by (clear - H3; Z.div_mod_to_equations; lia).
    assert (EF : ff = ff / 8 * 8) by (clear - R6; Z.div_mod_to_equations; lia).
    clear - H1 H2 H3 H5 H6 H7 R1 R2 R3 R4 R5 R7 R8 R9 R11 R12 O1 O2 O3 EA EN EF N8.
    unfold ADS_STACK, AFS_HDR, AFS_SIZE, AFS_FLAGS, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, PO_SIZE, ASHADOW_BASE in *.
    set (a8 := A / 8) in *. set (n8 := n / 8) in *. set (f8 := ff / 8) in *. set (ns := nsh n) in *. lia.
  Qed.
  Lemma pw_hull_apart : forall A n, AIMG_TOP <= A -> 0 <= n -> A + n + 64 <= AAPP_HI ->
    (hull_hi (A + n) <= ff \/ ff + 1024 <= hull_lo A) -> (A + n <= ALOWSH_LO \/ AHI_LO <= A) ->
    (hull_hi (A + n) <= bv_unsigned sp - 16384 \/ bv_unsigned sp <= hull_lo A) ->
    disjoint_from PW (sh (hull_lo A)) (sh (hull_hi (A + n)) - sh (hull_lo A)).
  Proof.
    intros A n H1 H2 H3 H4 H5 H6. pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof DSO as (O1 & O2 & O3).
    clear - H1 H2 H3 H4 H5 H6 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 O1 O2 O3.
    unfold PW, ADS_STACK, AFS_HDR, AFS_SIZE, AFS_FLAGS, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, PO_SIZE, hull_lo, hull_hi in *.
    cbn [disjoint_from]. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia.
  Qed.

  Lemma sn_keep : forall m, Pw m -> mem_inv asegs m ->
    ACONST m /\ LINV_P5 m /\ addressable m po PO_SIZE /\ wr_at asegs m po PO_SIZE /\ shvis m po (po + PO_SIZE)
    /\ addressable m pcons 48 /\ rw_cells asegs m (pcons + 32) [C8 (Z_to_bv 64 0)]
    /\ stk asegs m lo spz /\ wr_at asegs m ff 1024 /\ shvis m ff (ff + 1024) /\ wr_at asegs m (sh ff) 128 /\ wr_at asegs m fp 1.
  Proof.
    intros m HPwz MI. destruct (Pw_cz m HPwz) as [MU WM].
    pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof DSO as (O1 & O2 & O3). pose proof PCO as (P1 & P2 & P3).
    pose proof (SPOBJ po PO_SIZE ltac:(clear; tauto)) as SD. pose proof (SPOBJ pcons 48 ltac:(clear; tauto)) as SC.
    split; [eapply ACONST_frame; [exact AC1 | exact MU | exact WM | exact pw_aconst]|].
    split.
    { eapply LINV_P5_cl; [exact LV1|]. intros a Ha Hc. unfold wa. apply MU. rewrite unsigned_lit by lia. apply pw_out_img. exact Hc. }
    split; [eapply addressable_transport; [exact DSA | exact MU | exact WM |]|].
    { apply pw_sh_apart; [exact O1 | exact DS8 | unfold PO_SIZE; lia | unfold PO_SIZE, AAPP_HI in *; lia | | ].
      - unfold PO_SIZE in *. lia.
      - unfold PO_SIZE, ADS_STACK in *. lia. }
    split; [eapply wr_at_transport; [exact DSW | exact WM]|].
    split; [eapply shvis_transport; [exact DSV | exact MU | exact WM |]|].
    { apply pw_hull_apart; [exact O1 | unfold PO_SIZE; lia | exact DSH | exact HULL | exact O2 |].
      left. pose proof aceil_facts as (_ & AM & _). clear - DSM AM LO CEIL O1.
      unfold PO_SIZE, ADS_STACK, hull_lo, hull_hi in *. Z.div_mod_to_equations. lia. }
    split; [eapply addressable_transport; [exact PCA | exact MU | exact WM |]|].
    { apply pw_sh_apart; [exact P1 | exact PC8 | lia | exact P3 | lia | unfold ADS_STACK in *; lia]. }
    split.
    { eapply rw_cells_transport; [exact PCC | exact MU | exact WM |]. cbn [cells_size csize Nat.add Z.of_nat].
      assert (DP : po + PO_SIZE <= pcons \/ pcons + 48 <= po).
      { clear - DISJ. destruct (Z_le_gt_dec (po + PO_SIZE) pcons); [left; lia|]. destruct (Z_le_gt_dec (pcons + 48) po); [right; lia|].
        exfalso. apply (DISJ (Z.max po pcons)); unfold PO_SIZE in *; lia. }
      assert (SHF : sh ff + 128 <= pcons \/ pcons + 40 <= sh ff).
      { clear - P1 P2 P3 R4 R8 R9 R11 R5 R12. assert (E : ff / 8 * 8 <= ff < ff / 8 * 8 + 8) by (clear; Z.div_mod_to_equations; lia).
        unfold sh, ASHADOW_BASE, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, AFS_HDR, AFS_SIZE in *. set (f8 := ff / 8) in *. lia. }
      clear - SC SD DP SHF FFPC FPPC R1 R2 R12. unfold PW, ADS_STACK, PO_SIZE in *. cbn [disjoint_from]. lia. }
    split.
    { eapply stk_transport; [exact STK | exact MU | exact WM |]. intros x Hx. right.
      pose proof STK as (T1 & T2 & T3). destruct (T3 x Hx) as [HV _].
      pose proof (WM (wa x) HV) as HV'.
      assert (HX : AIMG_TOP <= bv_unsigned (wa x)) by (unfold wa; rewrite unsigned_lit by lia; unfold AIMG_TOP; lia).
      rewrite (BakeStackRep.wview_high m (wa x) HX) in HV'.
      destruct (m (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction]. }
    split; [eapply wr_at_transport; [exact FRW | exact WM]|].
    split.
    { unfold shvis in *. eapply stk_transport; [exact FSV | exact MU | exact WM |]. intros x Hx. right.
      pose proof FSV as (T1 & T2 & T3). destruct (T3 x Hx) as [HV _].
      pose proof (WM (wa x) HV) as HV'.
      assert (HX : AIMG_TOP <= bv_unsigned (wa x)).
      { assert (XB : sh (hull_lo ff) <= x < sh (hull_hi (ff + 1024))) by exact Hx.
        clear - XB R4 R8 R5 R9 R12.
        assert (E : sh (hull_hi (ff + 1024)) <= 2 ^ 44 + ASHADOW_BASE /\ AIMG_TOP <= sh (hull_lo ff)).
        { unfold sh, hull_lo, hull_hi, ASHADOW_BASE, AIMG_TOP, AFS_HDR, AFS_SIZE in *. Z.div_mod_to_equations. lia. }
        unfold wa. rewrite unsigned_lit by (unfold ASHADOW_BASE, AIMG_TOP in E; lia). lia. }
      rewrite (BakeStackRep.wview_high m (wa x) HX) in HV'.
      destruct (m (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction]. }
    split; [eapply wr_at_transport; [exact FSW | exact WM]|].
    eapply wr_at_transport; [exact FLW | exact WM].
  Qed.

  Lemma sn_keepT : forall m, Pw m -> mem_inv asegs m ->
    addressable m this 288 /\ rw_cells asegs m (this + 8) [C8 (Z_to_bv 64 pcons)]
    /\ rw_cells asegs m (this + 80) [C8 (Z_to_bv 64 icount)].
  Proof.
    intros m HPwz MI. destruct (Pw_cz m HPwz) as [MU WM].
    pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof THO as (T1 & T2 & T3).
    pose proof THS as THS'. pose proof THF as THF'. pose proof THP as THP'. pose proof THD as THD'. unfold dj2 in THS', THF', THP', THD'.
    assert (SHF : sh ff + 128 <= this \/ this + 288 <= sh ff).
    { clear - T1 T2 T3 R4 R8 R9 R11 R5 R12. assert (E : ff / 8 * 8 <= ff < ff / 8 * 8 + 8) by (clear; Z.div_mod_to_equations; lia).
      unfold sh, ASHADOW_BASE, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, AFS_HDR, AFS_SIZE in *. set (f8 := ff / 8) in *. lia. }

    assert (D1 : this + 288 <= bv_unsigned sp - 16384 \/ bv_unsigned sp <= this) by (clear - THS'; unfold ADS_STACK in *; lia).
    assert (DJ : forall k n, 0 <= k -> 0 <= n -> k + n <= 272 -> disjoint_from PW (this + k) n).
    { intros k n Hk Hn Hkn. unfold PW. cbn [disjoint_from].
      split; [clear - Hk Hn Hkn D1; lia|]. split; [clear - Hk Hn Hkn THD'; unfold PO_SIZE in *; lia|].
      split; [clear - Hk Hn Hkn THF'; lia|]. split; [clear - Hk Hn Hkn SHF; lia|]. split; [clear - Hk Hn Hkn THP'; lia | exact I]. }
    split; [eapply addressable_transport; [exact THA | exact MU | exact WM |]|].
    { apply pw_sh_apart; [exact T1 | exact TH8 | clear; lia | exact T3 | clear - THF'; lia | exact D1]. }
    split; [eapply rw_cells_transport; [exact THC1 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat]; apply DJ; clear; lia]|].
    eapply rw_cells_transport; [exact THC2 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat]; apply DJ; clear; lia].
  Qed.

  Lemma evWp : forall R X (k : nat), (k < 30)%nat ->
    ev (HLib.Eseed R (Wp ++ X)) (32 + N.of_nat k) = nth k Wp (Z_to_bv 64 0).
  Proof.
    intros R X k Hk. unfold HLib.Eseed, reg_ev. cbn [ev].
    destruct (N.ltb_spec (32 + N.of_nat k) 32); [lia|]. rewrite app_nth1 by (cbn [length Wp]; lia). f_equal. lia.
  Qed.

  Ltac evwp := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wp;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Lemma sn_vals : 0 <= po < 2 ^ 64 /\ 0 <= ff < 2 ^ 64 /\ 0 <= fp < 2 ^ 64 /\ 0 <= pcons < 2 ^ 64 /\ 0 <= icount < 2 ^ 64.
  Proof.
    pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof DSO as (O1 & O2 & O3). pose proof PCO as (P1 & P2 & P3).
    clear - R4 R5 R7 R8 R9 R12 O1 O3 P1 P3 ICN.
    unfold AIMG_TOP, AAPP_HI, PO_SIZE, AFS_HDR, AFS_FLAGS, AFS_SIZE in *. lia.
  Qed.

  Lemma kst_pd_ok : forall R X m, Pw m -> mem_inv asegs m -> know_ok asegs (HLib.Eseed R (Wp ++ X)) m kst_sn.
  Proof.
    intros R X m PW MI.
    destruct (sn_keep m PW MI) as (AC & (RL & _) & _ & _ & _ & _ & _ & ST & FW & _ & SW & LW).
    pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof sn_vals as (V1 & V2 & V3 & V4 & V5).
    assert (SHF : edenot (HLib.Eseed R (Wp ++ X)) (EVar 52) = Z_to_bv 64 ff) by reflexivity.
    assert (ESH : estart (HLib.Eseed R (Wp ++ X)) (SA PD_SHB SHBASE) = sh ff).
    { unfold PD_SHB. erewrite estart_sh; [| exact SHF | lia]. unfold sh, SHBASE, ASHADOW_BASE. lia. }
    assert (SH1 : 0x800d5000 <= sh ff /\ sh ff + 128 <= 2 ^ 44 + ASHADOW_BASE).
    { clear - R4 R5 R8 R9 R12. unfold sh, ASHADOW_BASE, AIMG_TOP, AFS_HDR, AFS_SIZE in *. Z.div_mod_to_equations. lia. }
    pose proof (ACONST_shbase m AC) as [_ CS]. pose proof (ACONST_uar m AC) as [_ CU].
    clear PW.
    unfold ADS_STACK, AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *.
    unfold know_ok, kst_sn. repeat apply Forall_cons; try apply Forall_nil.
    - apply kimg_relro. exact RL.
    - eapply (kword_of_rw_cells asegs _ m ASHBASE_CELL _ 0%nat (C8 (wz 0x7fff8000))); [exact CS | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off edenot]; rewrite unsigned_lit by lia; reflexivity
        | unfold ASHBASE_CELL; cbn; lia | unfold ASHBASE_CELL; cbn; lia | reflexivity].
    - eapply (kword_of_rw_cells asegs _ m AUAR_CELL _ 0%nat (C4 (wz 1))); [exact CU | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off edenot]; rewrite unsigned_lit by lia; reflexivity
        | unfold AUAR_CELL; cbn; lia | unfold AUAR_CELL; cbn; lia | reflexivity].
    - eapply kwr_of_stk; [exact ST | | |]; evwp; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwp. lia.
    - eapply kwr_of_wr_at; [exact FW | | |]; evwp; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwp. rewrite unsigned_lit by lia. lia.
    - eapply kwr_of_wr_at; [exact SW | rewrite ESH; lia | rewrite ESH; unfold elenZ; cbn [edenot]; rewrite unsigned_lit by lia; lia
                           | unfold elenZ; cbn [edenot]; rewrite unsigned_lit by lia; lia].
    - eapply kwr_of_wr_at; [exact LW | | |]; evwp; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwp. rewrite unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwp. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. rewrite ESH. evwp. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. rewrite ESH. evwp. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwp. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwp. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. rewrite ESH. evwp. rewrite !unsigned_lit by lia. lia.
  Qed.

  Lemma sn_keepU : forall m, Pw m ->
    umapx MI_A 32 (nval32 ASEGS) LBl m (this + 136) bl bc ents
    /\ gz m (this + 136) 40 /\ (bc <> 0 -> gz m bl (8 * bc)) /\ (forall p k v, In (p, (k, v)) ents -> gz m p 32).
  Proof.
    intros m HPwz. destruct (Pw_cz m HPwz) as [MU WM].
    assert (AG : forall a, umap_foot 32 (this + 136) bl bc ents a -> m (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
    { intros a Ha. destruct (UFO a Ha) as (O1 & _ & Ra). apply MU. rewrite unsigned_lit by (clear - Ra; lia). exact O1. }
    assert (GZ : forall a n, gz m1 a n -> (forall i, 0 <= i < n -> umap_foot 32 (this + 136) bl bc ents (a + i)) -> gz m a n).
    { intros a n G F0 i Hi. pose proof (G i Hi) as S. unfold sh0, shk in *.
      destruct (UFO (a + i) (F0 i Hi)) as (_ & O2 & Ra).
      assert (RS : 0 <= (a + i) / 8 + SHBASE < 2 ^ 64).
      { assert (0 <= (a + i) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; clear - Ra; lia | apply Z.div_lt_upper_bound; clear - Ra; lia]).
        unfold SHBASE. clear - H0. lia. }
      rewrite <- S. apply (PropExec.rdn_ext asegs 1 m m1 (Z_to_bv 64 ((a + i) / 8 + SHBASE))).
      - rewrite unsigned_lit by exact RS. clear - RS. cbn. lia.
      - intros x Hx. rewrite unsigned_lit in Hx by exact RS.
        assert (Ex : x = Z_to_bv 64 ((a + i) / 8 + SHBASE)).
        { apply bv_eq. rewrite unsigned_lit by exact RS. clear - Hx. cbn in Hx. lia. }
        subst x. apply MU. rewrite unsigned_lit by exact RS. exact O2. }
    split.
    { eapply (umapx_agree ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (nval32_agree ASEGS) ltac:(clear; lia) LBl LBl m1 m);
        [exact UM1 | exact AG | intros p n _ Hl; exact Hl]. }
    split; [apply (GZ _ _ UG1); intros i Hi; left; clear - Hi; lia|].
    split.
    { intros Hbc. apply (GZ _ _ (UG2 Hbc)). intros i Hi. right; left. split; [exact Hbc | clear - Hi; lia]. }
    intros p k v Hin. apply (GZ _ _ (UG3 p k v Hin)). intros i Hi. right; right. exists p. split; [| clear - Hi; lia].
    apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin].
  Qed.

  Definition shT (k : Z) : saddr := SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit k)) (ELit 3)) SHBASE.
  Definition kT (k : Z) : list kentry := [KWord (shT k) 1 (ELit 0); KDisj (shT k) (ELit 1) (SA PD_SHB SHBASE) (ELit 128)].

  Lemma evT : forall R X k, 0 <= k <= 288 ->
    edenot (HLib.Eseed R (Wp ++ X)) (EAlu ALU_ADD (EVar 32) (ELit k)) = Z_to_bv 64 (this + k).
  Proof.
    intros R X k Hk. pose proof THO as (T1 & T2 & T3).
    cbn [edenot]. change (ev (HLib.Eseed R (Wp ++ X)) 32) with (Z_to_bv 64 this).
    apply w_add; clear - Hk T1 T3; unfold AIMG_TOP, AAPP_HI in *; lia.
  Qed.

  Lemma shT_start : forall R X k, 0 <= k < 288 -> estart (HLib.Eseed R (Wp ++ X)) (shT k) = (this + k) / 8 + SHBASE.
  Proof.
    intros R X k Hk. pose proof THO as (T1 & T2 & T3). unfold shT.
    apply estart_sh; [apply evT; clear - Hk; lia | clear - Hk T1 T3; unfold AIMG_TOP, AAPP_HI in *; lia].
  Qed.

  Lemma shT_apart : forall k, 0 <= k < 288 ->
    (this + k) / 8 + SHBASE + 1 <= ff / 8 + SHBASE \/ ff / 8 + SHBASE + 128 <= (this + k) / 8 + SHBASE.
  Proof.
    intros k Hk. pose proof THF as THF'. unfold dj2 in THF'.
    pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    assert (EF : ff = ff / 8 * 8) by (clear - R6; Z.div_mod_to_equations; lia).
    assert (ET : this = this / 8 * 8) by (clear - TH8; Z.div_mod_to_equations; lia).
    clear - Hk THF' EF ET. set (f8 := ff / 8) in *. set (t8 := this / 8) in *.
    assert (E2 : (this + k) / 8 = t8 + k / 8) by (rewrite ET; rewrite Z.add_comm, Z.div_add by lia; lia).
    rewrite E2. assert (0 <= k / 8 < 36) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    destruct THF' as [A|A]; [right | left]; lia.
  Qed.

  Lemma kT_ok : forall R X m k, Pw m -> mem_inv asegs m -> 0 <= k < 288 ->
    know_ok asegs (HLib.Eseed R (Wp ++ X)) m (kT k).
  Proof.
    intros R X m k PW MI Hk. destruct (sn_keepT m PW MI) as (THAm & _).
    pose proof THO as (T1 & T2 & T3).
    pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof sn_vals as (V1 & V2 & V3 & V4 & V5).
    unfold know_ok, kT. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    - apply (kshadow0 _ m (EAlu ALU_ADD (EVar 32) (ELit k)) (this + k));
        [ apply evT; clear - Hk; lia | clear - Hk T1 T3; unfold AIMG_TOP, AAPP_HI in *; lia
        | eapply (sh0_of_addressable m this 288 (this + k)); [exact THAm | change (8 * (288 / 8)) with 288; clear - Hk; lia] ].
    - cbn [kentry_ok]. rewrite shT_start by exact Hk.
      assert (ESH : estart (HLib.Eseed R (Wp ++ X)) (SA PD_SHB SHBASE) = ff / 8 + SHBASE).
      { unfold LbB_DPdK.PD_SHB. apply estart_sh; [reflexivity | clear - V2; lia]. }
      rewrite ESH. unfold elenZ. cbn [edenot]. rewrite !unsigned_lit by (clear; lia).
      pose proof (shT_apart k Hk) as A. clear - A. lia.
  Qed.

  Lemma scT_flat : forall R X k, 0 <= k < 288 -> flat (HLib.Eseed R (Wp ++ X)) (shT k) 1.
  Proof.
    intros R X k Hk. pose proof THO as (T1 & T2 & T3). unfold flat. rewrite shT_start by exact Hk.
    assert (0 <= (this + k) / 8 < 2 ^ 44).
    { split; [apply Z.div_pos; clear - Hk T1; unfold AIMG_TOP in *; lia | apply Z.div_lt_upper_bound; clear - Hk T3; unfold AAPP_HI in *; lia]. }
    unfold SHBASE. clear - H0. lia.
  Qed.

  Definition tS (T : list fent) (ks : list (Z * nat)) : tab := (EVar 33, spz, -8192, 0, T, ks).
  Definition tF (T : list fent) (ks : list (Z * nat)) : tab := (EVar 52, ff, 0, 1024, T, ks).
  Definition tH (T : list fent) (ks : list (Z * nat)) : tab := (PD_SHB, ff / 8, SHBASE, SHBASE + 128, T, ks).
  Definition tL (T : list fent) (ks : list (Z * nat)) : tab := (EVar 53, fp, 0, 1, T, ks).

  Lemma sn_wins : spz + 0 <= spz /\ ff + 1024 <= spz - 8192 /\ ff / 8 + SHBASE + 128 <= spz - 8192 /\ fp + 1 <= spz - 8192
    /\ (ff + 1024 <= ff / 8 + SHBASE \/ ff / 8 + SHBASE + 128 <= ff) /\ fp + 1 <= ff
    /\ (fp + 1 <= ff / 8 + SHBASE \/ ff / 8 + SHBASE + 128 <= fp) /\ 0 <= ff / 8.
  Proof.
    pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    assert (EF : ff / 8 * 8 <= ff < ff / 8 * 8 + 8) by (clear; Z.div_mod_to_equations; lia).
    clear - R1 R2 R4 R5 R7 R8 R9 R11 R12 EF.
    unfold ADS_STACK, AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP, ALOWSH_LO, AHI_LO, SHBASE in *.
    set (f8 := ff / 8) in *. lia.
  Qed.

  Lemma tab_vals : bv_unsigned (edenot (wenv Wp) (EVar 33)) = spz /\ bv_unsigned (edenot (wenv Wp) (EVar 52)) = ff
    /\ bv_unsigned (edenot (wenv Wp) PD_SHB) = ff / 8 /\ bv_unsigned (edenot (wenv Wp) (EVar 53)) = fp.
  Proof.
    pose proof sn_vals as (V1 & V2 & V3 & V4 & V5).
    split; [reflexivity|]. split; [cbn; apply unsigned_lit; lia|]. split; [|cbn; apply unsigned_lit; lia].
    unfold PD_SHB. apply (srl3_val (wenv Wp) (EVar 52) ff); [reflexivity | lia].
  Qed.

  Lemma tabs_wf3 : forall SF FT HT ks1 ks2 ks3,
    fwcl (wbound Wp) SF = true -> fwcl (wbound Wp) FT = true -> fwcl (wbound Wp) HT = true ->
    fin (-8192) 0 (fkeys SF ++ ks1) = true -> fin 0 1024 (fkeys FT ++ ks2) = true -> fin SHBASE (SHBASE + 128) (fkeys HT ++ ks3) = true ->
    tabs_wf Wp [tS SF ks1; tF FT ks2; tH HT ks3].
  Proof.
    intros SF FT HT ks1 ks2 ks3 C1 C2 C3 F1 F2 F3.
    pose proof sn_wins as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8). pose proof tab_vals as (T1 & T2 & T3 & T4).
    pose proof sn_ranges as (R1 & _). pose proof sn_vals as (V1 & V2 & _).
    split.
    - repeat constructor; cbn [tb tB tlo thi ttbl tks tS tF tH]; try reflexivity; try assumption; unfold SHBASE in *; lia.
    - intros t1 t2 H1 H2 Hb. cbn [In] in H1, H2.
      destruct H1 as [<-|[<-|[<-|[]]]]; destruct H2 as [<-|[<-|[<-|[]]]]; cbn [tb tB tlo thi tS tF tH] in *;
        try (vm_compute in Hb; discriminate Hb); unfold SHBASE in *; lia.
  Qed.

  Lemma tabs_wf4 : forall SF FT HT LT ks1 ks2 ks3 ks4,
    fwcl (wbound Wp) SF = true -> fwcl (wbound Wp) FT = true -> fwcl (wbound Wp) HT = true -> fwcl (wbound Wp) LT = true ->
    fin (-8192) 0 (fkeys SF ++ ks1) = true -> fin 0 1024 (fkeys FT ++ ks2) = true -> fin SHBASE (SHBASE + 128) (fkeys HT ++ ks3) = true ->
    fin 0 1 (fkeys LT ++ ks4) = true ->
    tabs_wf Wp [tS SF ks1; tF FT ks2; tH HT ks3; tL LT ks4].
  Proof.
    intros SF FT HT LT ks1 ks2 ks3 ks4 C1 C2 C3 C4 F1 F2 F3 F4.
    pose proof sn_wins as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8). pose proof tab_vals as (T1 & T2 & T3 & T4).
    pose proof sn_ranges as (R1 & _). pose proof sn_vals as (V1 & V2 & V3 & _).
    split.
    - repeat constructor; cbn [tb tB tlo thi ttbl tks tS tF tH tL]; try reflexivity; try assumption; unfold SHBASE in *; lia.
    - intros t1 t2 H1 H2 Hb. cbn [In] in H1, H2.
      destruct H1 as [<-|[<-|[<-|[<-|[]]]]]; destruct H2 as [<-|[<-|[<-|[<-|[]]]]]; cbn [tb tB tlo thi tS tF tH tL] in *;
        try (vm_compute in Hb; discriminate Hb); unfold SHBASE in *; lia.
  Qed.

  Lemma wk_stk : forall m (ks : list (Z * nat)), stk asegs m lo spz -> fin (-8192) 0 ks = true ->
    forall k w, In (k, w) ks -> wr_at asegs m (spz + k) (Z.of_nat w).
  Proof.
    intros m ks ST Hf k w Hi. destruct (fin_In _ _ _ k w Hf Hi) as (H1 & H2 & H3).
    pose proof LO as LO'. unfold ADS_STACK in LO'.
    pose proof (wr_at_of_stk asegs m lo spz ST) as W. eapply wr_at_sub; [exact W | lia | lia | lia].
  Qed.
  Lemma wk_win : forall m A n (ks : list (Z * nat)) B lo0, wr_at asegs m A n -> A = B + lo0 ->
    fin lo0 (lo0 + n) ks = true -> forall k w, In (k, w) ks -> wr_at asegs m (B + k) (Z.of_nat w).
  Proof.
    intros m A n ks B lo0 W -> Hf k w Hi. destruct (fin_In _ _ _ k w Hf Hi) as (H1 & H2 & H3).
    eapply wr_at_sub; [exact W | lia | lia | lia].
  Qed.

  Definition inPW (iv : Z * Z) : Prop := exists iv', In iv' PWF /\ fst iv' <= fst iv /\ snd iv <= snd iv'.
  Lemma Pw_ext : forall m m' W, Pw m -> munch W m m' -> wmono asegs m m' -> Forall inPW W -> Pw m'.
  Proof.
    intros m m' W [MU0 WM0] MU WM HW. split; [| eapply wmono_trans; eassumption].
    eapply munch_trans; [exact MU0|]. eapply munch_weaken; [apply sub_fp_of; exact HW | exact MU].
  Qed.
  Lemma in_stk : forall a b, spz - 16384 <= a -> b <= spz -> inPW (a, b).
  Proof. intros a b H1 H2. exists (spz - 16384, spz). split; [left; reflexivity | cbn; lia]. Qed.
  Lemma in_p2 : forall a b, po + 2 <= a -> b <= po + 4 -> inPW (a, b).
  Proof. intros a b H1 H2. exists (po + 2, po + 4). split; [right; left; reflexivity | cbn; lia]. Qed.
  Lemma in_p8 : forall a b, po + 8 <= a -> b <= po + 20 -> inPW (a, b).
  Proof. intros a b H1 H2. exists (po + 8, po + 20). split; [right; right; left; reflexivity | cbn; lia]. Qed.
  Lemma in_fr : forall a b, ff <= a -> b <= ff + 1024 -> inPW (a, b).
  Proof. intros a b H1 H2. exists (ff, ff + 1024). split; [right; right; right; left; reflexivity | cbn; lia]. Qed.
  Lemma in_sh : forall a b, sh ff <= a -> b <= sh ff + 128 -> inPW (a, b).
  Proof. intros a b H1 H2. exists (sh ff, sh ff + 128). split; [right; right; right; right; left; reflexivity | cbn; lia]. Qed.
  Lemma in_fl : forall a b, fp <= a -> b <= fp + 1 -> inPW (a, b).
  Proof. intros a b H1 H2. exists (fp, fp + 1). split; [right; right; right; right; right; left; reflexivity | cbn; lia]. Qed.
  Lemma shb_eq : ff / 8 + SHBASE = sh ff.
  Proof. unfold sh, SHBASE, ASHADOW_BASE. lia. Qed.

  Definition W3 : list (Z * Z) := [(spz + -8192, spz + 0); (ff + 0, ff + 1024); (ff / 8 + SHBASE, ff / 8 + (SHBASE + 128))].
  Lemma winsT3_eq : forall SF FT HT ks1 ks2 ks3, winsT [tS SF ks1; tF FT ks2; tH HT ks3] = W3.
  Proof. intros. unfold winsT. cbn [map tB tlo thi tS tF tH]. reflexivity. Qed.

  Lemma Pw_step3 : forall SF FT HT ks1 ks2 ks3 m m', Pw m -> munch (winsT [tS SF ks1; tF FT ks2; tH HT ks3]) m m' ->
    wmono asegs m m' -> mem_inv asegs m' -> Pw m'.
  Proof.
    intros SF FT HT ks1 ks2 ks3 m m' HP MU WM _. eapply Pw_ext; [exact HP | exact MU | exact WM |].
    unfold winsT. cbn [map tB tlo thi tS tF tH]. rewrite !Z.add_assoc, shb_eq.
    apply Forall_cons; [apply in_stk; lia|]. apply Forall_cons; [apply in_fr; lia|]. apply Forall_cons; [apply in_sh; lia|].
    apply Forall_nil.
  Qed.
  Lemma Pw_step4 : forall SF FT HT LT ks1 ks2 ks3 ks4 m m', Pw m -> munch (winsT [tS SF ks1; tF FT ks2; tH HT ks3; tL LT ks4]) m m' ->
    wmono asegs m m' -> mem_inv asegs m' -> Pw m'.
  Proof.
    intros SF FT HT LT ks1 ks2 ks3 ks4 m m' HP MU WM _. eapply Pw_ext; [exact HP | exact MU | exact WM |].
    unfold winsT. cbn [map tB tlo thi tS tF tH tL]. rewrite !Z.add_assoc, shb_eq.
    apply Forall_cons; [apply in_stk; lia|]. apply Forall_cons; [apply in_fr; lia|]. apply Forall_cons; [apply in_sh; lia|].
    apply Forall_cons; [apply in_fl; lia|]. apply Forall_nil.
  Qed.

  Lemma HHb : asan_rt_hyps H.
  Proof. exact (rt_bp_base H HHbp). Qed.

  Lemma afs_ok_frame : forall a b, ff <= a -> b <= ff + 1024 -> afs_write_ok H ((4, ff, fp) :: LF) (a, b).
  Proof. intros a b H1 H2. right. exists (4, ff, fp). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. unfold fsz. cbn. lia. Qed.
  Lemma afs_ok_stack : forall a b, aceil <= a -> afs_write_ok H ((4, ff, fp) :: LF) (a, b).
  Proof.
    intros a b Ha. left. cbn [fst snd]. pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    clear - Ha R9 R12. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. lia.
  Qed.
  Lemma afs_ok_shadow : afs_write_ok H ((4, ff, fp) :: LF) (sh ff, sh ff + 128).
  Proof.
    left. cbn [fst snd]. pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    assert (EF : ff / 8 * 8 <= ff < ff / 8 * 8 + 8) by (clear; Z.div_mod_to_equations; lia).
    clear - R4 R5 R8 R9 R11 R12 EF.
    unfold sh, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AFS_HDR, AIMG_TOP, ALOWSH_LO, AHI_LO, ASHADOW_BASE in *.
    set (f8 := ff / 8) in *. lia.
  Qed.

  Lemma tabs_ok3 : forall m SF FT HT ks1 ks2 ks3, Pw m -> mem_inv asegs m ->
    ftbl Wp spz m SF -> ftbl Wp ff m FT -> ftbl Wp (ff / 8) m HT ->
    fin (-8192) 0 ks1 = true -> fin 0 1024 ks2 = true -> fin SHBASE (SHBASE + 128) ks3 = true ->
    tabs_ok Wp m [tS SF ks1; tF FT ks2; tH HT ks3].
  Proof.
    intros m SF FT HT ks1 ks2 ks3 HP MI H1 H2 H3 F1 F2 F3.
    destruct (sn_keep m HP MI) as (_ & _ & _ & _ & _ & _ & _ & ST & FW & _ & SW & _).
    apply Forall_cons; [split; [exact H1 | exact (wk_stk m ks1 ST F1)]|].
    apply Forall_cons; [split; [exact H2 | exact (wk_win m ff 1024 ks2 ff 0 FW ltac:(lia) F2)]|].
    apply Forall_cons; [split; [exact H3 | exact (wk_win m (sh ff) 128 ks3 (ff / 8) SHBASE SW ltac:(rewrite shb_eq; lia) F3)]|].
    apply Forall_nil.
  Qed.
  Lemma tabs_ok4 : forall m SF FT HT LT ks1 ks2 ks3 ks4, Pw m -> mem_inv asegs m ->
    ftbl Wp spz m SF -> ftbl Wp ff m FT -> ftbl Wp (ff / 8) m HT -> ftbl Wp fp m LT ->
    fin (-8192) 0 ks1 = true -> fin 0 1024 ks2 = true -> fin SHBASE (SHBASE + 128) ks3 = true -> fin 0 1 ks4 = true ->
    tabs_ok Wp m [tS SF ks1; tF FT ks2; tH HT ks3; tL LT ks4].
  Proof.
    intros m SF FT HT LT ks1 ks2 ks3 ks4 HP MI H1 H2 H3 H4 F1 F2 F3 F4.
    destruct (sn_keep m HP MI) as (_ & _ & _ & _ & _ & _ & _ & ST & FW & _ & SW & LW).
    apply Forall_cons; [split; [exact H1 | exact (wk_stk m ks1 ST F1)]|].
    apply Forall_cons; [split; [exact H2 | exact (wk_win m ff 1024 ks2 ff 0 FW ltac:(lia) F2)]|].
    apply Forall_cons; [split; [exact H3 | exact (wk_win m (sh ff) 128 ks3 (ff / 8) SHBASE SW ltac:(rewrite shb_eq; lia) F3)]|].
    apply Forall_cons; [split; [exact H4 | exact (wk_win m fp 1 ks4 fp 0 LW ltac:(lia) F4)]|].
    apply Forall_nil.
  Qed.

  Definition kwin (k1 k2 : Z) (l : list (Z * nat)) : list (Z * nat) :=
    List.filter (fun kw => (k1 <=? fst kw) && (fst kw + Z.of_nat (snd kw) <=? k2))%bool l.
  Definition tP2 (T : list fent) (ks : list (Z * nat)) : tab := (EVar 35, po, 2, 4, T, ks).
  Definition tP8 (T : list fent) (ks : list (Z * nat)) : tab := (EVar 35, po, 8, 20, T, ks).

  Lemma po_wins : po + PO_SIZE <= spz - 8192 \/ spz <= po.
  Proof. pose proof (SPOBJ po PO_SIZE ltac:(clear; tauto)) as SD. clear - SD. unfold ADS_STACK in *. lia. Qed.
  Lemma po_sh_wins : po + PO_SIZE <= ff / 8 + SHBASE \/ ff / 8 + SHBASE + 128 <= po.
  Proof.
    pose proof DSO as (O1 & O2 & O3). pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    assert (EF : ff / 8 * 8 <= ff < ff / 8 * 8 + 8) by (clear; Z.div_mod_to_equations; lia).
    clear - O1 O2 O3 R4 R5 R8 R9 R12 EF.
    unfold PO_SIZE, AFS_HDR, AFS_SIZE, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, SHBASE in *. set (f8 := ff / 8) in *. lia.
  Qed.

  Lemma tabs_wf5p : forall SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5,
    fwcl (wbound Wp) SF = true -> fwcl (wbound Wp) FT = true -> fwcl (wbound Wp) HT = true ->
    fwcl (wbound Wp) P2 = true -> fwcl (wbound Wp) P8 = true ->
    fin (-8192) 0 (fkeys SF ++ ks1) = true -> fin 0 1024 (fkeys FT ++ ks2) = true -> fin SHBASE (SHBASE + 128) (fkeys HT ++ ks3) = true ->
    fin 2 4 (fkeys P2 ++ ks4) = true -> fin 8 20 (fkeys P8 ++ ks5) = true ->
    tabs_wf Wp [tS SF ks1; tF FT ks2; tH HT ks3; tP2 P2 ks4; tP8 P8 ks5].
  Proof.
    intros SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5 C1 C2 C3 C4 C5 F1 F2 F3 F4 F5.
    pose proof sn_wins as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8). pose proof tab_vals as (T1 & T2 & T3 & T4).
    pose proof sn_ranges as (R1 & _). pose proof sn_vals as (V1 & V2 & V3 & _).
    pose proof po_wins as PW1. pose proof po_sh_wins as PW2. pose proof FFDS as PW3.
    assert (TP : bv_unsigned (edenot (wenv Wp) (EVar 35)) = po) by (cbn; apply unsigned_lit; clear - V1; lia).
    split.
    - pose proof DSH as DSH'.
      repeat constructor; cbn [tb tB tlo thi ttbl tks tS tF tH tP2 tP8]; try reflexivity; try assumption;
        unfold SHBASE, PO_SIZE, AAPP_HI in *; clear - W1 W2 W3 W8 T1 T2 T3 R1 V1 V2 V3 DSH'; lia.
    - intros t1 t2 H1 H2 Hb. cbn [In] in H1, H2.
      destruct H1 as [<-|[<-|[<-|[<-|[<-|[]]]]]]; destruct H2 as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        cbn [tb tB tlo thi tS tF tH tP2 tP8] in *;
        try (vm_compute in Hb; discriminate Hb); unfold SHBASE, PO_SIZE in *;
        first [ clear - W1 W2 W3 W5; lia | clear - PW1; lia | clear - PW2; lia | clear - PW3; lia ].
  Qed.

  Lemma Pw_step5p : forall SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5 m m', Pw m ->
    munch (winsT [tS SF ks1; tF FT ks2; tH HT ks3; tP2 P2 ks4; tP8 P8 ks5]) m m' ->
    wmono asegs m m' -> mem_inv asegs m' -> Pw m'.
  Proof.
    intros SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5 m m' HP MU WM _. eapply Pw_ext; [exact HP | exact MU | exact WM |].
    unfold winsT. cbn [map tB tlo thi tS tF tH tP2 tP8]. rewrite !Z.add_assoc, shb_eq.
    apply Forall_cons; [apply in_stk; clear; lia|]. apply Forall_cons; [apply in_fr; clear; lia|]. apply Forall_cons; [apply in_sh; clear; lia|].
    apply Forall_cons; [apply in_p2; clear; lia|]. apply Forall_cons; [apply in_p8; clear; lia|]. apply Forall_nil.
  Qed.

  Lemma tabs_ok5p : forall m SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5, Pw m -> mem_inv asegs m ->
    ftbl Wp spz m SF -> ftbl Wp ff m FT -> ftbl Wp (ff / 8) m HT -> ftbl Wp po m P2 -> ftbl Wp po m P8 ->
    fin (-8192) 0 ks1 = true -> fin 0 1024 ks2 = true -> fin SHBASE (SHBASE + 128) ks3 = true ->
    fin 2 4 ks4 = true -> fin 8 20 ks5 = true ->
    tabs_ok Wp m [tS SF ks1; tF FT ks2; tH HT ks3; tP2 P2 ks4; tP8 P8 ks5].
  Proof.
    intros m SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5 HP MI H1 H2 H3 H4 H5 F1 F2 F3 F4 F5.
    destruct (sn_keep m HP MI) as (_ & _ & _ & PWR & _ & _ & _ & ST & FW & _ & SW & LW).
    assert (PW2 : wr_at asegs m (po + 2) 2) by (eapply wr_at_sub; [exact PWR | clear; lia | unfold PO_SIZE; clear; lia | clear; lia]).
    assert (PW8 : wr_at asegs m (po + 8) 12) by (eapply wr_at_sub; [exact PWR | clear; lia | unfold PO_SIZE; clear; lia | clear; lia]).
    apply Forall_cons; [split; [exact H1 | exact (wk_stk m ks1 ST F1)]|].
    apply Forall_cons; [split; [exact H2 | exact (wk_win m ff 1024 ks2 ff 0 FW ltac:(clear; lia) F2)]|].
    apply Forall_cons; [split; [exact H3 | exact (wk_win m (sh ff) 128 ks3 (ff / 8) SHBASE SW ltac:(rewrite shb_eq; clear; lia) F3)]|].
    apply Forall_cons; [split; [exact H4 | exact (wk_win m (po + 2) 2 ks4 po 2 PW2 ltac:(clear; lia) ltac:(exact F4))]|].
    apply Forall_cons; [split; [exact H5 | exact (wk_win m (po + 8) 12 ks5 po 8 PW8 ltac:(clear; lia) ltac:(exact F5))]|].
    apply Forall_nil.
  Qed.

  Lemma afs_ok_po : forall a b, po <= a -> b <= po + PO_SIZE -> afs_write_ok H ((4, ff, fp) :: LF) (a, b).
  Proof.
    intros a b H1 H2. right. destruct DSin as (f & Hf & F1 & F2). exists f. split; [right; exact Hf|]. cbn [fst snd]. clear - H1 H2 F1 F2. lia.
  Qed.

  Lemma RFS_step5p : forall SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5 m m', as_RFS H ((4, ff, fp) :: LF) m ->
    munch (winsT [tS SF ks1; tF FT ks2; tH HT ks3; tP2 P2 ks4; tP8 P8 ks5]) m m' -> wmono asegs m m' ->
    as_RFS H ((4, ff, fp) :: LF) m'.
  Proof.
    intros SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5 m m' RF MU WM. eapply (ah_RFS_frame H HHb); [exact RF | exact MU | exact WM |].
    pose proof sn_ranges as (R1 & R2 & _).
    unfold winsT. cbn [map tB tlo thi tS tF tH tP2 tP8]. rewrite !Z.add_assoc, shb_eq.
    apply Forall_cons; [apply afs_ok_stack; clear - R2; unfold ADS_STACK in *; lia|].
    apply Forall_cons; [apply afs_ok_frame; clear; lia|]. apply Forall_cons; [exact afs_ok_shadow|].
    apply Forall_cons; [apply afs_ok_po; unfold PO_SIZE; clear; lia|].
    apply Forall_cons; [apply afs_ok_po; unfold PO_SIZE; clear; lia|]. apply Forall_nil.
  Qed.

  Lemma RFS_step3 : forall SF FT HT ks1 ks2 ks3 m m', as_RFS H ((4, ff, fp) :: LF) m ->
    munch (winsT [tS SF ks1; tF FT ks2; tH HT ks3]) m m' -> wmono asegs m m' -> as_RFS H ((4, ff, fp) :: LF) m'.
  Proof.
    intros SF FT HT ks1 ks2 ks3 m m' RF MU WM. eapply (ah_RFS_frame H HHb); [exact RF | exact MU | exact WM |].
    pose proof sn_ranges as (R1 & R2 & _).
    unfold winsT. cbn [map tB tlo thi tS tF tH]. rewrite !Z.add_assoc, shb_eq.
    apply Forall_cons; [apply afs_ok_stack; unfold ADS_STACK in *; lia|].
    apply Forall_cons; [apply afs_ok_frame; lia|]. apply Forall_cons; [exact afs_ok_shadow|]. apply Forall_nil.
  Qed.

  Definition shN (k : Z) : saddr := SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 58) (ELit k)) (ELit 3)) SHBASE.
  Definition shP (k : Z) : saddr := SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit k)) (ELit 3)) SHBASE.
  Definition POA : saddr := SA (EVar 35) 0.
  Definition kP : list kentry :=
    [KWr POA (ELit 20); KAlign (EVar 35) 8;
     KWord (shP 8) 1 (ELit 0); KWord (shP 12) 1 (ELit 0); KWord (shP 16) 1 (ELit 4); KWord (shP 2) 1 (ELit 0);
     KDisj (shP 8) (ELit 1) POA (ELit 20); KDisj (shP 12) (ELit 1) POA (ELit 20);
     KDisj (shP 16) (ELit 1) POA (ELit 20); KDisj (shP 2) (ELit 1) POA (ELit 20)].
  Definition kN : list kentry :=
    [KWord (SA (EVar 58) 20) 4 (EVar 59); KWord (SA (EVar 58) 24) 4 (EVar 60); KWord (SA (EVar 58) 28) 4 (EVar 61);
     KWord (shN 20) 1 (ELit 0); KWord (shN 24) 1 (ELit 0); KWord (shN 28) 1 (ELit 0);
     KDisj (SA (EVar 58) 20) (ELit 4) POA (ELit 20); KDisj (SA (EVar 58) 24) (ELit 4) POA (ELit 20);
     KDisj (SA (EVar 58) 28) (ELit 4) POA (ELit 20);
     KDisj (shN 20) (ELit 1) POA (ELit 20); KDisj (shN 24) (ELit 1) POA (ELit 20); KDisj (shN 28) (ELit 1) POA (ELit 20)].

  Lemma po_rng : AIMG_TOP <= po /\ po + 20 <= AAPP_HI /\ (po + 20 <= ALOWSH_LO \/ AHI_LO <= po).
  Proof. pose proof DSO as (O1 & O2 & O3). unfold PO_SIZE in *. split; [exact O1|]. split; [exact O3 | exact O2]. Qed.

  Lemma evP : forall R X k, 0 <= k <= 20 ->
    edenot (HLib.Eseed R (Wp ++ X)) (EAlu ALU_ADD (EVar 35) (ELit k)) = Z_to_bv 64 (po + k).
  Proof.
    intros R X k Hk. pose proof po_rng as (T1 & T3 & _).
    cbn [edenot]. change (ev (HLib.Eseed R (Wp ++ X)) 35) with (Z_to_bv 64 po).
    apply w_add; clear - Hk T1 T3; unfold AIMG_TOP, AAPP_HI in *; lia.
  Qed.
  Lemma shP_start : forall R X k, 0 <= k < 20 -> estart (HLib.Eseed R (Wp ++ X)) (shP k) = (po + k) / 8 + SHBASE.
  Proof.
    intros R X k Hk. pose proof po_rng as (T1 & T3 & _). unfold shP.
    apply estart_sh; [apply evP; clear - Hk; lia | clear - Hk T1 T3; unfold AIMG_TOP, AAPP_HI in *; lia].
  Qed.
  Lemma POA_start : forall R X, estart (HLib.Eseed R (Wp ++ X)) POA = po.
  Proof.
    intros R X. pose proof po_rng as (T1 & T3 & _). unfold estart, POA. cbn [a_base a_off edenot].
    change (ev (HLib.Eseed R (Wp ++ X)) 35) with (Z_to_bv 64 po).
    rewrite unsigned_lit by (clear - T1 T3; unfold AIMG_TOP, AAPP_HI in *; lia). clear; lia.
  Qed.
  Lemma po_sh_self : forall k, 0 <= k < 20 -> (po + k) / 8 + SHBASE + 1 <= po \/ po + 20 <= (po + k) / 8 + SHBASE.
  Proof.
    intros k Hk. pose proof po_rng as (T1 & T3 & T2).
    assert (E8 : po = po / 8 * 8) by (clear - DS8; Z.div_mod_to_equations; lia).
    assert (E2 : (po + k) / 8 = po / 8 + k / 8) by (rewrite E8 at 1; rewrite Z.add_comm, Z.div_add by (clear; lia); clear; lia).
    assert (K8 : 0 <= k / 8 < 3) by (split; [apply Z.div_pos; clear - Hk; lia | apply Z.div_lt_upper_bound; clear - Hk; lia]).
    rewrite E2. clear - T1 T2 T3 E8 K8. unfold AIMG_TOP, AAPP_HI, ALOWSH_LO, AHI_LO, SHBASE in *. set (p8 := po / 8) in *. lia.
  Qed.
  Lemma flatP : forall R X k n, 0 <= k -> 0 <= n -> k + n <= 20 -> flat (HLib.Eseed R (Wp ++ X)) (SA (EVar 35) k) n.
  Proof.
    intros R X k n Hk Hn Hkn. pose proof po_rng as (T1 & T3 & _). unfold flat, estart. cbn [a_base a_off edenot].
    change (ev (HLib.Eseed R (Wp ++ X)) 35) with (Z_to_bv 64 po).
    rewrite unsigned_lit by (clear - T1 T3; unfold AIMG_TOP, AAPP_HI in *; lia).
    clear - Hk Hn Hkn T1 T3. unfold AIMG_TOP, AAPP_HI in *. lia.
  Qed.
  Lemma flat_shP : forall R X k, 0 <= k < 20 -> flat (HLib.Eseed R (Wp ++ X)) (shP k) 1.
  Proof.
    intros R X k Hk. pose proof po_rng as (T1 & T3 & _). unfold flat. rewrite shP_start by exact Hk.
    assert (0 <= (po + k) / 8 < 2 ^ 44).
    { split; [apply Z.div_pos; clear - Hk T1; unfold AIMG_TOP in *; lia | apply Z.div_lt_upper_bound; clear - Hk T3; unfold AAPP_HI in *; lia]. }
    unfold SHBASE. clear - H0. lia.
  Qed.

  Lemma kP_ok : forall R X m, Pw m -> mem_inv asegs m -> know_ok asegs (HLib.Eseed R (Wp ++ X)) m kP.
  Proof.
    intros R X m PW MI. destruct (sn_keep m PW MI) as (_ & _ & DA & DW & _).
    pose proof po_rng as (T1 & T3 & _).
    assert (KS : forall k v, 0 <= k < 20 -> 0 <= v < 256 -> shk m (po + k) v ->
                 kentry_ok asegs (HLib.Eseed R (Wp ++ X)) m (KWord (shP k) 1 (ELit v))).
    { intros k v Hk Hv S. apply (kshadow _ m (EAlu ALU_ADD (EVar 35) (ELit k)) (po + k) v (ELit v));
        [ apply evP; clear - Hk; lia | clear - Hk T1 T3; unfold AIMG_TOP, AAPP_HI in *; lia | exact Hv | reflexivity | exact S ]. }
    assert (KD : forall k, 0 <= k < 20 -> kentry_ok asegs (HLib.Eseed R (Wp ++ X)) m (KDisj (shP k) (ELit 1) POA (ELit 20))).
    { intros k Hk. cbn [kentry_ok]. rewrite POA_start, shP_start by exact Hk.
      unfold elenZ. cbn [edenot]. rewrite !unsigned_lit by (clear; lia). pose proof (po_sh_self k Hk) as A. clear - A. lia. }
    assert (S0 : forall k, 0 <= k < 16 -> shk m (po + k) 0).
    { intros k Hk. apply (sh0_of_addressable m po 20 (po + k) DA). change (8 * (20 / 8)) with 16. clear - Hk; lia. }
    assert (S4 : shk m (po + 16) 4).
    { apply (shk_last_of_addressable m po 20 (po + 16) DA); [clear; intros E; discriminate E | change (8 * (20 / 8)) with 16; clear; lia]. }
    unfold know_ok, kP. repeat apply Forall_cons; try apply Forall_nil.
    - eapply kwr_of_wr_at; [exact DW | rewrite POA_start; clear; lia
                           | rewrite POA_start; unfold elenZ; cbn [edenot]; rewrite unsigned_lit by (clear; lia); unfold PO_SIZE; clear; lia
                           | unfold elenZ; cbn [edenot]; rewrite unsigned_lit by (clear; lia); clear; lia].
    - cbn [kentry_ok]. split; [clear; lia|]. cbn [edenot]. change (ev (HLib.Eseed R (Wp ++ X)) 35) with (Z_to_bv 64 po).
      rewrite unsigned_lit by (clear - T1 T3; unfold AIMG_TOP, AAPP_HI in *; lia). exact DS8.
    - apply KS; [clear; lia | clear; lia | apply S0; clear; lia].
    - apply KS; [clear; lia | clear; lia | apply S0; clear; lia].
    - apply KS; [clear; lia | clear; lia | exact S4].
    - apply KS; [clear; lia | clear; lia | apply S0; clear; lia].
    - apply KD; clear; lia.
    - apply KD; clear; lia.
    - apply KD; clear; lia.
    - apply KD; clear; lia.
  Qed.

  Lemma nd_facts : In (nd, (tid, (nk, bw, enc))) ents -> forall m, Pw m ->
    0 < nd /\ nd + 32 <= 2 ^ 47 /\ cell4 ASEGS m (nd + 20) nk /\ cell4 ASEGS m (nd + 24) bw /\ cell4 ASEGS m (nd + 28) enc
    /\ gz m nd 32.
  Proof.
    intros NIN m HP. destruct (sn_keepU m HP) as (U & _ & _ & G3).
    destruct (u_node U nd tid (nk, bw, enc) NIN) as (_ & H1 & H2 & _ & _ & _ & _ & NV & _).
    cbn in NV. destruct NV as (C1 & C2 & C3).
    split; [exact H1|]. split; [exact H2|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. exact (G3 nd tid _ NIN).
  Qed.
  Lemma nd_out : In (nd, (tid, (nk, bw, enc))) ents -> forall k, 0 <= k < 32 ->
    ~ (po <= nd + k < po + 20) /\ ~ (po <= (nd + k) / 8 + SHBASE < po + 20).
  Proof.
    intros NIN k Hk. destruct (UFO (nd + k)) as (O1 & O2 & _).
    { right; right. exists nd. split; [apply in_map_iff; exists (nd, (tid, (nk, bw, enc))); split; [reflexivity | exact NIN] | clear - Hk; lia]. }
    cbn [outside] in O1, O2. destruct O1 as (_ & O1 & _). destruct O2 as (_ & O2 & _). unfold PO_SIZE in *. split; assumption.
  Qed.
  Lemma evN : In (nd, (tid, (nk, bw, enc))) ents -> forall R X k, 0 <= k <= 32 ->
    edenot (HLib.Eseed R (Wp ++ X)) (EAlu ALU_ADD (EVar 58) (ELit k)) = Z_to_bv 64 (nd + k).
  Proof.
    intros NIN R X k Hk. destruct (nd_facts NIN m1 Pw_m1) as (N1 & N2 & _).
    cbn [edenot]. change (ev (HLib.Eseed R (Wp ++ X)) 58) with (Z_to_bv 64 nd).
    apply w_add; clear - Hk N1 N2; lia.
  Qed.
  Lemma ndA_start : In (nd, (tid, (nk, bw, enc))) ents -> forall R X k, 0 <= k <= 32 ->
    estart (HLib.Eseed R (Wp ++ X)) (SA (EVar 58) k) = nd + k.
  Proof.
    intros NIN R X k Hk. destruct (nd_facts NIN m1 Pw_m1) as (N1 & N2 & _). unfold estart. cbn [a_base a_off edenot].
    change (ev (HLib.Eseed R (Wp ++ X)) 58) with (Z_to_bv 64 nd). rewrite unsigned_lit by (clear - N1 N2; lia). reflexivity.
  Qed.
  Lemma shN_start : In (nd, (tid, (nk, bw, enc))) ents -> forall R X k, 0 <= k < 32 ->
    estart (HLib.Eseed R (Wp ++ X)) (shN k) = (nd + k) / 8 + SHBASE.
  Proof.
    intros NIN R X k Hk. destruct (nd_facts NIN m1 Pw_m1) as (N1 & N2 & _). unfold shN.
    apply estart_sh; [apply evN; [exact NIN | clear - Hk; lia] | clear - Hk N1 N2; lia].
  Qed.
  Lemma flatN : In (nd, (tid, (nk, bw, enc))) ents -> forall R X k n, 0 <= k -> 0 <= n -> k + n <= 32 ->
    flat (HLib.Eseed R (Wp ++ X)) (SA (EVar 58) k) n.
  Proof.
    intros NIN R X k n Hk Hn Hkn. destruct (nd_facts NIN m1 Pw_m1) as (N1 & N2 & _). unfold flat.
    rewrite (ndA_start NIN) by (clear - Hk Hn Hkn; lia). clear - Hk Hn Hkn N1 N2. lia.
  Qed.
  Lemma flat_shN : In (nd, (tid, (nk, bw, enc))) ents -> forall R X k, 0 <= k < 32 -> flat (HLib.Eseed R (Wp ++ X)) (shN k) 1.
  Proof.
    intros NIN R X k Hk. destruct (nd_facts NIN m1 Pw_m1) as (N1 & N2 & _). unfold flat. rewrite (shN_start NIN) by exact Hk.
    assert (0 <= (nd + k) / 8 < 2 ^ 44).
    { split; [apply Z.div_pos; clear - Hk N1; lia | apply Z.div_lt_upper_bound; clear - Hk N2; lia]. }
    unfold SHBASE. clear - H0. lia.
  Qed.

  Lemma kN_ok : In (nd, (tid, (nk, bw, enc))) ents -> forall R X m, Pw m -> mem_inv asegs m ->
    know_ok asegs (HLib.Eseed R (Wp ++ X)) m kN.
  Proof.
    intros NIN R X m PW MI. destruct (nd_facts NIN m PW) as (N1 & N2 & C1 & C2 & C3 & GZ).
    assert (KC : forall k v e, 0 <= k -> k + 4 <= 32 -> cell4 ASEGS m (nd + k) v -> edenot (HLib.Eseed R (Wp ++ X)) e = Z_to_bv 64 v ->
                 kentry_ok asegs (HLib.Eseed R (Wp ++ X)) m (KWord (SA (EVar 58) k) 4 e)).
    { intros k v e Hk1 Hk2 C He. apply (kword_of_cell4 _ m _ (nd + k) v e C);
        [apply (ndA_start NIN); clear - Hk1 Hk2; lia | clear - Hk1 N1; lia | clear - Hk2 N2; lia | exact He]. }
    assert (KS : forall k, 0 <= k < 32 -> kentry_ok asegs (HLib.Eseed R (Wp ++ X)) m (KWord (shN k) 1 (ELit 0))).
    { intros k Hk. apply (kshadow0 _ m (EAlu ALU_ADD (EVar 58) (ELit k)) (nd + k));
        [apply (evN NIN); clear - Hk; lia | clear - Hk N1 N2; lia | apply GZ; exact Hk]. }
    assert (KD1 : forall k, 0 <= k -> k + 4 <= 32 ->
                  kentry_ok asegs (HLib.Eseed R (Wp ++ X)) m (KDisj (SA (EVar 58) k) (ELit 4) POA (ELit 20))).
    { intros k Hk1 Hk2. cbn [kentry_ok]. rewrite POA_start, (ndA_start NIN) by (clear - Hk1 Hk2; lia).
      unfold elenZ. cbn [edenot]. rewrite !unsigned_lit by (clear; lia).
      destruct (nd_out NIN k ltac:(clear - Hk1 Hk2; lia)) as [A _]. destruct (nd_out NIN (k + 3) ltac:(clear - Hk1 Hk2; lia)) as [B _].
      clear - A B. lia. }
    assert (KD2 : forall k, 0 <= k < 32 -> kentry_ok asegs (HLib.Eseed R (Wp ++ X)) m (KDisj (shN k) (ELit 1) POA (ELit 20))).
    { intros k Hk. cbn [kentry_ok]. rewrite POA_start, (shN_start NIN) by exact Hk.
      unfold elenZ. cbn [edenot]. rewrite !unsigned_lit by (clear; lia). destruct (nd_out NIN k Hk) as [_ B]. clear - B. lia. }
    unfold know_ok, kN. repeat apply Forall_cons; try apply Forall_nil.
    - apply (KC 20 nk); [clear; lia | clear; lia | exact C1 | reflexivity].
    - apply (KC 24 bw); [clear; lia | clear; lia | exact C2 | reflexivity].
    - apply (KC 28 enc); [clear; lia | clear; lia | exact C3 | reflexivity].
    - apply KS; clear; lia.
    - apply KS; clear; lia.
    - apply KS; clear; lia.
    - apply KD1; clear; lia.
    - apply KD1; clear; lia.
    - apply KD1; clear; lia.
    - apply KD2; clear; lia.
    - apply KD2; clear; lia.
    - apply KD2; clear; lia.
  Qed.

  Lemma SF5 : stack_free_stmt H 5 AFS_FREE_5.
  Proof. destruct (rt_bp_ext H HHbp) as (_ & _ & _ & _ & _ & _ & X & _). exact X. Qed.

  Lemma tabs_wf1 : forall SF ks1, fwcl (wbound Wp) SF = true -> fin (-8192) 0 (fkeys SF ++ ks1) = true -> tabs_wf Wp [tS SF ks1].
  Proof.
    intros SF ks1 C1 F1.
    pose proof sn_wins as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8). pose proof tab_vals as (T1 & T2 & T3 & T4).
    pose proof sn_ranges as (R1 & _). pose proof sn_vals as (V1 & V2 & _).
    split.
    - repeat constructor; cbn [tb tB tlo thi ttbl tks tS]; try reflexivity; try assumption; unfold SHBASE in *; lia.
    - intros t1 t2 H1 H2 Hb. destruct H1 as [<-|[]]; destruct H2 as [<-|[]]. vm_compute in Hb. discriminate Hb.
  Qed.
  Lemma Pw_step1 : forall SF ks1 m m', Pw m -> munch (winsT [tS SF ks1]) m m' -> wmono asegs m m' -> mem_inv asegs m' -> Pw m'.
  Proof.
    intros SF ks1 m m' HP MU WM _. eapply Pw_ext; [exact HP | exact MU | exact WM |].
    unfold winsT. cbn [map tB tlo thi tS]. apply Forall_cons; [apply in_stk; clear; lia | apply Forall_nil].
  Qed.
  Lemma tabs_ok1 : forall m SF ks1, Pw m -> mem_inv asegs m -> ftbl Wp spz m SF -> fin (-8192) 0 ks1 = true ->
    tabs_ok Wp m [tS SF ks1].
  Proof.
    intros m SF ks1 HP MI H1 F1. destruct (sn_keep m HP MI) as (_ & _ & _ & _ & _ & _ & _ & ST & _).
    apply Forall_cons; [split; [exact H1 | exact (wk_stk m ks1 ST F1)] | apply Forall_nil].
  Qed.
  Lemma RFS_L_step1 : forall SF ks1 m m', as_RFS H LF m -> munch (winsT [tS SF ks1]) m m' -> wmono asegs m m' -> as_RFS H LF m'.
  Proof.
    intros SF ks1 m m' RF MU WM. eapply (ah_RFS_frame H HHb); [exact RF | exact MU | exact WM |].
    pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    unfold winsT. cbn [map tB tlo thi tS]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd].
    clear - R2 R9 R12. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, ADS_STACK in *. lia.
  Qed.

  Definition nopo (iv : Z * Z) : Prop :=
    (spz - 16384 <= fst iv /\ snd iv <= spz) \/ (ff <= fst iv /\ snd iv <= ff + 1024)
    \/ (sh ff <= fst iv /\ snd iv <= sh ff + 128) \/ (fp <= fst iv /\ snd iv <= fp + 1).
  Lemma po_cells_keep : forall W m m' k cs, munch W m m' -> wmono asegs m m' -> Forall nopo W ->
    0 <= k -> k + Z.of_nat (cells_size cs) <= 20 -> rw_cells asegs m (po + k) cs -> rw_cells asegs m' (po + k) cs.
  Proof.
    intros W m m' k cs MU WM FW Hk Hn RC. eapply rw_cells_transport; [exact RC | exact MU | exact WM |].
    pose proof (SPOBJ po PO_SIZE ltac:(clear; tauto)) as SD. pose proof po_sh_wins as PS. rewrite shb_eq in PS.
    pose proof FFDS as FD. pose proof FPDS as PD.
    set (n := Z.of_nat (cells_size cs)) in *. assert (Hn0 : 0 <= n) by (unfold n; clear; lia).
    clear - FW Hk Hn Hn0 SD PS FD PD. unfold PO_SIZE, ADS_STACK in *.
    induction FW as [|[x y] W' [A|[A|[A|A]]] FW IH]; cbn [disjoint_from fst snd] in *; [exact I | | | |];
      (split; [clear IH FW | exact IH]).
    - clear - A Hk Hn Hn0 SD. lia.
    - clear - A Hk Hn Hn0 FD. lia.
    - clear - A Hk Hn Hn0 PS. lia.
    - clear - A Hk Hn Hn0 PD. lia.
  Qed.

  Definition po4 (m : mem) : Prop :=
    rw_cells asegs m (po + 8) [C4 (Z_to_bv 64 nk)] /\ rw_cells asegs m (po + 12) [C4 (Z_to_bv 64 bw)]
    /\ rw_cells asegs m (po + 16) [C4 (Z_to_bv 64 enc)] /\ rw_cells asegs m (po + 2) [C2 (Z_to_bv 64 (sn_nw bw))].
  Lemma po4_keep : forall W m m', munch W m m' -> wmono asegs m m' -> Forall nopo W -> po4 m -> po4 m'.
  Proof.
    intros W m m' MU WM FW (C1 & C2 & C3 & C4).
    split; [apply (po_cells_keep W m m' 8 _ MU WM FW); [clear; lia | cbn; clear; lia | exact C1]|].
    split; [apply (po_cells_keep W m m' 12 _ MU WM FW); [clear; lia | cbn; clear; lia | exact C2]|].
    split; [apply (po_cells_keep W m m' 16 _ MU WM FW); [clear; lia | cbn; clear; lia | exact C3]|].
    apply (po_cells_keep W m m' 2 _ MU WM FW); [clear; lia | cbn; clear; lia | exact C4].
  Qed.
  Lemma nopo_w3 : forall SF FT HT ks1 ks2 ks3, Forall nopo (winsT [tS SF ks1; tF FT ks2; tH HT ks3]).
  Proof.
    intros SF FT HT ks1 ks2 ks3. unfold winsT. cbn [map tB tlo thi tS tF tH]. rewrite !Z.add_assoc, shb_eq.
    apply Forall_cons; [left; cbn [fst snd]; clear; lia|]. apply Forall_cons; [right; left; cbn [fst snd]; clear; lia|].
    apply Forall_cons; [right; right; left; cbn [fst snd]; clear; lia | apply Forall_nil].
  Qed.
  Lemma nopo_w1 : forall SF ks1, Forall nopo (winsT [tS SF ks1]).
  Proof.
    intros SF ks1. unfold winsT. cbn [map tB tlo thi tS].
    apply Forall_cons; [left; cbn [fst snd]; clear; lia | apply Forall_nil].
  Qed.
  Lemma nopo_sf : forall spa, spz - 16384 + AFS_STACK <= spa <= spz ->
    Forall nopo [(spa - AFS_STACK, spa); (fp, fp + 1); (sh ff, sh ff + fshn 4)].
  Proof.
    intros spa Hs. change (fshn 4) with 128.
    apply Forall_cons; [left; cbn [fst snd]; clear - Hs; lia|]. apply Forall_cons; [right; right; right; cbn [fst snd]; clear; lia|].
    apply Forall_cons; [right; right; left; cbn [fst snd]; clear; lia | apply Forall_nil].
  Qed.
  Lemma inPW_sf : forall spa, spz - 16384 + AFS_STACK <= spa <= spz ->
    Forall inPW [(spa - AFS_STACK, spa); (fp, fp + 1); (sh ff, sh ff + fshn 4)].
  Proof.
    intros spa Hs. change (fshn 4) with 128.
    apply Forall_cons; [apply in_stk; clear - Hs; lia|]. apply Forall_cons; [apply in_fl; clear; lia|].
    apply Forall_cons; [apply in_sh; clear; lia | apply Forall_nil].
  Qed.

  Lemma sf_stack_keep : forall d T m m', - 8192 + AFS_STACK <= d <= 0 -> fin d 0 (fkeys T) = true ->
    ftbl Wp spz m T -> munch [(spz + d - AFS_STACK, spz + d); (fp, fp + 1); (sh ff, sh ff + fshn 4)] m m' -> wmono asegs m m' ->
    ftbl Wp spz m' T.
  Proof.
    intros d T m m' Hs HF HT MU WM. eapply (ftbl_munch Wp spz m m' T _ d 0); [exact HT | exact MU | exact WM | exact HF |].
    pose proof sn_wins as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8). rewrite shb_eq in W3. change (fshn 4) with 128.
    cbn [disjoint_from]. clear - Hs W3 W4. unfold AFS_STACK in *. lia.
  Qed.

  Definition sn_Pok : machine_state -> Prop :=
    fun ms => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ Pw m' /\ as_RFS H LF m'
      /\ rw_cells asegs m' (po + 8) [C4 (Z_to_bv 64 nk)] /\ rw_cells asegs m' (po + 12) [C4 (Z_to_bv 64 bw)]
      /\ rw_cells asegs m' (po + 16) [C4 (Z_to_bv 64 enc)] /\ rw_cells asegs m' (po + 2) [C2 (Z_to_bv 64 (sn_nw bw))].

  Lemma sn_fin_ok : forall R m, rfull R ->
    PropExec.getr R 1 = ra -> PropExec.getr R 2 = sp -> PropExec.getr R 3 = gp -> PropExec.getr R 4 = tp ->
    PropExec.getr R 8 = s0 -> PropExec.getr R 9 = s1 -> PropExec.getr R 18 = s2 -> PropExec.getr R 19 = s3 ->
    PropExec.getr R 20 = s4 -> PropExec.getr R 21 = s5 -> PropExec.getr R 22 = s6 -> PropExec.getr R 23 = s7 ->
    PropExec.getr R 24 = s8 -> PropExec.getr R 25 = s9 -> PropExec.getr R 26 = s10 -> PropExec.getr R 27 = s11 ->
    PropExec.getr R 10 = Z_to_bv 64 0 ->
    Pw m -> mem_inv asegs m -> as_RFS H LF m -> po4 m ->
    sn_Pok (MS R F (ret_pc (PropExec.getr R 1)) fc None m (seg_rom asegs)).
  Proof.
    intros R m RF K1 K2 K3 K4 K8 K9 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K10 HP MI RFm (C1 & C2 & C3 & C4).
    rewrite (MS_full_eq R F _ fc m _ RF).
    rewrite K1, K2, K3, K4, K8, K9, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27, K10.
    do 15 eexists. split; [reflexivity|]. split; [exact MI|]. split; [exact HP|]. split; [exact RFm|].
    split; [exact C1|]. split; [exact C2|]. split; [exact C3 | exact C4].
  Qed.

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

End Sn.
