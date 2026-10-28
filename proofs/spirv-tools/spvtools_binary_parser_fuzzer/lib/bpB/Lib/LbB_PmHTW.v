From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_Conv LbB_MILB LbB_PrsStmt LbB_HKit LbB_HStKit LbB_PmExit LbB_PiStmt LbB_PiInit LbB_PmTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_RwStm LbB_PmHTK LbB_PmMagRS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoBP LbB_PmMagK LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_HdrGet LbB_PmHTS LbB_PmHT1 LbB_PmHTail LbB_PmMagW LbB_FSlots.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_TablImg.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require ContLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BG_MallocLarge2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac htw_csz := repeat match goal with |- context [Z.of_nat (cells_size ?cs)] =>
  let k := eval vm_compute in (Z.of_nat (cells_size cs)) in change (Z.of_nat (cells_size cs)) with k end.

Lemma htw_nth_b8 : forall (l : list Z) i, (i < length l)%nat ->
  nth_error (map (Z_to_bv 8) l) i = Some (Z_to_bv 8 (nth i l 1)).
Proof.
  induction l as [|z l IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; cbn; [reflexivity | apply IH; cbn in Hi; lia].
Qed.

Lemma htw_u8sub : forall m A (l : list byte) k n, u8arr asegs m A l -> (k + n <= length l)%nat ->
  u8arr asegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m A l k n U L.
  rewrite <- (firstn_skipn k l) in U. apply BsDepotInv.u8arr_app in U as [_ U].
  rewrite firstn_length_le in U by lia.
  rewrite <- (firstn_skipn n (skipn k l)) in U. apply BsDepotInv.u8arr_app in U as [U _]. exact U.
Qed.

Lemma htw_shad : forall ff m M' W, 0 <= ff -> ff <= 2 ^ 47 -> bp_shad ff [14; 20; 21]%nat m ->
  munch W m M' -> wmono asegs m M' ->
  (forall i, 0 <= i < 476 -> (i < 278 \/ 282 <= i) -> forall iv, In iv W -> ~ (fst iv <= sh ff + i < snd iv)) ->
  (forall i, 278 <= i < 282 -> fldA M' (sh ff + i) 1 0) -> bp_shad ff [14; 16; 20; 21]%nat M'.
Proof.
  intros ff m M' W H0 H47 SH MU WM OUT F0. unfold bp_shad in *.
  destruct SH as [(B0 & B1 & B) WR].
  assert (L1 : length (wo_sh [14; 20; 21]%nat) = 476%nat) by (vm_compute; reflexivity).
  assert (L2 : length (wo_sh [14; 16; 20; 21]%nat) = 476%nat) by (vm_compute; reflexivity).
  assert (CHK : forallb (fun i => orb (andb (Nat.leb 278 i) (Nat.ltb i 282))
                  (Z.eqb (nth i (wo_sh [14; 16; 20; 21]%nat) 1) (nth i (wo_sh [14; 20; 21]%nat) 1))) (seq 0 476) = true)
    by (vm_compute; reflexivity).
  assert (CHK0 : forallb (fun i => Z.eqb (nth i (wo_sh [14; 16; 20; 21]%nat) 1) 0) (seq 278 4) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in CHK, CHK0.
  split.
  - split; [exact B0 |]. split; [rewrite length_map, L2; rewrite length_map, L1 in B1; exact B1 |].
    intros i Hi. rewrite length_map, L2 in Hi.
    rewrite (htw_nth_b8 _ i ltac:(rewrite L2; lia)).
    destruct (andb (Nat.leb 278 i) (Nat.ltb i 282)) eqn:IN.
    + apply andb_prop in IN as [I1 I2]. apply Nat.leb_le in I1. apply Nat.ltb_lt in I2.
      pose proof (CHK0 i ltac:(apply in_seq; lia)) as C0. apply Z.eqb_eq in C0. rewrite C0.
      pose proof (F0 (Z.of_nat i) ltac:(lia)) as Fi.
      unfold fldA, fld in Fi. change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in Fi.
      apply LbB_TablImg.mrd_of_rdn1. unfold wa. exact Fi.
    + pose proof (CHK i ltac:(apply in_seq; lia)) as Ci. rewrite IN in Ci. cbn [orb] in Ci. apply Z.eqb_eq in Ci.
      rewrite Ci, <- (htw_nth_b8 _ i ltac:(rewrite L1; lia)).
      rewrite <- (B i ltac:(rewrite length_map, L1; lia)). unfold mrd, wa.
      assert (NI : Z.of_nat i < 278 \/ 282 <= Z.of_nat i).
      { apply Bool.andb_false_iff in IN as [IN|IN]; [apply Nat.leb_gt in IN | apply Nat.ltb_ge in IN]; lia. }
      rewrite (munch_at W m M' (sh ff + Z.of_nat i) MU).
      * reflexivity.
      * unfold sh in *. rewrite ASHADOW_BASE_val in *. pose proof (Z.div_pos ff 8 ltac:(lia) ltac:(lia)).
        assert (ff / 8 <= ff) by (apply Z.div_le_upper_bound; lia). lia.
      * intros iv Hiv. exact (OUT (Z.of_nat i) ltac:(lia) NI iv Hiv).
  - rewrite length_map, L2. rewrite length_map, L1 in WR. exact (wr_at_wmono _ _ _ _ WR WM).
Qed.

Section HTW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Lemma htw_keep : forall e ff fp XSc s LB LBs m m1 w c R R1,
    wpre H e -> winv H e ff fp XSc s LB m -> bp_slots H e ff m -> bp_shad ff [14; 20; 21]%nat m ->
    bp_rc H e ff R -> bp_rg ff R -> bp_wl H e ff w ->
    bp_ploop H ((6, ff, fp) :: w_LF e) e ff w s LB LBs m c ->
    munch (HT_W (sh ff) (wS1 e) (ff + 2224)) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    (forall i, 278 <= i < 282 -> fldA m1 (sh ff + i) 1 0) ->
    (forall r, In r HT_KEEP -> getr R1 r = getr R r) ->
    winv H e ff fp XSc s LB m1 /\ bp_slots H e ff m1 /\ bp_shad ff [14; 16; 20; 21]%nat m1
    /\ bp_rc H e ff R1 /\ bp_rg ff R1 /\ bp_ploop H ((6, ff, fp) :: w_LF e) e ff w s LB LBs m1 c.
  Proof.
    intros e ff fp XSc s LB LBs m m1 w c R R1 HP HI SL SH RC RG WL PL MU WM MI1 F0 KEEP.
    pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    clear G1 G14 G6.
    set (W := HT_W (sh ff) (wS1 e) (ff + 2224)) in *.
    assert (WE : W = [(sh ff + 278, sh ff + 282); (wS1 e - 64, wS1 e); (ff + 2224, ff + 2224 + 32)]).
    { subst W. unfold HT_W, HT_WIN, HG_STACK. reflexivity. }
    assert (ST1 : stk asegs m1 (w_lo e) (wSP e)).
    { apply (stk_keepW W m m1 _ _ (winv_stk H _ _ _ _ _ _ _ HI) MU WM). unfold AIMG_TOP. lia. }
    assert (FW : Forall (wwin H e ff) W).
    { rewrite WE. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
        unfold wwin; cbn [fst snd]; unfold WO_SAVED, WO_FLAGP; lia. }
    assert (HI1 : winv H e ff fp XSc s LB m1) by exact (winv_munch H HH e ff fp XSc s LB m m1 W HP HI MU WM MI1 ST1 FW).
    assert (FL : Forall (bp_flw H e ff) W).
    { rewrite WE. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
        unfold bp_flw; cbn [fst snd]; unfold WO_FLAGP; lia. }
    pose proof WL as (Wp & Wc & Ww & Wn & _).
    split; [exact HI1 |].
    split.
    { destruct SL as (S1 & S2 & S3).
      split; [|split]; (eapply rw_cells_transport; [eassumption | exact MU | exact WM |]);
        rewrite WE; htw_csz; cbn [disjoint_from]; repeat split; lia. }
    split.
    { apply (htw_shad ff m m1 W ltac:(lia) ltac:(lia) SH MU WM); [| exact F0].
      intros i Hi Hn iv Hiv. rewrite WE in Hiv. cbn [In] in Hiv.
      destruct Hiv as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia. }
    split.
    { destruct RC as (Rc2 & Rc3 & Rc4 & Rc8 & Rc9 & Rc19 & Rc20). unfold bp_rc.
      repeat match goal with |- _ /\ _ => split end; (eapply eq_trans; [apply KEEP; htin | assumption]). }
    split.
    { destruct RG as (M18 & M21 & M22 & M23 & M24 & M25 & M26 & M27). unfold bp_rg.
      repeat match goal with |- _ /\ _ => split end; (eapply eq_trans; [apply KEEP; htin | assumption]). }
    destruct PL as (ee & PK & PP & PH & AL & (B1 & B2 & BW & BN) & CC).
    assert (PP1 : bp_pp H w LB LBs m1 c) by exact (bp_pp_keepW H HH e ff fp XSc w s LB LBs m m1 c W HP HI WL PP MU WM FL).
    exists ee. split; [exact (bp_piw H HH e ff fp XSc s LB m1 w LBs c HP HI1 WL PP1 BW) |].
    split; [exact PP1 |]. split; [exact PH |]. split; [exact AL |].
    split.
    - split; [| split; [| split; [exact BW | exact BN]]].
      + apply (ht_fld_munch W m m1 _ _ _ B1 MU); [rewrite WE; cbn [disjoint_from]; change (Z.of_nat 8) with 8; repeat split; lia | lia | lia].
      + apply (ht_fld_munch W m m1 _ _ _ B2 MU); [rewrite WE; cbn [disjoint_from]; change (Z.of_nat 8) with 8; repeat split; lia | lia | lia].
    - rewrite Wc in *. eapply rw_cells_transport; [exact CC | exact MU | exact WM |].
      rewrite WE; htw_csz; cbn [disjoint_from]; repeat split; lia.
  Qed.

  Lemma bp_kgood_of : hdr_get_stmt -> forall e ff fp Q mo0,
    bp_kloop H e ff fp Q mo0 -> bp_kd4 H e ff fp Q mo0 -> bp_kgood H e ff fp Q mo0.
  Proof.
    intros HG e ff fp Q mo0 K0 KN.
    unfold bp_kgood, bp_hdr0. intros s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RG WL PL.
    pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    pose proof (wpre_geo H e HP) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof HI as (RFS & FF & RH & AC & MI & S0 & RA & ER & ST & SV & SF & WF & WFP & XP & FS & LVI).
    pose proof PL as (ee & PK & PP & PH & AL & (B1 & B2 & _ & BN) & CC).
    pose proof PP as (PR & PSH & HC & HU & HD & SOWN & LBOWN & CWR).
    pose proof WL as (Wp & Wc & Ww & Wn & WLB & Ws0 & Wlo & WB & Wshi).
    pose proof RC as (Rc2 & Rc3 & Rc4 & Rc8 & Rc9 & Rc19 & Rc20).
    pose proof RG as (M18 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
    pose proof SL as (SL1 & SL2 & SL3).
    pose proof SH as [_ SHW]. rewrite length_map in SHW.
    replace (Z.of_nat (length (wo_sh [14; 20; 21]%nat))) with 476 in SHW by (vm_compute; reflexivity).
    pose proof PH as PH'. unfold pi_hdr in PH'. destruct PH' as (_ & _ & _ & _ & PE & _ & PE01 & _).
    cbn [bp_st5 st_endian] in PE.
    assert (SP : bv_unsigned (wz (wS1 e)) = wS1 e) by (apply wz_unsigned; clear - G10 G11 G12 G13 G15; lia).
    assert (SH216 : sh (ff + 1728) = sh ff + 216).
    { unfold sh. assert (E : ff + 1728 = (ff / 8 + 216) * 8) by (clear - G1; Z.div_mod_to_equations; lia).
      rewrite E, Z.div_mul by lia. lia. }
    assert (SH2224 : sh (ff + 2224) = sh ff + 278).
    { unfold sh. assert (E : ff + 2224 = (ff / 8 + 278) * 8) by (clear - G1; Z.div_mod_to_equations; lia).
      rewrite E, Z.div_mul by lia. lia. }
    assert (MB8 : (ff + 1728) mod 8 = 0) by (clear - G1; Z.div_mod_to_equations; lia).
    assert (MH8 : (ff + 2224) mod 8 = 0) by (clear - G1; Z.div_mod_to_equations; lia).
    assert (MS16 : wS1 e mod 16 = 0) by (clear - G14; Z.div_mod_to_equations; lia).
    clear G14.
    assert (AOK : forall iv, wwin H e ff iv -> aconst_ok iv).
    { intros iv Wv. destruct (wwin_ok H e ff fp XSc iv FF G10 ltac:(clear - G11 G12; unfold WO_SAVED; lia)
        ltac:(clear - G13; unfold AAPP_HI; lia) Wv) as (_ & _ & AO & _). exact AO. }
    pose proof PK as [_ _ _ _ _ _ _ _ WOK _ _ _].
    destruct WOK as (pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh).
    rewrite WLB, Ww in Hin. rewrite Wn in Rg. rewrite Ww in W0, W16, Whi. rewrite Ww, Wn in Wdef, Wsh.
    assert (HinLB : In (pw, w_words e, k) LB).
    { destruct SOWN as (PERM & _). rewrite WLB in PERM.
      apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. left. exact Hin. }
    pose proof (blk_range H HH s LB m pw (w_words e) k RH HinLB) as (BR1 & BR2 & BR3 & BR4 & BR5 & _ & BR7).
    pose proof (blk_disj_reg H HH e ff fp XSc s LB m (sh ff + 278, sh ff + 282) pw (w_words e) k HP HI
                  ltac:(cbn [fst snd]; right; left; clear - G7 G8; lia) HinLB) as (DS1 & DS2).
    pose proof (blk_disj_reg H HH e ff fp XSc s LB m (ff + 2224, ff + 2256) pw (w_words e) k HP HI
                  ltac:(cbn [fst snd]; left; clear - G2; unfold WO_FLAGP; lia) HinLB) as (DH1 & _).
    cbn [fst snd] in DS1, DS2, DH1.
    assert (MW4 : w_words e mod 4 = 0) by (clear - W16; Z.div_mod_to_equations; lia).
    clear W16 BR2.
    assert (NSH : nsh (4 * w_n e) <= nsh k) by (unfold nsh; apply Z.div_le_mono; lia).
    assert (X25 : disjoint_from (HT_WIN (sh ff)) (w_words e) 20)
      by (cbn [HT_WIN disjoint_from]; clear - DS1 Rg BN; split; [lia | exact I]).
    assert (X27 : disjoint_from (HT_WIN (sh ff)) (sh (w_words e)) (nsh (4 * w_n e)))
      by (cbn [HT_WIN disjoint_from]; clear - DS2 NSH; split; [lia | exact I]).
    assert (X29 : ff + 2224 + 32 <= w_words e \/ w_words e + 20 <= ff + 2224) by (clear - DH1 Rg BN; lia).
    clear DS1 DS2 DH1.
    assert (MD : forall j, 0 <= j < 5 -> exists v, fld ASEGS m (w_words e + 4 * j) 4 v).
    { intros j Hj.
      assert (Dj : mdef m (w_words e + 4 * j) 4)
        by (apply (ContLib.mdef_sub m (w_words e) (4 * w_n e)); [exact Wdef | clear - Hj; lia | clear - Hj Rg BN; lia]).
      destruct (TablLib.mdef4_fld ASEGS m (w_words e + 4 * j) Dj ltac:(clear - Hj W0; lia) ltac:(clear - Hj Rg BN Whi; lia))
        as (v & _ & Fv).
      exists v. exact Fv. }
    destruct (MD 0 ltac:(lia)) as (v0 & F0). destruct (MD 1 ltac:(lia)) as (v1 & F1).
    destruct (MD 2 ltac:(lia)) as (v2 & F2). destruct (MD 3 ltac:(lia)) as (v3 & F3).
    destruct (MD 4 ltac:(lia)) as (v4 & F4).
    assert (A4 : addressable m (ff + 1728) 16).
    { unfold addressable. split; [lia |]. unfold SHAD. split; [clear - G2; lia |]. split; [exact MB8 |].
      rewrite SH216.
      pose proof (htw_u8sub m (sh ff) (map (Z_to_bv 8) (wo_sh [14; 20; 21]%nat)) 216 2 SH
                    ltac:(rewrite length_map; apply Nat.leb_le; vm_compute; reflexivity)) as U.
      rewrite skipn_map, firstn_map in U.
      replace (firstn 2 (skipn 216 (wo_sh [14; 20; 21]%nat))) with [0; 0] in U by (vm_compute; reflexivity).
      replace (shadow_of 16) with (map (Z_to_bv 8) [0; 0]) by reflexivity.
      change (Z.of_nat 216) with 216 in U. exact U. }
    assert (A23 : addressable m (w_words e) (4 * w_n e)).
    { unfold addressable. split; [clear - BN; lia |]. destruct Wsh as (S0' & S8 & U). unfold SHAD.
      split; [exact S0' |]. split; [exact S8 |].
      unfold cc_gen in U. apply BsDepotInv.u8arr_app in U as [U _]. exact U. }
    assert (A22 : forall i, 0 <= i < 5 -> fld ASEGS m (w_words e + 4 * i) 4 (Znth i [v0; v1; v2; v3; v4])).
    { intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) as [-> | [-> | [-> | [-> | ->]]]] by lia;
        [exact F0 | exact F1 | exact F2 | exact F3 | exact F4]. }
    assert (A11 : wr_at asegs m (ff + 2224) 32)
      by (apply (wr_at_sub m ff WO_FLAGP); [exact WF | lia | unfold WO_FLAGP; lia | lia]).
    assert (A12 : aconst_ok (ff + 2224, ff + 2224 + 32))
      by (apply AOK; unfold wwin; cbn [fst snd]; right; left; clear - G2; unfold WO_FLAGP; lia).
    assert (B2' : fld ASEGS m (ff + 1728 + 8) 8 (w_n e)) by (replace (ff + 1728 + 8) with (ff + 1736) by lia; exact B2).
    assert (D26 : disjoint_from (HT_WIN (sh ff)) (sh (ff + 1728)) (nsh 16)).
    { rewrite SH216. change (nsh 16) with 2. cbn [HT_WIN disjoint_from]. split; [lia | exact I]. }
    clear G1.
    pose proof (pm_htail H HH HG s msF mo R F fc m (ff + 3456) (sh ff) (wS1 e) (ff + 1728) ee (ff + 2224)
                  (w_words e) (w_n e) (w_lo e) [v0; v1; v2; v3; v4] Q) as PT.
    rewrite Rc2, SP in PT. apply PT; clear PT.
    - exact KR.
    - rewrite VIS. reflexivity.
    - exact RF.
    - exact MI.
    - exact AC.
    - unfold ht_a_pre.
      split; [exact Rc9 |]. split; [exact M18 |]. split; [exact Rc19 |]. split; [exact M25 |].
      split.
      { pose proof (pr_state _ _ _ _ _ _ _ PR) as PST. pose proof (sr_w5 _ _ _ _ _ _ _ PST) as EN.
        unfold fldA, fld. replace (ff + 3456 + 88) with (pw_p H w + ST_OFF + 40) by (rewrite Wp; unfold ST_OFF; lia).
        rewrite <- PE. exact (proj2 EN). }
      split.
      { pose proof (proj1 (rw_cells_app asegs m (wS1 e + 24) [C8 (wz (w_words e)); C8 (wz (w_n e)); C8 (wz ASHADOW_BASE)]
                      [C8 (wz (ff + 2224)); C8 (wz (ff + 3376))]) SL2) as (_ & SL2b).
        pose proof (proj1 (rw_cells_app asegs m _ [C8 (wz (ff + 2224))] [C8 (wz (ff + 3376))]) SL2b) as (SL2c & _).
        pose proof (rdn_of_rw_C8 m _ _ SL2c) as RDS.
        unfold fldA, fld.
        replace (wS1 e + 48) with (wS1 e + 24 + Z.of_nat (cells_size [C8 (wz (w_words e)); C8 (wz (w_n e)); C8 (wz ASHADOW_BASE)]))
          by (htw_csz; lia).
        exact RDS. }
      split; [lia |]. split; [lia |].
      split; [apply (wr_at_sub m (sh ff) 476); [exact SHW | lia | lia | lia] |].
      repeat split; lia.
    - assert (A14 : (0x6e8000 <= ff + 2224 /\ ff + 2224 + 32 <= 0x7fff7000)
                    \/ (0x10007fff8000 <= ff + 2224 /\ ff + 2224 + 32 <= 2 ^ 47)).
      { clear - G4 G5 G6 G16. destruct G6 as [G6|G6]; unfold aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP, AFS_SIZE in *; lia. }
      unfold ht_hg0.
      repeat match goal with |- _ /\ _ => split end;
        first [ assumption | reflexivity
              | (unfold AIMG_TOP, HG_STACK, LbB_TablStmt.TL_STACK, AAPP_HI; cbn [HT_WIN disjoint_from]; repeat split; lia) ].
    - destruct ST as (T0 & T1 & T). split; [lia |]. split; [lia |]. intros a Ha. apply T. lia.
    - exact G10.
    - unfold HG_STACK. lia.
    - lia.
    - lia.
    - unfold HT_WIN. constructor; [| constructor]. apply AOK. unfold wwin. cbn [fst snd]. right. right. lia.
    - cbn [HT_WIN disjoint_from]. repeat split; lia.
    - cbn [disjoint_from]. unfold HG_STACK. repeat split; lia.
    - pose proof (pr_hdrfn _ _ _ _ _ _ _ PR) as HF. rewrite Wp in HF. exact HF.
    - unfold HT_W, HT_WIN, HG_STACK. cbn [app disjoint_from]. repeat split; lia.
    - intros msF1 mo1 R1 m1 KR1 MP1 VIS1 RF1 RA1 R10 R17 KEEP MU WM MI1 STK1 AC1 F8 F9 F10 F11 HGP.
      assert (FA : forall i, 278 <= i < 282 -> fldA m1 (sh ff + i) 1 0).
      { intros i Hi. assert (i = 278 \/ i = 279 \/ i = 280 \/ i = 281) as [-> | [-> | [-> | ->]]] by lia; assumption. }
      destruct (htw_keep e ff fp XSc s LB LBs m m1 w c R R1 HP HI SL SH RC RG WL PL MU WM MI1 FA KEEP)
        as (HI1 & SL1' & SH1 & RC1 & RG1 & PL1).
      unfold bp_kloop, bp_hdr0 in K0.
      apply (K0 s LB LBs m1 mo1 msF1 R1 F fc XSc w c); [rewrite VIS1; reflexivity | exact RF1 | exact FZ | exact KR1
        | exact (ah_mpres_trans H HH _ _ _ MP MP1) | exact HP | exact HI1 | exact SL1' | exact SH1 | exact RC1 | exact RG1
        | exact WL | exact PL1].
    - intros msF1 mo1 R1 m1 KR1 MP1 VIS1 RF1 RA1 R10 KEEP MU WM MI1 STK1 AC1 F8 F9 F10 F11.
      assert (FA : forall i, 278 <= i < 282 -> fldA m1 (sh ff + i) 1 0).
      { intros i Hi. assert (i = 278 \/ i = 279 \/ i = 280 \/ i = 281) as [-> | [-> | [-> | ->]]] by lia; assumption. }
      destruct (htw_keep e ff fp XSc s LB LBs m m1 w c R R1 HP HI SL SH RC RG WL PL MU WM MI1 FA KEEP)
        as (HI1 & SL1' & SH1 & RC1 & RG1 & PL1).
      unfold bp_kd4, bp_hdr0 in KN.
      apply (KN s LB LBs m1 mo1 msF1 R1 F fc XSc w c); [rewrite VIS1; reflexivity | exact RF1 | exact FZ | exact KR1
        | exact (ah_mpres_trans H HH _ _ _ MP MP1) | exact HP | exact HI1 | exact SL1' | exact SH1 | exact RC1
        | split; [exact RG1 | exact R10] | exact WL | exact PL1].
  Qed.
End HTW.
