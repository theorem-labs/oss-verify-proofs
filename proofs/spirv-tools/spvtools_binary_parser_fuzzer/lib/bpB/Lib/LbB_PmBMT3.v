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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_Conv LbB_MILB LbB_PrsStmt LbB_HKit LbB_HStKit LbB_PmExit LbB_PiStmt LbB_PiInit LbB_PmTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_RwStm LbB_PmHTK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoBP LbB_Own LbB_RwStm LbB_PmHTK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHdr2 LbB_DStat LbB_DiagStmt LbB_PmBMRS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHex LbB_PmBMRS LbB_PmBMT LbB_WoDiagP LbB_WoDiagC LbB_WoDiagC2 LbB_WoShK LbB_PmMagK LbB_PmMagW LbB_PmHdr2 LbB_TablStmt LbB_TablImg LbB_PmSL.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Lemma b3_fld_of_cells4 : forall m a z, rw_cells asegs m a [C4 (Z_to_bv 64 z)] -> 0 <= a -> fldA m a 4 z.
Proof.
  intros m a z Hc Ha. unfold fldA, fld.
  pose proof (rw_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- rdn_of_ov. exact RD.
Qed.


Ltac b3_inl := cbn [In]; repeat (first [left; reflexivity | right]).

Ltac b3_kreg :=
  first
    [ assumption
    | match goal with |- _ ?R' ?n = _ =>
        match goal with K : forall r, In r _ -> _ R' r = _ ?R r |- _ =>
          transitivity (PropExec.getr R n); [exact (K n ltac:(b3_inl)) |
            first [ assumption
                  | match goal with Hr : _ R n = _ |- _ => etransitivity; [exact Hr | apply bv_eq; vm_compute; reflexivity] end ] ]
        end
      end
    | match goal with |- _ ?R' ?n = _ =>
        match goal with Hr : _ R' n = _ |- _ => etransitivity; [exact Hr | apply bv_eq; vm_compute; reflexivity] end
      end ].
Ltac b3_zn :=
  repeat match goal with |- context [Z.of_nat ?n] =>
    let z := eval vm_compute in (Z.of_nat n) in progress change (Z.of_nat n) with z end.

Lemma b3_len1 : length (wo_sh [14; 15; 20; 21]%nat) = 476%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma b3_cs : cstrA 148000 2.
Proof.
  assert (G : existsb (fun g => let '(b, sz, _) := g in (b =? 148000) && (sz =? 3)) aglobals = true) by (vm_compute; reflexivity).
  apply existsb_exists in G as ([[b sz] rz] & Hg & E).
  apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1, E2. subst b sz.
  apply (cstrA_of 148000 2 148000 3 rz); [vm_compute; reflexivity | exact Hg | lia | lia | lia].
Qed.

Ltac b3_wb Gs :=
  match goal with
  | |- fldA ?M (sh ?f + ?k) 1 ?v =>
      let N := eval vm_compute in (ASHADOW_BASE + k) in
      replace (sh f + k) with (4 * (f / 32) + N) by (rewrite <- Gs; b3_zn; unfold ASHADOW_BASE; lia);
      assumption
  end.

Section T3.
  #[local] Set Default Proof Using "All".
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV_P5 ds_repA.
  Hypothesis HTR : ds_tr_ok H.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV_P5 ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV_P5 ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV_P5 ds_repA.
  Variable e : went H.
  Variables ff fp : Z.
  Variable mo0 : Model.
  Variable w : piw H.
  Variable c0 : parserC.
  Variable LBs : list block.
  Variable s0 : as_St H.
  Variable LB0 : list block.
  Variable m0 : mem.
  Variable XSc0 : list (Z * Z).
  Hypothesis HP : wpre H e.
  Hypothesis HWL : bp_wl H e ff w.
  Hypothesis HPP : bp_pp H w LB0 LBs m0 c0.
  Hypothesis HI0 : winv H e ff fp XSc0 s0 LB0 m0.
  Hypothesis HMD : mdef m0 (pw_p H w) PARSER_SIZE.
  Hypothesis HAL : PM_RESERVE <= as_AL H s0.
  Hypothesis HMEAS : pm_meas_ok (pw_n H w) LBs.
  Hypothesis HPF : bp_pfresh H w s0 LB0 LBs m0 c0.
  Hypothesis HW : w_words e <> 0.
  Hypothesis HN : 5 <= w_n e.

  Local Abbreviation WSR := (wsr H ds_repA e ff fp mo0 w c0 LBs s0 LB0 m0).
  Local Abbreviation LF6 := ((6, ff, fp) :: w_LF e).
  Local Abbreviation wchunk := (w_chunk H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
  Local Abbreviation wexit := (w_exit H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
  Local Abbreviation wgeo := (w_geo H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
  Local Abbreviation wobj := (w_obj H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
  Local Abbreviation wkeepcl := (w_keep_client H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
  Local Abbreviation wcseq := (w_cseq H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL HMEAS).
  Local Abbreviation wdtor := (w_dtor H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL HMEAS).

  Lemma b3_geo : ff mod 64 = 0 /\ 32 * (ff / 32) = ff /\ 4 * (ff / 32) + ASHADOW_BASE = sh ff
    /\ 227200 <= ff / 32 <= 2 ^ 42 /\ 2 ^ 45 + 16 <= wS1 e <= 2 ^ 47 /\ wS1 e mod 16 = 0
    /\ 0x6e6000 + 0x9000 <= ff /\ ff + 4096 <= 2 ^ 47 /\ (ff + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= ff)
    /\ 0 <= sh ff /\ sh ff + 512 <= 2 ^ 64 /\ (sh ff + 512 <= ff \/ ff + 4096 <= sh ff).
  Proof.
    pose proof (hdr_geo H e ff fp XSc0 s0 LB0 m0 HP HI0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    pose proof (wframe_bounds H e ff fp XSc0 s0 LB0 m0 HP HI0) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
    assert (Hq : 32 * (ff / 32) = ff) by (clear - G1; Z.div_mod_to_equations; lia).
    assert (SHq : 4 * (ff / 32) + ASHADOW_BASE = sh ff).
    { unfold sh. rewrite <- Hq at 2. replace (32 * (ff / 32)) with ((4 * (ff / 32)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
    unfold WO_FLAGP in *.
    split; [exact G1|]. split; [exact Hq|]. split; [exact SHq|].
    split; [split; [clear - G2; Z.div_mod_to_equations; lia | clear - B4; Z.div_mod_to_equations; lia]|].
    split; [lia|]. split; [clear - G14; Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [lia|].
    split; [destruct G6 as [G6|G6]; unfold aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in G6; lia|].
    split; [lia|]. split; [lia|]. exact G9.
  Qed.

  Ltac b3_geo_intro := pose proof b3_geo as (Ga & Gq & Gs & Gb & Gc & Gd & Ge & Gf & Gg & Gh0 & Gh1 & Gh2).

  Lemma b3_shk : forall m m', bp_shad ff [14; 15; 20; 21]%nat m ->
    wxkeep H e ff fp LB0 [(ff + 1760, ff + 1760 + DS_SIZE)] m m' -> bp_shad ff [14; 15; 20; 21]%nat m'.
  Proof.
    intros m m' S K. b3_geo_intro.
    destruct (wkeepcl _ m m' K) as (LBk & XS & XP & XC).
    unfold bp_shad in *. eapply u8arr_keep; [|exact S].
    rewrite length_map, b3_len1. intros a Ha. change (Z.of_nat 476) with 476 in Ha.
    apply XP; [lia|].
    apply XC; [right; lia|].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold DS_SIZE. lia.
  Qed.

  Lemma b3_dso : forall m, bp_shad ff [14; 15; 20; 21]%nat m ->
    ds_obj H LF6 m (wS1 e) (ff + 1760) DS_SIZE /\ obj_inframe LF6 (ff + 1760) DS_SIZE.
  Proof.
    intros m S. b3_geo_intro.
    apply (wobj m 1760 DS_SIZE); [lia | unfold DS_SIZE; lia | unfold DS_SIZE, WO_FLAGP; lia | clear - Ga; Z.div_mod_to_equations; lia |].
    apply (bp_shad_addr ff _ m 1760 DS_SIZE S); [lia | clear - Ga; Z.div_mod_to_equations; lia | lia | reflexivity | unfold DS_SIZE; lia
      | unfold DS_SIZE; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity].
  Qed.

  Definition b3_R2 (R : bvmap 5 word) : Prop :=
    getr R 1 = wz 0xebcd4 /\ getr R 10 = wz (ff + 1760) /\ getr R 11 = wz 148000 /\ getr R 12 = wz 2
    /\ getr R 18 = wz (ff + 1760) /\ getr R 22 = wz (ff + 3504).
  Definition b3_R3 (R : bvmap 5 word) : Prop := getr R 18 = wz (ff + 1760) /\ getr R 22 = wz (ff + 3504).
  Definition b3_R4 (R : bvmap 5 word) : Prop :=
    getr R 1 = wz 0xebce0 /\ getr R 10 = wz (ff + 1760) /\ getr R 22 = wz (ff + 3504) /\ getr R 24 = wz (-4).
  Definition b3_R5 (R : bvmap 5 word) : Prop := getr R 22 = wz (ff + 3504) /\ getr R 24 = wz (-4).

  Section Run.
    Variables (Q : config -> Prop) (len spent : Z).
    Hypothesis HK : bp_kmagf H e ff fp Q mo0.
    Hypothesis HLN : len + 2 <= 1024.
    Hypothesis HSP : spent + ds_cost (len + 2) <= PM_RESERVE.

    Lemma b3_s6 : forall c, WSR BP_MAGF b3_R5 None (bp_shad ff [14; 20; 21]%nat) (spent + ds_cost (len + 2)) c -> as_SR H Q c.
    Proof.
      intros c Hc.
      apply (wexit Q BP_MAGF b3_R5 (fun R => getr R 22 = wz (ff + 3504)) (bp_shad ff [14; 20; 21]%nat) (spent + ds_cost (len + 2)) c
        [14; 20; 21]%nat (bp_slots H) (-4) Hc).
      - exact HSP.
      - exact HPF.
      - intros m S. exact S.
      - intros m SL _. exact SL.
      - intros R [R22 R24]. split; assumption.
      - lia.
      - exact HK.
    Qed.

    Lemma b3_s5 : forall c, WSR 0xebce0 b3_R5 None (bp_shad ff [14; 15; 20; 21]%nat) (spent + ds_cost (len + 2)) c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q 0xebce0 BP_MAGF b3_R5 b3_R5 None (bp_shad ff [14; 15; 20; 21]%nat) (bp_shad ff [14; 20; 21]%nat) (spent + ds_cost (len + 2)) c Hc); [|exact b3_s6].
      intros R F fc m XSc s LB [R22 R24] RC S HI HSL HSE. b3_geo_intro.
      pose proof Gs as Gs'. unfold ASHADOW_BASE in Gs'.
      pose proof (wgeo XSc s LB m HI) as (_ & GW2 & _).
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (bmR_te_bp R F fc m (ff / 32) (wS1 e)) as (R' & M' & RUN & MU & WM & POST).
      { unfold bmR_te_pre. rewrite Gq, Gs.
        split; [exact C2|]. split; [exact C19|]. split; [exact C20|].
        split.
        { pose proof (bp_wr_sub m _ 512 220 50 GW2 ltac:(lia) ltac:(lia) ltac:(lia)) as W50.
          match type of W50 with wr_at _ _ ?A _ => match goal with |- wr_at _ _ ?B _ =>
            replace B with A by (clear - Ga Gs'; Z.div_mod_to_equations; lia) end end.
          exact W50. }
        repeat split; first [assumption | lia]. }
      rewrite ?Gq, ?Gs in POST. decompose [and] POST. clear POST.
      eexists R', M', _. split; [exact RUN|]. split; [exact MU|]. split; [exact WM|].
      split; [apply Forall_cons; [|apply Forall_nil]; unfold bp_flw; cbn [fst snd]; unfold WO_FLAGP; lia|].
      split; [apply Forall_forall; intros; exact I|].
      split; [unfold bp_rc; repeat split; b3_kreg|]. split; [unfold b3_R5; split; b3_kreg|].
      apply (bp_shad_set ff [14; 15; 20; 21]%nat [14; 20; 21]%nat m M' _ [(220, 270)]
        (map (fun j => (220 + Z.of_nat j, 18446744073709551608)) (seq 0 50)) S MU WM).
      - vm_compute. reflexivity.
      - intros i Hi NI. rewrite b3_len1 in Hi. change (Z.of_nat 476) with 476 in Hi.
        assert (NI' : ~ (220 <= i < 270)) by (intro X; apply NI; cbn [in_rngs]; left; exact X).
        cbn [outside]. split; [lia | exact I].
      - cbn [map seq]. repeat (apply Forall_cons; [cbn [fst snd]; b3_wb Gs |]). apply Forall_nil.
    Qed.

    Lemma b3_s4 : forall c, WSR ADS_DTOR b3_R4 (Some (ff + 1760, -4, len + 2)) (bp_shad ff [14; 15; 20; 21]%nat) (spent + ds_cost (len + 2)) c -> as_SR H Q c.
    Proof.
      intros c Hc. b3_geo_intro.
      apply (wdtor HDTOR Q b3_R4 b3_R5 (bp_shad ff [14; 15; 20; 21]%nat) (bp_shad ff [14; 15; 20; 21]%nat) (spent + ds_cost (len + 2)) c
        0xebce0 (ff + 1760) (-4) (len + 2) Hc).
      - intros R (R1 & R10 & _). split; assumption.
      - reflexivity.
      - lia.
      - exact HSP.
      - unfold PO_PF. apply in_or_app. left. b3_inl.
      - lia.
      - unfold DS_SIZE. lia.
      - exact b3_dso.
      - intros R R' (_ & _ & R22 & R24) K. split; b3_kreg.
      - intros m m' S KX. exact (b3_shk m m' S KX).
      - exact b3_s5.
    Qed.

    Lemma b3_s3 : forall c, WSR 0xebcd4 b3_R3 (Some (ff + 1760, -4, len + 2)) (bp_shad ff [14; 15; 20; 21]%nat) (spent + ds_cost (len + 2)) c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q 0xebcd4 ADS_DTOR b3_R3 b3_R4 _ (bp_shad ff [14; 15; 20; 21]%nat) (bp_shad ff [14; 15; 20; 21]%nat) _ c Hc); [|exact b3_s4].
      intros R F fc m XSc s LB [R18 R22] RC S HI HSL HSE. b3_geo_intro.
      destruct HSE as (DB & DS & _ & _).
      pose proof (dla_err _ _ DSL _ _ _ _ _ _ DS) as ERR.
      apply b3_fld_of_cells4 in ERR; [|unfold DS_ERR_OFF; lia].
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (bmR_td_bp R F fc m (ff / 32) (wS1 e)) as (R' & M' & RUN & EM & POST).
      { unfold bmR_td_pre. rewrite !Gq, Gs.
        split; [exact C2|]. split; [exact R18|]. split; [exact C19|]. split; [exact C20|].
        split; [replace (ff + 2120) with (ff + 1760 + DS_ERR_OFF) by (unfold DS_ERR_OFF; lia); exact ERR|].
        repeat split; first [assumption | lia]. }
      subst M'. rewrite ?Gq, ?Gs in POST. decompose [and] POST. clear POST.
      exists R', m, []. split; [exact RUN|]. split; [apply munch_refl|]. split; [intros x Hx; exact Hx|].
      split; [apply Forall_nil|]. split; [apply Forall_nil|].
      split; [unfold bp_rc; repeat split; b3_kreg|]. split; [unfold b3_R4; repeat split; b3_kreg|]. exact S.
    Qed.

    Lemma b3_s2 : forall c, WSR APUT_CSEQ b3_R2 (Some (ff + 1760, -4, len)) (bm_mid_mem H e ff fp) spent c -> as_SR H Q c.
    Proof.
      intros c Hc. b3_geo_intro.
      destruct (cstrA_img 148000 2 m0 b3_cs (winv_mi H e ff fp XSc0 s0 LB0 m0 HI0)) as (I1 & I2 & I3 & I4 & I5).
      apply (wcseq HCSEQ Q b3_R2 b3_R3 (bm_mid_mem H e ff fp) (bp_shad ff [14; 15; 20; 21]%nat) spent c
        0xebcd4 (ff + 1760) (-4) len 148000 2 Hc).
      - intros R (R1 & R10 & R11 & R12 & _). repeat split; assumption.
      - reflexivity.
      - lia.
      - exact HSP.
      - lia.
      - unfold DS_SIZE. lia.
      - intros m (_ & OB & OI). split; assumption.
      - exact I3.
      - exact I1.
      - exact I2.
      - exact I4.
      - exact I5.
      - exact HLN.
      - intros R R' (_ & _ & _ & _ & R18 & R22) K K10. split; b3_kreg.
      - intros m m' (S & _) KX. exact (b3_shk m m' S KX).
      - exact b3_s3.
    Qed.

    Lemma b3_s1 : forall c, WSR 0xebcc0 (bm_mid_regs ff) (Some (ff + 1760, -4, len)) (bm_mid_mem H e ff fp) spent c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q 0xebcc0 APUT_CSEQ (bm_mid_regs ff) b3_R2 _ (bm_mid_mem H e ff fp) (bm_mid_mem H e ff fp) _ c Hc); [|exact b3_s2].
      intros R F fc m XSc s LB (R18 & R22 & R27) RC S HI HSL HSE. b3_geo_intro.
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (bmR_tq_bp R F fc m (ff / 32) (wS1 e)) as (R' & M' & RUN & EM & POST).
      { unfold bmR_tq_pre. rewrite !Gq, Gs.
        split; [exact C2|]. split; [exact R18|]. split; [exact C19|]. split; [exact C20|].
        repeat split; first [assumption | lia]. }
      subst M'. rewrite ?Gq, ?Gs in POST. decompose [and] POST. clear POST.
      exists R', m, []. split; [exact RUN|]. split; [apply munch_refl|]. split; [intros x Hx; exact Hx|].
      split; [apply Forall_nil|]. split; [apply Forall_nil|].
      split; [unfold bp_rc; repeat split; b3_kreg|]. split; [unfold b3_R2; repeat split; b3_kreg|]. exact S.
    Qed.
  End Run.

  Lemma pm_bm_t3 : forall (Q : config -> Prop), bp_kmagf H e ff fp Q mo0 -> forall len spent c,
    wsr H ds_repA e ff fp mo0 w c0 LBs s0 LB0 m0 0xebcc0 (bm_mid_regs ff) (Some (ff + 1760, -4, len))
        (bm_mid_mem H e ff fp) spent c ->
    len + 2 <= 1024 -> spent + ds_cost (len + 2) <= PM_RESERVE -> as_SR H Q c.
  Proof. intros Q HK len spent c Hc HL HS. exact (b3_s1 Q len spent HK HL HS c Hc). Qed.
End T3.
