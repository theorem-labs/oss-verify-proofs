From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_ContStmt LbB_Conv LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase LbB_Call LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_SR LbB_WoGen LbB_WoDefs LbB_WoKit LbB_PiStmt LbB_PiInit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRepFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BllocRep BG_Free6.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoBP LbB_PmExit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DiagStmt LbB_WoDiagP LbB_WoKit2 LbB_WoDiagF LbB_PmMagW LbB_PmHTK.
Import ListNotations.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac hinst X Hv HHv :=
  lazymatch type of X with
  | forall _ : asr, _ => specialize (X Hv); hinst X Hv HHv
  | asan_rt_hyps _ -> _ => specialize (X HHv)
  | _ => idtac
  end.

Definition WD_KEEP : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition WD_MKEEP : list reg := [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section WDA.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma bp_pp_mdef : forall (w : piw H) LB LBs m c, bp_pp H w LB LBs m c -> mdef m (pw_p H w) PARSER_SIZE.
  Proof.
    intros w LB LBs m c (PR & _).
    unfold parser_repA in PR.
    assert (D1 : mdef m (pw_p H w) ST_OFF) by (eapply pr_def; exact PR).
    assert (D2 : defined m (pw_p H w + ST_OFF) 240) by (eapply sr_def; eapply pr_state; exact PR).
    intros i Hi. unfold PARSER_SIZE in Hi.
    destruct (Z.lt_ge_cases i ST_OFF) as [L|L].
    - apply D1. unfold ST_OFF in *. lia.
    - replace (pw_p H w + i) with (pw_p H w + ST_OFF + (i - ST_OFF)) by ring. apply D2. unfold ST_OFF in *. lia.
  Qed.

  Lemma bp_al_res : forall (w : piw H) s st, bp_al H w s st -> PM_RESERVE <= as_AL H s.
  Proof.
    intros w s st (A1 & A2 & A3). pose proof (pm_prog_bounds (pi_c0 st)) as PB. unfold pm_phi, pm_cap in *. lia.
  Qed.
End WDA.

Section WDC.
  #[local] Set Default Proof Using "All".
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV_P5 ds_repA.
  Hypothesis HTR : ds_tr_ok H.
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

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Local Abbreviation LF6 := ((6, ff, fp) :: w_LF e) (only parsing).

  Definition wses (S : option (Z * Z * Z)) (LB : list block) (m : mem) : Prop :=
    match S with
    | None => Permutation LB LB0
    | Some (ds, err, len) => exists DB, ds_repA LB m ds err len DB /\ Permutation LB (DB ++ LB0) /\ lb_own DB m
    end.

  Definition wsr (pc : Z) (REGS : bvmap 5 word -> Prop) (S : option (Z * Z * Z)) (P : mem -> Prop) (spent : Z)
      (c : config) : Prop :=
    exists (s : as_St H) (R F : bvmap 5 word) (fc : bv 32) (m : mem) (XSc : list (Z * Z)) (LB : list block),
         as_AKREL H s c /\ as_MPRES H mo0 (cfg_model c)
      /\ as_VIS H s (cfg_ms c) = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) /\ rfull R /\ frm_zero fc
      /\ winv H e ff fp XSc s LB m /\ bp_slots H e ff m /\ bp_rc H e ff R /\ REGS R
      /\ BllocRep.agree_on (bp_pfoot (pw_p H w) c0) m0 m /\ lb_own LBs m
      /\ wses S LB m /\ P m
      /\ as_AL H s >= as_AL H s0 - spent.

  Definition wfree (S : option (Z * Z * Z)) (iv : Z * Z) : Prop :=
    match S with
    | None => True
    | Some (ds, _, _) => (snd iv <= ds \/ ds + DS_SIZE <= fst iv) /\ (snd iv <= sh ds \/ sh ds + nsh DS_SIZE <= fst iv)
    end.

  Definition wxkeep (X : list (Z * Z)) (m m' : mem) : Prop :=
    exists LBk XS, (forall b, In b LB0 -> In b LBk)
      /\ Forall (fs_scratch H LF6) XS /\ xpres H LBk (wS1 e) (X ++ XS) m m'.

  Ltac wgeo HI :=
    let G := fresh "G" in let B := fresh "B" in
    pose proof hdr_geo as G; hinst G H HH; specialize (G e ff fp _ _ _ _ HP HI);
    pose proof (wframe_bounds H e ff fp _ _ _ _ HP HI) as B.

  Definition wprot (a : Z) : Prop :=
    (ff + 3376 <= a < ff + 3424) \/ (ff + 3456 <= a < ff + 3744) \/ (sh ff + 422 <= a < sh ff + 428)
    \/ (sh ff + 432 <= a < sh ff + 468)
    \/ (exists pid A n, In (pid, A, n) LB0 /\ ((A <= a < A + n) \/ (sh A <= a < sh A + nsh n))).

  Lemma w_pfoot_prot : forall a, bp_pfoot (pw_p H w) c0 a -> wprot a.
  Proof.
    intros a HF.
    pose proof HWL as (Wp & Wc & _).
    pose proof HPP as (_ & _ & HC & _ & _ & SOWN & _).
    pose proof stblk_in as SB. hinst SB H HH.
    assert (E1 : sh (ff + 3456) = sh ff + 432) by (unfold sh; replace (ff + 3456) with (ff + 432 * 8) by lia; rewrite Z.div_add by lia; lia).
    assert (E2 : sh (ff + 3376) = sh ff + 422) by (unfold sh; replace (ff + 3376) with (ff + 422 * 8) by lia; rewrite Z.div_add by lia; lia).
    unfold bp_pfoot, parser_foot, state_foot in HF. rewrite Wp, HC, Wc in HF.
    destruct HF as [[HF|[HF|(b & Hb & HF)]]|[HF|[HF|[HF|(b & Hb & HF)]]]].
    - right; left. unfold PARSER_SIZE in HF. lia.
    - right; left. unfold ST_OFF in HF. lia.
    - destruct (SB LB0 (pw_LB0 H w) LBs (pc_state c0) b SOWN Hb) as (pid & Hin).
      right; right; right; right. exists pid, (fst b), (snd b). split; [exact Hin | left; lia].
    - left. lia.
    - right; right; right; left. rewrite E1 in HF. change (nsh PARSER_SIZE) with 36 in HF. lia.
    - right; right; left. rewrite E2 in HF. change (nsh 48) with 6 in HF. lia.
    - destruct (SB LB0 (pw_LB0 H w) LBs (pc_state c0) b SOWN Hb) as (pid & Hin).
      right; right; right; right. exists pid, (fst b), (snd b). split; [exact Hin | right; lia].
  Qed.

  Lemma w_prot_flw : forall a iv, wprot a -> bp_flw H e ff iv -> ~ (fst iv <= a < snd iv).
  Proof.
    intros a iv HA FL Hin.
    pose proof FL as (_ & F1 & F2 & F3 & F4).
    destruct HA as [A|[A|[A|[A|(pid & A & n & Hb & A1)]]]]; try lia.
    pose proof blk_disj as BD. hinst BD H HH.
    destruct (BD e ff fp XSc0 s0 LB0 m0 iv pid A n HP HI0 FL Hb) as [D1 D2]. lia.
  Qed.

  Lemma w_pf_munch : forall m m' W, BllocRep.agree_on (bp_pfoot (pw_p H w) c0) m0 m -> munch W m m' ->
    Forall (bp_flw H e ff) W -> BllocRep.agree_on (bp_pfoot (pw_p H w) c0) m0 m'.
  Proof.
    intros m m' W AG MU FW x Hx Hr.
    pose proof munch_at as MA. hinst MA H HH.
    change (wa x) with (Z_to_bv 64 x).
    rewrite (MA W m m' x MU Hr); [exact (AG x Hx Hr)|].
    intros iv Hiv. apply (w_prot_flw x iv (w_pfoot_prot x Hx)). rewrite Forall_forall in FW. exact (FW iv Hiv).
  Qed.

  Lemma w_flw_lo : forall iv, bp_flw H e ff iv -> snd iv <= wS1 e.
  Proof.
    intros iv (F & _).
    wgeo HI0.
    destruct B as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    unfold AINTRIN_STACK in *. lia.
  Qed.

  Lemma w_ses_munch : forall S XSc s LB m m' W, winv H e ff fp XSc s LB m -> wses S LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (bp_flw H e ff) W -> Forall (wfree S) W -> wses S LB m'.
  Proof.
    intros [[[ds err] len]|] XSc s LB m m' W HI SES MU WM FW FS; [|exact SES].
    destruct SES as (DB & REP & PM & OWN).
    exists DB. split; [|split; [exact PM | exact (lb_own_wmono _ _ _ OWN WM)]].
    pose proof munch_at as MA. hinst MA H HH.
    pose proof blk_disj as BD. hinst BD H HH.
    eapply (dla_frame _ _ DSL LB LB m m' ds err len DB REP);
      [| intros b Hb; exact (proj1 (proj2 (dla_blocks _ _ DSL LB m ds err len DB REP) b Hb))].
    intros a Ha Hin. apply (MA W m m' a MU Ha). intros iv Hiv.
    rewrite Forall_forall in FW, FS. pose proof (FW iv Hiv) as FL. pose proof (FS iv Hiv) as FR. cbn [wfree] in FR.
    destruct Hin as [Hin|[(b & Hb & Hin)|[(b & Hb & Hin)|Hin]]].
    - lia.
    - destruct b as [[pid A] n].
      assert (HbL : In (pid, A, n) LB) by (apply (Permutation_in _ (Permutation_sym PM)); apply in_or_app; left; exact Hb).
      destruct (BD e ff fp XSc s LB m iv pid A n HP HI FL HbL) as [D1 D2]. cbn [blk_addr blk_size fst snd] in Hin. lia.
    - destruct b as [[pid A] n].
      assert (HbL : In (pid, A, n) LB) by (apply (Permutation_in _ (Permutation_sym PM)); apply in_or_app; left; exact Hb).
      destruct (BD e ff fp XSc s LB m iv pid A n HP HI FL HbL) as [D1 D2]. cbn [blk_addr blk_size fst snd] in Hin. lia.
    - lia.
  Qed.

  Lemma w_slots_munch : forall m m' W, bp_slots H e ff m -> munch W m m' -> wmono asegs m m' ->
    Forall (bp_flw H e ff) W -> bp_slots H e ff m'.
  Proof.
    intros m m' W (C1 & C2 & C3) MU WM FW.
    assert (DJ : forall k n, 0 <= k -> disjoint_from W (wS1 e + k) n).
    { intros k n Hk. apply disj_of_all. intros iv Hiv. right. rewrite Forall_forall in FW.
      pose proof (w_flw_lo iv (FW iv Hiv)) as L. lia. }
    split; [|split].
    - eapply (rw_cells_transport asegs W m m'); [exact C1 | exact MU | exact WM |]. replace (wS1 e) with (wS1 e + 0) by lia. apply DJ; lia.
    - eapply (rw_cells_transport asegs W m m'); [exact C2 | exact MU | exact WM |]. apply DJ; lia.
    - eapply (rw_cells_transport asegs W m m'); [exact C3 | exact MU | exact WM |]. apply DJ; lia.
  Qed.

  Definition wreg (a : Z) : Prop :=
    (ff <= a < ff + 4096) \/ (sh ff <= a < sh ff + 512) \/ wS1 e <= a
    \/ (exists pid A n, In (pid, A, n) LB0 /\ ((A <= a < A + n) \/ (sh A <= a < sh A + nsh n))).

  Definition wxok (iv : Z * Z) : Prop :=
    (ff + 8 <= fst iv /\ snd iv <= ff + WO_FLAGP /\ (snd iv <= ff + 3376 \/ ff + 3744 <= fst iv))
    \/ iv = (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8).

  Lemma w_xc : forall LBk X XS a, (forall b, In b LB0 -> In b LBk) -> Forall (fs_scratch H LF6) XS ->
    0 <= a < 2 ^ 64 -> wreg a -> (forall iv, In iv X -> ~ (fst iv <= a < snd iv)) -> xclient H LBk (wS1 e) (X ++ XS) a.
  Proof.
    intros LBk X XS a INC FS Ha RG NX.
    wgeo HI0.
    destruct G as (G64 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct B as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof HI0 as (RF0 & FF0 & RH0 & _).
    pose proof bp_rin_ex as RE. hinst RE H HH.
    pose proof aceil_facts as ACF.
    assert (SHE : sh (ff + 4096) = sh ff + 512) by (unfold sh; replace (ff + 4096) with (ff + 512 * 8) by lia; rewrite Z.div_add by lia; lia).
    pose proof (sh_mono (as_FSB H) ff ltac:(unfold AFS_HDR in *; lia)) as SM1.
    pose proof (sh_mono (ff + 4096) (as_FSB H + AFS_SIZE) G4) as SM2.
    split.
    - unfold aclient_addr. destruct RG as [R1|[R2|[R3|(pid & A & n & Hb & [R4|R4])]]].
      + right; right; right; right; left. unfold AFS_HDR in *. lia.
      + right; right; right; right; right; left. lia.
      + left. exact R3.
      + right; right; left. exists (pid, A, n). split; [exact (INC _ Hb)|]. cbn [blk_addr blk_size fst snd]. lia.
      + right; right; right; left. exists (pid, A, n). split; [exact (INC _ Hb)|]. cbn [blk_addr blk_size fst snd]. lia.
    - intros RI. destruct (RE (X ++ XS) a RI) as (iv & Hin & Hiv). apply in_app_or in Hin as [Hin|Hin]; [exact (NX iv Hin Hiv)|].
      rewrite Forall_forall in FS. pose proof (FS iv Hin) as FSi.
      destruct (wfsw_ok H HH e ff fp m0 iv RF0 FF0 G9 FSi) as (_ & _ & _ & W0 & W1 & W2 & W3 & _).
      destruct RG as [R1|[R2|[R3|(pid & A & n & Hb & [R4|R4])]]]; try lia.
      + pose proof (ah_blocks H HH _ _ _ _ RH0 Hb) as AB. cbn [blk_addr blk_size fst snd] in AB.
        destruct AB as (A0 & A16 & An & AT & AC & AF & AA).
        assert (AH : A + n <= AAPP_HI) by (unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AAPP_HI in *; lia).
        pose proof (fsobj_scratch H HH LF6 A n m0 iv RF0 (fsobj_block H HH s0 LB0 m0 LF6 pid A n RH0 Hb) ltac:(lia) An AH AA FSi). lia.
      + pose proof (ah_blocks H HH _ _ _ _ RH0 Hb) as AB. cbn [blk_addr blk_size fst snd] in AB.
        destruct AB as (A0 & A16 & An & AT & AC & AF & AA).
        assert (AH : A + n <= AAPP_HI) by (unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AAPP_HI in *; lia).
        pose proof (fsobj_scratch_sh H HH LF6 A n m0 iv RF0 (fsobj_block H HH s0 LB0 m0 LF6 pid A n RH0 Hb) ltac:(lia) An AH FSi). lia.
  Qed.

  Lemma w_xok_out : forall iv a, wxok iv -> (wprot a \/ wS1 e <= a) -> ~ (fst iv <= a < snd iv).
  Proof.
    intros iv a XO RA Hin.
    wgeo HI0.
    destruct G as (G64 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct B as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof HI0 as (RF0 & FF0 & RH0 & _).
    pose proof aceil_facts as ACF.
    destruct XO as [(X1 & X2 & X3)| ->]; cbn [fst snd] in Hin.
    - destruct RA as [[A|[A|[A|[A|(pid & A & n & Hb & A1)]]]]|A]; try (unfold WO_FLAGP, AINTRIN_STACK in *; lia).
      pose proof (ah_blocks H HH _ _ _ _ RH0 Hb) as AB. cbn [blk_addr blk_size fst snd] in AB.
      destruct AB as (A0 & A16 & An & AT & AC & AF & AA).
      unfold aapp, aapp_lo, aapp_hi in G5. unfold sh, nsh in *. rewrite ASHADOW_BASE_val in *.
      unfold WO_FLAGP, AFS_HDR, AFS_SIZE, ALOWSH_LO, AHI_LO in *.
      clear - X1 X2 Hin A1 A0 An AT AC AF G3 G4 G5 ACF. Z.div_mod_to_equations. lia.
    - unfold RtB_Td.ATDLOC in Hin.
      destruct RA as [[A|[A|[A|[A|(pid & A & n & Hb & A1)]]]]|A].
      + lia.
      + lia.
      + unfold sh in A. rewrite ASHADOW_BASE_val in A. clear - A Hin B0. Z.div_mod_to_equations. lia.
      + unfold sh in A. rewrite ASHADOW_BASE_val in A. clear - A Hin B0. Z.div_mod_to_equations. lia.
      + pose proof (ah_blocks H HH _ _ _ _ RH0 Hb) as AB. cbn [blk_addr blk_size fst snd] in AB.
        destruct AB as (A0 & A16 & An & AT & AC & AF & AA).
        destruct A1 as [A1|A1].
        * unfold AIMG_TOP in *. lia.
        * unfold sh in A1. rewrite ASHADOW_BASE_val in A1. clear - A1 Hin A0. Z.div_mod_to_equations. lia.
      + lia.
  Qed.

  Lemma w_prot_reg : forall a, wprot a -> wreg a.
  Proof.
    intros a [A|[A|[A|[A|A]]]].
    - left. lia.
    - left. lia.
    - right; left. lia.
    - right; left. lia.
    - right; right; right. exact A.
  Qed.

  Lemma w_post_keep : forall LBk X XS m m', (forall b, In b LB0 -> In b LBk) -> Forall wxok X -> Forall (fs_scratch H LF6) XS ->
    xpres H LBk (wS1 e) (X ++ XS) m m' ->
    bp_slots H e ff m -> BllocRep.agree_on (bp_pfoot (pw_p H w) c0) m0 m -> lb_own LBs m ->
    bp_slots H e ff m' /\ BllocRep.agree_on (bp_pfoot (pw_p H w) c0) m0 m' /\ lb_own LBs m'.
  Proof.
    intros LBk X XS m m' INC XO FS XP (C1 & C2 & C3) AG OWN.
    set (Pk := fun a => wreg a /\ (forall iv, In iv X -> ~ (fst iv <= a < snd iv))).
    assert (AGx : BllocRep.agree_on Pk m m').
    { intros x (RG & NX) Hr. exact (proj1 (XP x Hr (w_xc LBk X XS x INC FS Hr RG NX))). }
    rewrite Forall_forall in XO.
    assert (SLk : forall a, wS1 e <= a -> Pk a).
    { intros a Ha. split; [right; right; left; exact Ha|]. intros iv Hiv. exact (w_xok_out iv a (XO iv Hiv) (or_intror Ha)). }
    pose proof HPP as (_ & _ & _ & _ & _ & (SO1 & _) & _).
    pose proof HWL as (_ & _ & _ & _ & WLB & _).
    split; [|split].
    - split; [|split].
      + eapply (BG_Free6.rw_cells_pteq Pk m m' AGx); [exact C1|]. intros a Ha. apply SLk. lia.
      + eapply (BG_Free6.rw_cells_pteq Pk m m' AGx); [exact C2|]. intros a Ha. apply SLk. lia.
      + eapply (BG_Free6.rw_cells_pteq Pk m m' AGx); [exact C3|]. intros a Ha. apply SLk. lia.
    - intros x Hx Hr. pose proof (w_pfoot_prot x Hx) as PX.
      rewrite (AGx x (conj (w_prot_reg x PX) (fun iv Hiv => w_xok_out iv x (XO iv Hiv) (or_introl PX))) Hr).
      exact (AG x Hx Hr).
    - unfold lb_own in *. rewrite Forall_forall in OWN |- *. intros [[pid A] n] Hb.
      assert (Hb0 : In (pid, A, n) LB0).
      { apply (Permutation_in _ (Permutation_sym SO1)). apply in_or_app. right. exact Hb. }
      pose proof (OWN _ Hb) as WR. cbn [blk_addr blk_size fst snd] in WR |- *.
      eapply (BG_Free6.wr_at_pteq Pk m m' AGx A n WR). intros x Hx.
      pose proof (ah_blocks H HH _ _ _ _ (proj1 (proj2 (proj2 HI0))) Hb0) as AB. cbn [blk_addr blk_size fst snd] in AB.
      split.
      + right; right; right. exists pid, A, n. split; [exact Hb0 | left; lia].
      + intros iv Hiv. pose proof (XO iv Hiv) as XOi. intros Hin.
        wgeo HI0.
        destruct G as (G64 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
        destruct AB as (A0 & A16 & An & AT & AC & AF & AA).
        destruct XOi as [(X1 & X2 & X3)| ->]; cbn [fst snd] in Hin.
        * unfold WO_FLAGP, AFS_HDR, AFS_SIZE in *. lia.
        * unfold RtB_Td.ATDLOC, AIMG_TOP in *. lia.
  Qed.

  Lemma w_geo : forall XSc s LB m, winv H e ff fp XSc s LB m ->
    wr_at asegs m ff 4096 /\ wr_at asegs m (ff / 8 + 2147450880) 512 /\ 1048576 <= ff /\ ff + 4096 <= 2 ^ 47
    /\ 2 ^ 45 <= wS1 e /\ wS1 e + 192 <= 2 ^ 47 /\ (ff + 4096 <= wS1 e \/ wS1 e + 192 <= ff)
    /\ ((ff / 8 + 2147450880) + 512 <= ff \/ ff + 4096 <= ff / 8 + 2147450880).
  Proof.
    intros XSc s LB m HI.
    wgeo HI.
    destruct G as (G64 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct B as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof HI as (RF & FF & RH & AC & MI & S0 & RA & ER & ST & SV & SF & WF & WFP & XP & FS & LV).
    pose proof (ah_frm_shvis H HH _ m (6, ff, fp) RF (or_introl eq_refl)) as SHV.
    unfold ff_addr, ff_class in SHV. cbn [fst snd] in SHV. change (fsz 6) with 4096 in SHV.
    unfold shvis in SHV.
    assert (HL : hull_lo ff = ff) by (unfold hull_lo; rewrite G64; lia).
    assert (M64 : (ff + 4096) mod 64 = 0).
    { replace (ff + 4096) with (ff + 64 * 64) by lia. rewrite Z.mod_add by lia. exact G64. }
    assert (HHi : hull_hi (ff + 4096) = ff + 4096).
    { unfold hull_hi. rewrite M64. replace ((64 - 0) mod 64) with 0 by reflexivity. lia. }
    rewrite HL, HHi in SHV.
    pose proof (wr_at_of_stk asegs m _ _ SHV) as WSH.
    assert (SHE : sh (ff + 4096) = sh ff + 512) by (unfold sh; replace (ff + 4096) with (ff + 512 * 8) by lia; rewrite Z.div_add by lia; lia).
    rewrite SHE in WSH. replace (sh ff + 512 - sh ff) with 512 in WSH by lia.
    assert (SHv : sh ff = ff / 8 + 2147450880) by (unfold sh; rewrite ASHADOW_BASE_val; lia).
    rewrite SHv in WSH.
    assert (W8 : wr_at asegs m (ff + WO_FLAGP) 8) by (eapply rw_cells_wr_at; [exact SF | cbn; lia]).
    assert (WFF : wr_at asegs m ff 4096).
    { replace 4096 with (WO_FLAGP + 8) by (unfold WO_FLAGP; lia). apply bp_wr_merge; [unfold WO_FLAGP; lia | lia | exact WF | exact W8]. }
    split; [exact WFF|]. split; [exact WSH|].
    rewrite <- SHv. unfold WO_FLAGP, AINTRIN_STACK, AIMG_TOP, AFS_HDR in *.
    clear - G1 B2 B4 B5 B7 B8 B9. repeat split; lia.
  Qed.

  Lemma w_geo2 : ff + 4096 <= w_lo e /\ w_lo e + 32768 <= wS1 e /\ wS1 e + 192 <= wSP e.
  Proof.
    wgeo HI0.
    destruct G as (G64 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    lia.
  Qed.

  Lemma w_obj : forall m k n, 0 <= k -> 0 < n -> k + n <= WO_FLAGP -> (ff + k) mod 8 = 0 -> addressable m (ff + k) n ->
    ds_obj H LF6 m (wS1 e) (ff + k) n /\ obj_inframe LF6 (ff + k) n.
  Proof.
    intros m k n Hk Hn Hkn H8 AD.
    wgeo HI0.
    destruct G as (G64 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct B as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    assert (OI : obj_inframe LF6 (ff + k) n).
    { exists (6, ff, fp). split; [left; reflexivity|]. unfold ff_addr, ff_class. cbn [fst snd]. change (fsz 6) with 4096.
      unfold WO_FLAGP in *. lia. }
    split; [| exact OI].
    split; [exact AD|]. split; [exact H8|]. split; [right; exact OI|].
    split; [unfold AIMG_TOP, AFS_HDR in *; lia|]. split; [unfold WO_FLAGP in *; lia|].
    split; [left; unfold ADS_STACK, WO_FLAGP in *; lia|].
    unfold app_obj. unfold aapp, aapp_lo, aapp_hi in G5. unfold WO_FLAGP, AFS_HDR, AFS_SIZE, AAPP_HI in *. lia.
  Qed.

  Lemma w_keep_client : forall X m m', wxkeep X m m' -> exists LBk XS, xpres H LBk (wS1 e) (X ++ XS) m m' /\
    forall a, ((ff <= a < ff + WO_FLAGP) \/ (sh ff <= a < sh ff + 512)) -> Forall (fun iv : Z * Z => a < fst iv \/ snd iv <= a) X ->
    xclient H LBk (wS1 e) (X ++ XS) a.
  Proof.
    intros X m m' (LBk & XS & INC & FS & XP).
    exists LBk, XS. split; [exact XP|]. intros a RNG NX.
    wgeo HI0.
    destruct G as (G64 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct B as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    apply (w_xc LBk X XS a INC FS).
    - unfold WO_FLAGP in *. lia.
    - unfold WO_FLAGP in *. destruct RNG as [R1|R2]; [left; lia | right; left; lia].
    - intros iv Hiv Hin. rewrite Forall_forall in NX. pose proof (NX iv Hiv). lia.
  Qed.

  Lemma w_xagree : forall X m m', wxkeep X m m' ->
    BllocRep.agree_on (fun a => ((ff <= a < ff + WO_FLAGP) \/ (sh ff <= a < sh ff + 512))
                                /\ Forall (fun iv : Z * Z => a < fst iv \/ snd iv <= a) X) m m'.
  Proof.
    intros X m m' WK x (RNG & NX) Hr.
    destruct (w_keep_client X m m' WK) as (LBk & XS & XP & XC).
    exact (proj1 (XP x Hr (XC x RNG NX))).
  Qed.

  Lemma w_fld_keep : forall X m m' a k v, wxkeep X m m' ->
    ((ff <= a /\ a + Z.of_nat k <= ff + WO_FLAGP) \/ (sh ff <= a /\ a + Z.of_nat k <= sh ff + 512)) ->
    Forall (fun iv : Z * Z => a + Z.of_nat k <= fst iv \/ snd iv <= a) X ->
    fldA m a k v -> fldA m' a k v.
  Proof.
    intros X m m' a k v WK RNG DX HF.
    pose proof (w_xagree X m m' WK) as AG.
    wgeo HI0.
    destruct G as (G64 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct B as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    unfold fldA in *.
    eapply (fld_agree ASEGS m m' a k v); [ unfold WO_FLAGP in *; lia | unfold WO_FLAGP in *; lia | exact HF |].
    intros x Hx. unfold zwin in Hx. apply (AG x); [| unfold WO_FLAGP in *; lia].
    split; [unfold WO_FLAGP in *; lia|].
    rewrite Forall_forall in DX |- *. intros iv Hiv. pose proof (DX iv Hiv). lia.
  Qed.

  Lemma w_start : forall (Q : config -> Prop) msF mo R F fc pc (REGS : bvmap 5 word -> Prop) (P : mem -> Prop),
    as_VIS H s0 msF = MS R F (Z_to_bv 64 pc) fc None m0 (seg_rom asegs) -> rfull R -> frm_zero fc ->
    as_AKREL H s0 (mkCfg msF mo) -> as_MPRES H mo0 mo -> bp_slots H e ff m0 -> bp_rc H e ff R -> REGS R -> P m0 ->
    (forall c, wsr pc REGS None P 0 c -> as_SR H Q c) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q msF mo R F fc pc REGS P VIS RF FZ KR MP SL RC RG HPm K.
    apply K.
    pose proof HPP as (_ & _ & _ & _ & _ & _ & OWN & _).
    exists s0, R, F, fc, m0, XSc0, LB0.
    split; [exact KR|]. split; [exact MP|]. split; [exact VIS|]. split; [exact RF|]. split; [exact FZ|].
    split; [exact HI0|]. split; [exact SL|]. split; [exact RC|]. split; [exact RG|].
    split; [intros x _ _; reflexivity|]. split; [exact OWN|]. split; [apply Permutation_refl|].
    split; [exact HPm|]. lia.
  Qed.

  Lemma w_chunk_w : forall (Q : config -> Prop) pc pc' (REGS REGS' : bvmap 5 word -> Prop) S (P P' : mem -> Prop) spent c,
    wsr pc REGS S P spent c ->
    (forall R F fc m XSc s LB, REGS R -> bp_rc H e ff R -> P m -> winv H e ff fp XSc s LB m -> bp_slots H e ff m ->
       wses S LB m ->
       exists R' M' W,
         CatSim.msteps asegs (MS R F (wz pc) fc None m (seg_rom asegs)) (MS R' F (wz pc') fc None M' (seg_rom asegs))
         /\ munch W m M' /\ wmono asegs m M' /\ Forall (bp_flw H e ff) W /\ wses S LB M'
         /\ bp_rc H e ff R' /\ REGS' R' /\ P' M') ->
    (forall c', wsr pc' REGS' S P' spent c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros Q pc pc' REGS REGS' S P P' spent [msF mo]
      (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & HI & SL & RC & RG & AG & OWN & SES & HPm & AL) CH K.
    cbn [cfg_ms cfg_model] in *.
    destruct (CH R F fc m XSc s LB RG RC HPm HI SL SES) as (R' & M' & W & MS & MU & WM & FW & FS & RC' & RG' & HP').
    pose proof HI as (RFS & FF & RH & AC & MI & S0 & RA & ER & ST & SV & SF & WF & WFP & XP & FSc & LV).
    pose proof (msteps_mem_inv asegs _ _ MS MI) as MI'. cbn [ms_mem] in MI'.
    wgeo HI.
    destruct G as (G64 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct B as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof stk_keepW as SK. hinst SK H HH.
    assert (ST' : stk asegs M' (w_lo e) (wSP e)).
    { apply (SK W m M' (w_lo e) (wSP e) ST MU WM). unfold AIMG_TOP, AFS_HDR in *. lia. }
    assert (FWW : Forall (wwin H e ff) W).
    { eapply Forall_impl; [| exact FW]. intros iv ([Fr|[Fs|Fk]] & _); unfold wwin.
      - right; left. exact Fr.
      - right; right. exact Fs.
      - left. unfold WO_SAVED. lia. }
    pose proof (winv_munch H HH e ff fp XSc s LB m M' W HP HI MU WM MI' ST' FWW) as HI'.
    eapply (sr_msteps H HH s msF mo R F (Z_to_bv 64 pc) fc m R' (Z_to_bv 64 pc') M' Q KR VIS RF MS).
    intros msF1 mo1 KR1 MP1 VIS1 RF1.
    apply K. exists s, R', F, fc, M', XSc, LB.
    split; [exact KR1|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP1)|]. split; [exact VIS1|].
    split; [exact RF1|]. split; [exact FZ|]. split; [exact HI'|].
    split; [exact (w_slots_munch m M' W SL MU WM FW)|]. split; [exact RC'|]. split; [exact RG'|].
    split; [exact (w_pf_munch m M' W AG MU FW)|]. split; [exact (lb_own_wmono _ _ _ OWN WM)|].
    split; [exact FS|]. split; [exact HP'|]. exact AL.
  Qed.

  Lemma w_chunk : forall (Q : config -> Prop) pc pc' (REGS REGS' : bvmap 5 word -> Prop) S (P P' : mem -> Prop) spent c,
    wsr pc REGS S P spent c ->
    (forall R F fc m XSc s LB, REGS R -> bp_rc H e ff R -> P m -> winv H e ff fp XSc s LB m -> bp_slots H e ff m ->
       wses S LB m ->
       exists R' M' W,
         CatSim.msteps asegs (MS R F (wz pc) fc None m (seg_rom asegs)) (MS R' F (wz pc') fc None M' (seg_rom asegs))
         /\ munch W m M' /\ wmono asegs m M' /\ Forall (bp_flw H e ff) W /\ Forall (wfree S) W
         /\ bp_rc H e ff R' /\ REGS' R' /\ P' M') ->
    (forall c', wsr pc' REGS' S P' spent c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros Q pc pc' REGS REGS' S P P' spent [msF mo]
      (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & HI & SL & RC & RG & AG & OWN & SES & HPm & AL) CH K.
    cbn [cfg_ms cfg_model] in *.
    destruct (CH R F fc m XSc s LB RG RC HPm HI SL SES) as (R' & M' & W & MS & MU & WM & FW & FS & RC' & RG' & HP').
    pose proof HI as (RFS & FF & RH & AC & MI & S0 & RA & ER & ST & SV & SF & WF & WFP & XP & FSc & LV).
    pose proof (msteps_mem_inv asegs _ _ MS MI) as MI'. cbn [ms_mem] in MI'.
    wgeo HI.
    destruct G as (G64 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct B as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof stk_keepW as SK. hinst SK H HH.
    assert (ST' : stk asegs M' (w_lo e) (wSP e)).
    { apply (SK W m M' (w_lo e) (wSP e) ST MU WM). unfold AIMG_TOP, AFS_HDR in *. lia. }
    assert (FWW : Forall (wwin H e ff) W).
    { eapply Forall_impl; [| exact FW]. intros iv ([Fr|[Fs|Fk]] & _); unfold wwin.
      - right; left. exact Fr.
      - right; right. exact Fs.
      - left. unfold WO_SAVED. lia. }
    pose proof (winv_munch H HH e ff fp XSc s LB m M' W HP HI MU WM MI' ST' FWW) as HI'.
    eapply (sr_msteps H HH s msF mo R F (Z_to_bv 64 pc) fc m R' (Z_to_bv 64 pc') M' Q KR VIS RF MS).
    intros msF1 mo1 KR1 MP1 VIS1 RF1.
    apply K. exists s, R', F, fc, M', XSc, LB.
    split; [exact KR1|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP1)|]. split; [exact VIS1|].
    split; [exact RF1|]. split; [exact FZ|]. split; [exact HI'|].
    split; [exact (w_slots_munch m M' W SL MU WM FW)|]. split; [exact RC'|]. split; [exact RG'|].
    split; [exact (w_pf_munch m M' W AG MU FW)|]. split; [exact (lb_own_wmono _ _ _ OWN WM)|].
    split; [exact (w_ses_munch S XSc s LB m M' W HI SES MU WM FW FS)|]. split; [exact HP'|]. exact AL.
  Qed.

  Lemma w_exit : forall (Q : config -> Prop) pc (REGS REGSx : bvmap 5 word -> Prop) (P : mem -> Prop) spent c
      (L : list nat) (SL : went H -> Z -> mem -> Prop) (r : Z),
    wsr pc REGS None P spent c -> spent <= PM_RESERVE ->
    bp_pfresh H w s0 LB0 LBs m0 c0 ->
    (forall m, P m -> bp_shad ff L m) ->
    (forall m, bp_slots H e ff m -> P m -> SL e ff m) ->
    (forall R, REGS R -> REGSx R /\ getr R 24 = wz r) -> - 2 ^ 31 <= r < 2 ^ 31 ->
    bp_kexit H e ff fp L pc SL REGSx Q mo0 ->
    as_SR H Q c.
  Proof.
    intros Q pc REGS REGSx P spent [msF mo] L SL r
      (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & HI & SL0 & RC & RG & AG & OWN & SES & HPm & AL)
      Hsp PF SH SLk RX Hr K.
    cbn [cfg_ms cfg_model wses] in *.
    destruct (RX R RG) as [RX1 R24].
    eapply (K s LB LBs m mo msF R F fc XSc w r VIS RF FZ KR MP HP HI (SLk m SL0 HPm) (SH m HPm) RC RX1 R24 Hr HWL).
    exists c0.
    pose proof HPP as (PR & PSH & HC & HU & HD & SOWN & LBOWN & CWR).
    pose proof HI as (RFS & FF & RH & AC & MI & S0 & RA & ER & ST & SV & SF & WF & WFP & XP & FSc & LV).
    pose proof HI0 as (_ & _ & RH0 & _).
    pose proof HWL as (Wp & Wc & _ & Wn & _ & _ & Wlo & WB & Wshi).
    pose proof HP as (_ & _ & (Hn0 & Hn1) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & _).
    wgeo HI0.
    destruct B as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof bp_pfresh_err as BE. hinst BE H HH. specialize (BE LINV_P5).
    eapply (BE w s0 LB0 LBs m0 c0 s LB m spent RH0 PF).
    - rewrite Wn. exact Hn0.
    - rewrite HC, Wc. unfold WO_FLAGP in *. lia.
    - exact HMD.
    - exact AL.
    - exact Hsp.
    - exact SES.
    - exact AG.
    - exact RH.
    - exact OWN.
    - exact MI.
    - destruct ER as (ev & E). exists ev. rewrite <- TP. exact E.
    - rewrite WB. exact RA.
    - exact AC.
    - rewrite Wlo, Wshi. exact S0.
    - exact LV.
  Qed.

  Lemma w_exitL : forall (Q : config -> Prop) pc (REGS REGSx : bvmap 5 word -> Prop) (P : mem -> Prop) spent c
      (L : list nat) (SL : went H -> Z -> mem -> Prop) (r : Z),
    wsr pc REGS None P spent c -> spent <= PM_RESERVE ->
    bp_ploop H LF6 e ff w s0 LB0 LBs m0 c0 ->
    (forall m, P m -> bp_shad ff L m) ->
    (forall m, bp_slots H e ff m -> P m -> SL e ff m) ->
    (forall R, REGS R -> REGSx R /\ getr R 24 = wz r) -> - 2 ^ 31 <= r < 2 ^ 31 ->
    bp_kexit H e ff fp L pc SL REGSx Q mo0 ->
    as_SR H Q c.
  Proof.
    intros Q pc REGS REGSx P spent [msF mo] L SL r
      (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & HI & SL0 & RC & RG & AG & OWN & SES & HPm & AL)
      Hsp PF SH SLk RX Hr K.
    cbn [cfg_ms cfg_model wses] in *.
    destruct (RX R RG) as [RX1 R24].
    eapply (K s LB LBs m mo msF R F fc XSc w r VIS RF FZ KR MP HP HI (SLk m SL0 HPm) (SH m HPm) RC RX1 R24 Hr HWL).
    exists c0.
    pose proof HPP as (PR & PSH & HC & HU & HD & SOWN & LBOWN & CWR).
    pose proof HI as (RFS & FF & RH & AC & MI & S0 & RA & ER & ST & SV & SF & WF & WFP & XP & FSc & LV).
    pose proof HI0 as (_ & _ & RH0 & _).
    pose proof HWL as (Wp & Wc & _ & Wn & _ & _ & Wlo & WB & Wshi).
    pose proof HP as (_ & _ & (Hn0 & Hn1) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & _).
    wgeo HI0.
    destruct B as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof bp_ploop_err as BE. hinst BE H HH. specialize (BE LINV_P5).
    eapply (BE LF6 e ff w s0 LB0 LBs m0 c0 s LB m spent RH0 PF).
    - rewrite Wn. exact Hn0.
    - rewrite HC, Wc. unfold WO_FLAGP in *. lia.
    - exact HMD.
    - exact AL.
    - exact Hsp.
    - exact SES.
    - exact AG.
    - exact RH.
    - exact OWN.
    - exact MI.
    - destruct ER as (ev & E). exists ev. rewrite <- TP. exact E.
    - rewrite WB. exact RA.
    - exact AC.
    - rewrite Wlo, Wshi. exact S0.
    - exact LV.
  Qed.
End WDC.
