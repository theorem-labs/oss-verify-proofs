(* fuzz_preset image B' (asan-ubsan pin d663f82d7f48, #102), parse_value 0x8637c: the walk's
   COMPOSITION. The kit's record text tparse_value_specX d CTX CTX0 CW (lib/A/PRH_FnParse.v): the post-implication form with
   the hull use, the outcome and the outcome of an injected reading, rd_ledger_move over the grant-all trace with g_most
   and the refused peak, and in each result arm the free-order tie (pj_foR against the model's prhPv_frees) and, on
   success, the node's capacity words (pj_ncapR), concluded in the re-hiding relation SRr' segs RZ_cf - from the four
   segments at the cuts of PvB_Defs.v: entry .. C1 (PvB_A pvA_holds), C1 .. N / exit (PvB_D pvD_holds), N .. exit
   (PvB_N pvN_seg), exit .. ret (PvB_X pvX_holds). Each segment runs plain SRr to the continuation post pv_FINK (the
   final post in the record's relation); the composed run is lifted once (YGcfRhLift.ra_rh_of_SRr). It has no image
   fact of its own. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetHullBudget.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Instance PIBt : PrhImg := prh_img_B.

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.


(* the record's post Q at an entry en (the kit's tpvP_Q, lib/A/PRH_FnParse.v), from the cut's pv_Q, read and built through
   the two records (PvB_Defs.v pvQ_R, PRH_FnParse.v tpvP_R) *)
Lemma pvTop_Q : forall en ly' S' Hp' W' regs' mem' md',
  pv_Q B en ly' S' Hp' W' regs' mem' md' ->
  tpvP_Q B (pe_d en) (pe_ly en) (pe_S en) (pe_q en) (pe_text en) (pe_len en) (pe_p en) (pe_tb en) (pe_v en)
    (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) ly' S' Hp' W' regs' mem' md'.
Proof.
intros en ly' S' Hp' W' regs' mem' md' ((code & Hcode & HQm) & _).
apply pvQ_R_of in HQm. destruct HQm as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HR).
apply (tpvP_Q_of_R md' (ok := ok) (res := res) (tr := tr) (okr := okr) (D := D) (Lam' := Lam') (peak' := peak')
  (cnt' := cnt') (fail' := fail') (ran' := ran')).
pose proof (pvq_fresh HR) as Hfresh. pose proof (pvq_perm HR) as Hab. pose proof (pvq_fr HR) as Hfr.
pose proof (pvq_peak HR) as Hpk. pose proof (pvq_arm HR) as Hres.
refine {| tpvP_run := pvq_run HR; tpvP_ledger := pvq_ledger HR; tpvP_room := pvq_room HR; tpvP_hull := pvq_hull HR;
  tpvP_live := proj1 (pvq_rp HR); tpvP_pos := proj2 (pvq_rp HR); tpvP_outcome := pvq_outc HR;
  tpvP_injected := pvq_inj HR; tpvP_ledger_move := pvq_move HR; tpvP_blocks_move := _; tpvP_bytes := pvq_bytes HR;
  tpvP_lsum := pvq_lsum HR; tpvP_arm := _ |}.
- unfold rd_blocks_move. repeat split; assumption.
- destruct res as [[t r]|].
  + destruct Hres as (Hc & Hft & H1 & H2 & Hnc & H3). subst code.
    split; [exact Hcode|]. split; [exact Hft|]. split; [exact H1|]. split; [exact H2|]. split; [exact Hnc|]. exact H3.
  + destruct Hres as (Hc & Hft & H1 & H2). subst code.
    split; [exact Hcode|]. split; [exact Hft|]. split; [exact H1|]. exact H2.
Qed.

(* the four segments' statements, as the segment files prove them: each a plain run to the continuation post *)
Hypothesis SEG_A : forall en, pv_pre B ARx en ->
  (forall W2 ms2 md2, pv_at_C1 B ARx en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK B ARx en)) ->
  SRr SEGS (pe_W en) (cfg_at (fx := fx0) SEGS (pa_sigma AS_parse_value) (pe_regs en) (pe_mem en) (pe_md en))
    (pv_FINK B ARx en).
Hypothesis SEG_D : forall en W' ms mdc, pv_pre B ARx en ->
  (forall CTX CTX0 CW, tparse_items_specX (fx := fx0) (PI := PIBt) (PA := PA) B ARx SK (pe_d en) CTX CTX0 CW) ->
  pv_at_C1 B ARx en W' ms mdc ->
  (forall W2 ms2 md2, pv_at_N B ARx en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK B ARx en)) ->
  (forall W2 ms2 md2, pv_at_exit B ARx en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK B ARx en)) ->
  SRr SEGS W' (mkCfg ms mdc) (pv_FINK B ARx en).
Hypothesis SEG_N : forall en W' ms mdc, pv_pre B ARx en -> pv_at_N B ARx en W' ms mdc ->
  (forall W2 ms2 md2, pv_at_exit B ARx en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK B ARx en)) ->
  SRr SEGS W' (mkCfg ms mdc) (pv_FINK B ARx en).
Hypothesis SEG_X : forall en W' ms mdc, pv_pre B ARx en -> pv_at_exit B ARx en W' ms mdc ->
  SRr SEGS W' (mkCfg ms mdc) (pv_FINK B ARx en).

(* the record text (lib/A/PRH_FnParse.v), at each depth d FROM parse_items' text at the same depth d (the step of the
   parse_value / parse_items pair; lib/A/VrdUnit.v's depth induction closes it, with parse_items at d from parse_value
   at d + 1) *)
Theorem pvTop_compose_step : forall d,
  (forall CTX CTX0 CW, @tparse_items_specX fx0 rc ci cp PIBt RL B_prog_listing PA B ARx SK d CTX CTX0 CW) ->
  forall CTX CTX0 CW, @tparse_value_specX fx0 rc ci cp PIBt RL B_prog_listing PA B ARx SK d CTX CTX0 CW.
Proof.
intros d TPI CTX CTX0 CW ly S Hp W regs mem md ch e q text len p tb v Lam peak cnt fail ran most own
  HPRE HMN HCTX HUNIV HCURE HCWE HCH HCUR Ha0 Ha1 HRD HROOM HWR HPKS HPK24 HHB HFR.
set (en := mkPvEnt ly S Hp W regs mem md ch e q text len p tb v Lam peak cnt fail ran most own CTX CTX0 CW d).
assert (HP : pv_pre B ARx en).
{ unfold pv_pre; cbn.
  refine (conj HPRE (conj HCTX (conj HUNIV (conj HCURE (conj HCH (conj HCUR (conj Ha0 (conj Ha1 (conj HRD
    (conj HROOM (conj HFR (conj HMN (conj HPKS (conj HPK24 (conj HCWE (conj HWR HHB)))))))))))))))). }
(* the composed plain run to pv_FINK, lifted once into the record's relation *)
apply (YGcfRhLift.ra_rh_of_SRr SEGS YGcfRehidePost.RZ_cf).
eapply SRr_mono; [apply (SEG_A en HP); intros W2 ms2 md2 HC1;
  apply (SEG_D en W2 ms2 md2 HP TPI HC1);
  [intros W3 ms3 md3 HN; apply (SEG_N en W3 ms3 md3 HP HN); intros W4 ms4 md4 HX; exact (SEG_X en W4 ms4 md4 HP HX)
  |intros W4 ms4 md4 HX; exact (SEG_X en W4 ms4 md4 HP HX)]|].
intros W1 c1 _ HK. unfold pv_FINK in HK.
eapply YSRrG.SRr'_mono; [exact HK|].
intros W' c' _ (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & Hfrm & Hfk & HPW & HJ & Hwin & Hpres & HQ).
exists fx', ly', S', Hp', regs', mem', md', k, WS.
split; [exact Hc|]. split; [exact Hfrm|]. split; [exact Hfk|]. split; [exact HPW|]. split; [exact HJ|].
split; [exact Hwin|]. split; [exact Hpres|].
(* the m-form post: the record's Q and the memnorm keep, from the cut's pv_Q (memnorm at the exit memory) *)
split; [exact (pvTop_Q en ly' S' Hp' W' regs' mem' md' HQ)|].
destruct HQ as (_ & HMN'). intros _. exact HMN'.
Qed.

(* the same at every depth, from parse_items' text at every depth *)
Theorem pvTop_compose : forall d CTX CTX0 CW,
  (forall d' CTX' CTX0' CW', @tparse_items_specX fx0 rc ci cp PIBt RL B_prog_listing PA B ARx SK d' CTX' CTX0' CW') ->
  @tparse_value_specX fx0 rc ci cp PIBt RL B_prog_listing PA B ARx SK d CTX CTX0 CW.
Proof. intros d CTX CTX0 CW TPI. exact (pvTop_compose_step d (TPI d) CTX CTX0 CW). Qed.

End c.
