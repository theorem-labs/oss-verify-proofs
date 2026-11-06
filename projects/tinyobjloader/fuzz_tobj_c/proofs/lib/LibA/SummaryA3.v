(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "word_byte"; "ax_base"; "mkAX"; "shadow_addr"; "xr_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "ss_next"; "eval"; "rm"; "obj_range"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "fst"; "option"; "snd"; "Some"; "bool"; "true"; "None"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "smatchA"; "SPA"; "jpredA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "LQPA"; "import_postA"; "import_subA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3.SA3"; "import_okPA3"; "import_postA3"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "import_okP"; "import_post"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA2"; "import_okPA2"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundF SymSoundR SymFrame SymEntail SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section SA3.
Variable segs : list Segment.

Definition import_okPA3 (rho : valuation) (ms : machine_state) (R : list sobj) (s : wsub)
           (Pre L C : axst) (Xk : list (sv * sv)) (rhoL : valuation) : Prop := ltac2:(tb__ "0|12|
S1cS43Vrho;Vms;VR;Vs;S1VPre;A1M0S1VL;A1M1VrhoL;A7S1cS11S8S8A2M2S21S21SaS1bG2R4S2VL;A1A3S1cS36S34Q40M3ScVrhoL;S12S8S8R5A3A2A2M4R4A2S37R4S38G4S34G3ScVrhoL;S14S8S8R5A3A2A2A2A2A2S1cS36Z0M5R4A2S37R4Z8M6A2A2S1bSaR4VR;A3S1eS1cS36S12S21S21SeVrho;R5A2M7A3S34G3S3S38S34G3ScVrhoL;S4VL;A1A2A2S39R7G6A2M8A2R6A2A2M9A2S37G9S14S21S21G7A3A2A2A1F_;F_;F_;F_;FoR;Fj;Fa;Fr;G2S21S1bG2R2VXk;A3S1cS36S34G3ScVrho;S12S8S8R3A3A2A2MaR2A2S37R2S38GaS34G3ScVrho;S14S8S8R3A3A2A2A2A2A2S1cS1dS13S35Q8A1MbA1McSdVrhoL;S6S34G3ScVrho;S4VC;A1A2A2MdR3A2MeA2SdVrho;GeA2A3S1cS21S1cS36G5R1A2S37R1G6A2A2S1eS1dGcSdVrho;S3S38GdS39R5G6A2A2R2A2A2S18GbA1MfA3A1S1eS1dGcSdVrhoL;S3S38GdS39R6G6A2A2R3A2A2GfA3A1F_;F_;Fj;S21SaS1cS36G5R2A2S37R2G6A2A2S1bSaR2S45G0G1A2A3S1eS1cS36S12S21S21SeVrhoL;R3A2M10A3S34G3S3S38GdG8A2R4A2A2M11A2S37G11S14S21S21G10A3A2A2A1F_;F_;Fo';Fj;A2A2F_;F_;Fa;Fr;A2A2").

Definition import_postA3 (s : wsub) (Pre L C : axst) (R : list sobj) (Xk : list (sv * sv)) : axst := ltac2:(tb__ "0|1|
S5S44Vs;SbS1VPre;A1A1S1VL;A1SbS1VC;A1A1VR;A5S19S11S8S8A2M0VXk;S3cG0G0S7S33Vs;VPre;VL;VC;A4A1S2VL;A1A4A3S4VC;A1A3").

Lemma import_postA3_full : ltac2:(tb__ "0|0|
S25S0S0S0SfSaA1S1dS0S3bR5R4R3R2R1S2R2A1A6S32R5R4R3R2R1A5A3FR;FC;FL;FPre;Fs;").
Proof. intros. reflexivity. Qed.
Lemma import_okPA2_PA3 : ltac2:(tb__ "0|0|
S9S22SfSaA1S25S0S0S0S9S20S46R8R7R6R5R4R3R2R1A8S3aR8R7R6R5R4R3R2S2R2A1R1A9A2FrhoL;FC;FL;FPre;Fs;FR;Fms;Frho;").
Proof. intros. unfold import_okPA2, import_okPA3. tauto. Qed.
Lemma import_okPA3_sub : ltac2:(tb__ "0|2|
S9S22SfSaA1S25S0S0S0SfS11S8S8A2M0A1M1G1S9G0S1bG0R1R3A3S1bG0R2R5A3F_;Fr;S3aRbRaR9R8R7R6R5R4R2A9S3aRcRbRaR9R8R7R6R4R3A9F_;F_;FrhoL;FXk';FXk;FC;FL;FPre;Fs;FR;Fms;Frho;").
Proof. intros rho ms R s Pre L C Xk Xk' rhoL Hs (A & B & D). split; [exact A|]. split; [exact B|]. intros r a Hr. apply D. apply Hs. exact Hr. Qed.

Lemma import_post_linkPA3 : ltac2:(tb__ "0|5|
S0S0S25SfSaA1M0SfS0A1SfS11S8S8A2M1A1S9SfS35Q40A1A1M2SfS2cA1M3S22S2bG3S22S2bS0S9G2G1S1bG1R1RdA3S1bG1R2S2R13A1A3F_;Fr;S1dS13G0A1S2fR12R11R10A3S15G0RfA2A3S1dS16S2eR13R12R11R10RfA5S17A3S26Vsegs;ReRdR14S10G3S29RcS2aRbRaA2A4M4A5S1bS0R7R11A3S41SbS1R15A1A1S24S23R10R13S1aRcRfRdA3A3R14A2R7A3S26Vsegs;R8R7R9G4A5S3aR12S1aReR11RfA3R15R16R17RaR18R13R9A9S1fS9S9S1cS42R14S1aR10R13R11A3R17R18S1R19A1S1R1aA1S1RcA1R1RbA9S26Vsegs;R1RaS3bR18R19RcR1aR17R15A6S10G3S29RfS2aReRdA2A4A5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;FtpL;FrhoL;FL;Fmd';Fms';Ftr';Fmd;Fms;Ftr;Ftp;Frho;FXk;FPosts;FR;Fs;FPre;FC;").
Proof using .
  intros C Pre s R Posts Xk rho tp tr ms md tr' ms' md' L rhoL tpL HXk He Hchk HsmA HinL HagL HsmAL (Hok & Hshc & Hkeep).
  pose proof HsmA as (Hsm & HMI & Hwf & Hsh & Hhz). pose proof HsmAL as (HsmL & HMIL & HwfL & HshL & HhzL).
  unfold call_checkPA in Hchk. apply andb_prop in Hchk as [Hchk HXA].
  pose proof (proj1 (forallb_forall _ _) HXA L HinL) as HXL. unfold post_okXA in HXL.
  apply andb_prop in HXL as [HXL HwfI]. apply andb_prop in HXL as [HXL HwfL']. apply andb_prop in HXL as [HXL Hbq]. apply andb_prop in HXL as [HXv Hbv].
  assert (Hfr : entails_fr (ax_S C) (ax_S Pre) s = Some R).
  { rewrite entails_frA_ref_eq in He. unfold entails_frA_ref in He. destruct (entails_fr (ax_S C) (ax_S Pre) s) as [R0|]; [|discriminate].
    match type of He with (if ?c then _ else _) = _ => destruct c; [|discriminate] end. congruence. }
  unfold virt in Hsm, HsmL. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm, HsmL.
  destruct (import_post_linkP segs (ax_S C) (ax_S Pre) s R (map ax_S Posts) rho tr (vms md tp ms) (vmd md) tr' (vms md' tpL ms') (vmd md') (ax_S L) rhoL
              Hfr Hchk Hsm ltac:(apply in_map_iff; exists L; auto) HagL HsmL Hok) as (rho' & HLK & HSP).
  exists rho'. split; [exact HLK|].
  split; [unfold virt; cbn [fst snd cfg_ms cfg_model w_tr w_cfg]; exact HSP|].
  split; [exact HMIL|].
  pose proof Hwf as HwfC0. unfold axwf in HwfC0. apply andb_prop in HwfC0 as [HXC0 HbC0].
  split.
  { unfold axwf in HwfI |- *. unfold import_postA, import_postA3 in HwfI |- *. cbn [ax_X ax_S ax_base] in HwfI |- *.
    apply andb_prop in HwfI as [HXI HbI]. rewrite forallb_app in HXI |- *. apply andb_prop in HXI as [HX1 HX2]. rewrite HX2, HbI.
    rewrite (proj2 (forallb_forall _ _)); [reflexivity|]. intros r Hr. exact (proj1 (forallb_forall _ _) HX1 r (HXk r Hr)). }
  split; [|exact HhzL].

  pose proof HLK as (A1 & A2 & A3 & A4).
  unfold shadow_ok in HshL |- *. unfold import_postA3, import_subA. cbn [ax_X ax_base ax_S].
  unfold axwf in HwfL'. apply andb_prop in HwfL' as [HXb Hbb].
  apply sv_eqb_sound in Hbq.

  pose proof Hwf as HwfC. unfold axwf in HwfC. apply andb_prop in HwfC as [HXC HbC].
  assert (EbC : eval rho' (ax_base C) = eval rho (ax_base C)).
  { symmetry. exact (eval_agree_vals (ss_next (ax_S C)) rho rho' _ A1 HbC). }
  assert (EbL : eval rho' (ax_base C) = eval rhoL (ax_base L)).
  { rewrite <- Hbq. apply (call_linkP_eval rho (vms md tp ms) R s (ax_S Pre) (ax_S C) (ax_S L) rho' rhoL (ax_base L) HLK Hbv Hbb). }

  unfold call_checkP in Hchk. apply andb_prop in Hchk as [Hchk Hposts].
  pose proof (proj1 (forallb_forall _ _) Hposts (ax_S L) ltac:(apply in_map_iff; exists L; auto)) as HP.
  unfold post_okP in HP. apply andb_prop in HP as [HP _]. apply andb_prop in HP as [HP HswfL]. apply andb_prop in HP as [_ Hpv].
  assert (E1 : forall oL, In oL (ss_objs (ax_S L)) ->
            obj_range (rho_sub rho' (import_sub s (ss_next (ax_S Pre)) (ax_S L) (ss_next (ax_S C)))) oL = obj_range rhoL oL).
  { intros oL HoL.
    pose proof (state_vars_all_and _ _ Hpv HswfL) as VARS. unfold state_vars_all in VARS.
    apply andb_prop in VARS as [VARS _]. apply andb_prop in VARS as [_ VOB].
    apply (obj_range_agree_vars (fun v => post_vars s (ss_next (ax_S Pre)) (ss_next (ax_S C)) v && (v <? ss_next (ax_S L))%positive)).
    - intros v0 H. apply andb_prop in H as [H1 H2]. apply Pos.ltb_lt in H2. cbn [rho_sub rw]. apply A4; [exact H1 | lia].
    - intros l0. cbn [rho_sub rl]. destruct A3 as [_ AL]. rewrite <- AL. cbn [rho_sub rho_absorb rl]. destruct A1 as [_ AL1]. exact (AL1 l0).
    - exact (proj1 (forallb_forall _ _) VOB oL HoL). }
  destruct (entails_frA_sound segs C Pre s R rho tp tr ms md He HsmA) as (HsmPre & _ & _ & HwfR & HinR).
  assert (ER : forall oR, In oR R -> obj_range rho' oR = obj_range rho oR).
  { intros oR HoR. exact (obj_range_agree_vals (ss_next (ax_S C)) rho rho' oR A1 (proj1 (forallb_forall _ _) HwfR oR HoR)). }
  apply Forall_app. split.
  -
    apply Forall_forall. intros [b l] HrK. pose proof (HXk _ HrK) as Hr. pose proof (proj1 (Forall_forall _ _) Hsh _ Hr) as Hx.
    pose proof (proj1 (forallb_forall _ _) HXC _ Hr) as Hbl. unfold xr_below in Hbl. cbn [fst snd] in Hbl. apply andb_prop in Hbl as [Hb1 Hl1].
    unfold xr_ok in Hx |- *. cbn [fst snd] in Hx |- *.
    rewrite <- (eval_agree_vals (ss_next (ax_S C)) rho rho' b A1 Hb1).
    rewrite <- (eval_agree_vals (ss_next (ax_S C)) rho rho' l A1 Hl1).
    rewrite EbC.
    destruct Hx as (H8 & Hnw & Hx). split; [exact H8|]. split; [exact Hnw|].
    intros a Ha. destruct (Hx a Ha) as (Hoff & Hout & Hwd & v & Hv & Henc).
    assert (OUT : forall x, outside_all rho (ss_objs (ax_S C)) x ->
              (forall o', In o' (new_objs (ax_S Pre) (ax_S L)) -> ~ (fst (obj_range rhoL o') <= bv_unsigned x < snd (obj_range rhoL o'))) ->
              outside_all rho' (ss_objs (import_post s (ss_next (ax_S Pre)) (ax_S L) (ss_next (ax_S C)) R)) x).
    { intros x HoutX HnewX. unfold import_post. cbn [ss_objs set_objs subst_state]. apply outside_all_app_iff. split.
      * apply Forall_forall. intros o' Ho'. apply in_map_iff in Ho' as (oL & <- & HoL). cbn zeta.
        rewrite obj_range_subst, (E1 oL HoL).
        destruct (new_objs_spec (ax_S Pre) (ax_S L) oL HoL) as [FR|NEW]; [|exact (HnewX oL NEW)].
        apply existsb_exists in FR as (oP & HinP & SF). rewrite (same_frame_range rhoL oL oP SF).
        assert (E2 : obj_range rhoL oP = obj_range (rho_sub (rho_absorb rho R (vms md tp ms)) s) oP).
        { apply (obj_range_agree_vals (ss_next (ax_S Pre))); [exact HagL|].
          pose proof (smatchA_swf segs _ _ _ _ HsmPre) as W. exact (proj1 (forallb_forall _ _) (swf_objs _ W) oP HinP). }
        rewrite E2. destruct (entails_fr_ranges_ex segs (ax_S C) (ax_S Pre) s R rho tr (vms md tp ms) (vmd md) Hfr Hsm oP HinP) as (oC & HoC & ->).
        exact (proj1 (Forall_forall _ _) HoutX oC HoC).
      * apply Forall_forall. intros oR HoR. cbn zeta. rewrite (ER oR HoR). exact (proj1 (Forall_forall _ _) HoutX oR (HinR oR HoR)). }
    assert (Hj0 : 0 <= (bv_unsigned (eval rho (ax_base C)) + a / 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Eba : shadow_addr (bv_unsigned (eval rho (ax_base C))) a
                  = word_byte (bv_unsigned (eval rho (ax_base C)) + a / 8) ((bv_unsigned (eval rho (ax_base C)) + a / 8) mod 8)).
    { unfold shadow_addr. rewrite word_byte_self; [reflexivity | lia]. }
    destruct (Hkeep (b, l) a HrK Ha) as (Hrm & Hdef & Hnewo).
    split; [exact Hoff|]. split; [|split].
    + rewrite Eba. apply OUT; [rewrite <- Eba; exact Hout | intros o' Ho'; exact (Hnewo _ o' Hj0 Ho')].
    + intros j Hj. destruct (Hwd j Hj) as [Hoj Hrj].
      split; [apply OUT; [exact Hoj | intros o' Ho'; exact (Hnewo j o' Hj Ho')] | rewrite A2; exact (Hdef j Hj Hrj)].
    + exists v. split; [|exact Henc]. rewrite A2, Hrm. exact Hv.
  -
    apply Forall_forall. intros r' Hr'. apply in_map_iff in Hr' as ([b l] & <- & Hr).
    pose proof (proj1 (Forall_forall _ _) HshL _ Hr) as Hx.
    pose proof (proj1 (forallb_forall _ _) HXv _ Hr) as Hv. cbn [fst snd] in Hv. apply andb_prop in Hv as [Hvb Hvl].
    pose proof (proj1 (forallb_forall _ _) HXb _ Hr) as Hbl. unfold xr_below in Hbl. cbn [fst snd] in Hbl. apply andb_prop in Hbl as [Hbb' Hlb].
    unfold xr_ok in Hx |- *. unfold xr_subst. cbn [fst snd] in Hx |- *.
    rewrite (call_linkP_eval rho (vms md tp ms) R s (ax_S Pre) (ax_S C) (ax_S L) rho' rhoL b HLK Hvb Hbb').
    rewrite (call_linkP_eval rho (vms md tp ms) R s (ax_S Pre) (ax_S C) (ax_S L) rho' rhoL l HLK Hvl Hlb).
    rewrite EbL.
    destruct Hx as (H8 & Hnw & Hx). split; [exact H8|]. split; [exact Hnw|].
    intros a Ha. destruct (Hx a Ha) as (Hoff & Hout & Hwd & v & Hv & Henc).
    assert (OUT : forall x, outside_all rhoL (ss_objs (ax_S L)) x ->
              (forall oR, In oR R -> ~ (fst (obj_range rho oR) <= bv_unsigned x < snd (obj_range rho oR))) ->
              outside_all rho' (ss_objs (import_post s (ss_next (ax_S Pre)) (ax_S L) (ss_next (ax_S C)) R)) x).
    { intros x HoutX HRX. unfold import_post. cbn [ss_objs set_objs subst_state].
      apply outside_all_app_iff. split.
      * apply Forall_forall. intros o' Ho'. apply in_map_iff in Ho' as (oL & <- & HoL). cbn zeta.
        rewrite obj_range_subst, (E1 oL HoL). exact (proj1 (Forall_forall _ _) HoutX oL HoL).
      * apply Forall_forall. intros oR HoR. cbn zeta. rewrite (ER oR HoR). exact (HRX oR HoR). }
    assert (Hj0 : 0 <= (bv_unsigned (eval rhoL (ax_base L)) + a / 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Eba : shadow_addr (bv_unsigned (eval rhoL (ax_base L))) a
                  = word_byte (bv_unsigned (eval rhoL (ax_base L)) + a / 8) ((bv_unsigned (eval rhoL (ax_base L)) + a / 8) mod 8)).
    { unfold shadow_addr. rewrite word_byte_self; [reflexivity | lia]. }
    split; [exact Hoff|]. split; [|split].
    + rewrite Eba. apply OUT; [rewrite <- Eba; exact Hout | intros oR HoR; exact (Hshc (b, l) a _ oR Hr Ha Hj0 HoR)].
    + intros j Hj. destruct (Hwd j Hj) as [Hoj Hrj].
      split; [apply OUT; [exact Hoj | intros oR HoR; exact (Hshc (b, l) a j oR Hr Ha Hj HoR)] | rewrite A2; exact Hrj].
    + exists v. split; [|exact Henc]. rewrite A2. exact Hv.
Qed.

Theorem call_soundPA3 : ltac2:(tb__ "0|5|
S3fOF_;S28S28S0S0S25SfSaA1M0SfS11S0S2dA2M1A1SfS11S8S8A2M2A1S40S9SfS35Q40A1A1M3G2S1bG2R1R5A3S1bG2R2S2RbA1A3F_;Fr;S1dS13G0A1S2fRaR9R8A3S15G0R7A2A3S1dS16S2eRbRaR9R8S3cG1S0S12S0S2dA2R7A4A5S17A3S9G3S3eVsegs;R11S27Vsegs;RfRdR2R1A5S31Vsegs;SbS1RdA1A1R2R1RaA5A4Ftp1;Frho1;SfS2cA1M4S22S2bS26Vsegs;R9R8R10S10G4S29R3S2aR2R1A2A4A5R13RaR9R4R2A4R13S24S23RbRfS1aR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S0S2dG4S22S2bS9G3G4S22S2bS1bG1S10S0S2dRaR9A4R14A3S26Vsegs;R12R11R19S10G4S29R9S2aR8R7A2A4A5R1cR13R12RaR8A4S41SbS1R1aA1A1S24S23R14R18S1aR9R13RaA3A3R19A2R8A3S26Vsegs;R9R8ReS10G4S29R7S2aR6R5A2A4A5ReS24S23R16R1aS1aRbR15RcA3A3R1bA2R15RaR9R8R6A6S1cS3aR17S1aRcR16RdA3R1bR1cR1dR10R1eR19RbA9S9S42R18S1aRdR17ReA3R1cR1dS1R1eA1S1R1fA1S1R11A1R1RcA9S3eVsegs;R23S27Vsegs;S30R11S24S23R19R1dS1aReR18RfA3A3R1eA2R18RdRcA5S3bR1eR1fR12R20R1dR1bA6R2RcA5R1aA4F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;S3eVsegs;R12S27Vsegs;R11RfR8R7A5R9A4F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;Fok;").
Proof using .
  intros ok J Jp C Pre s R Posts Xk Q rho tp HXk He Hchk Hsum Hin Hout.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs C Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp n); [|split; [exact HsmPre|exact (Hin tr ms md Hsm Hk)]].
  intros w' (L & JL & rhoL & tpL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (Hout L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm Hk HagL HsmL Hk') as [Hok Hcont].
  destruct (import_post_linkPA3 C Pre s R (map fst Posts) Xk rho tp tr ms md tr' ms' md' L rhoL tpL HXk He Hchk Hsm
              ltac:(apply in_map_iff; exists (L, JL); auto) HagL HsmL Hok) as (rho' & HLK & HSP).
  apply (Hcont rho' HLK n HgQ). split; [exact HSP|]. exact Hk'.
Qed.

Theorem call_completePA3 : ltac2:(tb__ "0|5|
S28S28S0S0S25SfSaA1M0SfS11S0S2dA2M1A1SfS11S8S8A2M2A1S3fOF_;S9SfS35Q40A1A1M3G2S1bG2R1R5A3S1bG2R2S2RbA1A3F_;Fr;S1dS13G0A1S2fRaR9R8A3S15G0R7A2A3S1dS16S2eRbRaR9R8S3cG1S0S12S0S2dA2R7A4A5S17A3S9G3S3dVsegs;S27Vsegs;RfRdR2R1A5S31Vsegs;SbS1RdA1A1R2R1RaA5A3Ftp1;Frho1;SfS2cA1M4S22S2bS26Vsegs;R9R8R10S10G4S29R3S2aR2R1A2A4A5R13RaR9R4R2A4R13S24S23RbRfS1aR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S0S2dG4S22S2bS9G3G4S22S2bS1bG1S10S0S2dRaR9A4R14A3S26Vsegs;R12R11R19S10G4S29R9S2aR8R7A2A4A5R1cR13R12RaR8A4S41SbS1R1aA1A1S24S23R14R18S1aR9R13RaA3A3R19A2R8A3S26Vsegs;R9R8ReS10G4S29R7S2aR6R5A2A4A5ReS24S23R16R1aS1aRbR15RcA3A3R1bA2R15RaR9R8R6A6S1cS3aR17S1aRcR16RdA3R1bR1cR1dR10R1eR19RbA9S9S42R18S1aRdR17ReA3R1cR1dS1R1eA1S1R1fA1S1R11A1R1RcA9S3dVsegs;S27Vsegs;S30R11S24S23R19R1dS1aReR18RfA3A3R1eA2R18RdRcA5S3bR1eR1fR12R20R1dR1bA6R2RcA5R1aA3F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;S3dVsegs;S27Vsegs;R11RfR8R7A5R9A3F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Proof using .
  intros J Jp C Pre s R Posts Xk Q rho tp HXk He Hchk Hsum Hin Hout.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs C Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre (Hin tr ms md Hsm Hk))) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & JL & rhoL & tpL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (Hout L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm Hk HagL HsmL Hk') as [Hok Hcont].
  destruct (import_post_linkPA3 C Pre s R (map fst Posts) Xk rho tp tr ms md tr' ms' md' L rhoL tpL HXk He Hchk Hsm
              ltac:(apply in_map_iff; exists (L, JL); auto) HagL HsmL Hok) as (rho' & HLK & HSP).
  destruct (Hcont rho' HLK _ (conj HSP Hk')) as (w'' & Hsteps' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

End SA3.
