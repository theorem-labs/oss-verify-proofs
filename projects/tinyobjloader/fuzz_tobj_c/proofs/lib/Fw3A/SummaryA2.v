(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "word_byte"; "ax_X"; "ax_base"; "shadow_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sobj"; "eval"; "ss_next"; "rm"; "obj_range"; "@Corelib.Init.Datatypes"; "list"; "pair"; "fst"; "option"; "snd"; "Some"; "bool"; "prod"; "true"; "None"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "smatchA"; "SPA"; "jpredA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "call_checkPA"; "entails_frA"; "import_postA"; "J_ofPA"; "LQPA"; "import_okPA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA2.SA2"; "import_okPA2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "import_okP"; "new_objs"; "@Corelib.Lists.ListDef"; "map"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundF SymSoundR SymFrame SymEntail SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section SA2.
Variable segs : list Segment.

Definition import_okPA2 (rho : valuation) (ms : machine_state) (R : list sobj) (s : wsub)
           (Pre L C : axst) (rhoL : valuation) : Prop := ltac2:(tb__ "0|12|
S7S3dVrho;Vms;VR;Vs;S1VPre;A1M0S1VL;A1M1VrhoL;A7S7S19ScScA2M2S1cS1cSdS31G2R4S3VL;A1A3S7S32S2fQ40M3SeVrhoL;S14ScScR5A3A2A2M4R4A2S33R4S34G4S2fG3SeVrhoL;S16ScScR5A3A2A2A2A2A2S7S32Z0M5R4A2S33R4Z8M6A2A2S31SdR4VR;A3S9S7S32S14S1cS1cS11Vrho;R5A2M7A3S2fG3S2S34S2fG3SeVrhoL;S4VL;A1A2A2S35R7G6A2M8A2R6A2A2M9A2S33G9S16S1cS1cG7A3A2A2A1F_;F_;F_;F_;FoR;Fj;Fa;Fr;G2S1cS31G2R2S3VC;A1A3S7S32S2fG3SeVrho;S14ScScR3A3A2A2MaR2A2S33R2S34GaS2fG3SeVrho;S16ScScR3A3A2A2A2A2A2S7S8S15S30Q8A1MbA1McS10VrhoL;S5S2fG3SeVrho;S4VC;A1A2A2MdR3A2MeA2S10Vrho;GeA2A3S7S1cS7S32G5R1A2S33R1G6A2A2S9S8GcS10Vrho;S2S34GdS35R5G6A2A2R2A2A2S1bGbA1MfA3A1S9S8GcS10VrhoL;S2S34GdS35R6G6A2A2R3A2A2GfA3A1F_;F_;Fj;S1cSdS7S32G5R2A2S33R2G6A2A2S31SdR2S3eG0G1A2A3S9S7S32S14S1cS1cS11VrhoL;R3A2M10A3S2fG3S2S34GdG8A2R4A2A2M11A2S33G11S16S1cS1cG10A3A2A2A1F_;F_;Fo';Fj;A2A2F_;F_;Fa;Fr;A2A2").

Lemma import_okPA_PA2 : ltac2:(tb__ "0|0|
SbS1dS12SdA1S20S0S0S0SbS2eR8R7R6R5R4R3R2R1A8S36R9R8R7R6R5R4R3R2A8F_;FrhoL;FC;FL;FPre;Fs;FR;Fms;Frho;").
Proof.
  intros rho ms R s Pre L C rhoL (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros r a Hr Ha. split; [|split].
  - pose proof (urange (eval rho (ax_base C))) as RB.
    assert (Hz : 0 <= bv_unsigned (eval rho (ax_base C)) + a / 8) by (pose proof (urange (eval rho (fst r))); lia).
    rewrite (shadow_addr_word_byte _ a Hz). apply (proj1 (H3 r a _ Hr Ha ltac:(apply Z.mod_pos_bound; lia))).
  - intros j Hj Hd. rewrite (proj1 (H3 r a j Hr Ha Hj)). exact Hd.
  - intros j o' Hj Ho'. exact (proj2 (H3 r a j Hr Ha Hj) o' Ho').
Qed.

Lemma import_post_linkPA2 : ltac2:(tb__ "0|4|
S0S0S20S12SdA1M0S12S0A1SbS12S30Q40A1A1M1S12S27A1M2S1dS26G2S1dS26S0SbG1S8S15G0A1S2aR10RfReA3S17G0RdA2A3S8S18S29R11R10RfReRdA5S1aA3S21Vsegs;RdRcR12S13G2S24RbS25RaR9A2A4M3A5S31S0R6RfA3S3bSfS1R13A1A1S1fS1eRfR11S6RbReRcA3A3R12A2R6A3S21Vsegs;R7R6R8G3A5S36R11S6RdR10ReA3R13R14R15R9R16R8A8SaSbSbS7S3cR13S6RfR12R10A3R15R16S1R17A1S1R18A1S1RbA1R1RaA9S21Vsegs;R1R9S2bR16R17RbR18R15A5S13G2S24ReS25RdRcA2A4A5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;FtpL;FrhoL;FL;Fmd';Fms';Ftr';Fmd;Fms;Ftr;Ftp;Frho;FPosts;FR;Fs;FPre;FC;").
Proof using .
  intros C Pre s R Posts rho tp tr ms md tr' ms' md' L rhoL tpL He Hchk HsmA HinL HagL HsmAL (Hok & Hshc & Hkeep).
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
  split; [exact HMIL|]. split; [exact HwfI|]. split; [|exact HhzL].

  pose proof HLK as (A1 & A2 & A3 & A4).
  unfold shadow_ok in HshL |- *. unfold import_postA, import_subA. cbn [ax_X ax_base ax_S].
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
    apply Forall_forall. intros [b l] Hr. pose proof (proj1 (Forall_forall _ _) Hsh _ Hr) as Hx.
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
    destruct (Hkeep (b, l) a Hr Ha) as (Hrm & Hdef & Hnewo).
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

Theorem call_soundPA2 : ltac2:(tb__ "0|4|
S39OF_;S23S23S0S0S20S12SdA1M0S12S19S0S28A2M1A1S3aSbS12S30Q40A1A1M2S8S15G0A1S2aR8R7R6A3S17G0R5A2A3S8S18S29R9R8R7R6S3fG1S0S14S0S28A2R5A4A5S1aA3SbG2S38Vsegs;RfS22Vsegs;RdRbR2R1A5S2dVsegs;SfS1RbA1A1R2R1R8A5A4Ftp1;Frho1;S12S27A1M3S1dS26S21Vsegs;R8R7ReS13G3S24R3S25R2R1A2A4A5R11R9R8R4R2A4R11S1fS1eRaRdS6R3R9R4A3A3ReA2R9R5R3A4F_;F_;Fmd;Fms;Ftr;S0S28G3S1dS26SbG2G3S1dS26S31G1S13S0S28RaR9A4R12A3S21Vsegs;R11R10R17S13G3S24R9S25R8R7A2A4A5R1aR12R11RaR8A4S3bSfS1R18A1A1S1fS1eR13R16S6R9R12RaA3A3R17A2R8A3S21Vsegs;R9R8ReS13G3S24R7S25R6R5A2A4A5ReS1fS1eR15R18S6RbR14RcA3A3R19A2R14RaR9R8R6A6S7S36R16S6RcR15RdA3R19R1aR1bR10R1cRbA8SbS3cR17S6RdR16ReA3R1aR1bS1R1cA1S1R1dA1S1R11A1R1RcA9S38Vsegs;R21S22Vsegs;S2cR11S1fS1eR18R1bS6ReR17RfA3A3R1cA2R17RdRcA5S2bR1cR1dR12R1eR1bA5R2RcA5R19A4F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;S38Vsegs;R10S22Vsegs;RfRdR7R6A5R8A4F_;F_;F_;F_;F_;Ftp;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJp;FJ;Fok;").
Proof using .
  intros ok J Jp C Pre s R Posts Q rho tp He Hchk Hsum Hin Hout.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs C Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp n); [|split; [exact HsmPre|exact (Hin tr ms md Hsm Hk)]].
  intros w' (L & JL & rhoL & tpL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (Hout L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm Hk HagL HsmL Hk') as [Hok Hcont].
  destruct (import_post_linkPA2 C Pre s R (map fst Posts) rho tp tr ms md tr' ms' md' L rhoL tpL He Hchk Hsm
              ltac:(apply in_map_iff; exists (L, JL); auto) HagL HsmL Hok) as (rho' & HLK & HSP).
  apply (Hcont rho' HLK n HgQ). split; [exact HSP|]. exact Hk'.
Qed.

Theorem call_completePA2 : ltac2:(tb__ "0|4|
S23S23S0S0S20S12SdA1M0S12S19S0S28A2M1A1S39OF_;SbS12S30Q40A1A1M2S8S15G0A1S2aR8R7R6A3S17G0R5A2A3S8S18S29R9R8R7R6S3fG1S0S14S0S28A2R5A4A5S1aA3SbG2S37Vsegs;S22Vsegs;RdRbR2R1A5S2dVsegs;SfS1RbA1A1R2R1R8A5A3Ftp1;Frho1;S12S27A1M3S1dS26S21Vsegs;R8R7ReS13G3S24R3S25R2R1A2A4A5R11R9R8R4R2A4R11S1fS1eRaRdS6R3R9R4A3A3ReA2R9R5R3A4F_;F_;Fmd;Fms;Ftr;S0S28G3S1dS26SbG2G3S1dS26S31G1S13S0S28RaR9A4R12A3S21Vsegs;R11R10R17S13G3S24R9S25R8R7A2A4A5R1aR12R11RaR8A4S3bSfS1R18A1A1S1fS1eR13R16S6R9R12RaA3A3R17A2R8A3S21Vsegs;R9R8ReS13G3S24R7S25R6R5A2A4A5ReS1fS1eR15R18S6RbR14RcA3A3R19A2R14RaR9R8R6A6S7S36R16S6RcR15RdA3R19R1aR1bR10R1cRbA8SbS3cR17S6RdR16ReA3R1aR1bS1R1cA1S1R1dA1S1R11A1R1RcA9S37Vsegs;S22Vsegs;S2cR11S1fS1eR18R1bS6ReR17RfA3A3R1cA2R17RdRcA5S2bR1cR1dR12R1eR1bA5R2RcA5R19A3F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;S37Vsegs;S22Vsegs;RfRdR7R6A5R8A3F_;F_;F_;F_;F_;Ftp;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Proof using .
  intros J Jp C Pre s R Posts Q rho tp He Hchk Hsum Hin Hout.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs C Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre (Hin tr ms md Hsm Hk))) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & JL & rhoL & tpL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (Hout L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm Hk HagL HsmL Hk') as [Hok Hcont].
  destruct (import_post_linkPA2 C Pre s R (map fst Posts) rho tp tr ms md tr' ms' md' L rhoL tpL He Hchk Hsm
              ltac:(apply in_map_iff; exists (L, JL); auto) HagL HsmL Hok) as (rho' & HLK & HSP).
  destruct (Hcont rho' HLK _ (conj HSP Hk')) as (w'' & Hsteps' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

End SA2.
