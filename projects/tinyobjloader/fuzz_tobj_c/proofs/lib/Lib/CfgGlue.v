(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "sstate"; "holds"; "agree_below"; "ss_next"; "ss_facts"; "sprop_below"; "eval"; "sobj"; "rl"; "rw"; "ss_lenient"; "sv_below"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "andb"; "option"; "false"; "Some"; "pair"; "app"; "nat"; "negb"; "orb"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "vn_state"; "vn_rank"; "add_facts"; "enode"; "SPfamE"; "vn_var"; "edge"; "SPfam"; "to_enode"; "vmeas"; "cfg_edges"; "e_leaf"; "e_src"; "e_sub"; "e_tgt"; "eedge_ok"; "@Corelib.Init.Logic"; "eq"; "or"; "False"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "LQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_id_below"; "rho_absorb"; "sv_subst"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "lf_state"; "uleq"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "entails_fr"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "ltb"; "leb"; "mul"; "pow"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.ECfgI"; "to_enodeI"; "vmeasI"; "echeckI"; "check_ecfgI"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_check"; "import_post"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section GlueG.
Variable segs : list Segment.

Lemma SP_entails_sem1 : ltac2:(tb__ "0|0|
SeS39A1S38OF_;F_;S2S2SeS1A1S3bS0S32S2cSfS4aR6R5R3A3S10A3S2cSfS48S1S7S5R6A1A1R5A3S10A3S36S1S3R4A1S6R8A1A3S36S1S3S3aR5R6A2A1R7A3F_;S30Vsegs;RaR9R5R4A5S30Vsegs;RbS1eR8R9A2S3aR6R7A2R5A5F_;F_;F_;F_;Fw;Frho;Fs;FF;FT0;FL;FK;").
Proof using .
  intros K L T0 F s rho w He Hb HF [Hsm Hk]. split; [|exact Hk].
  apply smatch_add_facts; [eapply entails_sound; eauto | | exact Hb].
  apply HF. destruct w as [tr [ms md]].
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))).
Qed.

Lemma exit_reenter_G : ltac2:(tb__ "0|1|
S32OF_;SeS39A1S38OF_;F_;S0OF_;S45SeS2A1S35S2S2SeS1A1S3bS47S2S1eR2R3A2R6A3S2cSfS4aR5R4R2A3S10A3S2cSfS3cR3R9A2S10A3S0S0RdR2A1S4RdR3R2A3RfR3A1F_;F_;Frho';Frho;S2cSfS48S1S7S5R7A1A1R6A3S10A3S0ReR1A1M0S36S1S3R2A1S6RbA1A3S36S1S3S3aR3R9A2A1RaA3F_;F_;Frho;S0RfR1A1S34Vsegs;R12S30Vsegs;R11RcR2A4S32S2dS23Vsegs;R12R11RfR1A5G0A2Lw;A4F_;Frho;F_;F_;F_;F_;F_;F_;Fs;FF;FT0;FE;FQ;Fcuts;Fg;FG;FK;Fok;").
Proof using .
  intros ok K G g cuts Q E T0 F s Hin He Hid HG Hb HF rho Hg.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hsp. left. exists (add_facts F T0), (rho_sub rho s).
  split; [exact Hin|]. split.
  - eapply HG; [exact Hg|]. apply rho_sub_agree. exact Hid.
  - eapply SP_entails_sem1; [exact He | exact Hb | apply HF; exact Hg | exact Hsp].
Qed.

Lemma exit_post_G : ltac2:(tb__ "0|0|
S32OF_;SeS39A1S38OF_;F_;S45S0SeS2A1SeS40A1S2S2SeS1A1S3bS47S40S42S1eR2R3A2S41A2R5A3S2cSfS4aR5R4R2A3S10A3S2cSfS3cR3RaA2S10A3S2cSfS48S1S7S5R6A1A1R5A3S10A3S0S4RdRcR1A3S36S1S3R2A1S6RaA1A3S36S1S3S3aR3R8A2A1R9A3F_;F_;Frho;S0S4ReRdR1A3S34Vsegs;R11S30Vsegs;R10RbR2A4S32S2dS23Vsegs;R11S0S4R11R10R1A3Lr;ReR1A5S31Vsegs;R11R10RfRdR1A6A2Lw;A4F_;Frho;F_;F_;F_;F_;F_;Fs;FF;FP0;FE;Fposts;Fcuts;Frho0;Fn;FK;Fok;").
Proof using .
  intros ok K n rho0 cuts posts E P0 F s Hin He Hid Hb HF rho Hag.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hsp. right. exists (mkLeaf (add_facts F P0) RsSymJump), (rho_sub rho s).
  split; [exact Hin|]. split.
  - eapply agree_below_trans; [exact Hag|]. apply rho_sub_agree. exact Hid.
  - pose proof (SP_entails_sem1 K E P0 F s rho w He Hb (HF rho Hag) Hsp) as [Hsm Hk]. split; assumption.
Qed.

Lemma eexit_reenter_G : ltac2:(tb__ "0|1|
SeS39A1S38OF_;F_;S0OF_;S45SeS1bA1S32OF_;S1bS1bSeS1A1S2S3bS47S1bR4R7A3S2cS2S1cR5A1S1eR4R3A2A3S2cSfS4aS1cR7A1R4R3A3S10A3S2cSfS3cR4RbA2S10A3S0S0RfR2A1S4RfR3R2A3R11R3A1F_;F_;Frho';Frho;S2cSfS48S1S7S5R7A1A1R8A3S10A3S0R10R1A1S36S1S3R2A1S6S1cRdA1A1A3S36S1S3S3aR3RaA2A1RcA3F_;F_;Frho;S4cS4dS1dRbA1Z1A2S1dRcA1M0A2S4cZ0G0A2S0R13R1A1S33Vsegs;S30Vsegs;R15S1cR10A1R2A4S32S2dS20Vsegs;R16S37S1bS1fS24R15A1R13A4S25R11R3A2R1A5R12R1A1A2Lw;A3F_;Frho;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fs;FT0;FF;FC;FE;FQ;Fcuts;Fg;FG;FK;").
Proof using .
  intros K G g cuts Q E C F T0 s Hin HC He Hid HG Hb HF Hrk Hr0 rho Hg w Hsp.
  exists w. split; [apply wsteps_refl|]. left.
  exists (to_enode G C), (rho_sub rho s). split; [apply in_map; exact Hin|].
  cbn [to_enode en_state en_ghost en_meas fst snd]. split.
  - eapply HG; [exact Hg|]. apply rho_sub_agree. exact Hid.
  - split.
    + rewrite HC. eapply SP_entails_sem1; [exact He | exact Hb | apply HF; exact Hg | exact Hsp].
    + unfold vmeas.
      pose proof (urange (eval (rho_sub rho s) (vn_var C))) as R1.
      pose proof (urange (eval rho (vn_var E))) as R2. nia.
Qed.

Lemma eexit_post_G : ltac2:(tb__ "0|0|
SeS39A1S38OF_;F_;S45S0SeS1bA1SeS40A1S1bS2SeS1A1S3bS47S40S42S1eR2R3A2S41A2R5A3S2cSfS4aS1cR5A1R4R2A3S10A3S2cSfS3cR3RaA2S10A3S2cSfS48S1S7S5R6A1A1R5A3S10A3S0S4RdRcR1A3S36S1S3R2A1S6S1cRaA1A1A3S36S1S3S3aR3R8A2A1R9A3F_;F_;Frho;S0S4ReRdR1A3S33Vsegs;S30Vsegs;R10S1cRbA1R2A4S32S2dS20Vsegs;R11S37S1bS1fS24S0S4R11R10R1A3Lr;A1ReA4S25RcR3A2R1A5S31Vsegs;R11R10RfRdR1A6A2Lw;A3F_;Frho;F_;F_;F_;F_;F_;Fs;FF;FP0;FE;Fposts;Fcuts;Frho0;Fn;FK;").
Proof using .
  intros K n rho0 cuts posts E P0 F s Hin He Hid Hb HF rho Hag w Hsp.
  exists w. split; [apply wsteps_refl|]. right.
  exists (mkLeaf (add_facts F P0) RsSymJump), (rho_sub rho s). split; [exact Hin|]. split.
  - eapply agree_below_trans; [exact Hag|]. apply rho_sub_agree. exact Hid.
  - pose proof (SP_entails_sem1 K (vn_state E) P0 F s rho w He Hb (HF rho Hag) Hsp) as [Hsm Hk]. split; assumption.
Qed.

End GlueG.

Section ECfgI.
Variable segs : list Segment.

Definition vmeasI (n : vnode) (rho : valuation) : Z := ltac2:(tb__ "0|0|
S4dS50S52S51Z2Z40A2S58Q40S8Vrho;S21Vn;A1A2A2A2Z100A2S1dVn;A1A2").

Definition to_enodeI (G : valuation -> Prop) (n : vnode) : enode := ltac2:(tb__ "0|1|
S15S1aS2S0OF_;M0A2S0S46Frho;S15S2G0S1cVn;A1VG;A4S55Vn;A1A4").

Definition echeckI (g : positive) (nodes : list vnode) (e : edge) : bool := ltac2:(tb__ "0|a|
S12S1bA1SfLx;M0S49S1bVnodes;S28Ve;A1A3S1bG0S49S1bVnodes;S2aVe;A1A3S1bS11S11S11S11S11S11S11S3cS29Ve;A1M1Vg;A2S5cVg;S5S1cR2A1A1M2A2A2SdG2S21R2A1M3A2A2S4fZ0M4S1dR1A1M5A2A2S4eG5Z100M6A2A2S4fG4S1dR2A1M7A2A2S4eG7G6A2A2S19S44S6S27Ve;A1A1M8G3Z1S3eG1S21R1A1A2M9A4S11S44G8G3G4G9A4S4eG5G7A2A2A2A2Lnj;S13X12x2Lni;S13X12x2").

Definition check_ecfgI (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list vnode) : bool := ltac2:(tb__ "0|1|
S11S48S1bS1bS18ScS1cR1A1A1A1Ln;Vcuts;A3S12SeS22A1M0A1SfLx;S26Vsegs;Vfuel;Vcutpcs;Vg;S37S1bS2S1cVcuts;A4S37S1bS2S1cVexits;A4A6G0S48S22S56Vg;S16S1bVcuts;Vexits;A3A2R1A3Les;S13X12x2A2").

Lemma echeckI_sound : ltac2:(tb__ "0|0|
S45S0OF_;SeS1bA1S22S0S0R5R2A1S4R7R3R2A3R7R3A1F_;F_;Fr2;Fr1;S2cSfS56R5R3R2A3S10A3S2bS37S1bS1fS54R5A1R4A4R3A2F_;F_;Fe;Fnodes;FG;Fg;").
Proof using .
  intros g G nodes e HG H. unfold echeckI in H. unfold eedge_ok.
  intros Ti Tj Hi Hj rho rho' Hag Hg HF.
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (e_src e)) as [ni|] eqn:Ei; [|discriminate].
  destruct (nth_error nodes (e_tgt e)) as [nj|] eqn:Ej; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  cbn [to_enodeI en_state en_ghost en_meas fst snd] in *.
  apply andb_prop in H as [H Hdec].
  apply andb_prop in H as [H Hri2]. apply andb_prop in H as [H Hri1].
  apply andb_prop in H as [H Hrj2]. apply andb_prop in H as [H Hrj1].
  apply andb_prop in H as [H Hvb]. apply andb_prop in H as [Hid Hgle].
  apply Pos.leb_le in Hgle. apply Z.leb_le in Hrj1. apply Z.ltb_lt in Hrj2. apply Z.leb_le in Hri1. apply Z.ltb_lt in Hri2.
  split.
  - eapply HG; [exact Hg|]. eapply agree_below_trans.
    + eapply agree_below_le; [exact Hgle | exact Hag].
    + apply rho_sub_agree. exact Hid.
  - unfold vmeasI. rewrite <- eval_subst.
    rewrite (eval_agree _ rho rho' (vn_var ni) Hag Hvb).
    pose proof (urange (eval rho' (sv_subst (e_sub e) (vn_var nj)))) as R1.
    pose proof (urange (eval rho' (vn_var ni))) as R2.
    apply orb_prop in Hdec. destruct Hdec as [Hlt | Heq].
    + pose proof (uleq_sound rho' _ _ 1 _ HF Hlt) as U1. unfold U in U1. nia.
    + apply andb_prop in Heq as [Hu Hr]. apply Z.ltb_lt in Hr.
      pose proof (uleq_sound rho' _ _ 0 _ HF Hu) as U1. unfold U in U1. nia.
Qed.

Theorem cfg_complete_autoI : ltac2:(tb__ "0|2|
S17SeS46A1S45SeS1bA1M0G0S0OF_;SeS39A1S38OF_;F_;S32OF_;S0S0R5R2A1S4R9R3R2A3R7R3A1F_;F_;Fr2;Fr1;S2cSfS57R9R8R7R6R5A5S10A3S1bS0S47S1bR2R8A3R8R2A1S33Vsegs;S30Vsegs;R8S1cR4A1M1R3A4S32S2dS20Vsegs;R9S37S1bS1fS54RaA1RcA4S55R5R4A2R1A5R8R1A1A2Lw;A3F_;F_;Frho;FE;S1bS0S47S1bR2RaA3R9R2A1S33Vsegs;S30Vsegs;R9G1R3A4R8A3F_;F_;Frho;Fn;F_;F_;F_;FQ;FK;FG;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits G K Q HG Hchk Hexits n rho Hin Hg.
  unfold check_ecfgI in Hchk. apply andb_prop in Hchk as [Hstrict Hchk].
  destruct (cfg_edges segs fuel cutpcs g (map vn_state cuts) (map vn_state exits)) as [es|] eqn:Hes; [|discriminate].
  change (vn_state n) with (en_state (to_enodeI G n)).
  apply (cfg_complete_gen segs fuel cutpcs g (map (to_enodeI G) cuts) (map (to_enodeI G) exits) es K Q).
  - apply forallb_forall. intros m Hm. apply in_map_iff in Hm as (m0 & <- & Hm0).
    exact (proj1 (forallb_forall _ _) Hstrict m0 Hm0).
  - rewrite !map_map. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He.
    apply (echeckI_sound g G); [exact HG|]. exact (proj1 (forallb_forall _ _) Hchk e He).
  - intros E rhoE HinE HgE. apply in_map_iff in HinE as (E0 & <- & HinE0).
    exact (Hexits E0 rhoE HinE0 HgE).
  - apply in_map_iff. exists n. auto.
  - exact Hg.
Qed.

Lemma eexit_reenter_I : ltac2:(tb__ "0|2|
SeS39A1S38OF_;F_;S0OF_;S45SeS1bA1S32OF_;S1bS1bSeS1A1S2S3bS47S1bR4R7A3S2cS2S1cR5A1S1eR4R3A2A3S2cSfS4aS1cR7A1R4R3A3S10A3S2cSfS3cR4RbA2S10A3S0S0RfR2A1S4RfR3R2A3R11R3A1F_;F_;Frho';Frho;S2cSfS48S1S7S5R7A1A1R8A3S10A3S0R10R1A1S36S1S3R2A1S6S1cRdA1A1A3S2fS36S1S3S3aR3RaA2M0A1RcA3S4cS58Q40M1S8R3S21ReA1A2A2S58G1S8G0S21RdA1A2A2A2A2F_;F_;Frho;S4cZ0S1dRbA1A2S4cS4dS1dRcA1Z1A2S1dRdA1A2S0R13R1A1S33Vsegs;S30Vsegs;R15S1cR10A1R2A4S32S2dS20Vsegs;R16S37S1bS1fS54R15A1R13A4S55R11R3A2R1A5R12R1A1A2Lw;A3F_;Frho;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fs;FT0;FF;FC;FE;FQ;Fcuts;Fg;FG;FK;").
Proof using .
  intros K G g cuts Q E C F T0 s Hin HC He Hid HG Hb HF Hr0 Hrk rho Hg w Hsp.
  exists w. split; [apply wsteps_refl|]. left.
  assert (FACTS : Forall (holds rho) (ss_facts (vn_state E))).
  { destruct Hsp as [Hsm _]. destruct w as [tr [ms md]].
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). }
  destruct (HF rho Hg FACTS) as [HF1 HV].
  exists (to_enodeI G C), (rho_sub rho s). split; [apply in_map; exact Hin|].
  cbn [to_enodeI en_state en_ghost en_meas fst snd]. split.
  - eapply HG; [exact Hg|]. apply rho_sub_agree. exact Hid.
  - split.
    + rewrite HC. eapply SP_entails_sem1; [exact He | exact Hb | intros _; exact HF1 | exact Hsp].
    + unfold vmeasI.
      pose proof (urange (eval (rho_sub rho s) (vn_var C))) as R1.
      pose proof (urange (eval rho (vn_var E))) as R2. nia.
Qed.

Lemma eexit_post_I : ltac2:(tb__ "0|0|
SeS39A1S38OF_;F_;S45S0SeS1bA1SeS40A1S1bS2SeS1A1S3bS47S40S42S1eR2R3A2S41A2R5A3S2cSfS4aS1cR5A1R4R2A3S10A3S2cSfS3cR3RaA2S10A3S2cSfS48S1S7S5R6A1A1R5A3S10A3S0S4RdRcR1A3S36S1S3R2A1S6S1cRaA1A1A3S36S1S3S3aR3R8A2A1R9A3F_;F_;Frho;S0S4ReRdR1A3S33Vsegs;S30Vsegs;R10S1cRbA1R2A4S32S2dS20Vsegs;R11S37S1bS1fS54S0S4R11R10R1A3Lr;A1ReA4S55RcR3A2R1A5S31Vsegs;R11R10RfRdR1A6A2Lw;A3F_;Frho;F_;F_;F_;F_;F_;Fs;FF;FP0;FE;Fposts;Fcuts;Frho0;Fn;FK;").
Proof using .
  intros K n rho0 cuts posts E P0 F s Hin He Hid Hb HF rho Hag w Hsp.
  exists w. split; [apply wsteps_refl|]. right.
  exists (mkLeaf (add_facts F P0) RsSymJump), (rho_sub rho s). split; [exact Hin|]. split.
  - eapply agree_below_trans; [exact Hag|]. apply rho_sub_agree. exact Hid.
  - pose proof (SP_entails_sem1 segs K (vn_state E) P0 F s rho w He Hb (HF rho Hag) Hsp) as [Hsm Hk]. split; assumption.
Qed.

End ECfgI.

Section Contra.
Variable segs : list Segment.

Lemma SP_facts : ltac2:(tb__ "0|0|
SeS39A1S38OF_;F_;S2S0S32S30Vsegs;R4R3R2R1A5S36S1S3R3A1S6R4A1A3F_;Fw;Frho;FE;FK;").
Proof using .
  intros K E rho [tr [ms md]] [Hsm _].
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))).
Qed.

Lemma exit_contra : ltac2:(tb__ "0|0|
S32OF_;SeS39A1S38OF_;F_;S0OF_;S2S35S0R4R1A1S36S1S3R2A1S6R4A1A3S2eF_;F_;Frho;S0R5R1A1S34Vsegs;R8S30Vsegs;R7R5R2A4R4A4F_;Frho;F_;FQ;FE;FG;FK;Fok;").
Proof using .
  intros ok K G E Q HX rho Hg n Hn w Hsp. exfalso. exact (HX rho Hg (SP_facts K E rho w Hsp)).
Qed.

Lemma eexit_contra : ltac2:(tb__ "0|0|
SeS39A1S38OF_;F_;S0OF_;S2S32OF_;S0R4R1A1S36S1S3R2A1S6R4A1A3S2eF_;F_;Frho;S0R5R1A1S33Vsegs;S30Vsegs;R7R5R2A4R4A3F_;Frho;F_;FQ;FE;FG;FK;").
Proof using .
  intros K G E Q HX rho Hg w Hsp. exfalso. exact (HX rho Hg (SP_facts K E rho w Hsp)).
Qed.

End Contra.

Section CallP.
Variable segs : list Segment.

Theorem call_sound_P : ltac2:(tb__ "0|3|
S0OF_;S32OF_;SeS39A1S38OF_;F_;M0G0S2S2S3bSeS9A1M1SeS40A1S35S0S2cS12G1A1S4bR7R6R5A3S14G1R4A2A3S2cSfS5aR8R7R6R5R4A5S10A3S0ReR1A1S34Vsegs;ReS30Vsegs;RdRaR2A4S31Vsegs;RcS5RaA1R2R7A5A4F_;Frho1;S53RfS3aS3dR5R8R1A3R9A2A1Fms;S40S0S47S40R2R9A3S4S5ReA1M2R8R2A3S34Vsegs;R12S30Vsegs;R10S5bRdG2S43R4A1S5RfA1RcA5R3A4RaA4F_;F_;Frho';FL;S34Vsegs;RfS30Vsegs;ReRcR6A4R7A4F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FK';FK;Fok;FPR;").
Proof using .
  intros PR ok K K' C Pre s R Posts Q rho He Hchk Hsum HPR Hcont.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R ms) s) (HPR ms) n); [|split; [exact HsmPre|exact Hk]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  destruct (import_post_link segs C Pre s R Posts rho tr ms md tr' ms' md' L rhoL He Hchk Hsm HinL HagL HsmL)
    as (rho' & (HAG & _) & HSP).
  exact (Hcont L rho' HinL HAG n HgQ _ (conj HSP Hk')).
Qed.

Theorem call_complete_P : ltac2:(tb__ "0|3|
S0OF_;SeS39A1S38OF_;F_;M0G0S2S2S3bSeS9A1M1SeS40A1S32OF_;S0S2cS12G1A1S4bR7R6R5A3S14G1R4A2A3S2cSfS5aR8R7R6R5R4A5S10A3S0RdR1A1S33Vsegs;S30Vsegs;RdRaR2A4S31Vsegs;RcS5RaA1R2R7A5A3F_;Frho1;S53ReS3aS3dR5R8R1A3R9A2A1Fms;S40S0S47S40R2R9A3S4S5ReA1M2R8R2A3S33Vsegs;S30Vsegs;R10S5bRdG2S43R4A1S5RfA1RcA5R3A4RaA3F_;F_;Frho';FL;S33Vsegs;S30Vsegs;ReRcR6A4R7A3F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FK';FK;FPR;").
Proof using .
  intros PR K K' C Pre s R Posts Q rho He Hchk Hsum HPR Hcont.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R ms) s) (HPR ms) _ (conj HsmPre Hk)) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  destruct (import_post_link segs C Pre s R Posts rho tr ms md tr' ms' md' L rhoL He Hchk Hsm HinL HagL HsmL)
    as (rho' & (HAG & _) & HSP).
  destruct (Hcont L rho' HinL HAG _ (conj HSP Hk')) as (w'' & Hsteps' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Lemma rw_call : ltac2:(tb__ "0|0|
S0SeS9A1S53S3bS45S2cS59Q40A1SbS3aS3dR5R4R3A3R2A2R1A2S8R5S3fR2R1A2A2A3Fi;Fs;Fms;FR;Frho;").
Proof using . intros. cbn [rho_sub rw]. apply eval_absorb. Qed.
Lemma rl_call : ltac2:(tb__ "0|0|
S0SeS9A1S53S3bS2cS45SeS59Q8A1A1F_;SaS3aS3dR4R3R2A3R1A2A1SaR4A1A3Fs;Fms;FR;Frho;").
Proof using . reflexivity. Qed.

End CallP.
