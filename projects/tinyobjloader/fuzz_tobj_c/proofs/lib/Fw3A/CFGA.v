(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "entailsA"; "axwf"; "sym_runA"; "ax_X"; "ax_base"; "mkLeafA"; "ax_setS"; "xrs_covered_f"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "option"; "nat"; "prod"; "andb"; "Some"; "false"; "pair"; "app"; "fst"; "snd"; "length"; "option_map"; "negb"; "orb"; "None"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "False"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "sprop"; "ss_facts"; "holds"; "agree_below"; "ss_pc"; "sv"; "sprop_below"; "sv_below"; "SLit"; "ss_lenient"; "eval"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "SPA"; "stableA"; "ok_frameA"; "LQA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA.CFGA"; "edgeA"; "lnodeA"; "vnodeA"; "enodeA"; "jnodeA"; "vna_state"; "lna_state"; "SPfamA"; "cfg_edgesA"; "ena_state"; "ea_leaf"; "ena_meas"; "leaf_refuted"; "SPfamEA"; "ena_pred"; "leaf_okA"; "vna_rank"; "addpf"; "ea_src"; "ea_sub"; "ea_tgt"; "edge_okA"; "lna_rank"; "lna_vars"; "to_enodeA"; "vmeasA"; "vna_var"; "cuts_edgesA"; "echeck2A"; "eedge_okA"; "leaf_matches1A"; "leaf_okA_ref"; "leaves_edgesA"; "lmeasA"; "mkEdgeA"; "nodes_atA"; "check_ecfg2A"; "cuts_edgesA_pf"; "echeckA"; "first_matchA"; "leaf_matches1A_p"; "leaf_matchesA"; "leaf_refuted_p"; "leaves_edgesA_ref"; "to_enodeLA"; "SPfamGA"; "cfg_edgesA_pf"; "check_cfgA"; "check_cutA"; "check_ecfgA"; "first_matchA_p"; "leaves_edgesA_pf"; "to_jnodeLA"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "filter"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "etriple"; "assn"; "tripleN"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "rho_sub"; "sv_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "pfacts"; "mk_pf"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "withGA"; "ax_add_facts"; "@Stdlib.ZArith.BinInt.Z"; "le"; "eqb"; "add"; "mul"; "pow"; "leb"; "lt"; "ltb"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vdir"; "LMAX"; "forallb_lazy"; "infer_sub"; "B64"; "existsb_lazy"; "add_facts"; "lex_check"; "lex_val"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA"; "mk_pf_f"; "@Corelib.Init.Nat"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "uleq"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "eqb"; "@Corelib.Init.Peano"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EntailFast"; "entails_p_f"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From Stdlib Require Import Zwf Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundF SymSoundR SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymDigFast SymObjFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import XformFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EntailFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA CompleteA EntailA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA.
Import ListNotations.
Open Scope Z_scope.

Definition withGA (G : valuation -> Prop) (J : jpredA) : jpredA := ltac2:(tb__ "0|0|
S24ScS7aQ40A1A1ScS82A1S83S1fVG;R4A1VJ;R4R3R2R1A4A2Lmd;Ltr;Ltp;Lrho;").

Definition ax_add_facts (F : list sprop) (A : axst) : axst := ltac2:(tb__ "0|0|
SaVA;S95VF;S1VA;A1A2A2").

Section CFGA.
Variable segs : list Segment.

Lemma stableA_withG : ltac2:(tb__ "0|0|
S71S24OFx;S32S24S24R4R2A1S29R6R3R2A3R6R3A1F_;F_;Frho';Frho;S34Vsegs;R4R2A3S34Vsegs;R5S84R4R3A2A3F_;F_;FJ;FG;Fn;").
Proof using .
  intros n G J HG HJ rho rho' tp tr md md' Hag Hme [Hg Hj]. split; [eapply HG; eauto | eapply HJ; eauto].
Qed.

Definition leaf_refuted (L : axst) : bool := ltac2:(tb__ "0|1|
S9eS27S1VL;A1A1S2eZ1A1Z0M0S2eG0A1A4").

Lemma leaf_refuted_sound : ltac2:(tb__ "0|0|
S24S0S1eSdS44R1A1SeA3S79S26S28R3A1S27S1R2A1A1A3S22F_;F_;FL;Frho;").
Proof using .
  intros rho L H Hf. pose proof (uleq_sound rho _ _ _ _ Hf H) as U1.
  rewrite !U_SLit in U1 by lia. lia.
Qed.

Definition leaf_matches1A (g : positive) (L X : axst) : bool := ltac2:(tb__ "0|3|
SdSdL_;M0S87S2aS1VL;A1M1A1S2aS1VX;A1M2A1A2S92Vg;G1G2A3S7cG0S7dR1Vg;A2S4VL;VX;R1A3S14Xdx2Ts;S14Xdx2").

Definition leaf_matchesA (g : positive) (L : axst) (targets : list axst) : bool := ltac2:(tb__ "0|0|
S94S0S56Vg;VL;A2Vtargets;A3").

Lemma leaf_matches1A_true : ltac2:(tb__ "0|1|
S71S0S0S1eSdS56R3R2R1A3SeA3S1fS1eSdS7dS92R4S1R3A1S1R2A1A3M0R4A2SeA3S1eSdS4R3R2G0A3SeA3A2F_;FX;FL;Fg;").
Proof using .
  intros g L X H. unfold leaf_matches1A in H.
  destruct (ss_pc (ax_S L) =? ss_pc (ax_S X)); [|discriminate].
  destruct (wsub_id_below (infer_sub g (ax_S L) (ax_S X)) g); [|discriminate]. auto.
Qed.

Definition leaf_okA_ref (g : positive) (targets : list axst) (L : leafA) : bool := ltac2:(tb__ "0|1|
SdSdL_;S44S3VL;A1M0A1SeS61Vg;G0Vtargets;A3Xdx2").

Definition leaf_refuted_p (pf : pfacts) : bool := uleq_pf pf (SLit 1) 0 (SLit 0).
Definition leaf_matches1A_p (pf : pfacts) (g : positive) (L X : axst) : bool := ltac2:(tb__ "0|3|
SdSdL_;M0S87S2aS1VL;A1M1A1S2aS1VX;A1M2A1A2S92Vg;G1G2A3S7cG0S7dR1Vg;A2G0Sa3Vpf;G1G2R1A4G0SbS27G1A1S7VL;A1R1S7VX;A1A4G0S31S7fR1S8VX;A1A2S8VL;A1A2S5VX;A1S14Xdx2S14Xdx2S14Xdx2S14Xdx2Ts;S14Xdx2").
Lemma leaf_refuted_p_eq : ltac2:(tb__ "0|0|
S0S1eSdS62S81S27S1R1A1A1A1A1S44R1A1A3FL;").
Proof using . reflexivity. Qed.
Lemma leaf_matches1A_p_eq : ltac2:(tb__ "0|0|
S71S0S0S1eSdS60S81S27S1R2A1A1A1R3R2R1A4S56R3R2R1A3A3FX;FL;Fg;").
Proof using . intros g L X. unfold leaf_matches1A_p, leaf_matches1A, entailsA, EntailFast.entails_f. rewrite DigFastA.mk_pf_f_eq. reflexivity. Qed.
Definition leaf_okA (g : positive) (targets : list axst) (L : leafA) : bool := ltac2:(tb__ "0|1|
S9aS27S1S3VL;A1M0A1A1A1S80SdSdL_;S62R1A1SeS94S0S60R1Vg;G0A3Vtargets;A3Xdx2Tpf;").
Lemma leaf_okA_ref_eq : ltac2:(tb__ "0|0|
S71ScS0A1S2S1eSdS47R3R2R1A3S57R3R2R1A3A3FL;Ftargets;Fg;").
Proof using .
  intros g targets L. unfold leaf_okA, leaf_okA_ref, leaf_matchesA. cbv zeta. rewrite DigFastA.mk_pf_f_eq, leaf_refuted_p_eq.
  destruct (leaf_refuted (la_state L)); [reflexivity|].
  induction targets as [|X rest IH]; cbn [existsb_lazy]; [reflexivity|]. rewrite leaf_matches1A_p_eq, IH. reflexivity.
Qed.
Lemma forallb_lazy_leaf_okA_ref : ltac2:(tb__ "0|0|
S71ScS0A1ScS2A1S1eSdS91S2S47R3R2A2R1A3S91S2S57R3R2A2R1A3A3Fleaves;Ftargets;Fg;").
Proof using . intros g targets leaves. induction leaves as [|L r IH]; cbn [forallb_lazy]; [reflexivity|]. rewrite leaf_okA_ref_eq, IH. reflexivity. Qed.

Definition check_cutA (fuel : nat) (cutpcs : list Z) (g : positive)
           (targets : list axst) (T : axst) : bool := ltac2:(tb__ "0|2|
SdSdL_;S12S12S99Vg;S25S1VT;A1M0A1A2S1bS2fG0A1A1A2S5VT;A1A2SfScS2A1M1A1SdLx;S6Vsegs;Vfuel;Vcutpcs;VT;SeA5G1S91S2S47Vg;Vtargets;A2R1A3Lleaves;S14Xfx2S14Xdx2").

Definition check_cfgA (fuel : nat) (cutpcs : list Z) (g : positive)
           (cuts exits : list axst) : bool := ltac2:(tb__ "0|0|
S91S0S68Vfuel;Vcutpcs;Vg;S16S0Vcuts;Vexits;A3A4Vcuts;A3").

Definition cfg_residualA (fuel : nat) (cutpcs : list Z) (g : positive)
           (cuts exits : list axst) : list (Z * option (list leafA)) := ltac2:(tb__ "0|2|
S78S0S11S72SfScS2A1M0A1M1A2S0S15S72G1S2aS1R1A1A1G1G1Lx;S6Vsegs;Vfuel;Vcutpcs;R1SeA5G0S13G0S70S2S2S1bS47Vg;S16S0Vcuts;Vexits;A3R1A3A1LL;R1A3A2Lleaves;S1dG0A1Xfx2A4LT;Vcuts;A4").

Definition SPfamA (J : jpredA) (fam : list axst) (tp : list word) : assn := ltac2:(tb__ "0|0|
S73S20S0S0S20S24S24S1fS6dS0R2Vfam;A3S33Vsegs;VJ;R2R1Vtp;R3A6A2Lrho;A2LT;A2Lw;").

Lemma SPfamA_app : ltac2:(tb__ "0|1|
S32ScS0A1M0G0ScS7aQ40A1A1S73S23S3fR5S16S0R4R3A3R2R1A4S21S3fR5R4R2R1A4S3fR5R3R2R1A4A2A2Fw;Ftp;Ff2;Ff1;FJ;").
Proof using .
  intros J f1 f2 tp w. unfold SPfamA. split.
  - intros (T & rho & Hin & Hsp). apply in_app_or in Hin as [Hin|Hin]; [left|right]; exists T, rho; auto.
  - intros [(T & rho & Hin & Hsp)|(T & rho & Hin & Hsp)]; exists T, rho; (split; [apply in_or_app; auto|auto]).
Qed.

Lemma leaf_matches_soundA : ltac2:(tb__ "0|0|
S32S71S0ScS0A1S24ScS7aQ40A1A1S73S34Vsegs;R6R7A3S1eSdS61R7R6R5A3SeA3S33Vsegs;R9R7R5R4R3A6S3fRaR7R5R4A4F_;F_;F_;Fw;Ftp;Frho;Ftargets;FL;Fg;FJ;").
Proof using .
  intros J g L targets rho tp w HJ Hm Hsp.
  unfold leaf_matchesA in Hm. rewrite existsb_lazy_eq in Hm. apply existsb_exists in Hm as (X & Hin & Hm).
  apply leaf_matches1A_true in Hm as [Hid He].
  exists X, (rho_sub rho (infer_sub g (ax_S L) (ax_S X))). split; [exact Hin|].
  eapply SPA_entails; eauto.
Qed.

Lemma leaf_okA_sound_ref : ltac2:(tb__ "0|0|
S32S71ScS0A1S2S24ScS7aQ40A1A1S73S34Vsegs;R6R7A3S1eSdS57R7R6R5A3SeA3S33Vsegs;R9S3R6A1R5R4R3A6S3fRaR8R5R4A4F_;F_;F_;Fw;Ftp;Frho;FL;Ftargets;Fg;FJ;").
Proof using .
  intros J g targets L rho tp w HJ H Hsp. unfold leaf_okA_ref in H.
  destruct (leaf_refuted (la_state L)) eqn:Hr.
  - exfalso. eapply (leaf_refuted_sound rho); [exact Hr|]. eapply smatchA_facts. exact (proj1 Hsp).
  - eapply leaf_matches_soundA; eauto.
Qed.

Lemma leaf_okA_sound : ltac2:(tb__ "0|0|
S32S71ScS0A1S2S24ScS7aQ40A1A1S73S34Vsegs;R6R7A3S1eSdS47R7R6R5A3SeA3S33Vsegs;R9S3R6A1R5R4R3A6S3fRaR8R5R4A4F_;F_;F_;Fw;Ftp;Frho;FL;Ftargets;Fg;FJ;").
Proof using .
  intros J g targets L rho tp w HJ H Hsp. rewrite leaf_okA_ref_eq in H. exact (leaf_okA_sound_ref J g targets L rho tp w HJ H Hsp).
Qed.

Theorem cfg_soundA : ltac2:(tb__ "0|1|
S10ScS72A1S71ScS0A1M0G0S32S73OF_;S76ScS7aQ40A1A1S35Vsegs;R3R4A3S34Vsegs;R8R5A3S1eSdS67RbRaR9R8R7A5SeA3S0S24S6dS0R2RaA3S74Vsegs;R9S33Vsegs;RaR3R2R7A5S73S21S3fRbRdR8R1A4R9R1A1A2Lw;A4F_;Frho;FE;S0S24S6dS0R2RcA3S74Vsegs;RaS33Vsegs;RbR3R2R8A5R9A4F_;Frho;FT;F_;F_;F_;F_;Ftp;FQ;Fok;FJ;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits J ok Q tp Hok HJ Hchk Hexits T rho HinT.
  assert (Hloop : triple segs ok (SPfamA J cuts tp) Q).
  { apply triple_loop.
    unfold SPfamA at 1. apply triple1_ex; intros T'. apply triple1_ex; intros rho'.
    apply triple1_pure; intros HinT'.
    unfold check_cfgA in Hchk. rewrite forallb_lazy_eq in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk T' HinT') as Hc.
    unfold check_cutA in Hc.
    destruct (Pos.leb g (ss_next (ax_S T')) && negb (ss_lenient (ax_S T')) && axwf T') eqn:Hle; [|discriminate].
    apply andb_prop in Hle as [Hle _]. apply andb_prop in Hle as [Hle Hlen]. apply Pos.leb_le in Hle.
    destruct (ss_lenient (ax_S T')) eqn:Hlen'; [discriminate|].
    destruct (sym_runA segs fuel cutpcs T' true) as [leaves|] eqn:Hrun; [|discriminate]. rewrite forallb_lazy_eq in Hc.
    eapply triple1_seq_l.
    { eapply sym_run_soundA; eauto. eapply stableA_mono; [exact Hle|exact HJ]. }
    intros m Hgm w Hw. destruct Hw as (L & rho'' & HinL & Hag & Hsm & Hk).
    pose proof (proj1 (forallb_forall _ _) Hc L HinL) as HmL.
    pose proof (leaf_okA_sound J g (cuts ++ exits) L rho'' tp w HJ HmL (conj Hsm Hk)) as Hfam.
    apply SPfamA_app in Hfam as [Hcut|Hexit].
    - exact (Hgm w (or_introl Hcut)).
    - destruct Hexit as (E & rhoE & HinE & HspE). exact (Hexits E rhoE HinE m Hgm w HspE). }
  eapply triple_conseq; [| intros w Hw; exact Hw | exact Hloop].
  intros w Hw. exists T, rho. auto.
Qed.

Lemma smatchA_add_facts : ltac2:(tb__ "0|0|
S24ScS7aQ40A1A1ScS26A1S0S11ScS82A1Sa2A2S37Vsegs;R5R4R2R1A5S79S26S28R6A1R4A3S1eSdS6fS26S2cS25S1R4A1A1A1R5A3SeA3S37Vsegs;R8R7S85R6R5A2R4A5F_;F_;F_;Fw;FA;FF;Ftp;Frho;").
Proof using .
  intros rho tp F A w (Hsm & HMI & Hwf & Hsh) HF Hb. split; [|split; [exact HMI | split; [exact Hwf | exact Hsh]]].
  apply smatch_add_facts; assumption.
Qed.

Lemma SPA_entails_sem : ltac2:(tb__ "0|1|
S32S71S0S0ScS26A1S7cS24ScS7aQ40A1A1M0S73S1eSdS4R7R6R4A3SeA3S1eSdS7dR5R9A2SeA3S34Vsegs;RaRbA3S1eSdS6fS26S2cS25S1R9A1A1A1R8A3SeA3S24G0ScS82A1S83R11R4R3R2R1A4S79S26S28R5A1S27S1R10A1A1A3S79S26S28S7eR6ReA2A1RfA3F_;F_;Fmd;Ftr;Ftp;Frho;S33Vsegs;ReRcR8R7R6A6S33Vsegs;RfS85RbRcA2S7eR9RaA2R8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fs;FF;FT0;FL;Fg;FJ;").
Proof using .
  intros J g L T0 F s rho tp w He Hid HJ Hb HF [Hsm Hk].
  split; [|eapply HJ; [apply rho_sub_agree; exact Hid | apply mat_equiv_refl | exact Hk]].
  apply smatchA_add_facts; [eapply smatchA_entails; eauto | | exact Hb].
  eapply HF; [exact Hk|]. eapply smatchA_facts; exact Hsm.
Qed.

Lemma exit_reenterA : ltac2:(tb__ "0|1|
S73OF_;S32S71ScS0A1S76S0S0ScS26A1S7cScS7aQ40A1A1M0S6dS0S85R3R4A2R7A3S1eSdS4R6R5R3A3SeA3S1eSdS7dR4RaA2SeA3S34Vsegs;RbRcA3S1eSdS6fS26S2cS25S1R8A1A1A1R7A3SeA3S24G0ScS82A1S83R12R4R3R2R1A4S79S26S28R5A1S27S1RfA1A1A3S79S26S28S7eR6RdA2A1ReA3F_;F_;Fmd;Ftr;Ftp;Frho;S24S74Vsegs;R11S33Vsegs;R10RcR1R8A5S73S21S3fR11RfR9R1A4ReR1A1A2Lw;A4Frho;F_;F_;F_;F_;F_;F_;Ftp;Fs;FF;FT0;FE;FQ;Fcuts;Fg;FJ;Fok;").
Proof using .
  intros ok J g cuts Q E T0 F s tp Hin He Hid HJ Hb HF rho.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hsp. left. exists (ax_add_facts F T0), (rho_sub rho s).
  split; [exact Hin|]. eapply SPA_entails_sem; eauto.
Qed.

Lemma exit_postA : ltac2:(tb__ "0|0|
S73OF_;S32S71S24ScS0A1ScS2A1S0ScS7aQ40A1A1S6dS2S9R2S9dA2R3A3S24S74Vsegs;RaS33Vsegs;S84S24S29R9R8R1A3Lr;R9A2R4R1R3A5S73S21S3fS84S24S29RaR9R1A3Lr;RaA2R7R4R1A4S36Vsegs;RaR9R8R4R6R1A7A2Lw;A4Frho;F_;Ftp;FP;Fposts;Fcuts;Frho0;Fn;FJ0;Fok;").
Proof using .
  intros ok J0 n rho0 cuts posts P tp Hin rho.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w [Hsm [Hag Hk]]. right. exists (mkLeafA P RsSymJump), rho. auto.
Qed.

Lemma SPA_withG_intro : ltac2:(tb__ "0|0|
S32S71S0S24ScS7aQ40A1A1S73S33Vsegs;R6R4R3R2R1A6S33Vsegs;S84S24S29R7R5R1A3Lr;R7A2R5R4R3R2A6F_;Fw;Ftp;Frho;FA;Fn;FJ0;").
Proof using . intros J0 n A rho tp w [Hsm Hk]. split; [exact Hsm|]. split; [apply agree_below_refl | exact Hk]. Qed.

Definition jnodeA : Type := (axst * jpredA)%type.

Record edgeA := mkEdgeA { ea_src : nat; ea_leaf : axst; ea_tgt : nat; ea_sub : wsub }.

Fixpoint first_matchA (g : positive) (L : axst) (targets : list axst) (j : nat) : option (nat * wsub) :=
  match targets with
  | [] => None
  | X :: rest =>
      if leaf_matches1A g L X then Some (j, infer_sub g (ax_S L) (ax_S X))
      else first_matchA g L rest (S j)
  end.

Fixpoint leaves_edgesA_ref (g : positive) (i : nat) (leaves : list leafA) (targets : list axst) : option (list edgeA) :=
  match leaves with
  | [] => Some []
  | L :: rest =>
      if leaf_refuted (la_state L) then leaves_edgesA_ref g i rest targets else
      match first_matchA g (la_state L) targets 0, leaves_edgesA_ref g i rest targets with
      | Some (j, s), Some es => Some (mkEdgeA i (la_state L) j s :: es)
      | _, _ => None
      end
  end.

Fixpoint first_matchA_p (pf : pfacts) (g : positive) (L : axst) (targets : list axst) (j : nat) : option (nat * wsub) :=
  match targets with
  | [] => None
  | X :: rest =>
      if leaf_matches1A_p pf g L X then Some (j, infer_sub g (ax_S L) (ax_S X))
      else first_matchA_p pf g L rest (S j)
  end.
Lemma first_matchA_p_eq : ltac2:(tb__ "0|0|
S71S0ScS0A1S10S1eSfS11S10S7cA2A1S6aS81S27S1R3A1A1A1R4R3R2R1A5S5fR4R3R2R1A4A3Fj;Ftargets;FL;Fg;").
Proof using . intros g L targets. induction targets as [|X rest IH]; intros j; cbn [first_matchA_p first_matchA]; [reflexivity|]. rewrite leaf_matches1A_p_eq, IH. reflexivity. Qed.
Fixpoint leaves_edgesA (g : positive) (i : nat) (leaves : list leafA) (targets : list axst) : option (list edgeA) :=
  match leaves with
  | [] => Some []
  | L :: rest =>
      let pf := DigFastA.mk_pf_f (ss_facts (ax_S (la_state L))) in
      if leaf_refuted_p pf then leaves_edgesA g i rest targets else
      match first_matchA_p pf g (la_state L) targets 0, leaves_edgesA g i rest targets with
      | Some (j, s), Some es => Some (mkEdgeA i (la_state L) j s :: es)
      | _, _ => None
      end
  end.
Lemma leaves_edgesA_ref_eq : ltac2:(tb__ "0|0|
S71S10ScS2A1ScS0A1S1eSfScS38A1A1S58R4R3R2R1A4S63R4R3R2R1A4A3Ftargets;Fleaves;Fi;Fg;").
Proof using .
  intros g i leaves targets. induction leaves as [|L rest IH]; cbn [leaves_edgesA leaves_edgesA_ref]; [reflexivity|].
  cbv zeta. rewrite DigFastA.mk_pf_f_eq, leaf_refuted_p_eq, first_matchA_p_eq, IH. reflexivity.
Qed.

Fixpoint cuts_edgesA (fuel : nat) (cutpcs : list Z) (g : positive) (i : nat)
         (cuts : list axst) (targets : list axst) : option (list edgeA) :=
  match cuts with
  | [] => Some []
  | T :: rest =>
      if negb (Pos.leb g (ss_next (ax_S T)) && negb (ss_lenient (ax_S T)) && axwf T) then None else
      match sym_runA segs fuel cutpcs T true with
      | Some leaves =>
          match leaves_edgesA g i leaves targets, cuts_edgesA fuel cutpcs g (S i) rest targets with
          | Some es, Some es' => Some (es ++ es')
          | _, _ => None
          end
      | None => None
      end
  end.

Definition cfg_edgesA (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list axst) : option (list edgeA) := ltac2:(tb__ "0|0|
S53Vfuel;Vcutpcs;Vg;U0Vcuts;S16S0Vcuts;Vexits;A3A6").

Definition addpf (e : edgeA) : edgeA * pfacts := ltac2:(tb__ "0|0|
S15S38S80Ve;S9aS27S1S42Ve;A1A1A1A1A4").
Fixpoint leaves_edgesA_pf (g : positive) (i : nat) (leaves : list leafA) (targets : list axst) : option (list (edgeA * pfacts)) :=
  match leaves with
  | [] => Some []
  | L :: rest =>
      let pf := DigFastA.mk_pf_f (ss_facts (ax_S (la_state L))) in
      if leaf_refuted_p pf then leaves_edgesA_pf g i rest targets else
      match first_matchA_p pf g (la_state L) targets 0, leaves_edgesA_pf g i rest targets with
      | Some (j, s), Some es => Some ((mkEdgeA i (la_state L) j s, pf) :: es)
      | _, _ => None
      end
  end.
Lemma leaves_edgesA_pf_eq : ltac2:(tb__ "0|2|
S71S10ScS2A1ScS0A1S1eSfScS11S38S80A2M0A1M1A1S6bR4R3R2R1A4S1aScS38A1G1S78S38G0S49A3S58R4R3R2R1A4A4A3Ftargets;Fleaves;Fi;Fg;").
Proof using .
  intros g i leaves targets. induction leaves as [|L rest IH]; [reflexivity|].
  change (leaves_edgesA_pf g i (L :: rest) targets) with
    (let pf := DigFastA.mk_pf_f (ss_facts (ax_S (la_state L))) in
     if leaf_refuted_p pf then leaves_edgesA_pf g i rest targets else
     match first_matchA_p pf g (la_state L) targets 0, leaves_edgesA_pf g i rest targets with
     | Some (j, s), Some es => Some ((mkEdgeA i (la_state L) j s, pf) :: es)
     | _, _ => None
     end).
  change (leaves_edgesA g i (L :: rest) targets) with
    (let pf := DigFastA.mk_pf_f (ss_facts (ax_S (la_state L))) in
     if leaf_refuted_p pf then leaves_edgesA g i rest targets else
     match first_matchA_p pf g (la_state L) targets 0, leaves_edgesA g i rest targets with
     | Some (j, s), Some es => Some (mkEdgeA i (la_state L) j s :: es)
     | _, _ => None
     end).
  cbv zeta. rewrite IH.
  destruct (leaf_refuted_p _); [reflexivity|].
  destruct (first_matchA_p _ _ _ _ _) as [[j s]|]; destruct (leaves_edgesA g i rest targets); reflexivity.
Qed.
Fixpoint cuts_edgesA_pf (fuel : nat) (cutpcs : list Z) (g : positive) (i : nat) (cuts : list axst) (targets : list axst) : option (list (edgeA * pfacts)) :=
  match cuts with
  | [] => Some []
  | T :: rest =>
      if negb (Pos.leb g (ss_next (ax_S T)) && negb (ss_lenient (ax_S T)) && axwf T) then None else
      match sym_runA segs fuel cutpcs T true with
      | Some leaves =>
          match leaves_edgesA_pf g i leaves targets, cuts_edgesA_pf fuel cutpcs g (S i) rest targets with
          | Some es, Some es' => Some (es ++ es')
          | _, _ => None
          end
      | None => None
      end
  end.
Lemma cuts_edgesA_pf_eq : ltac2:(tb__ "0|3|
S10ScS72A1S71ScS0A1M0S10G0S1eSfScS11S38S80A2M1A1M2A1S5dR6R5R4R2R3R1A6S1aScS38A1G2S78S38G1S49A3S53R6R5R4R2R3R1A6A4A3Ftargets;Fi;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts. induction cuts as [|T rest IH]; intros i targets; [reflexivity|].
  change (cuts_edgesA_pf fuel cutpcs g i (T :: rest) targets) with
    (if negb (Pos.leb g (ss_next (ax_S T)) && negb (ss_lenient (ax_S T)) && axwf T) then None else
      match sym_runA segs fuel cutpcs T true with
      | Some leaves =>
          match leaves_edgesA_pf g i leaves targets, cuts_edgesA_pf fuel cutpcs g (S i) rest targets with
          | Some es, Some es' => Some (es ++ es')
          | _, _ => None
          end
      | None => None
      end).
  change (cuts_edgesA fuel cutpcs g i (T :: rest) targets) with
    (if negb (Pos.leb g (ss_next (ax_S T)) && negb (ss_lenient (ax_S T)) && axwf T) then None else
      match sym_runA segs fuel cutpcs T true with
      | Some leaves =>
          match leaves_edgesA g i leaves targets, cuts_edgesA fuel cutpcs g (S i) rest targets with
          | Some es, Some es' => Some (es ++ es')
          | _, _ => None
          end
      | None => None
      end).
  rewrite IH. destruct (negb _); [reflexivity|]. destruct (sym_runA segs fuel cutpcs T true) as [leaves|]; [|reflexivity].
  rewrite leaves_edgesA_pf_eq. destruct (leaves_edgesA g i leaves targets) as [es|]; destruct (cuts_edgesA fuel cutpcs g (S i) rest targets) as [es'|]; cbn [option_map]; try reflexivity.
  rewrite map_app. reflexivity.
Qed.
Definition cfg_edgesA_pf (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list axst) : option (list (edgeA * pfacts)) := ltac2:(tb__ "0|0|
S5dVfuel;Vcutpcs;Vg;U0Vcuts;S16S0Vcuts;Vexits;A3A6").
Lemma cfg_edgesA_pf_eq : ltac2:(tb__ "0|3|
S10ScS72A1S71ScS0A1M0G0S1eSfScS11S38S80A2M1A1M2A1S66R5R4R3R2R1A5S1aScS38A1G2S78S38G1S49A3S40R5R4R3R2R1A5A4A3Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using . intros. unfold cfg_edgesA_pf, cfg_edgesA. apply cuts_edgesA_pf_eq. Qed.
Lemma forallb_map_addpf : ltac2:(tb__ "0|2|
S38SdF_;M0S80G0F_;ScS38A1S38S1eSdR3S9aS27S1S42R1A1A1A1A1R1A2R4R1A1A3Fe;S1eSdS6fS11S38S80A2M1G1R4S18S38S80R1A3S17S38S80R1A3A2Lep;S78S38G1S49R2A4A3S6fS38R4R2A3A3F_;Fes;FQ;FP;").
Proof using . intros P Q es H. induction es as [|e r IH]; cbn [map forallb]; [reflexivity|]. rewrite IH. unfold addpf. cbn [fst snd]. rewrite H. reflexivity. Qed.

Definition edge_okA (nodes : list jnodeA) (e : edgeA) : Prop := ltac2:(tb__ "0|2|
S3cS3cS1eSfS3cA1M0S6eS3cVnodes;S4aVe;A1A3S13S3cR2A2M1A3S1eG0S6eS3cVnodes;S4cVe;A1A3G1A3S24S24ScS7aQ40A1A1ScS82A1S83S29S25S1S17S0S32R9A3A1A1R5R4A3S18S0S32RaR6R4R3R2A7S79S26S28R6A1S27S1S42Ve;A1A1A1A3S18S0S32RbS7eR7S4bVe;A1A2R6R5R4A7F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;F_;F_;FTj;FTi;").

Definition SPfamGA (nodes : list jnodeA) (tp : list word) : assn := ltac2:(tb__ "0|0|
S73S20S0S0S20S32S32S20S24S24S1fS6dS11S0S32A2S15S0S32R3R2A4Vnodes;A3S33Vsegs;R2R3R1Vtp;R4A6A2Lrho;A2LJ;A2LT;A2Lw;").

Lemma first_matchA_spec : ltac2:(tb__ "0|1|
S71S0ScS0A1S10S10S7cS1eSfS11S10S7cA2M0A1S5fR6R5R4R3A4S13G0S15S10S7cR2R1A4A2A3S20S0S0S1fS1eSfS0A1S6eS0R6S9bR4R5A2A3S13S0R1A2A3S1fSa1R5R4A2S1fS1eSdS7dR3R8A2SeA3S1eSdS4R7R1R3A3SeA3A2A2A2LX;A2F_;Fs;Fj;Fj0;Ftargets;FL;Fg;").
Proof using .
  induction targets as [|X rest IH]; intros j0 j s H; cbn in H; [discriminate|].
  destruct (leaf_matches1A g L X) eqn:E.
  - injection H as <- <-. exists X. rewrite Nat.sub_diag. apply leaf_matches1A_true in E as [A B]. repeat split; auto.
  - destruct (IH (S j0) j s H) as (X' & Hn & Hle & A & B). exists X'.
    replace (j - j0)%nat with (S (j - S j0))%nat by lia. cbn. repeat split; auto. lia.
Qed.

Lemma leaves_edgesA_spec_ref : ltac2:(tb__ "0|2|
S71S10ScS2A1ScS0A1ScS38A1M0S1eSfG0A1S63R5R4R3R2A4S13G0R1A2A3S2S6dS2R1R5A3S21S1eSdS44S3R2A1A1SeA3S20S10S10S20S7cS7cS20S0S0S1fS6dS38S5aRaS3R5A1M1R3R2A4R7A3S1fS1eSfS0A1S6eS0R8R3A3S13S0R1A2A3S1fS1eSdS7dR2RbA2SeA3S1eSdS4G1R1R2A3SeA3A2A2A2LX;A2Ls;A2Lj;A2A2F_;FL;F_;Fes;Ftargets;Fleaves;Fi;Fg;").
Proof using .
  induction leaves as [|L0 rest IH]; intros targets es H L Hin; cbn in H; [destruct Hin|].
  destruct (leaf_refuted (la_state L0)) eqn:Hr.
  - destruct Hin as [<-|Hin]; [left; exact Hr|]. exact (IH targets es H L Hin).
  - destruct (first_matchA g (la_state L0) targets 0) as [[j s]|] eqn:Hm; [|discriminate].
    destruct (leaves_edgesA_ref g i rest targets) as [es'|] eqn:He; [|discriminate]. injection H as <-.
    destruct Hin as [<-|Hin].
    + right. destruct (first_matchA_spec g (la_state L0) targets 0 j s Hm) as (X & Hn & _ & A & B).
      rewrite Nat.sub_0_r in Hn. exists j, s, X. split; [cbn; auto|]. auto.
    + destruct (IH targets es' He L Hin) as [Hr'|(j' & s' & X & Hin' & Hn & A & B)]; [left; exact Hr'|].
      right. exists j', s', X. split; [cbn; auto|]. auto.
Qed.

Lemma leaves_edgesA_spec : ltac2:(tb__ "0|2|
S71S10ScS2A1ScS0A1ScS38A1M0S1eSfG0A1S58R5R4R3R2A4S13G0R1A2A3S2S6dS2R1R5A3S21S1eSdS44S3R2A1A1SeA3S20S10S10S20S7cS7cS20S0S0S1fS6dS38S5aRaS3R5A1M1R3R2A4R7A3S1fS1eSfS0A1S6eS0R8R3A3S13S0R1A2A3S1fS1eSdS7dR2RbA2SeA3S1eSdS4G1R1R2A3SeA3A2A2A2LX;A2Ls;A2Lj;A2A2F_;FL;F_;Fes;Ftargets;Fleaves;Fi;Fg;").
Proof using .
  intros g i leaves targets es H. rewrite leaves_edgesA_ref_eq in H. exact (leaves_edgesA_spec_ref g i leaves targets es H).
Qed.

Lemma cuts_edgesA_spec : ltac2:(tb__ "0|7|
S10ScS72A1S71ScS0A1M0S10G0ScS38A1M1S1eSfG1A1S53R7R6R5R3R4R2A6S13G1R1A2A3S10S0S1eSfS0A1M2S6eS0R7R2A3S13S0R1A2M3A3S1fS98R9S25S1R2A1M4A1A2S1fS1eSdS2fG4A1S14A3S1fS1eSdS5R2A1SeA3S20ScS2A1M5G5S1fS1eSfG5A1S6Vsegs;RcRbR3SeA5S13G5R1A2A3S2S6dS2R1R2A3S21S1eSdS44S3R2A1A1SeA3S20S10S10S20S7cS7cS20S0S0S1fS6dS38S5aS9cRdR9A2S3R5A1M6R3R2A4RbA3S1fS1eG2S6eS0RcR3A3G3A3S1fS1eSdS7dR2RfA2SeA3S1eSdS4G6R1R2A3SeA3A2A2A2LX;A2Ls;A2Lj;A2A2F_;FL;A2Lleaves;A2A2A2A2F_;FT;Fk;F_;Fes;Ftargets;Fi0;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  induction cuts as [|T0 rest IH]; intros i0 targets es H k T Hn; [destruct k; discriminate|].
  cbn [cuts_edgesA] in H.
  destruct (Pos.leb g (ss_next (ax_S T0)) && negb (ss_lenient (ax_S T0)) && axwf T0) eqn:Hg; cbn [negb] in H; [|discriminate].
  destruct (sym_runA segs fuel cutpcs T0 true) as [leaves|] eqn:Hrun; [|discriminate].
  destruct (leaves_edgesA g i0 leaves targets) as [es1|] eqn:He1; [|discriminate].
  destruct (cuts_edgesA fuel cutpcs g (S i0) rest targets) as [es2|] eqn:He2; [|discriminate].
  injection H as <-.
  apply andb_prop in Hg as [Hg Hwf]. apply andb_prop in Hg as [Hg Hlen].
  destruct k as [|k].
  - cbn in Hn. injection Hn as ->. split; [apply Pos.leb_le; exact Hg|].
    split; [destruct (ss_lenient (ax_S T)); [discriminate|reflexivity]|]. split; [exact Hwf|].
    exists leaves. split; [exact Hrun|]. intros L HinL.
    destruct (leaves_edgesA_spec g i0 leaves targets es1 He1 L HinL) as [Hr|(j & s & X & A & B & C & D)]; [left; exact Hr|].
    right. exists j, s, X. rewrite Nat.add_0_r. split; [apply in_or_app; left; exact A|]. auto.
  - cbn in Hn. destruct (IH (S i0) targets es2 He2 k T Hn) as (Hg' & Hl' & Hw' & leaves' & Hrun' & HL).
    split; [exact Hg'|]. split; [exact Hl'|]. split; [exact Hw'|]. exists leaves'. split; [exact Hrun'|]. intros L HinL.
    destruct (HL L HinL) as [Hr|(j & s & X & A & B & C & D)]; [left; exact Hr|]. right. exists j, s, X.
    replace (i0 + S k)%nat with (S i0 + k)%nat by lia. split; [apply in_or_app; right; exact A|]. auto.
Qed.

Theorem cfg_sound_genA : ltac2:(tb__ "0|6|
S10ScS72A1S71ScS3cA1M0G0ScS38A1M1S73OF_;S76ScS7aQ40A1A1S0S32S6dS11S0S32A2M2S15S0S32R2R1A4M3R8A3S35Vsegs;R6R2A3F_;FJ;FT;S0S32S6dG2G3R9A3S34Vsegs;S25S1R3A1A1R2A3F_;FJ;FT;S1eSfG1A1S40RbRaR9S78G2S0S17S0S32A2M4R8A4S78G2S0G4R7A4A5S13G1R6A2A3S79S38S4dS16S3cR9R8A3A1R7A3S0S32S24S6dG2S15S0S32R3R2A4M5RcA3S74Vsegs;RbS33Vsegs;R3R4R2R9A5S73S21S65RfRaR1A3RbR1A1A2Lw;A4F_;Frho;FJE;FE;S0S32S24S6dG2G5ReA3S74Vsegs;RcS33Vsegs;R3R4R2RaA5RbA4F_;Frho;FJ;FT;F_;F_;F_;F_;F_;Ftp;FQ;Fok;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es ok Q tp Hok Hst Hes Hedges Hexits T J rho HinT.
  assert (Hloop : triple segs ok (SPfamGA cuts tp) Q).
  { apply triple_loop.
    unfold SPfamGA at 1. apply triple1_ex; intros T'. apply triple1_ex; intros J'. apply triple1_ex; intros rho'.
    apply triple1_pure; intros HinT'.
    destruct (In_nth_error _ _ HinT') as [k Hk].
    assert (HkT : nth_error (map fst cuts) k = Some T') by (rewrite nth_error_map, Hk; reflexivity).
    unfold cfg_edgesA in Hes.
    destruct (cuts_edgesA_spec fuel cutpcs g (map fst cuts) 0 (map fst cuts ++ map fst exits) es Hes k T' HkT)
      as (Hle & Hlen & Hwf & leaves & Hrun & HL).
    eapply triple1_seq_l.
    { eapply (sym_run_soundA segs fuel cutpcs T' leaves ok J' rho' tp Hrun); [exact (Hok T' J' HinT') | exact Hlen | exact (Hst T' J' HinT')]. }
    intros m Hgm w Hw. destruct Hw as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as [Hr|(j & s & X & HinE & HnX & Hid & Hent)].
    { exfalso. eapply (leaf_refuted_sound rho''); [exact Hr|]. eapply smatchA_facts; exact Hsm. }
    rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold edge_okA in EOK. cbn [ea_src ea_tgt ea_leaf ea_sub] in EOK.
    rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold jnodeA in *.
    destruct (nth_error (cuts ++ exits) j) as [[Xs JX]|] eqn:HnXG; cbn in HnX; [|discriminate].
    injection HnX as ->.
    destruct w as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in Hkk.
    assert (HJX : JX (rho_sub rho'' s) tp tr md).
    { eapply (EOK (T', J') (X, JX)); [| reflexivity | apply agree_below_refl | exact Hkk |].
      - rewrite nth_error_app1; [exact Hk|]. apply nth_error_Some. congruence.
      - eapply smatchA_facts; exact Hsm. }
    assert (HSPX : SPA segs JX X (rho_sub rho'' s) tp (tr, mkCfg ms md)).
    { split; [eapply smatchA_entails; eauto | exact HJX]. }
    destruct (Nat.lt_ge_cases j (length cuts)) as [Hj|Hj].
    - apply Hgm. left. exists X, JX, (rho_sub rho'' s). split; [|exact HSPX].
      rewrite nth_error_app1 in HnXG by exact Hj. eapply nth_error_In; eauto.
    - rewrite nth_error_app2 in HnXG by exact Hj.
      exact (Hexits X JX (rho_sub rho'' s) (nth_error_In _ _ HnXG) m Hgm _ HSPX). }
  eapply triple_conseq; [| intros w Hw; exact Hw | exact Hloop].
  intros w Hw. exists T, J, rho. auto.
Qed.

Definition enodeA : Type := ltac2:(tb__ "0|0|
S11S11S0S32A2S24S72F_;A2").
Definition ena_state (n : enodeA) : axst := fst (fst n).
Definition ena_pred (n : enodeA) : jpredA := snd (fst n).
Definition ena_meas (n : enodeA) : valuation -> Z := snd n.

Definition eedge_okA (nodes : list enodeA) (e : edgeA) : Prop := ltac2:(tb__ "0|4|
S3bS3bS1eSfS3bA1M0S6eS3bVnodes;S4aVe;A1A3S13S3bR2A2M1A3S1eG0S6eS3bVnodes;S4cVe;A1A3G1A3S24S24ScS7aQ40A1A1ScS82A1S83S29S25S1S41R9A1A1A1R5R4A3S46RaR6R4R3R2A5S79S26S28R6A1S27S1S42Ve;A1A1A1A3S1fS46RbS7eR7S4bVe;A1A2M2R6R5R4A5S1fS86Z0S43RbG2A2M3A2S8cG3S43RcR8A2A2A2A2F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;F_;F_;FTj;FTi;").

Definition SPfamEA (nodes : list enodeA) (tp : list word) (bound : Z) : world -> Prop := ltac2:(tb__ "0|1|
S73S20S3bS3bS20S24S24S1fS6dS3bR2Vnodes;A3S1fS33Vsegs;S46R2A1S41R2A1R1Vtp;R3A6S1fS86Z0S43R2R1A2M0A2S8cG0Vbound;A2A2A2A2Lrho;A2Ln;A2Lw;").

Theorem cfg_complete_genA : ltac2:(tb__ "0|4|
S10ScS72A1S71ScS3bA1M0G0ScS38A1M1S73OF_;ScS7aQ40A1A1S3bS6dS3bR1R6A3S34Vsegs;S25S1S41R2A1A1A1S46R2A1A3F_;Fn;S3bS24S24S6dS3bR3R9A3S29S25S1S41R4A1A1A1R3R2A3S1eS72S43R5R3A2S43R5R4A2A3F_;F_;Frho';Frho;Fn;S1eSfG1A1S40RaR9R8S78S3bS0S41R7A4S78S3bS0S41R6A4A5S13G1R5A2A3S79S38S55S16S3bR8R7A3A1R6A3S3bS24S6dS3bR2RaA3S75Vsegs;S33Vsegs;S46R3A1M2S41R3A1M3R2R8A5S73S21S45RdR9S43R4R3A2R1A4RaR1A1A2Lw;A3F_;Frho;FE;S3bS24S6dS3bR2RcA3S75Vsegs;S33Vsegs;G2G3R2R9A5RaA3F_;Frho;Fn;F_;F_;F_;F_;F_;Ftp;FQ;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es Q tp Hst Hms Hes Hedges Hexits n rho Hin.
  set (I := fun (a : Z) (w : world) =>
              exists n rho, In n (cuts ++ exits) /\ SPA segs (ena_pred n) (ena_state n) rho tp w /\ ena_meas n rho = a /\ 0 <= a).
  assert (ROUND : forall n0 rho0 w, In n0 cuts -> SPA segs (ena_pred n0) (ena_state n0) rho0 tp w ->
            exists w' nj rhoj, wsteps segs w w' /\ In nj (cuts ++ exits)
              /\ SPA segs (ena_pred nj) (ena_state nj) rhoj tp w'
              /\ 0 <= ena_meas nj rhoj < ena_meas n0 rho0).
  { intros n0 rho0 w Hcut Hsp0.
    destruct (In_nth_error _ _ Hcut) as [k Hk].
    assert (HkT : nth_error (map ena_state cuts) k = Some (ena_state n0)) by (rewrite nth_error_map, Hk; reflexivity).
    unfold cfg_edgesA in Hes.
    destruct (cuts_edgesA_spec fuel cutpcs g (map ena_state cuts) 0 (map ena_state cuts ++ map ena_state exits) es Hes k _ HkT)
      as (Hle & Hlen & Hwf & leaves & Hrun & HL).
    destruct (sym_run_etripleA segs fuel cutpcs (ena_state n0) leaves (ena_pred n0) rho0 tp Hlen (Hst n0 Hcut) Hrun w Hsp0) as (w' & Hsteps & HLQ).
    destruct HLQ as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as [Hr|(j & s & X & HinE & HnX & Hid & Hent)].
    { exfalso. eapply (leaf_refuted_sound rho''); [exact Hr|]. eapply smatchA_facts; exact Hsm. }
    rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold eedge_okA in EOK. cbn [ea_src ea_tgt ea_leaf ea_sub] in EOK.
    rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold enodeA in *.
    destruct (nth_error (cuts ++ exits) j) as [nj|] eqn:HnXG; cbn in HnX; [|discriminate]. injection HnX as HX.
    destruct w' as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in Hkk.
    assert (FACTS : Forall (holds rho'') (ss_facts (ax_S (la_state L)))) by (eapply smatchA_facts; exact Hsm).
    destruct (EOK n0 nj ltac:(rewrite nth_error_app1; [exact Hk| apply nth_error_Some; congruence]) eq_refl rho'' rho'' tp tr md
                (agree_below_refl _ _) Hkk FACTS) as [HGj HMj].
    rewrite (Hms n0 rho0 rho'' Hcut Hag) in HMj.
    exists (tr, mkCfg ms md), nj, (rho_sub rho'' s). split; [exact Hsteps|]. split; [eapply nth_error_In; exact HnXG|].
    split; [|exact HMj]. split; [rewrite HX; eapply smatchA_entails; eauto | exact HGj]. }
  assert (BODY : forall a, etriple segs (I a) (fun w => (exists a', (Zwf 0 a' a) /\ I a' w) \/ Q w)).
  { intros a w (n0 & rho0 & Hin0 & Hsp0 & Hm0 & Ha0).
    apply in_app_or in Hin0 as [Hcut|Hexit].
    - destruct (ROUND n0 rho0 w Hcut Hsp0) as (w' & nj & rhoj & Hsteps & Hinj & Hspj & Hmj).
      exists w'. split; [exact Hsteps|]. left. exists (ena_meas nj rhoj). split; [unfold Zwf; lia|].
      exists nj, rhoj. split; [exact Hinj|]. split; [exact Hspj|]. split; [reflexivity|lia].
    - destruct (Hexits n0 rho0 Hexit w Hsp0) as (w' & Hsteps & [Hfam|Hq]).
      + destruct Hfam as (n1 & rho1 & Hin1 & Hsp1 & Hm1).
        exists w'. split; [exact Hsteps|]. left. exists (ena_meas n1 rho1). split; [unfold Zwf; lia|].
        exists n1, rho1. split; [apply in_or_app; left; exact Hin1|].
        split; [exact Hsp1|]. split; [reflexivity|lia].
      + exists w'. split; [exact Hsteps|]. right. exact Hq. }
  pose proof (@etriple_loop segs Z (Zwf 0) (Zwf_well_founded 0) I Q BODY) as LOOP.
  intros w Hw.
  destruct (Z_lt_le_dec (ena_meas n rho) 0) as [Hneg|Hnn].
  - exfalso. destruct (ROUND n rho w Hin Hw) as (w' & nj & rhoj & _ & _ & _ & Hmj). lia.
  - apply (LOOP (ena_meas n rho)). exists n, rho. split; [apply in_or_app; left; exact Hin|].
    split; [exact Hw|]. split; [reflexivity|lia].
Qed.

Record vnodeA := mkVNA { vna_state : axst; vna_rank : Z; vna_var : sv }.

Definition vmeasA (n : vnodeA) (rho : valuation) : Z := ltac2:(tb__ "0|0|
S88S89S48Vn;A1S8aZ2Z40A2A2S7bQ40S30Vrho;S52Vn;A1A2A2A2").

Definition to_enodeA (J : jpredA) (n : vnodeA) : enodeA := ltac2:(tb__ "0|0|
S15S11S0S32A2S24S72Frho;S15S0S32S3dVn;A1VJ;A4S51Vn;A1A4").

Definition echeckA (g : positive) (nodes : list vnodeA) (e : edgeA) : bool := ltac2:(tb__ "0|6|
SfS3aA1SdLx;M0S6eS3aVnodes;S4aVe;A1A3S3aG0S6eS3aVnodes;S4cVe;A1A3S3aS12S12S12S12S7dS4bVe;A1M1Vg;A2S99Vg;S25S1S3dR2A1A1A1M2A2A2S2dG2S52R2A1M3A2A2S8bZ0S48R1A1M4A2A2S1cS8dG4S48R2A1M5A2S12S87G4G5A2S9eS27S1S42Ve;A1A1A1S7fG1S52R1A1A2Z1G3A4A2A2A2Lnj;S14Xfx2Lni;S14Xfx2").

Definition check_ecfgA (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list vnodeA) : bool := ltac2:(tb__ "0|1|
S12S6fS3aS3aS2dS25S1S3dR1A1A1A1S52R1A1A2Ln;Vcuts;A3SfScS38A1M0A1SdLx;S40Vfuel;Vcutpcs;Vg;S78S3aS0S3dVcuts;A4S78S3aS0S3dVexits;A4A5G0S6fS38S5eVg;S16S3aVcuts;Vexits;A3A2R1A3Les;S14Xfx2A2").

Lemma echeck_soundA : ltac2:(tb__ "0|0|
S71S32ScS3aA1S38S34Vsegs;R4R3A3S1eSdS5eR5R3R2A3SeA3S55S78S3aS3bS50R5A1R4A4R3A2F_;F_;Fe;Fnodes;FJ;Fg;").
Proof using .
  intros g J nodes e HJ H. unfold echeckA in H. unfold eedge_okA.
  intros Ti Tj Hi Hj rho rho' tp tr md Hag Hg HF.
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (ea_src e)) as [ni|] eqn:Ei; [|discriminate].
  destruct (nth_error nodes (ea_tgt e)) as [nj|] eqn:Ej; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  cbn [to_enodeA ena_state ena_pred ena_meas fst snd] in *.
  apply andb_prop in H as [H Hdec]. apply andb_prop in H as [H Hrk].
  apply andb_prop in H as [H Hvb]. apply andb_prop in H as [Hid Hgle].
  apply Pos.leb_le in Hgle. apply Z.leb_le in Hrk.
  split.
  - eapply HJ; [| apply mat_equiv_refl | exact Hg]. eapply agree_below_trans.
    + eapply agree_below_le; [exact Hgle | exact Hag].
    + apply rho_sub_agree. exact Hid.
  - unfold vmeasA. rewrite <- eval_subst.
    rewrite (eval_agree _ rho rho' (vna_var ni) Hag Hvb).
    pose proof (urange (eval rho' (sv_subst (ea_sub e) (vna_var nj)))) as R1.
    pose proof (urange (eval rho' (vna_var ni))) as R2.
    apply orb_prop in Hdec. destruct Hdec as [Hlt | Heq].
    + apply Z.ltb_lt in Hlt. nia.
    + apply andb_prop in Heq as [Heq Hu]. apply Z.eqb_eq in Heq.
      pose proof (uleq_sound rho' _ _ 1 _ HF Hu) as U1. unfold U in U1. rewrite Heq. lia.
Qed.

Theorem cfg_complete_autoA : ltac2:(tb__ "0|2|
S10ScS72A1S71ScS3aA1M0G0S32S73OF_;ScS7aQ40A1A1S34Vsegs;R6R3A3S3aS6dS3aR1R7A3S98R9S25S1S3dR2A1A1A1A2F_;Fn;S1eSdS69RaR9R8R7R6A5SeA3S3aS24S6dS3aR2R9A3S75Vsegs;S33Vsegs;R9S3dR3A1M1R2R7A5S73S21S45S78S3aS3bS50RaA1RcA4R8S51R4R3A2R1A4R9R1A1A2Lw;A3F_;Frho;FE;S3aS24S6dS3aR2RbA3S75Vsegs;S33Vsegs;RaG1R2R8A5R9A3F_;Frho;Fn;F_;F_;F_;F_;Ftp;FQ;FJ;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits J Q tp HJ Hg Hchk Hexits n rho Hin.
  unfold check_ecfgA in Hchk. apply andb_prop in Hchk as [Hvars Hchk].
  destruct (cfg_edgesA fuel cutpcs g (map vna_state cuts) (map vna_state exits)) as [es|] eqn:Hes; [|discriminate].
  change (vna_state n) with (ena_state (to_enodeA J n)). change J with (ena_pred (to_enodeA J n)) at 1.
  apply (cfg_complete_genA fuel cutpcs g (map (to_enodeA J) cuts) (map (to_enodeA J) exits) es Q tp).
  - intros m Hm. apply in_map_iff in Hm as (m0 & <- & Hm0). cbn. eapply stableA_mono; [exact (Hg m0 Hm0) | exact HJ].
  - intros m r r' Hm Hag. apply in_map_iff in Hm as (m0 & <- & Hm0). cbn in Hag |- *. unfold vmeasA.
    rewrite (eval_agree _ r r' (vna_var m0) Hag (proj1 (forallb_forall _ _) Hvars m0 Hm0)). reflexivity.
  - rewrite !map_map. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He.
    apply (echeck_soundA g J); [exact HJ|]. exact (proj1 (forallb_forall _ _) Hchk e He).
  - intros E rhoE HinE. apply in_map_iff in HinE as (E0 & <- & HinE0). exact (Hexits E0 rhoE HinE0).
  - apply in_map_iff. exists n. auto.
Qed.

Lemma eexit_postA : ltac2:(tb__ "0|0|
S32S71S24ScS3aA1ScS2A1S3aScS7aQ40A1A1S6dS2S9S3dR2A1S9dA2R3A3S24S75Vsegs;S33Vsegs;S84S24S29R9R8R1A3Lr;R9A2S3dR4A1R1R3A5S73S21S45S78S3aS3bS50S84S24S29RaR9R1A3Lr;RaA2A1R7A4R4S51R5R2A2R1A4S36Vsegs;RaR9R8R4R6R1A7A2Lw;A3Frho;F_;Ftp;FP;Fposts;Fcuts;Frho0;Fn;FJ0;").
Proof using .
  intros J0 n rho0 cuts posts P tp Hin rho w [Hsm [Hag Hk]]. exists w. split; [apply wsteps_refl|].
  right. exists (mkLeafA (vna_state P) RsSymJump), rho. auto.
Qed.

Lemma eexit_reenterA : ltac2:(tb__ "0|2|
S32S71ScS3aA1S73OF_;S3aS3aScS26A1S0S7cScS7aQ40A1A1M0S6dS3aR5R8A3S1eS0S3dR6A1S85R5R4A2A3S1eSdS4S3dR8A1R5R4A3SeA3S1eSdS7dR5RcA2SeA3S34Vsegs;RdReA3S1eSdS6fS26S2cS25S1R8A1A1A1R9A3SeA3S24G0ScS82A1S83R14R4R3R2R1A4S79S26S28R5A1S27S1S3dR11A1A1A1A3S79S26S28S7eR6ReA2A1R10A3F_;F_;Fmd;Ftr;Ftp;Frho;S86S88S48RcA1Z1A2S48RdA1M1A2S86Z0G1A2S24S75Vsegs;S33Vsegs;R14S3dR10A1R1RbA5S73S21S45S78S3aS3bS50R15A1R13A4RcS51R11R2A2R1A4R12R1A1A2Lw;A3Frho;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Fs;FT0;FF;FC;FE;FQ;Fcuts;Fg;FJ;").
Proof using .
  intros J g cuts Q E C F T0 s tp Hin HC He Hid HJ Hb HF Hrk Hr0 rho w Hsp.
  exists w. split; [apply wsteps_refl|]. left.
  exists (to_enodeA J C), (rho_sub rho s). split; [apply in_map; exact Hin|].
  cbn [to_enodeA ena_state ena_pred ena_meas fst snd]. split.
  - rewrite HC. eapply SPA_entails_sem; eauto.
  - unfold vmeasA.
    pose proof (urange (eval (rho_sub rho s) (vna_var C))) as R1.
    pose proof (urange (eval rho (vna_var E))) as R2. nia.
Qed.

Record lnodeA := mkLNA { lna_state : axst; lna_rank : Z; lna_vars : list (vdir * sv) }.

Definition lmeasA (n : lnodeA) (rho : valuation) : Z := ltac2:(tb__ "0|1|
S88S89S4eVn;A1S8aS93S8eS90A1A2A2S89S97Vrho;S4fVn;A1M0A2S8aS93S8eS9bS90S19S11S8fS2bA2G0A2A2A1A2A2A2").

Definition to_enodeLA (J : jpredA) (n : lnodeA) : enodeA := ltac2:(tb__ "0|0|
S15S11S0S32A2S24S72Frho;S15S0S32S3eVn;A1VJ;A4S59Vn;A1A4").

Definition echeck2A (g : positive) (nodes : list lnodeA) (e : edgeA) : bool := ltac2:(tb__ "0|9|
SfS39A1SdLx;M0S6eS39Vnodes;S4aVe;A1A3S39G0S6eS39Vnodes;S4cVe;A1A3S39S12S12S12S12S12S12S7dS4bVe;A1M1Vg;A2S99Vg;S25S1S3eR2A1A1A1A2A2S6fS11S8fS2bA2M2G2S2dS25S1S3eR3A1A1A1S18S8fS2bR1A3A2Lc;S4fR2A1M3A3A2S9fS19G2G3A2M4S90A2A2S9fS19G2S4fR1A1M5A2M6S90A2A2S8bZ0S4eR1A1M7A2A2S1cS8dG7S4eR2A1M8A2S12S12S87G7G8A2Sa0G6G4A2A2S96S27S1S42Ve;A1A1A1G1G5G3A4A2A2A2Lnj;S14Xfx2Lni;S14Xfx2").

Definition check_ecfg2A (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list lnodeA) : bool := ltac2:(tb__ "0|2|
S12S6fS39S39S6fS11S8fS2bA2M0G0S2dS25S1S3eR2A1A1A1S18S8fS2bR1A3A2Lc;S4fR1A1A3Ln;Vcuts;A3SfScS38A1M1A1SdLx;S40Vfuel;Vcutpcs;Vg;S78S39S0S3eVcuts;A4S78S39S0S3eVexits;A4A5G1S6fS38S54Vg;S16S39Vcuts;Vexits;A3A2R1A3Les;S14Xfx2A2").

Lemma lmeasA_nonneg : ltac2:(tb__ "0|1|
S39S24S86Z0M0S4eR2A1A2S86G0S59R3R2A2A2F_;Frho;Fn;").
Proof using .
  intros n rho H. unfold lmeasA. pose proof (lex_val_range rho (lna_vars n)).
  pose proof (B64_pos (LMAX)). pose proof (B64_pos (LMAX - length (lna_vars n))). nia.
Qed.

Lemma echeck2_soundA : ltac2:(tb__ "0|0|
S71S32ScS39A1S38S34Vsegs;R4R3A3S1eSdS54R5R3R2A3SeA3S55S78S39S3bS64R5A1R4A4R3A2F_;F_;Fe;Fnodes;FJ;Fg;").
Proof using .
  intros g J nodes e HJ H. unfold echeck2A in H. unfold eedge_okA.
  intros Ti Tj Hi Hj rho rho' tp tr md Hag Hg HF.
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (ea_src e)) as [ni|] eqn:Ei; [|discriminate].
  destruct (nth_error nodes (ea_tgt e)) as [nj|] eqn:Ej; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  cbn [to_enodeLA ena_state ena_pred ena_meas fst snd] in *.
  apply andb_prop in H as [H Hdec]. apply andb_prop in H as [H Hrk].
  apply andb_prop in H as [H Hlj]. apply andb_prop in H as [H Hli].
  apply andb_prop in H as [H Hvb]. apply andb_prop in H as [Hid Hgle].
  apply Pos.leb_le in Hgle. apply Z.leb_le in Hrk. apply Nat.leb_le in Hli. apply Nat.leb_le in Hlj.
  split.
  - eapply HJ; [| apply mat_equiv_refl | exact Hg]. eapply agree_below_trans.
    + eapply agree_below_le; [exact Hgle | exact Hag].
    + apply rho_sub_agree. exact Hid.
  - split; [apply lmeasA_nonneg; exact Hrk|].
    unfold lmeasA.
    pose proof (lex_part_bound (rho_sub rho' (ea_sub e)) (lna_vars nj) Hlj) as Bj.
    pose proof (lex_val_range rho (lna_vars ni)) as Ri.
    pose proof (B64_pos (LMAX - length (lna_vars ni))) as Pi. pose proof (B64_pos LMAX) as PL.
    apply orb_prop in Hdec. destruct Hdec as [Hlt | Heq].
    + apply Z.ltb_lt in Hlt. nia.
    + apply andb_prop in Heq as [Heq Hlex]. apply andb_prop in Heq as [Heq Hlen].
      apply Z.eqb_eq in Heq. apply Nat.eqb_eq in Hlen.
      pose proof (lex_check_sound rho' _ _ _ _ HF Hlex Hlen) as L.
      rewrite <- (lex_val_agree _ rho rho' (lna_vars ni) Hag Hvb) in L.
      rewrite Heq, Hlen. nia.
Qed.

Theorem cfg_complete_auto2A : ltac2:(tb__ "0|2|
S10ScS72A1S71ScS39A1M0G0S32S73OF_;ScS7aQ40A1A1S34Vsegs;R6R3A3S39S6dS39R1R7A3S98R9S25S1S3eR2A1A1A1A2F_;Fn;S1eSdS5cRaR9R8R7R6A5SeA3S39S24S6dS39R2R9A3S75Vsegs;S33Vsegs;R9S3eR3A1M1R2R7A5S73S21S45S78S39S3bS64RaA1RcA4R8S59R4R3A2R1A4R9R1A1A2Lw;A3F_;Frho;FE;S39S24S6dS39R2RbA3S75Vsegs;S33Vsegs;RaG1R2R8A5R9A3F_;Frho;Fn;F_;F_;F_;F_;Ftp;FQ;FJ;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits J Q tp HJ Hg Hchk Hexits n rho Hin.
  unfold check_ecfg2A in Hchk. apply andb_prop in Hchk as [Hvars Hchk].
  destruct (cfg_edgesA fuel cutpcs g (map lna_state cuts) (map lna_state exits)) as [es|] eqn:Hes; [|discriminate].
  change (lna_state n) with (ena_state (to_enodeLA J n)). change J with (ena_pred (to_enodeLA J n)) at 1.
  apply (cfg_complete_genA fuel cutpcs g (map (to_enodeLA J) cuts) (map (to_enodeLA J) exits) es Q tp).
  - intros m Hm. apply in_map_iff in Hm as (m0 & <- & Hm0). cbn. eapply stableA_mono; [exact (Hg m0 Hm0) | exact HJ].
  - intros m r r' Hm Hag. apply in_map_iff in Hm as (m0 & <- & Hm0). cbn in Hag |- *. unfold lmeasA.
    rewrite (lex_val_agree _ r r' (lna_vars m0) Hag (proj1 (forallb_forall _ _) Hvars m0 Hm0)). reflexivity.
  - rewrite !map_map. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He.
    apply (echeck2_soundA g J); [exact HJ|]. exact (proj1 (forallb_forall _ _) Hchk e He).
  - intros E rhoE HinE. apply in_map_iff in HinE as (E0 & <- & HinE0). exact (Hexits E0 rhoE HinE0).
  - apply in_map_iff. exists n. auto.
Qed.

Definition to_jnodeLA (J : jpredA) (n : lnodeA) : jnodeA := ltac2:(tb__ "0|0|
S15S0S32S3eVn;A1VJ;A4").

Lemma echeck2_edge_okA : ltac2:(tb__ "0|0|
S71S32ScS39A1S38S34Vsegs;R4R3A3S1eSdS54R5R3R2A3SeA3S4dS78S39S3cS6cR5A1R4A4R3A2F_;F_;Fe;Fnodes;FJ;Fg;").
Proof using .
  intros g J nodes e HJ H. unfold echeck2A in H. unfold edge_okA.
  intros Ti Tj Hi Hj rho rho' tp tr md Hag Hg HF.
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (ea_src e)) as [ni|] eqn:Ei; [|discriminate].
  destruct (nth_error nodes (ea_tgt e)) as [nj|] eqn:Ej; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  cbn [to_jnodeLA fst snd] in *.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [Hid Hgle].
  apply Pos.leb_le in Hgle.
  eapply HJ; [| apply mat_equiv_refl | exact Hg]. eapply agree_below_trans.
  - eapply agree_below_le; [exact Hgle | exact Hag].
  - apply rho_sub_agree. exact Hid.
Qed.

Theorem cfg_sound_auto2A : ltac2:(tb__ "0|2|
S10ScS72A1S71ScS39A1M0G0S32S73OF_;S76ScS7aQ40A1A1S35Vsegs;R3R4A3S34Vsegs;R8R5A3S39S6dS39R1R9A3S98RbS25S1S3eR2A1A1A1A2F_;Fn;S1eSdS5cRcRbRaR9R8A5SeA3S39S24S6dS39R2RbA3S74Vsegs;RaS33Vsegs;RbS3eR3A1M1R2R8A5S73S21S3fRcS78S39S0S3eReA4R9R1A4RaR1A1A2Lw;A4F_;Frho;FE;S39S24S6dS39R2RdA3S74Vsegs;RbS33Vsegs;RcG1R2R9A5RaA4F_;Frho;Fn;F_;F_;F_;F_;F_;Ftp;FQ;Fok;FJ;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits J ok Q tp Hok HJ Hg Hchk Hexits n rho Hin.
  unfold check_ecfg2A in Hchk. apply andb_prop in Hchk as [Hvars Hchk].
  destruct (cfg_edgesA fuel cutpcs g (map lna_state cuts) (map lna_state exits)) as [es|] eqn:Hes; [|discriminate].
  refine (cfg_sound_genA fuel cutpcs g (map (to_jnodeLA J) cuts) (map (to_jnodeLA J) exits) es ok Q tp _ _ _ _ _ (lna_state n) J rho _).
  - intros T J' HinT. apply in_map_iff in HinT as (m & Heq & Hm). unfold to_jnodeLA in Heq. injection Heq as <- <-. exact Hok.
  - intros T J' HinT. apply in_map_iff in HinT as (m & Heq & Hm). unfold to_jnodeLA in Heq. injection Heq as <- <-.
    eapply stableA_mono; [exact (Hg m Hm) | exact HJ].
  - rewrite !map_map. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He.
    apply (echeck2_edge_okA g J); [exact HJ|]. exact (proj1 (forallb_forall _ _) Hchk e He).
  - intros E JE rhoE HinE. apply in_map_iff in HinE as (E0 & Heq & HinE0).
    unfold to_jnodeLA in Heq. injection Heq as <- <-.
    eapply triple_conseq; [intros w Hw; exact Hw | | exact (Hexits E0 rhoE HinE0)].
    intros w [Hw|Hw]; [left | right; exact Hw].
    destruct Hw as (T & rho1 & HinT & Hsp1). apply in_map_iff in HinT as (n1 & <- & Hn1).
    exists (lna_state n1), J, rho1. split; [|exact Hsp1]. apply in_map_iff. exists n1. split; [reflexivity | exact Hn1].
  - apply in_map_iff. exists n. auto.
Qed.

Definition nodes_atA (ok : assn) (nodes : list jnodeA) (Q : assn) (tp : list word) (m : nat) : Prop := ltac2:(tb__ "0|0|
S0S32S24S6dS11S0S32A2S15S0S32R3R2A4Vnodes;A3S77Vsegs;Vok;Vm;S33Vsegs;R3R4R2Vtp;A5VQ;A5F_;Frho;FJ;FT;").

Theorem cfg_sound_recA : ltac2:(tb__ "0|5|
S10ScS72A1S71ScS3cA1M0G0ScS38A1M1S73OF_;S76ScS7aQ40A1A1S0S32S6dS11S0S32A2M2S15S0S32R2R1A4M3R8A3S35Vsegs;R6R2A3F_;FJ;FT;S0S32S6dG2G3R9A3S34Vsegs;S25S1R3A1A1R2A3F_;FJ;FT;S1eSfG1A1S40RbRaR9S78G2S0S17S0S32A2M4R8A4S78G2S0G4R7A4A5S13G1R6A2A3S79S38S4dS16S3cR9R8A3A1R7A3S10S0S32S24S6dG2S15S0S32R3R2A4RdA3S5bRcRfRbRaR5A5S77Vsegs;RdR6S33Vsegs;R4R5R3RbA5RcA5F_;F_;Frho;FJE;FE;Fm;S10S5bR9RcR8R7R1A5Fn;F_;F_;F_;F_;F_;Ftp;FQ;Fok;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es ok Q tp Hok Hst Hes Hedges Hexits n.
  induction n as [|n IH]; intros T J rho HinT.
  - intros _ w _. exact I.
  - destruct (In_nth_error _ _ HinT) as [k Hk].
    assert (HkT : nth_error (map fst cuts) k = Some T) by (rewrite nth_error_map, Hk; reflexivity).
    unfold cfg_edgesA in Hes.
    destruct (cuts_edgesA_spec fuel cutpcs g (map fst cuts) 0 (map fst cuts ++ map fst exits) es Hes k T HkT)
      as (Hle & Hlen & Hwf & leaves & Hrun & HL).
    intros HgQS. pose proof (@guards_mono segs ok (S n) n Q ltac:(lia) HgQS) as HgQ.
    apply (sym_run_soundA segs fuel cutpcs T leaves ok J rho tp Hrun (Hok T J HinT) Hlen (Hst T J HinT) n).
    intros w Hw. destruct Hw as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as [Hr|(j & s & X & HinE & HnX & Hid & Hent)].
    { exfalso. eapply (leaf_refuted_sound rho''); [exact Hr|]. eapply smatchA_facts; exact Hsm. }
    rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold edge_okA in EOK. cbn [ea_src ea_tgt ea_leaf ea_sub] in EOK.
    rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold jnodeA in *.
    destruct (nth_error (cuts ++ exits) j) as [[Xs JX]|] eqn:HnXG; cbn in HnX; [|discriminate].
    injection HnX as ->.
    destruct w as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in Hkk.
    assert (HJX : JX (rho_sub rho'' s) tp tr md).
    { eapply (EOK (T, J) (X, JX)); [| reflexivity | apply agree_below_refl | exact Hkk |].
      - rewrite nth_error_app1; [exact Hk|]. apply nth_error_Some. congruence.
      - eapply smatchA_facts; exact Hsm. }
    assert (HSPX : SPA segs JX X (rho_sub rho'' s) tp (tr, mkCfg ms md)).
    { split; [eapply smatchA_entails; eauto | exact HJX]. }
    destruct (Nat.lt_ge_cases j (length cuts)) as [Hj|Hj].
    + rewrite nth_error_app1 in HnXG by exact Hj.
      exact (IH X JX (rho_sub rho'' s) (nth_error_In _ _ HnXG) HgQ _ HSPX).
    + rewrite nth_error_app2 in HnXG by exact Hj.
      exact (Hexits n X JX (rho_sub rho'' s) (nth_error_In _ _ HnXG) IH HgQ _ HSPX).
Qed.

Corollary cfg_sound_recA_triple : ltac2:(tb__ "0|6|
S10ScS72A1S71ScS3cA1M0G0ScS38A1M1S73OF_;S76ScS7aQ40A1A1S0S32S6dS11S0S32A2M2S15S0S32R2R1A4M3R8A3S35Vsegs;R6R2A3F_;FJ;FT;S0S32S6dG2G3R9A3S34Vsegs;S25S1R3A1A1R2A3F_;FJ;FT;S1eSfG1A1S40RbRaR9S78G2S0S17S0S32A2M4R8A4S78G2S0G4R7A4A5S13G1R6A2A3S79S38S4dS16S3cR9R8A3A1R7A3S10S0S32S24S6dG2S15S0S32R3R2A4M5RdA3S5bRcRfRbRaR5A5S77Vsegs;RdR6S33Vsegs;R4R5R3RbA5RcA5F_;F_;Frho;FJE;FE;Fm;S0S32S24S6dG2G5ReA3S74Vsegs;RcS33Vsegs;R3R4R2RaA5RbA4F_;Frho;FJ;FT;F_;F_;F_;F_;F_;Ftp;FQ;Fok;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es ok Q tp Hok Hst Hes Hedges Hexits T J rho HinT n.
  exact (cfg_sound_recA fuel cutpcs g cuts exits es ok Q tp Hok Hst Hes Hedges Hexits n T J rho HinT).
Qed.

End CFGA.
