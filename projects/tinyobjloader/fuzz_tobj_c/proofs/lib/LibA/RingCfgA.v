(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingCfg"; "rnode"; "rmeas"; "node_okb"; "rn_ghost"; "rcheck"; "rn_state"; "to_enodeR"; "@Corelib.Init.Datatypes"; "list"; "bool"; "option"; "true"; "app"; "nat"; "Some"; "andb"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "agree_below"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.RingCfgA.RCA"; "RJ"; "rnA"; "SPfamRA"; "srcA"; "agree_wm"; "e2e"; "check_rcfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "edgeA"; "cuts_edgesA"; "ea_leaf"; "ea_src"; "ea_sub"; "ea_tgt"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "mkAX"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "eedge_ok"; "enode"; "mkEdge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Zwf Wellfounded.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue RingBuf Ring RingCfg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section RCA.
Variable segs : list Segment.
Variable g : positive.
Variable vn : positive.
Variable ln lp : positive.
Variable X : list (sv * sv).
Variable xb : sv.
Variable J0 : jpredA.
Variable rho0 : valuation.

Definition agree_wm (rho rho' : valuation) : Prop := ltac2:(tb__ "0|1|
S19S33S3dR1Vg;A2S18S17Q40A1M0S12Vrho;R2A2S12Vrho';R2A2A3F_;Fi;G0S18S9S17Q8A1A1S11Vrho;R1A2S11Vrho';R1A2A3Fa;A2").

Hypothesis J0_ok : ltac2:(tb__ "0|0|
S10S10S7S17Q40A1A1S7S35A1S34S34S22R6R5A2S3bVsegs;R5R3R2A4VJ0;R8R6R5R4A4VJ0;R8R7R6R4A4F_;F_;F_;Fmd';Fmd;Ftr;Ftp;Frho';Frho;").

Definition axof (S : sstate) : axst := ltac2:(tb__ "0|0|
S31VS;VX;Vxb;A3").
Definition rnA (nd : rnode) : axst := axof (rn_state nd).
Definition srcA (nd : rnode) : axst := axof (src_state nd).

Definition RJ (nd : rnode) : jpredA := ltac2:(tb__ "0|0|
S10S7S17Q40A1A1S7S35A1S34S19VJ0;R4R3R2R1A4S3Vg;Vvn;Vln;Vlp;Vrho0;Vnd;R4A7A2Lmd;Ltr;Ltp;Lrho;").

Lemma agree_below_wm : ltac2:(tb__ "0|0|
S33S10S10S3cVg;R3A2S13R4R3R2A3S22R4R3A2F_;F_;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' Hle (Hw & _ & Hm). split; [|exact Hm]. intros i Hi. apply Hw. lia.
Qed.

Lemma stableA_RJ : ltac2:(tb__ "0|0|
S0S18S8S2Vg;Vvn;Vln;Vlp;R1A5SaA3S16Vsegs;S14S5R2A1A1S1eR2A1A3F_;Fnd;").
Proof using J0_ok.
  intros nd Hok rho rho' tp tr md md' Hag Hme [HJ HG].
  destruct (node_okb_spec g vn ln lp nd Hok) as (_ & Hg & _).
  split; [eapply J0_ok; [eapply agree_below_wm; [exact Hg|exact Hag] | exact Hme | exact HJ]|].
  exact (proj1 (ghost_agree g vn ln lp rho0 nd rho rho' Hok Hag HG)).
Qed.

Definition SPfamRA (cuts : list rnode) (tp : list word) (bound : Z) : world -> Prop := ltac2:(tb__ "0|1|
S1cS1aS0S0S1aS10S10S19S2bS0R2Vcuts;A3S19S15Vsegs;S1eR2A1S1fR2A1R1Vtp;R3A6S19S36Z0S1Vln;R2R1A3M0A2S37G0Vbound;A2A2A2A2Lrho;A2Lnd;A2Lw;").

Lemma SPA_srcA : ltac2:(tb__ "0|0|
S0S10S7S17Q40A1A1S1cS18S8S2Vg;Vvn;Vln;Vlp;R4A5SaA3S15Vsegs;S1eR5A1S1fR5A1R4R3R2A6S15Vsegs;S1eR6A1S21R6A1R5R4R3A6F_;F_;Fw;Ftp;Frho;Fnd;").
Proof using .
  intros nd rho tp w Hok [Hsm [HJ HG]]. split; [|split; assumption].
  unfold srcA, src_state. change (axof (add_facts (rn_gfacts nd) (rn_state nd))) with (ax_add_facts (rn_gfacts nd) (rnA nd)).
  apply smatchA_add_facts; [exact Hsm | eapply (gfacts_sound g vn ln lp rho0); eauto |].
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (node_okb_spec g vn ln lp nd Hok)))))).
Qed.

Definition e2e (e : edgeA) : edge := ltac2:(tb__ "0|0|
S3aS28Ve;A1S30S27Ve;A1A1S2aVe;A1S29Ve;A1A4").

Theorem rcfg_completeA : ltac2:(tb__ "0|5|
ScS7S32A1S7S0A1M0G0S7S25A1M1S1cOF_;S7S17Q40A1A1S18S8S2cS0S2Vg;Vvn;Vln;Vlp;A4R5A3SaA3S18S9G1A1S26Vsegs;R8R7Vg;U0S2dS0S2fS21R6A4S2dS0S2fS1fSbS0R6R5A3A4A7SdG1R4A2A3S2eS25S25S38S2dS0S39S6Vg;Vvn;Vln;Vlp;Vrho0;A5SbS0R8R7A3A4S23R1A1A2Le;R5A3S0S10S2bS0R2R9A3S3Vg;Vvn;Vln;Vlp;Vrho0;R3R2A7M2S1dVsegs;S15Vsegs;S1eR4A1M3S1fR4A1M4R3R8A5S1cS1bS20RdR9S1Vln;R5R4A3R1A4RaR1A1A2Lw;A3F_;F_;Frho;FE;S0S10S2bS0R2RbA3G2S1dVsegs;S15Vsegs;G3G4R3R9A5RaA3F_;F_;Frho;Fn;F_;F_;F_;F_;Ftp;FQ;Fes;Fexits;Fcuts;Fcutpcs;Ffuel;").
Proof using J0_ok.
  intros fuel cutpcs cuts exits es Q tp Hok Hes Hedges Hexits n rho Hin Hg.
  set (I := fun (a : Z) (w : world) =>
              exists nd rho, In nd (cuts ++ exits) /\ SPA segs (RJ nd) (rnA nd) rho tp w /\ rmeas ln nd rho = a /\ 0 <= a).
  assert (EDGE : forall n0 rho1 w, In n0 cuts -> SPA segs (RJ n0) (rnA n0) rho1 tp w ->
            exists w' nj rhoj, wsteps segs w w' /\ In nj (cuts ++ exits) /\ SPA segs (RJ nj) (rnA nj) rhoj tp w'
                               /\ 0 <= rmeas ln nj rhoj < rmeas ln n0 rho1).
  { intros n0 rho1 w Hcut Hsp0.
    destruct (In_nth_error _ _ Hcut) as [k Hk].
    pose proof (proj1 (forallb_forall _ _) Hok n0 Hcut) as Hok0.
    assert (HkT : nth_error (map srcA cuts) k = Some (srcA n0)) by (rewrite nth_error_map, Hk; reflexivity).
    destruct (cuts_edgesA_spec segs fuel cutpcs g (map srcA cuts) 0 (map rnA (cuts ++ exits)) es Hes k _ HkT)
      as (Hle & Hlen & Hwf & leaves & Hrun & HL).
    pose proof (node_okb_spec g vn ln lp n0 Hok0) as (Hlen0 & _).
    pose proof (SPA_srcA n0 rho1 tp w Hok0 Hsp0) as Hsp1.
    assert (Hst : stableA segs (ss_next (ax_S (srcA n0))) (RJ n0)).
    { unfold srcA, axof, src_state. cbn [ax_S add_facts ss_next]. apply stableA_RJ. exact Hok0. }
    destruct (sym_run_etripleA segs fuel cutpcs (srcA n0) leaves (RJ n0) rho1 tp Hlen Hst Hrun w Hsp1) as (w' & Hsteps & HLQ).
    destruct HLQ as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as [Hr|(j & s & Xt & HinE & HnX & Hid & Hent)].
    { exfalso. eapply (leaf_refuted_sound rho''); [exact Hr|]. eapply smatchA_facts; exact Hsm. }
    rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold eedge_ok, e2e in EOK. cbn [e_src e_tgt e_leaf e_sub] in EOK.
    rewrite nth_error_map in HnX.
    destruct (nth_error (cuts ++ exits) j) as [nj|] eqn:HnXG; cbn in HnX; [|discriminate]. injection HnX as HX.
    destruct w' as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in Hkk.
    assert (FACTS : Forall (holds rho'') (ss_facts (ax_S (la_state L)))) by (eapply smatchA_facts; exact Hsm).
    assert (Hni : nth_error (map (to_enodeR g vn ln lp rho0) (cuts ++ exits)) k = Some (to_enodeR g vn ln lp rho0 n0)).
    { rewrite nth_error_map, nth_error_app1, Hk; [reflexivity|]. apply nth_error_Some. congruence. }
    assert (Hnj : nth_error (map (to_enodeR g vn ln lp rho0) (cuts ++ exits)) j = Some (to_enodeR g vn ln lp rho0 nj)).
    { rewrite nth_error_map, HnXG. reflexivity. }
    destruct Hkk as [HJ'' HG''].

    assert (Hag0 : agree_below (ss_next (rn_state n0)) rho1 rho'').
    { unfold srcA, axof, src_state in Hag. cbn [ax_S add_facts ss_next] in Hag. exact Hag. }
    destruct (EOK (to_enodeR g vn ln lp rho0 n0) (to_enodeR g vn ln lp rho0 nj) Hni Hnj rho'' rho''
                (agree_below_refl _ _) HG'' FACTS) as [HGj HMj].
    cbn [to_enodeR en_state en_ghost en_meas fst snd] in HGj, HMj.
    rewrite (proj2 (ghost_agree g vn ln lp rho0 n0 rho1 rho'' Hok0 Hag0 (proj2 (proj2 Hsp0)))) in HMj.
    exists (tr, mkCfg ms md), nj, (rho_sub rho'' s). split; [exact Hsteps|]. split; [eapply nth_error_In; exact HnXG|].
    split; [|exact HMj]. split.
    - rewrite HX. eapply smatchA_entails; eauto.
    - split; [|exact HGj]. eapply J0_ok; [| apply mat_equiv_refl | exact HJ''].
      eapply (agree_below_wm g); [lia|]. apply rho_sub_agree. exact Hid. }
  assert (BODY : forall a, etriple segs (I a) (fun w => (exists a', (Zwf 0 a' a) /\ I a' w) \/ Q w)).
  { intros a w (n0 & rho1 & Hin0 & Hsp0 & Hm0 & Ha0).
    apply in_app_or in Hin0 as [Hcut|Hexit].
    - destruct (EDGE n0 rho1 w Hcut Hsp0) as (w' & nj & rhoj & Hsteps & Hinj & Hspj & Hmj).
      exists w'. split; [exact Hsteps|]. left. exists (rmeas ln nj rhoj). split; [unfold Zwf; lia|].
      exists nj, rhoj. split; [exact Hinj|]. split; [exact Hspj|]. split; [reflexivity|lia].
    - destruct (Hexits n0 rho1 Hexit (proj2 (proj2 Hsp0)) w Hsp0) as (w' & Hsteps & [Hfam|Hq]).
      + destruct Hfam as (n1 & rho2 & Hin1 & Hsp1 & Hm1).
        exists w'. split; [exact Hsteps|]. left. exists (rmeas ln n1 rho2). split; [unfold Zwf; lia|].
        exists n1, rho2. split; [apply in_or_app; left; exact Hin1|]. split; [exact Hsp1|]. split; [reflexivity|lia].
      + exists w'. split; [exact Hsteps|]. right. exact Hq. }
  pose proof (@etriple_loop segs Z (Zwf 0) (Zwf_well_founded 0) I Q BODY) as LOOP.
  intros w Hw.
  destruct (Z_lt_le_dec (rmeas ln n rho) 0) as [Hneg|Hnn].
  - exfalso. destruct (EDGE n rho w Hin Hw) as (w' & nj & rhoj & _ & _ & _ & Hm). lia.
  - apply (LOOP (rmeas ln n rho)). exists n, rho. split; [apply in_or_app; left; exact Hin|].
    split; [exact Hw|]. split; [reflexivity|lia].
Qed.

Definition check_rcfgA (fuel : nat) (cutpcs : list Z) (cuts exits : list rnode) : bool := ltac2:(tb__ "0|2|
SeS2cS0S2Vg;Vvn;Vln;Vlp;A4Vcuts;A3S9S7S25A1M0A1S8Lx;S26Vsegs;Vfuel;Vcutpcs;Vg;U0S2dS0S2fS21Vcuts;A4S2dS0S2fS1fSbS0Vcuts;Vexits;A3M1A4A7G0S2cS25S25S4Vg;Vvn;Vln;Vlp;G1S23R1A1A6Le;R1A3Les;SfX9x2A2").

Theorem rcfg_complete_autoA : ltac2:(tb__ "0|4|
ScS7S32A1S7S0A1M0G0S1cOF_;S7S17Q40A1A1S18S8S24R6R5R4R3A4SaA3S0S10S2bS0R2R6A3S3Vg;Vvn;Vln;Vlp;Vrho0;R3R2A7M1S1dVsegs;S15Vsegs;S1eR4A1M2S1fR4A1M3R3R6A5S1cS1bS20RaR7S1Vln;R5R4A3R1A4R8R1A1A2Lw;A3F_;F_;Frho;FE;S0S10S2bS0R2R8A3G1S1dVsegs;S15Vsegs;G2G3R3R7A5R8A3F_;F_;Frho;Fn;F_;F_;Ftp;FQ;Fexits;Fcuts;Fcutpcs;Ffuel;").
Proof using J0_ok.
  intros fuel cutpcs cuts exits Q tp Hchk Hexits n rho Hin Hg.
  unfold check_rcfgA in Hchk. apply andb_prop in Hchk as [Hok Hchk].
  destruct (cuts_edgesA segs fuel cutpcs g 0 (map srcA cuts) (map rnA (cuts ++ exits))) as [es|] eqn:Hes; [|discriminate].
  eapply (rcfg_completeA fuel cutpcs cuts exits es Q tp Hok Hes); [|exact Hexits|exact Hin|exact Hg].
  apply Forall_forall. intros e He. apply rcheck_sound. exact (proj1 (forallb_forall _ _) Hchk e He).
Qed.

Lemma reenter_cutA : ltac2:(tb__ "0|0|
S7S0A1S0S10S7S17Q40A1A1S32S1cS2bS0R5R6A3S15Vsegs;S1eR6A1S1fR6A1R5R4R2A6S36Z0S1Vln;R7R6A3A2S37S1Vln;R8R7A3R5A2S20RaR7R6R5A4F_;F_;F_;F_;Fw;Fbound;Ftp;Frho';FN;Fcuts;").
Proof using .
  intros cuts N rho' tp bound w Hin Hsp H0 Hlt.
  exists N, rho'. split; [exact Hin|]. split; [exact Hsp|]. lia.
Qed.

End RCA.
