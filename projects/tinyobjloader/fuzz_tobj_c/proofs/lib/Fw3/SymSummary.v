(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sstate"; "ss_next"; "sobj"; "smatch"; "rw"; "sv"; "rl"; "rm"; "agree_below"; "ss_objs"; "obj_range"; "eval"; "sv_below"; "swf"; "holds"; "sprop"; "SVar"; "mkVal"; "ob_base"; "ob_hi"; "ob_lo"; "obj_holds"; "obj_wf"; "sv_eqb"; "tfact"; "cell"; "odefault"; "ranges_disjoint"; "sfcsr"; "sprop_below"; "c_off"; "c_val"; "ob_cells"; "ob_dflt"; "outside_all"; "pairwise_disjoint"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "tf_expr"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "or"; "not"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "pair"; "andb"; "option"; "prod"; "Some"; "orb"; "nat"; "app"; "fst"; "negb"; "false"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "set_objs"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "ms_rom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.Call"; "jpost"; "LQP"; "call_linkP"; "call_checkP"; "J_ofP"; "call_link"; "import_okP"; "new_objs"; "post_okP"; "rho_join"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "rho_absorb"; "wsub_get"; "in_ranges"; "subst_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "jpred"; "SPJ"; "SP"; "LQJ"; "LQ"; "stableJ"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "filter"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "sv_vars_all"; "wsub_bound"; "import_post"; "call_check"; "shift_sub"; "import_sub"; "obj_vars_all"; "same_frame"; "sprop_vars_all"; "state_vars_all"; "wsub_below"; "wsub_dom_below"; "fresh_count"; "join_rw"; "pos_add_nat"; "post_ok"; "post_vars_ok"; "dflt_vars_all"; "import_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "tripleN"; "assn"; "w_cfg"; "w_tr"; "@Stdlib.PArith.BinPos.Pos"; "ltb"; "to_nat"; "le"; "lt"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@Corelib.Init.Peano"; "lt"; "le"; "@Corelib.Init.Nat"; "add"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundR SymFrame SymEntail SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint shift_sub (nf : positive) (cnt : nat) (nc : positive) : wsub :=
  match cnt with
  | O => []
  | S c => (nf, SVar nc) :: shift_sub (Pos.succ nf) c (Pos.succ nc)
  end.

Definition pos_add_nat (p : positive) (n : nat) : positive := Pos.of_nat (Pos.to_nat p + n).

Definition fresh_count (nf : positive) (L : sstate) : nat := ltac2:(tb__ "0|0|
S8fS84S2VL;A1A1S84Vnf;A1A2").

Definition import_sub (s : wsub) (nf : positive) (L : sstate) (nc : positive) : wsub := ltac2:(tb__ "0|0|
S3dS39S31S6A2Vs;S6dVnf;S75Vnf;VL;A2Vnc;A3A3").

Definition import_next (nf : positive) (L : sstate) (nc : positive) : positive := ltac2:(tb__ "0|0|
S77Vnc;S75Vnf;VL;A2A2").

Definition import_post (s : wsub) (nf : positive) (L : sstate) (nc : positive) (R : list sobj) : sstate := ltac2:(tb__ "0|0|
S5aS6eVs;Vnf;VL;Vnc;A4VL;S7bVnf;VL;Vnc;A3A3S1S44R1S3dS3SaR1A1VR;A3A2TS';").

Definition wsub_below (s : wsub) (n : positive) : bool := ltac2:(tb__ "0|1|
S62S39S31S6A2M0G0SdVn;S41S31S6R1A3A2Lje;Vs;A3").

Definition wsub_dom_below (s : wsub) (nf : positive) : bool := ltac2:(tb__ "0|1|
S62S39S31S6A2M0G0S83S3eS31S6R1A3Vnf;A2Lje;Vs;A3").

Definition same_frame (o o' : sobj) : bool := ltac2:(tb__ "0|0|
S37S37S18S13Vo;A1S13Vo';A1A2S18S15Vo;A1S15Vo';A1A2A2S18S14Vo;A1S14Vo';A1A2A2").

Fixpoint sv_vars_all (f : positive -> bool) (e : sv) : bool :=
  match e with
  | SLit _ => true
  | SVar i => f i
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => sv_vars_all f a && sv_vars_all f b
  | SExt _ _ a => sv_vars_all f a
  | SLBytes _ i _ => sv_vars_all f i
  end.

Fixpoint sprop_vars_all (f : positive -> bool) (p : sprop) : bool :=
  match p with
  | SPBranch _ a b | SPUlt a b | SPUle a b | SPEq a b => sv_vars_all f a && sv_vars_all f b
  | SPNot q => sprop_vars_all f q
  | SPTrue => true
  | SPAlign i _ => f i
  end.

Definition dflt_vars_all (f : positive -> bool) (d : odefault) : bool := ltac2:(tb__ "0|1|
S1bS33Ld;Vd;S35S35S35S31S35Ll;M0G0S32S6S34S39S32S32A2A1S34S19A1S37S69Vf;R3A2S62S19S19S69Vf;S2aR1A1A2Lt;R1A3A2Ltmpl;Lflds;Lcnt;Lesz;X1bx6").

Definition obj_vars_all (f : positive -> bool) (o : sobj) : bool := ltac2:(tb__ "0|0|
S37S37S37S37S69Vf;S13Vo;A1A2S69Vf;S15Vo;A1A2A2S69Vf;S14Vo;A1A2A2S62S1aS1aS37S69Vf;S1fR1A1A2S69Vf;S20R1A1A2A2Lc;S21Vo;A1A3A2S7aVf;S22Vo;A1A2A2").

Definition state_vars_all (f : positive -> bool) (S : sstate) : bool := ltac2:(tb__ "0|2|
S37S37S37S37S37S62S6S69Vf;A1M0S28VS;A1A3S62S6G0S27VS;A1A3A2S1dS33Lx;S26VS;A1S35S6S69Vf;R1A2Lv;M1X1dx2A2S38S6A1S33Lx;S29VS;A1G1S35X38x2A2S62S3S6fVf;A1SaVS;A1A3A2S62S10S71Vf;A1S25VS;A1A3A2").

Definition wsub_bound (s : wsub) (i : positive) : bool := ltac2:(tb__ "0|1|
S63S39S31S6A2M0G0S88S3eS31S6R1A3Vi;A2Lje;Vs;A3").

Definition post_vars_ok (s : wsub) (nf nc : positive) (L : sstate) : bool := ltac2:(tb__ "0|0|
S72S31S3bS3bS3fS83R1Vnf;A2A1S6aVs;R1A2A2S83R1Vnc;A2A2Lv;VL;A2").

Definition post_ok (Pre : sstate) (s : wsub) (nc : positive) (R : list sobj) (L : sstate) : bool := ltac2:(tb__ "0|1|
S37S37S37S37S87S2VPre;A1M0S2VL;A1A2S62S3S3S63S3S70R1A1SaVPre;A1A3Lo;SaVL;A1A3A2S79Vs;G0Vnc;VL;A4A2SeVL;A1A2SeS6bVs;G0VL;Vnc;VR;A5A1A2").

Definition call_check (C Pre : sstate) (s : wsub) (R : list sobj) (Posts : list leaf) : bool := ltac2:(tb__ "0|1|
S37S37S37S73Vs;S2VC;A1M0A2S74Vs;S2VPre;A1A2A2S87PaG0A2A2S62S42S42S78VPre;Vs;G0VR;S43R1A1A5LL;VPosts;A3A2").

Fixpoint join_rw (f g : positive -> word) (nc nf : positive) (cnt : nat) : positive -> word :=
  match cnt with
  | O => f
  | S c => fun v => if Pos.eqb v nc then g nf else join_rw f g (Pos.succ nc) (Pos.succ nf) c v
  end.

Lemma join_rw_below : ltac2:(tb__ "0|2|
S3cS31S45Q40A1M0F_;M1G1S31S31S31S86R1R3A2S2bG0S76R6R5R4R3R7R2A6R6R2A1A3F_;Fv;Fnf;Fnc;Fg;Ff;Fcnt;").
Proof.
  induction cnt as [|c IH]; intros f g nc nf v Hv; cbn; [reflexivity|].
  destruct (Pos.eqb_spec v nc); [lia|]. apply IH. lia.
Qed.

Lemma wsub_get_app : ltac2:(tb__ "0|2|
S34S39S31S6A2M0A1M1G1S31S2bS6S58S3dG0R3R2A3R1A2S33S6L_;S6aR3R1A2S58R3R1A2S58R2R1A2X33x2A3Fi;Fs2;Fs1;").
Proof.
  induction s1 as [|[j e] t IH]; intros s2 i; cbn; [reflexivity|].
  destruct (Pos.eqb_spec i j); cbn.
  - subst. rewrite Pos.eqb_refl. reflexivity.
  - rewrite IH. destruct (Pos.eqb_spec j i); [congruence|]. cbn. reflexivity.
Qed.

Lemma wsub_get_unbound : ltac2:(tb__ "0|0|
S56S31S2bS33S6aR2R1A2S40A3S2bS6S58R3R2A2S11R2A1A3F_;Fi;Fs;").
Proof.
  induction s as [|[j e] t IH]; intros i H; cbn in *; [reflexivity|].
  destruct (Pos.eqb_spec i j); cbn in *.
  - subst. rewrite Pos.eqb_refl in H. discriminate.
  - destruct (Pos.eqb_spec j i); [congruence|]. apply IH. exact H.
Qed.

Lemma wsub_bound_app : ltac2:(tb__ "0|2|
S34S39S31S6A2M0A1M1G1S31S2bS33S6aS3dG0R3R2A3R1A2S3bS6aR3R1A2S6aR2R1A2A2A3Fi;Fs2;Fs1;").
Proof. intros. unfold wsub_bound. apply existsb_app. Qed.

Lemma shift_sub_eval : ltac2:(tb__ "0|3|
S3cS31S45Q40A1M0F_;M1G1S31S31S31S31S34S45Q8A1M2A1F_;G0S38G2A1F_;S2bS33S6aS6dR4R8R5A3R3A2S35A3S2cS2bG0ScS12S76R8R7R6R5R9A5R3R2A3S58S6dR5R9R6A3R4A2A2R7R4A1A3S2dS31S31S2cS2bS6S58S6dR6RaR7A3R5A2S11R1A1A3S85R7R1A2A2Lk;A2A2F_;Frm0;Frl0;Fv;Fnf;Fnc;Fg;Ff;Fcnt;").
Proof.
  induction cnt as [|c IH]; intros f g nc nf v rl0 rm0 Hb; cbn in Hb; [discriminate|].
  cbn [shift_sub wsub_get]. destruct (Pos.eqb_spec v nf).
  - subst. cbn. rewrite Pos.eqb_refl. split; [reflexivity|]. exists nc. split; [reflexivity|lia].
  - cbn in Hb. destruct (Pos.eqb_spec nf v); [congruence|]. cbn in Hb.
    destruct (IH f g (Pos.succ nc) (Pos.succ nf) v rl0 rm0 Hb) as [E (k & Hk & Hge)].
    rewrite Hk in *. cbn in E |- *. destruct (Pos.eqb_spec k nc); [lia|].
    split; [exact E|]. exists k. split; [reflexivity|lia].
Qed.

Lemma shift_sub_bound : ltac2:(tb__ "0|0|
S3cS31S31S31S2eS2bS33S6aS6dR3R4R2A3R1A2S35A3S2cS85R3R1A2S8cS84R1A1S8eS84R3A1R4A2A2A2A2Fv;Fnc;Fnf;Fcnt;").
Proof.
  induction cnt as [|c IH]; intros nf nc v.
  - cbn. split; [discriminate | lia].
  - pose proof (IH (Pos.succ nf) (Pos.succ nc) v) as IH'. rewrite Pos2Nat.inj_succ in IH'.
    unfold wsub_bound in IH' |- *. cbn [shift_sub existsb fst].
    destruct (Pos.eqb_spec nf v); cbn [orb].
    + subst. split; [intros _; lia | reflexivity].
    + rewrite IH'. split; intros [A B]; split; lia.
Qed.

Lemma shift_sub_unbound_get : ltac2:(tb__ "0|0|
S3cS31S31S31S2bS33S6aS6dR3R4R2A3R1A2S40A3S2bS6S58S6dR4R5R3A3R2A2S11R2A1A3F_;Fv;Fnc;Fnf;Fcnt;").
Proof. intros. apply wsub_get_unbound. assumption. Qed.

Lemma eval_agree_vars : ltac2:(tb__ "0|1|
S31S33F_;S0S0S6S31S2bS33R5R1A1S35A3S2bS45Q40A1M0S5R5R2A2S5R4R2A2A3F_;Fv;S31S2bS34S45Q8A1A1S7R5R1A2S7R4R1A2A3Fl;S2bS33S69R6R3A2S35A3S2bG0ScR6R4A2ScR5R4A2A3F_;F_;F_;Fe;Frho';Frho;Ff;").
Proof.
  intros f rho rho' e Hv Hl. induction e; cbn; intros H;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2)); try reflexivity.
  - apply Hv. exact H.
  - rewrite (IHe H). reflexivity.
  - rewrite Hl, (IHe H). reflexivity.
Qed.

Lemma holds_agree_vars : ltac2:(tb__ "0|0|
S31S33F_;S0S0S10S31S2bS33R5R1A1S35A3S2bS45Q40A1S5R5R2A2S5R4R2A2A3F_;Fv;S31S2bS34S45Q8A1A1S7R5R1A2S7R4R1A2A3Fl;S2bS33S71R6R3A2S35A3S2eSfR6R4A2SfR5R4A2A2F_;F_;F_;Fp;Frho';Frho;Ff;").
Proof.
  intros f rho rho' p Hv Hl. induction p; cbn; intros H;
    try (apply andb_prop in H as [H1 H2];
         rewrite (eval_agree_vars f rho rho' _ Hv Hl H1), (eval_agree_vars f rho rho' _ Hv Hl H2));
    try (split; intros X; exact X).
  - specialize (IHp H). split; intros X Y; apply X; apply IHp; exact Y.
  - rewrite (Hv i H). split; intros X; exact X.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma obj_holds_agree_vars : ltac2:(tb__ "0|0|
S31S33F_;S0S0S48S3S31S2bS33R6R1A1S35A3S2bS45Q40A1S5R6R2A2S5R5R2A2A3F_;Fv;S31S2bS34S45Q8A1A1S7R6R1A2S7R5R1A2A3Fl;S2bS33S6fR7R3A2S35A3S16Vsegs;R7R5R4A4S16Vsegs;R7R6R5A4F_;F_;F_;F_;Fo;Fms;Frho';Frho;Ff;").
Proof using .
  intros f rho rho' ms o Hv Hl Ho (Hb & Hw & Hc & Hd & Hdl).
  unfold obj_vars_all in Ho. apply andb_prop in Ho as [Ho Hdv]. apply andb_prop in Ho as [Ho Hcells]. apply andb_prop in Ho as [Ho Hhi]. apply andb_prop in Ho as [Hbase Hlo].
  pose proof (eval_agree_vars f rho rho' _ Hv Hl Hbase) as EB.
  assert (ELO : obj_lo_of rho' o = obj_lo_of rho o).
  { unfold obj_lo_of, soff. rewrite (eval_agree_vars f rho rho' _ Hv Hl Hlo). reflexivity. }
  assert (EHI : obj_hi_of rho' o = obj_hi_of rho o).
  { unfold obj_hi_of, soff. rewrite (eval_agree_vars f rho rho' _ Hv Hl Hhi). reflexivity. }
  assert (EC : forall c, In c (ob_cells o) -> soff rho' (c_off c) = soff rho (c_off c) /\ eval rho' (c_val c) = eval rho (c_val c)).
  { intros c Hin. pose proof (proj1 (forallb_forall _ _) Hcells c Hin) as W. apply andb_prop in W as [W1 W2].
    unfold soff. rewrite (eval_agree_vars f rho rho' _ Hv Hl W1), (eval_agree_vars f rho rho' _ Hv Hl W2). auto. }
  assert (COV : forall off, covered rho' (ob_cells o) off <-> covered rho (ob_cells o) off).
  { intros off. unfold covered. rewrite !Exists_exists. split; intros (c & Hin & Hic); exists c; split; auto;
      unfold in_cell in *; destruct (EC c Hin) as [E1 _]; [rewrite <- E1 | rewrite E1]; exact Hic. }
  unfold obj_holds. rewrite <- EB, ELO, EHI. split; [exact Hb|]. split; [exact Hw|]. split; [|split].
  - apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (A & B & C).
    destruct (EC c Hin) as [E1 E2]. unfold cell_holds, oaddr in *. rewrite E1, E2, <- EB. repeat split; assumption.
  - intros off Hoff Hnc. specialize (Hd off Hoff ltac:(intros X; apply Hnc; apply COV; exact X)).
    destruct (ob_dflt o); cbn in *; try exact Hd; rewrite <- Hl; exact Hd.
  - eapply dflt_inv_exprs; [exact Hl | | exact Hdl].
    destruct (ob_dflt o); try exact I. cbn in Hdv. apply andb_prop in Hdv as [Hcnt Htm].
    split; [apply (eval_agree_vars f); assumption|].
    apply Forall_forall. intros t Hin. apply (eval_agree_vars f); [assumption | assumption |].
    exact (proj1 (forallb_forall _ _) Htm t Hin).
Qed.

Lemma obj_range_agree_vars : ltac2:(tb__ "0|0|
S31S33F_;S0S0S3S31S2bS33R5R1A1S35A3S2bS45Q40A1S5R5R2A2S5R4R2A2A3F_;Fv;S31S2bS34S45Q8A1A1S7R5R1A2S7R4R1A2A3Fl;S2bS33S6fR6R3A2S35A3S2bS39S32S32A2SbR5R4A2SbR6R4A2A3F_;F_;F_;Fo;Frho';Frho;Ff;").
Proof using .
  intros f rho rho' o Hv Hl Ho.
  unfold obj_vars_all in Ho. apply andb_prop in Ho as [Ho _]. apply andb_prop in Ho as [Ho _]. apply andb_prop in Ho as [Ho Hhi]. apply andb_prop in Ho as [Hbase Hlo].
  unfold obj_range, obj_lo_of, obj_hi_of, soff.
  rewrite (eval_agree_vars f rho rho' _ Hv Hl Hbase), (eval_agree_vars f rho rho' _ Hv Hl Hlo), (eval_agree_vars f rho rho' _ Hv Hl Hhi).
  reflexivity.
Qed.

Lemma smatch_agree_vars : ltac2:(tb__ "0|2|
S31S33F_;S0S0S1S39S34S47A1S65A2S31S2bS33R6R1A1S35A3S2bS45Q40A1M0S5R6R2A2S5R5R2A2A3F_;Fv;S31S2bS34S45Q8A1M1A1S7R6R1A2S7R5R1A2A3Fl;S2bG0S38G1A1F_;S8R6A1S8R5A1A3S2bS33S72R8R5A2S35A3S4Vsegs;R8R6R5A4S4Vsegs;R8R7R6A4F_;F_;F_;F_;F_;Fw;FS;Frho';Frho;Ff;").
Proof using .
  intros f rho rho' S [tr [ms md]] Hv Hl Hm Hs Hsm.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold state_vars_all in Hs.
  apply andb_prop in Hs as [Hs Hfa]. apply andb_prop in Hs as [Hs Hob]. apply andb_prop in Hs as [Hs Hrv].
  apply andb_prop in Hs as [Hs Hfc]. apply andb_prop in Hs as [Hrg Hfr].
  assert (NTH : forall (l : list sv) n, forallb (sv_vars_all f) l = true -> sv_vars_all f (nth n l (SLit 0)) = true).
  { intros l. induction l as [|x t IH]; intros n Hfl; destruct n; cbn in *; try reflexivity;
      apply andb_prop in Hfl as [A B]; [exact A | apply IH; exact B]. }
  assert (EREG : forall r, eval rho' (reg_sv S r) = eval rho (reg_sv S r)).
  { intros r. unfold reg_sv. destruct (Z.eqb r 0); [reflexivity|].
    symmetry. apply (eval_agree_vars f); auto. }
  assert (EFREG : forall r, eval rho' (freg_sv S r) = eval rho (freg_sv S r)).
  { intros r. unfold freg_sv. symmetry. apply (eval_agree_vars f); auto. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hroc|].
  split. { intros r Hr. rewrite EREG. apply Hregs. exact Hr. }
  split. { intros r. rewrite EFREG. apply Hfregs. }
  split. { destruct (ss_fcsr S); cbn in *; [exact Hfcsr|]. rewrite <- (eval_agree_vars f rho rho' _ Hv Hl Hfc). exact Hfcsr. }
  split. { unfold resv_match in *. destruct (ss_resv S); destruct (ms_resv ms); try exact Hresv.
           rewrite <- (eval_agree_vars f rho rho' _ Hv Hl Hrv). exact Hresv. }
  split.
  { destruct Hmem as (Hall & Hpd & Hfrm). split; [|split].
    - apply Forall_forall. intros o Hin. eapply obj_holds_agree_vars; eauto.
      + apply (proj1 (forallb_forall _ _) Hob). exact Hin.
      + exact (proj1 (Forall_forall _ _) Hall o Hin).
    - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd.
      erewrite map_ext_in; [exact Hpd|]. intros o Hin. eapply obj_range_agree_vars; eauto.
      apply (proj1 (forallb_forall _ _) Hob). exact Hin.
    - intros a Ha. rewrite <- Hm. apply Hfrm. unfold outside_all in *.
      apply Forall_forall. intros o Hin. cbn zeta.
      rewrite <- (obj_range_agree_vars f rho rho' o Hv Hl (proj1 (forallb_forall _ _) Hob o Hin)).
      exact (proj1 (Forall_forall _ _) Ha o Hin). }
  apply Forall_forall. intros p Hin. apply (holds_agree_vars f rho rho' p Hv Hl).
  - apply (proj1 (forallb_forall _ _) Hfa). exact Hin.
  - exact (proj1 (Forall_forall _ _) Hfacts p Hin).
Qed.

End WithSegs.

Lemma sv_below_vars_all : ltac2:(tb__ "0|0|
S31S6S2bS33SdR2R1A2S35A3S2bS33S69S31S83R1R4A2Li;R2A2S35A3F_;Fe;Fn;").
Proof.
  intros n e. induction e; cbn; intros H; auto;
    apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity.
Qed.

Lemma obj_wf_vars_all : ltac2:(tb__ "0|0|
S31S3S2bS33S17R2R1A2S35A3S2bS33S6fS31S83R1R4A2Lv;R2A2S35A3F_;Fo;Fn;").
Proof.
  intros n o H. destruct (obj_wf_parts n o H) as (Hb & Hlo & Hhi & Hc). pose proof (obj_wf_dflt n o H) as Hd. unfold obj_vars_all.
  rewrite (sv_below_vars_all _ _ Hb), (sv_below_vars_all _ _ Hlo), (sv_below_vars_all _ _ Hhi). cbn [andb].
  apply andb_true_intro. split.
  - apply forallb_forall. intros c Hin. pose proof (proj1 (forallb_forall _ _) Hc c Hin) as W.
    unfold cell_wf in W. apply andb_prop in W as [W Wv]. apply andb_prop in W as [W Wo].
    rewrite (sv_below_vars_all _ _ Wo), (sv_below_vars_all _ _ Wv). reflexivity.
  - destruct (ob_dflt o); try reflexivity. cbn in Hd |- *. apply andb_prop in Hd as [H1 H2].
    rewrite (sv_below_vars_all _ _ H1). cbn. apply forallb_forall. intros t Ht. apply sv_below_vars_all.
    exact (proj1 (forallb_forall _ _) H2 t Ht).
Qed.

Lemma sv_vars_all_true : ltac2:(tb__ "0|0|
S6S2bS33S69S31S35L_;R1A2S35A3Fe;").
Proof. induction e; cbn; rewrite ?IHe1, ?IHe2, ?IHe; reflexivity. Qed.

Definition agree_vals (n : positive) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|0|
S2cS31S86R1Vn;A2S2bS45Q40A1S5Vrho;R2A2S5Vrho';R2A2A3F_;Fi;S31S2bS34S45Q8A1A1S7Vrho;R1A2S7Vrho';R1A2A3Fl;A2").

Lemma agree_below_vals : ltac2:(tb__ "0|0|
S31S0S0S9R3R2R1A3S68R4R3R2A3F_;Frho';Frho;Fn;").
Proof. intros n rho rho' (A & B & _). split; assumption. Qed.

Lemma agree_vals_refl : ltac2:(tb__ "0|0|
S31S0S68R2R1R1A3Frho;Fn;").
Proof. intros. split; intros; reflexivity. Qed.

Lemma agree_vals_trans : ltac2:(tb__ "0|0|
S31S0S0S0S68R4R3R2A3S68R5R3R2A3S68R6R5R3A3F_;F_;Fr3;Fr2;Fr1;Fn;").
Proof. intros n r1 r2 r3 [A1 B1] [A2 B2]. split; intros; [rewrite A1 by assumption; auto | rewrite B1; auto]. Qed.

Lemma agree_vals_le : ltac2:(tb__ "0|0|
S31S31S0S0S85R4R3A2S68R4R3R2A3S68R6R4R3A3F_;F_;Frho';Frho;Fm;Fn;").
Proof. intros n m rho rho' Hle [A B]. split; [intros i Hi; apply A; lia | exact B]. Qed.

Lemma agree_vals_below : ltac2:(tb__ "0|0|
S31S0S0S68R3R2R1A3S45Q40A1S2bS38S45Q8A1A1S8R4R1A2S8R3R1A2A3Fa;S9R5R4R3A3F_;F_;Frho';Frho;Fn;").
Proof. intros n rho rho' [A B] C. split; [exact A | split; [exact B | exact C]]. Qed.

Lemma eval_agree_vals : ltac2:(tb__ "0|0|
S31S0S0S6S68R4R3R2A3S2bS33SdR5R2A2S35A3S2bS45Q40A1ScR5R3A2ScR4R3A2A3F_;F_;Fe;Frho';Frho;Fn;").
Proof.
  intros n rho rho' e [A B] Hb. apply (eval_agree_vars (fun i => Pos.ltb i n)).
  - intros v Hv. apply A. apply Pos.ltb_lt. exact Hv.
  - exact B.
  - apply sv_below_vars_all. exact Hb.
Qed.

Lemma holds_agree_vals : ltac2:(tb__ "0|0|
S31S0S0S10S68R4R3R2A3S2bS33S1eR5R2A2S35A3S2eSfR5R3A2SfR4R3A2A2F_;F_;Fp;Frho';Frho;Fn;").
Proof.
  intros n rho rho' p [A B] Hb. apply (holds_agree_vars (fun i => Pos.ltb i n)).
  - intros v Hv. apply A. apply Pos.ltb_lt. exact Hv.
  - exact B.
  - revert Hb. induction p; cbn; intros Hb; auto;
      apply andb_prop in Hb as [H1 H2]; rewrite (sv_below_vars_all _ _ H1), (sv_below_vars_all _ _ H2); reflexivity.
Qed.

Lemma obj_range_agree_vals : ltac2:(tb__ "0|0|
S31S0S0S3S68R4R3R2A3S2bS33S17R5R2A2S35A3S2bS39S32S32A2SbR4R3A2SbR5R3A2A3F_;F_;Fo;Frho';Frho;Fn;").
Proof.
  intros n rho rho' o [A B] Hwf. apply (obj_range_agree_vars (fun i => Pos.ltb i n)).
  - intros v Hv. apply A. apply Pos.ltb_lt. exact Hv.
  - exact B.
  - apply obj_wf_vars_all. exact Hwf.
Qed.

Section Call.
Variable segs : list Segment.

Definition rho_join (rho rhoL : valuation) (nc nf : positive) (cnt : nat) (m : word -> option byte) : valuation := ltac2:(tb__ "0|0|
S12S76S5Vrho;A1S5VrhoL;A1Vnc;Vnf;Vcnt;A5S7Vrho;A1Vm;A3").

Lemma wsub_get_below : ltac2:(tb__ "0|0|
S56S31S31S2bS33S73R3R2A2S35A3S2bS33S6aR4R2A2S35A3S2bS33SdR4S58R5R3A2A2S35A3F_;F_;Fv;Fn;Fs;").
Proof using .
  induction s as [|[j e] t IH]; intros n v Hsb Hb; cbn in *; [discriminate|].
  apply andb_prop in Hsb as [He Ht]. destruct (Pos.eqb_spec v j); [exact He|].
  apply IH; [exact Ht|]. destruct (Pos.eqb_spec j v); [congruence|]. exact Hb.
Qed.

Lemma wsub_bound_dom : ltac2:(tb__ "0|0|
S56S31S31S2bS33S74R3R2A2S35A3S2bS33S6aR4R2A2S35A3S86R3R4A2F_;F_;Fv;Fnf;Fs;").
Proof using .
  intros s nf v Hdom Hb. unfold wsub_dom_below in Hdom. unfold wsub_bound in Hb.
  apply existsb_exists in Hb as ([j e] & Hin & Hj). cbn in Hj. apply Pos.eqb_eq in Hj. subst j.
  pose proof (proj1 (forallb_forall _ _) Hdom _ Hin) as D. cbn in D. apply Pos.ltb_lt in D. exact D.
Qed.

Lemma import_agree : ltac2:(tb__ "0|2|
S0S0S0S56S31S31S1S45Q40A1M0S38S45Q8A1M1A1F_;S2bS33S73R5R3A2S35A3S2bS33S74R6R5A2S35A3S8dS84R6A1S84S2R4A1A1A2S2bS31G0F_;S5RaA1S5RbA1A3S2bS31S34G1A1F_;S7RbA1S7RcA1A3S68R9S55RcRaA2RbA3S31S2bS33S3bS3bS3fS83R1RbA2A1S6aRcR1A2A2S83R1RaA2A2S35A3S8cS84R2A1S84S2RaA1A1A2S2bG0S5RfR3A2S5S55S54R11RfRcRdS75RdRbA2RaA6S6eReRdRbRcA4A2R3A2A3F_;F_;Fv;F_;F_;F_;F_;F_;F_;Fm;FL;Fnc;Fnf;Fs;FrhoL;FrhoA;Frho;").
Proof using .
  intros rho rhoA rhoL s nf nc L m Hsb Hdom Hle HrwA HrlA Hag v Hv Hlt.
  set (cnt := fresh_count nf L). set (rhoX := rho_join rho rhoL nc nf cnt m).
  cbn [rho_sub rw]. unfold import_sub. fold cnt. rewrite wsub_get_app.
  destruct Hag as [AR AL].
  destruct (wsub_bound s v) eqn:Hb.
  -
    pose proof (wsub_bound_dom s nf v Hdom Hb) as Hvnf.
    rewrite <- (AR v Hvnf). cbn [rho_sub rw].
    apply (eval_agree_vars (fun i => Pos.ltb i nc)).
    + intros i Hi. apply Pos.ltb_lt in Hi. unfold rhoX, rho_join. cbn [rw].
      rewrite join_rw_below by exact Hi. rewrite HrwA. reflexivity.
    + rewrite HrlA. reflexivity.
    + apply sv_below_vars_all. eapply wsub_get_below; eauto.
  - destruct (wsub_bound (shift_sub nf cnt nc) v) eqn:Hb2.
    +
      destruct (shift_sub_eval cnt (rw rho) (rw rhoL) nc nf v (rl rho) m Hb2) as [E _].
      unfold rhoX, rho_join. rewrite E. reflexivity.
    +
      rewrite (shift_sub_unbound_get _ _ _ _ Hb2). cbn [eval rw].
      pose proof (shift_sub_bound cnt nf nc v) as SB. rewrite Hb2 in SB.
      assert (Hvnf : (v < nf)%positive).
      { destruct (Pos.ltb_spec v nf) as [X|X]; [exact X|]. exfalso.
        assert (false = true); [|discriminate]. apply SB. unfold cnt, fresh_count. split; [exact X|lia]. }
      assert (Hvnc : (v < nc)%positive).
      { destruct (Pos.ltb_spec v nf); [|lia]. cbn in Hv. destruct (Pos.ltb_spec v nc); [assumption|discriminate]. }
      unfold rhoX, rho_join. cbn [rw]. rewrite join_rw_below by exact Hvnc.
      rewrite <- (AR v Hvnf). cbn [rho_sub rw]. rewrite (wsub_get_unbound _ _ Hb). cbn [eval]. rewrite HrwA. reflexivity.
Qed.

Lemma smatch_set_rm : ltac2:(tb__ "0|2|
S0S1S39S34S47A1S65A2S45Q40A1M0S38S45Q8A1A1M1F_;G0S23R5SaR4A1R1A3S2bG1R3R2A1S8R6R2A2A3F_;Fa;S4Vsegs;R5R4R3A4S4Vsegs;S12S5R6A1S7R6A1R3A3R5R4A4F_;F_;Fm;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] m Hm Hsm.
  assert (EV : forall e, eval (mkVal (rw rho) (rl rho) m) e = eval rho e).
  { intros e. induction e; cbn; rewrite ?IHe1, ?IHe2, ?IHe; reflexivity. }
  assert (SO : forall e, soff (mkVal (rw rho) (rl rho) m) e = soff rho e).
  { intros e. unfold soff. rewrite EV. reflexivity. }
  assert (HO : forall p, holds (mkVal (rw rho) (rl rho) m) p <-> holds rho p).
  { intros p. induction p; cbn; rewrite ?EV; try (split; intros X; exact X).
    split; intros X Y; apply X; [apply (proj2 IHp) | apply (proj1 IHp)]; exact Y. }
  assert (RG : forall o, obj_range (mkVal (rw rho) (rl rho) m) o = obj_range rho o).
  { intros o. unfold obj_range, obj_lo_of, obj_hi_of. rewrite EV, !SO. reflexivity. }
  assert (CV : forall cells off, covered (mkVal (rw rho) (rl rho) m) cells off <-> covered rho cells off).
  { intros cells off. unfold covered, in_cell. rewrite !Exists_exists. split; intros (c & Hin & Hc); exists c; rewrite ?SO in *; auto. }
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hroc|].
  split; [intros r Hr; rewrite EV; apply Hregs; exact Hr|].
  split; [intros r; rewrite EV; apply Hfregs|].
  split; [destruct (ss_fcsr S); cbn in *; rewrite ?EV; exact Hfcsr|].
  split; [unfold resv_match in *; destruct (ss_resv S); destruct (ms_resv ms); rewrite ?EV; exact Hresv|].
  split.
  - destruct Hmem as (Hall & Hpd & Hfr). split; [|split].
    + apply Forall_forall. intros o Hin. pose proof (proj1 (Forall_forall _ _) Hall o Hin) as (Hb & Hw & Hc & Hd & Hdl).
      unfold obj_holds. unfold obj_lo_of, obj_hi_of in *. rewrite EV, !SO.
      split; [exact Hb|]. split; [exact Hw|]. split; [|split].
      * apply Forall_forall. intros c Hc'. pose proof (proj1 (Forall_forall _ _) Hc c Hc') as (A & B & C).
        unfold cell_holds, oaddr in *. rewrite !SO, !EV. repeat split; assumption.
      * intros off Hoff Hnc. specialize (Hd off Hoff ltac:(intros X; apply Hnc; apply CV; exact X)).
        destruct (ob_dflt o); cbn in *; exact Hd.
      * eapply dflt_inv_exprs; [| | exact Hdl]; [intros; reflexivity|].
        destruct (ob_dflt o); try exact I. split; [symmetry; apply EV|]. apply Forall_forall. intros t _. symmetry. apply EV.
    + apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd. erewrite map_ext_in; [exact Hpd|]. intros o _. apply RG.
    + intros a Ha. cbn. rewrite Hm; [apply Hfr|]; unfold outside_all in *; apply Forall_forall; intros o Hin;
        pose proof (proj1 (Forall_forall _ _) Ha o Hin) as X; cbn beta in X |- *; rewrite ?RG in X; rewrite ?RG; exact X.
  - apply Forall_forall. intros p Hin. apply HO. exact (proj1 (Forall_forall _ _) Hfacts p Hin).
Qed.

Lemma sv_vars_all_and : ltac2:(tb__ "0|0|
S31S33F_;S31S6S2bS33S69R3R1A2S35A3S2bS33SdR3R2A2S35A3S2bS33S69S31S37R6R1A1S83R1R5A2A2Lv;R3A2S35A3F_;F_;Fe;Fn;Ff;").
Proof using .
  intros f n e. induction e; cbn; intros H1 H2; auto;
    try (apply andb_prop in H1 as [A1 B1]; apply andb_prop in H2 as [A2 B2]; rewrite (IHe1 A1 A2), (IHe2 B1 B2); reflexivity).
  rewrite H1, H2. reflexivity.
Qed.

Lemma sprop_vars_all_and : ltac2:(tb__ "0|0|
S31S33F_;S31S10S2bS33S71R3R1A2S35A3S2bS33S1eR3R2A2S35A3S2bS33S71S31S37R6R1A1S83R1R5A2A2Lv;R3A2S35A3F_;F_;Fp;Fn;Ff;").
Proof using .
  intros f n p. induction p; cbn; intros H1 H2; auto;
    try (apply andb_prop in H1 as [A1 B1]; apply andb_prop in H2 as [A2 B2];
         rewrite (sv_vars_all_and f n _ A1 A2), (sv_vars_all_and f n _ B1 B2); reflexivity).
  rewrite H1, H2. reflexivity.
Qed.

Lemma state_vars_all_and : ltac2:(tb__ "0|0|
S31S33F_;S1S2bS33S72R2R1A2S35A3S2bS33SeR2A1S35A3S2bS33S72S31S37R5R1A1S83R1S2R4A1A2A2Lv;R3A2S35A3F_;F_;FS;Ff;").
Proof using .
  intros f S Hs Hwf. unfold state_vars_all in *.
  apply andb_prop in Hs as [Hs Hfa]. apply andb_prop in Hs as [Hs Hob]. apply andb_prop in Hs as [Hs Hrv].
  apply andb_prop in Hs as [Hs Hfc]. apply andb_prop in Hs as [Hrg Hfr].
  pose proof (swf_regs_below S Hwf) as H5. pose proof (swf_fregs_below S Hwf) as H4.
  pose proof (swf_objs S Hwf) as H0. pose proof (swf_facts S Hwf) as H.
  assert (H2 : match ss_fcsr S with FcsrFrm0 => true | FcsrVal v => sv_below (ss_next S) v end = true) by (swf_split Hwf; assumption).
  assert (H1 : match ss_resv S with None => true | Some v => sv_below (ss_next S) v end = true) by (swf_split Hwf; assumption).
  set (n := ss_next S) in *.
  assert (L1 : forall l, forallb (sv_vars_all f) l = true -> forallb (sv_below n) l = true ->
               forallb (sv_vars_all (fun v => f v && Pos.ltb v n)) l = true).
  { intros l A B. apply forallb_forall. intros e Hin. apply sv_vars_all_and.
    - exact (proj1 (forallb_forall _ _) A e Hin). - exact (proj1 (forallb_forall _ _) B e Hin). }
  rewrite (L1 _ Hrg H5), (L1 _ Hfr H4). cbn [andb].
  repeat (apply andb_true_intro; split).
  - destruct (ss_fcsr S); [reflexivity|]. apply sv_vars_all_and; assumption.
  - destruct (ss_resv S); [|reflexivity]. apply sv_vars_all_and; assumption.
  - apply forallb_forall. intros o Hin.
    pose proof (proj1 (forallb_forall _ _) Hob o Hin) as A. pose proof (proj1 (forallb_forall _ _) H0 o Hin) as B.
    unfold obj_vars_all in A |- *. unfold obj_wf in B.
    apply andb_prop in A as [A Ad]. apply andb_prop in A as [A Ac]. apply andb_prop in A as [A Ahi]. apply andb_prop in A as [Ab Alo].
    apply andb_prop in B as [B Bd]. apply andb_prop in B as [B Bc]. apply andb_prop in B as [B Bhi]. apply andb_prop in B as [Bb Blo].
    rewrite (sv_vars_all_and f n _ Ab Bb), (sv_vars_all_and f n _ Alo Blo), (sv_vars_all_and f n _ Ahi Bhi). cbn [andb].
    apply andb_true_intro. split.
    + apply forallb_forall. intros c Hc.
      pose proof (proj1 (forallb_forall _ _) Ac c Hc) as A1. pose proof (proj1 (forallb_forall _ _) Bc c Hc) as B1.
      apply andb_prop in A1 as [A2 A3]. unfold cell_wf in B1.
      apply andb_prop in B1 as [B1 Bv]. apply andb_prop in B1 as [B1 Bo].
      rewrite (sv_vars_all_and f n _ A2 Bo), (sv_vars_all_and f n _ A3 Bv). reflexivity.
    + destruct (ob_dflt o); try reflexivity. cbn in Ad, Bd |- *.
      apply andb_prop in Ad as [A1 A2]. apply andb_prop in Bd as [B1 B2].
      rewrite (sv_vars_all_and f n _ A1 B1). cbn. apply forallb_forall. intros t Ht.
      apply sv_vars_all_and; [exact (proj1 (forallb_forall _ _) A2 t Ht) | exact (proj1 (forallb_forall _ _) B2 t Ht)].
  - apply forallb_forall. intros p Hin. apply sprop_vars_all_and.
    + exact (proj1 (forallb_forall _ _) Hfa p Hin). + exact (proj1 (forallb_forall _ _) H p Hin).
Qed.

Lemma same_frame_range : ltac2:(tb__ "0|0|
S0S3S3S2bS33S70R2R1A2S35A3S2bS39S32S32A2SbR4R3A2SbR4R2A2A3F_;Fo';Fo;Frho;").
Proof using .
  intros rho o o' H. unfold same_frame in H.
  apply andb_prop in H as [H Hhi]. apply andb_prop in H as [Hb Hlo].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hlo. apply sv_eqb_sound in Hhi.
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hlo, Hhi. reflexivity.
Qed.

Lemma pos_add_nat_ge : ltac2:(tb__ "0|0|
S31S3cS85R2S77R2R1A2A2Fn;Fp;").
Proof using . intros p n. unfold pos_add_nat. lia. Qed.

Definition call_link (rho : valuation) (ms : machine_state) (R : list sobj) (s : wsub)
           (Pre C L : sstate) (rho' rhoL : valuation) : Prop := ltac2:(tb__ "0|2|
S2cS9S2VC;A1M0Vrho;Vrho';A3S2cS9S2VPre;A1M1S55S57Vrho;VR;Vms;A3Vs;A2VrhoL;A3S31S2bS33S3bS3bS3fS83R1G1A2A1S6aVs;R1A2A2S83R1G0A2A2S35A3S8cS84R2A1S84S2VL;A1A1A2S2bS45Q40A1S5VrhoL;R3A2ScVrho';S58S6eVs;G1VL;G0A4R3A2A2A3F_;F_;Fv;A2A2").

Lemma import_post_link : ltac2:(tb__ "0|4|
S1S1S56S34S3A1M0S34S42A1S0S34S47A1M1S48S46G1S48S46S42S0S2bS38G0A1S89ReRdRcA3S3aG0RbA2A3S2bS33S6cRfReRdRcRbA5S35A3S4Vsegs;RbR10S36G1S65RaS66R9R8A2A4M2A4S61S42R5RdA3S9S2R11A1S55S57RdRfRbA3R10A2R5A3S4Vsegs;R6S43R7A1G2A4S2dS0S0S2cS50R10ReR12R13R14R15S43R9A1M3R1R8A9S4Vsegs;R1S6bR13S2R14A1G3S2R15A1R12A5S36G1S65RcS66RbRaA2A4A4A2Lrho';A2F_;F_;F_;F_;F_;F_;FrhoL;FL;Fmd';Fms';Ftr';Fmd;Fms;Ftr;Frho;FPosts;FR;Fs;FPre;FC;").
Proof using .
  intros C Pre s R Posts rho tr ms md tr' ms' md' L rhoL He Hchk Hsm HinL HagL HsmL.
  unfold call_check in Hchk.
  apply andb_prop in Hchk as [Hchk Hposts]. apply andb_prop in Hchk as [Hchk Hg]. apply andb_prop in Hchk as [Hsb Hdom].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & HR & HpdR & HwfR & HinR).
  set (rhoA := rho_absorb rho R ms) in *. set (rho1 := rho_sub rhoA s) in *.
  set (nf := ss_next Pre) in *. set (nc := ss_next C) in *.
  set (cnt := fresh_count nf (lf_state L)).
  set (rho' := rho_join rho rhoL nc nf cnt (rm rho)).
  pose proof (proj1 (forallb_forall _ _) Hposts L HinL) as HP. cbn beta in HP. unfold post_ok in HP.
  apply andb_prop in HP as [HP HswfI]. apply andb_prop in HP as [HP HswfL]. apply andb_prop in HP as [HP Hpv].
  apply andb_prop in HP as [Hle Hframes]. apply Pos.leb_le in Hle.
  assert (HAG : agree_below nc rho rho').
  { split; [|split]; cbn; try reflexivity. intros i Hi. unfold rho', rho_join. cbn. rewrite join_rw_below by exact Hi. reflexivity. }
  exists rho'. split.
  { split; [exact HAG|]. split; [exact HagL|].
    intros v Hv1 Hv2. unfold rho'.
    rewrite (import_agree rho rhoA rhoL s nf nc (lf_state L) (rm rho) Hsb Hdom ltac:(lia) eq_refl eq_refl (agree_below_vals _ _ _ HagL) v Hv1 Hv2).
    reflexivity. }

  set (rhoX := rho_join rho rhoL nc nf cnt (rm rhoL)).
  set (s' := import_sub s nf (lf_state L) nc). set (nc' := import_next nf (lf_state L) nc).

  assert (STEP1 : smatch segs (rho_sub rhoX s') (lf_state L) (tr', mkCfg ms' md')).
  { pose proof (state_vars_all_and _ _ Hpv HswfL) as VARS.
    eapply (smatch_agree_vars segs _ rhoL (rho_sub rhoX s')); [ | | | exact VARS | exact HsmL].
    - intros v Hv. cbn beta in Hv. apply andb_prop in Hv as [Hv1 Hv2]. apply Pos.ltb_lt in Hv2.
      unfold rhoX, s', cnt.
      exact (import_agree rho rhoA rhoL s nf nc (lf_state L) (rm rhoL) Hsb Hdom ltac:(lia) eq_refl eq_refl (agree_below_vals _ _ _ HagL) v Hv1 ltac:(lia)).
    - destruct HagL as (_ & AL & _). cbn in AL |- *. intros l. rewrite <- AL. reflexivity.
    - cbn. reflexivity. }

  assert (HswfS : swf (subst_state s' (lf_state L) nc') = true).
  { unfold import_post in HswfI. fold nf s' nc' in HswfI.
    unfold swf in HswfI |- *. cbn [set_objs ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in HswfI.
    repeat (apply andb_prop in HswfI; destruct HswfI as [HswfI ?]).
    rewrite forallb_app in H0. apply andb_prop in H0 as [H0 _].
    repeat (apply andb_true_intro; split); assumption. }
  pose proof (smatch_subst_intro segs rhoX s' (lf_state L) nc' _ HswfS STEP1) as STEP2.

  assert (STEP3 : smatch segs rhoX (set_objs (subst_state s' (lf_state L) nc')
                                     (ss_objs (subst_state s' (lf_state L) nc') ++ R)) (tr', mkCfg ms' md')).
  { eapply (smatch_frame_out segs rho rhoX R nc); try eassumption.
    -
      split; [|split]; cbn.
      + intros i Hi. unfold rhoX, rho_join. cbn. rewrite join_rw_below by exact Hi. reflexivity.
      + intros l. reflexivity.
      + intros a. destruct HagL as (_ & _ & AM). rewrite <- AM. reflexivity.
    - cbn. apply pos_add_nat_ge.
    - intros a.
      assert (R1 : rom_ok segs ms) by (destruct Hsm as (_ & _ & _ & _ & X & _); exact X).
      assert (R2 : rom_ok segs ms') by (destruct HsmL as (_ & _ & _ & _ & X & _); exact X).
      rewrite R1, R2. reflexivity.
    - intros o' oR Hin' HinR'. cbn in Hin'. apply in_map_iff in Hin' as (oL & <- & HinL').
      rewrite obj_range_subst.
      pose proof (proj1 (forallb_forall _ _) Hframes oL HinL') as FR. apply existsb_exists in FR as (oP & HinP & SF).
      assert (E1 : obj_range (rho_sub rhoX s') oL = obj_range rhoL oL).
      { pose proof (state_vars_all_and _ _ Hpv HswfL) as VARS. unfold state_vars_all in VARS.
        apply andb_prop in VARS as [VARS _]. apply andb_prop in VARS as [_ VOB].
        apply (obj_range_agree_vars (fun v => (negb (v <? nf)%positive || wsub_bound s v || (v <? nc)%positive) && (v <? ss_next (lf_state L))%positive)).
        - intros v Hv. apply andb_prop in Hv as [Hv1 Hv2]. apply Pos.ltb_lt in Hv2.
          unfold rhoX, s', cnt.
          exact (import_agree rho rhoA rhoL s nf nc (lf_state L) (rm rhoL) Hsb Hdom ltac:(lia) eq_refl eq_refl (agree_below_vals _ _ _ HagL) v Hv1 ltac:(lia)).
        - destruct HagL as (_ & AL & _). cbn in AL |- *. intros l. rewrite <- AL. reflexivity.
        - exact (proj1 (forallb_forall _ _) VOB oL HinL'). }
      rewrite E1, (same_frame_range rhoL oL oP SF).
      assert (E2 : obj_range rhoL oP = obj_range rho1 oP).
      { apply (obj_range_agree nf). exact HagL.
        pose proof (smatch_swf segs _ _ _ HsmPre) as W. exact (proj1 (forallb_forall _ _) (swf_objs _ W) oP HinP). }
      rewrite E2. unfold rho1, rhoA. eapply entails_fr_ranges; eauto. }

  unfold import_post. fold nf s' nc'.
  assert (STEP4 : smatch segs (mkVal (rw rhoX) (rl rhoX) (rm rho))
                    (set_objs (subst_state s' (lf_state L) nc') (ss_objs (subst_state s' (lf_state L) nc') ++ R))
                    (tr', mkCfg ms' md')).
  { apply smatch_set_rm; [|exact STEP3]. intros a Ha. cbn [set_objs ss_objs] in Ha.
    unfold rhoX, rho_join. cbn [rm]. destruct HagL as (_ & _ & AM). rewrite <- (AM a). unfold rho1, rho_sub. cbn [rm].
    unfold rhoA, rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho R a) as [Hin|Hnin]; [|reflexivity].
    exfalso. destruct Hin as (oR & HinR' & Hrg).
    unfold outside_all in Ha. apply Forall_app in Ha as [_ Ha].
    pose proof (proj1 (Forall_forall _ _) Ha oR HinR') as X. cbn beta in X. apply X.
    rewrite (obj_range_agree_vars (fun v => Pos.ltb v nc) rho); [exact Hrg| | |].
    - intros v Hv. apply Pos.ltb_lt in Hv. unfold rhoX, rho_join. cbn [rw]. rewrite join_rw_below by exact Hv. reflexivity.
    - intros l. reflexivity.
    - apply obj_wf_vars_all. exact (proj1 (forallb_forall _ _) HwfR oR HinR'). }
  exact STEP4.
Qed.

Theorem call_sound : ltac2:(tb__ "0|3|
S7cOF_;S34S47A1S46OF_;F_;M0G0S1S1S56S34S3A1M1S34S42A1S80S0S2bS38G1A1S89R7R6R5A3S3aG1R4A2A3S2bS33S6cR8R7R6R5R4A5S35A3S0S7eVsegs;RdS5dVsegs;RcR9R1A4S5fVsegs;RbS2R9A1R1R6A5A4Frho1;S42S0S61S42R2R8A3S9S2RdA1M2R7R2A3S7eVsegs;R11S5dVsegs;RfS6bRcG2S43R4A1S2ReA1RbA5R3A4R9A4F_;F_;Frho';FL;S7eVsegs;ReS5dVsegs;RdRbR5A4R6A4F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FK';FK;Fok;").
Proof using .
  intros ok K K' C Pre s R Posts Q rho He Hchk Hsum Hcont.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R ms) s) n); [|split; [exact HsmPre|exact Hk]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  destruct (import_post_link C Pre s R Posts rho tr ms md tr' ms' md' L rhoL He Hchk Hsm HinL HagL HsmL)
    as (rho' & (HAG & _) & HSP).
  exact (Hcont L rho' HinL HAG n HgQ _ (conj HSP Hk')).
Qed.

Theorem call_soundN : ltac2:(tb__ "0|3|
S7cOF_;S34S47A1S46OF_;F_;M0G0S1S1S56S34S3A1M1S34S42A1S80S0S3cS2bS38G1A1S89R8R7R6A3S3aG1R5A2A3S2bS33S6cR9R8R7R6R5A5S35A3S0S7fVsegs;ReR4S5dVsegs;RdRaR1A4S5fVsegs;RcS2RaA1R1R7A5A5Frho1;S42S0S61S42R2R9A3S9S2ReA1M2R8R2A3S7fVsegs;R12R8S5dVsegs;R10S6bRdG2S43R4A1S2RfA1RcA5R3A4RaA5F_;F_;Frho';FL;S7fVsegs;RfR5S5dVsegs;ReRcR6A4R7A5F_;F_;F_;F_;Fm;Frho;FQ;FPosts;FR;Fs;FPre;FC;FK';FK;Fok;").
Proof using .
  intros ok K K' C Pre s R Posts Q rho m He Hchk Hsum Hcont.
  intros HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R ms) s)); [|split; [exact HsmPre|exact Hk]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  destruct (import_post_link C Pre s R Posts rho tr ms md tr' ms' md' L rhoL He Hchk Hsm HinL HagL HsmL)
    as (rho' & (HAG & _) & HSP).
  exact (Hcont L rho' HinL HAG HgQ _ (conj HSP Hk')).
Qed.

Theorem call_complete : ltac2:(tb__ "0|3|
S34S47A1S46OF_;F_;M0G0S1S1S56S34S3A1M1S34S42A1S7cOF_;S0S2bS38G1A1S89R7R6R5A3S3aG1R4A2A3S2bS33S6cR8R7R6R5R4A5S35A3S0S7dVsegs;S5dVsegs;RcR9R1A4S5fVsegs;RbS2R9A1R1R6A5A3Frho1;S42S0S61S42R2R8A3S9S2RdA1M2R7R2A3S7dVsegs;S5dVsegs;RfS6bRcG2S43R4A1S2ReA1RbA5R3A4R9A3F_;F_;Frho';FL;S7dVsegs;S5dVsegs;RdRbR5A4R6A3F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FK';FK;").
Proof using .
  intros K K' C Pre s R Posts Q rho He Hchk Hsum Hcont.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R ms) s) _ (conj HsmPre Hk)) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  destruct (import_post_link C Pre s R Posts rho tr ms md tr' ms' md' L rhoL He Hchk Hsm HinL HagL HsmL)
    as (rho' & (HAG & _) & HSP).
  destruct (Hcont L rho' HinL HAG _ (conj HSP Hk')) as (w'' & Hsteps' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Theorem call_soundJ : ltac2:(tb__ "0|3|
S7cOF_;S5bS5bS5bS5bS1S1S56S34S3A1M0S34S42A1S80S0S2bS38G0A1S89R7R6R5A3S3aG0R4A2A3S2bS33S6cR8R7R6R5R4A5S35A3S0S7eVsegs;RfS5cVsegs;RdR9R1A4S5eVsegs;RcS2R9A1R1R6A5A4Frho1;S34S47A1M1S48S46S4Vsegs;R7RdS36G1S65R3S66R2R1A2A4A4R12R8R4R2A3R12S55S57R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S42S0S0G1S48S46G1S46S61S42R8RfA3S4Vsegs;ReR14S36G1S65R6S66R5R4A2A4A4R19RfR7R5A3S50R10R7R13R14R15R16S43RbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S42S0S61S42R2RaA3S9S2RfA1M2R9R2A3S7eVsegs;R15S5cVsegs;R11S6bReG2S43R4A1S2R10A1RdA5R3A4RbA4F_;F_;Frho';FL;S7eVsegs;R12S5cVsegs;R11RdR7A4R8A4F_;F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;Fok;").
Proof using .
  intros ok J Jp Jp' Jc' C Pre s R Posts Q rho He Hchk Hsum Hin Hout Hcont.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R ms) s) n); [|split; [exact HsmPre|exact (Hin tr ms md Hsm Hk)]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  destruct (import_post_link C Pre s R Posts rho tr ms md tr' ms' md' L rhoL He Hchk Hsm HinL HagL HsmL)
    as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  exact (Hcont L rho' HinL HAG n HgQ _ (conj HSP (Hout L rho' rhoL tr ms md tr' md' HinL Hsm Hk HLK Hk'))).
Qed.

Theorem call_soundNJ : ltac2:(tb__ "0|3|
S7cOF_;S5bS5bS5bS5bS1S1S56S34S3A1M0S34S42A1S80S0S3cS2bS38G0A1S89R8R7R6A3S3aG0R5A2A3S2bS33S6cR9R8R7R6R5A5S35A3S0S7fVsegs;R10R4S5cVsegs;ReRaR1A4S5eVsegs;RdS2RaA1R1R7A5A5Frho1;S34S47A1M1S48S46S4Vsegs;R8ReS36G1S65R3S66R2R1A2A4A4R13R9R4R2A3R13S55S57RaRdR4A3ReA2R5R3A3F_;F_;Fmd;Fms;Ftr;S42S0S0G1S48S46G1S46S61S42R8R10A3S4Vsegs;RfR15S36G1S65R6S66R5R4A2A4A4R1aR10R7R5A3S50R11R7R14R15R16R17S43RbA1RaR9A9R1aRaR6R5A3R1aRcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S42S0S61S42R2RbA3S9S2R10A1M2RaR2A3S7fVsegs;R16RaS5cVsegs;R12S6bRfG2S43R4A1S2R11A1ReA5R3A4RcA5F_;F_;Frho';FL;S7fVsegs;R13R7S5cVsegs;R12ReR8A4R9A5F_;F_;F_;F_;F_;F_;Fm;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;Fok;").
Proof using .
  intros ok J Jp Jp' Jc' C Pre s R Posts Q rho m He Hchk Hsum Hin Hout Hcont.
  intros HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R ms) s)); [|split; [exact HsmPre|exact (Hin tr ms md Hsm Hk)]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  destruct (import_post_link C Pre s R Posts rho tr ms md tr' ms' md' L rhoL He Hchk Hsm HinL HagL HsmL)
    as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  exact (Hcont L rho' HinL HAG HgQ _ (conj HSP (Hout L rho' rhoL tr ms md tr' md' HinL Hsm Hk HLK Hk'))).
Qed.

Theorem call_completeJ : ltac2:(tb__ "0|3|
S5bS5bS5bS5bS1S1S56S34S3A1M0S34S42A1S7cOF_;S0S2bS38G0A1S89R7R6R5A3S3aG0R4A2A3S2bS33S6cR8R7R6R5R4A5S35A3S0S7dVsegs;S5cVsegs;RdR9R1A4S5eVsegs;RcS2R9A1R1R6A5A3Frho1;S34S47A1M1S48S46S4Vsegs;R7RdS36G1S65R3S66R2R1A2A4A4R12R8R4R2A3R12S55S57R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S42S0S0G1S48S46G1S46S61S42R8RfA3S4Vsegs;ReR14S36G1S65R6S66R5R4A2A4A4R19RfR7R5A3S50R10R7R13R14R15R16S43RbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S42S0S61S42R2RaA3S9S2RfA1M2R9R2A3S7dVsegs;S5cVsegs;R11S6bReG2S43R4A1S2R10A1RdA5R3A4RbA3F_;F_;Frho';FL;S7dVsegs;S5cVsegs;R11RdR7A4R8A3F_;F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;").
Proof using .
  intros J Jp Jp' Jc' C Pre s R Posts Q rho He Hchk Hsum Hin Hout Hcont.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R ms) s) _ (conj HsmPre (Hin tr ms md Hsm Hk))) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  destruct (import_post_link C Pre s R Posts rho tr ms md tr' ms' md' L rhoL He Hchk Hsm HinL HagL HsmL)
    as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  destruct (Hcont L rho' HinL HAG _ (conj HSP (Hout L rho' rhoL tr ms md tr' md' HinL Hsm Hk HLK Hk'))) as (w'' & Hsteps' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Definition jpost : Type := ltac2:(tb__ "0|0|
S0S0S34S47A1S46OF_;F_;F_;F_;").

Definition LQP (n : positive) (rho0 : valuation) (Posts : list (sstate * jpost)) : assn := ltac2:(tb__ "0|0|
S7cS2dS1S1S2dS4bS4bS2dS0S0S2cS61S39S1S4bA2S36S1S4bR3R2A4VPosts;A3S2cS68Vn;Vrho0;R1A3S2cS4Vsegs;R1R3R4A4R2Vrho0;R1S82R4A1S67S81R4A1A1A4A2A2A2Lrho';A2LJL;A2LL;A2Lw;").

Lemma LQJ_LQP : ltac2:(tb__ "0|2|
S5bS31S0S34S42A1S7cS5eVsegs;R5R4R3R2R1A6S4cR5R4S8aS42S39S1S0S0S34S47A1M0S46OFm;Ft;Fr;F_;M1A2S42S36S1G1S43R1A1S0S0G0S46RbR3R2R1A3Lm;Lt;Lr;L_;A4LL;R3A4R2A4F_;Fw;Fleaves;Frho0;Fn;FJ;").
Proof using .
  intros J n rho0 leaves w (L & rho' & Hin & Hag & Hsm & Hk).
  exists (lf_state L), (fun _ r t m => J r t m), rho'. split; [apply in_map_iff; exists L; auto|].
  split; [apply agree_below_vals; exact Hag|]. split; [exact Hsm | exact Hk].
Qed.

Lemma LQP_intro : ltac2:(tb__ "0|1|
S31S0S34S39S1S4bA2M0A1S1S4bS0S7cS5bS61G0S36S1S4bR5R4A4R6A3S5cVsegs;R2R6R4R3A5S68RaR9R5A3R4R6S82R5A1S67S81R5A1A1A3R8RbR7S82R6A1S67S81R6A1A1A4F_;S4cRcRbRaR6A4F_;F_;F_;F_;FJ;Fw;Frho;FJL;FL;FPosts;Frho0;Fn;").
Proof using .
  intros n rho0 Posts L JL rho w J Hin [Hsm Hk] Hag HJ. exists L, JL, rho. auto.
Qed.

Definition post_okP (Pre : sstate) (s : wsub) (nc : positive) (R : list sobj) (L : sstate) : bool := ltac2:(tb__ "0|1|
S37S37S37S87S2VPre;A1M0S2VL;A1A2S79Vs;G0Vnc;VL;A4A2SeVL;A1A2SeS6bVs;G0VL;Vnc;VR;A5A1A2").

Definition call_checkP (C Pre : sstate) (s : wsub) (R : list sobj) (Posts : list sstate) : bool := ltac2:(tb__ "0|1|
S37S37S37S73Vs;S2VC;A1M0A2S74Vs;S2VPre;A1A2A2S87PaG0A2A2S62S1S53VPre;Vs;G0VR;A4VPosts;A3A2").

Definition new_objs (Pre L : sstate) : list sobj := ltac2:(tb__ "0|0|
S64S3S3S3fS63S3S70R1A1SaVPre;A1A3A1Lo;SaVL;A1A3").

Definition call_linkP (rho : valuation) (ms : machine_state) (R : list sobj) (s : wsub)
           (Pre C L : sstate) (rho' rhoL : valuation) : Prop := ltac2:(tb__ "0|3|
S2cS68S2VC;A1M0Vrho;Vrho';A3S2cS45Q40A1M1S2bS38S45Q8A1A1S8Vrho';R1A2S8VrhoL;R1A2A3Fa;S2cS68S2VPre;A1M2S55S57Vrho;VR;Vms;A3Vs;A2VrhoL;A3S31S2bS33S3bS3bS3fS83R1G2A2A1S6aVs;R1A2A2S83R1G0A2A2S35A3S8cS84R2A1S84S2VL;A1A1A2S2bG1S5VrhoL;R3A2ScVrho';S58S6eVs;G2VL;G0A4R3A2A2A3F_;F_;Fv;A2A2A2").

Definition import_okP (rho : valuation) (ms : machine_state) (R : list sobj) (s : wsub)
           (Pre L : sstate) (rhoL : valuation) : Prop := ltac2:(tb__ "0|0|
S2cS45Q40A1S59Vrho;VR;R1A3S2bS38S45Q8A1A1S8VrhoL;R2A2S8S55S57Vrho;VR;Vms;A3Vs;A2R2A2A3F_;Fa;S3S3S61S3R2S52VPre;VL;A2A3S61S3R2VR;A3S1cSbVrhoL;R4A2SbVrho;R3A2A2F_;F_;FoR;Fo';A2").

Lemma rm_absorb_in : ltac2:(tb__ "0|0|
S0S34S3A1S48S56S45Q40A1S59R5R4R1A3S2bS38S45Q8A1A1S8S55S57R6R5R4A3R3A2R2A2S49R4R2A2A3F_;Fa;Fs;Fms;FR;Frho;").
Proof using .
  intros rho R ms s a H. unfold rho_sub, rho_absorb. cbn [rm].
  destruct (in_ranges_dec rho R a) as [|Hn]; [reflexivity | exfalso; exact (Hn H)].
Qed.

Lemma rm_absorb_out : ltac2:(tb__ "0|0|
S0S34S3A1S48S56S45Q40A1S30S59R5R4R1A3A1S2bS38S45Q8A1A1S8S55S57R6R5R4A3R3A2R2A2S8R6R2A2A3F_;Fa;Fs;Fms;FR;Frho;").
Proof using .
  intros rho R ms s a H. unfold rho_sub, rho_absorb. cbn [rm].
  destruct (in_ranges_dec rho R a) as [Hi|]; [exfalso; exact (H Hi) | reflexivity].
Qed.

Lemma smatch_frame_outP : ltac2:(tb__ "0|3|
S0S0S34S3A1S31S1S48S34S47A1M0S48S46S8bS3S16Vsegs;R9R4A3R7A3S24RaR8A2S2bS33S62S3S17R8A1R9A3S35A3S68R9RcRbA3S45Q40A1M1S59ReRcR1A3S2bS38S45Q8A1A1M2S8ReR2A2S49RaR2A2A3F_;Fa;S85RbS2RaA1A2G1S2bG2S4aR9R1A2S4aRbR1A2A3Fa;S4Vsegs;RfRcS36G0S65RaS66R9R8A2A4A4S3S3S61S3R2SaRfA1A3S61S3R2R12A3S1cSbR14R4A2SbR15R3A2A2F_;F_;FoR;Fo';S4Vsegs;R11S44ReS3dS3SaReA1R10A3A2S36G0S65RcS66RbRaA2A4A4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';Fms;FS';Fn;FR;FrhoX;Frho;").
Proof using .
  intros rho rhoX R n S' ms tr' ms' md' HR Hpd Hwf Hag Hrm Hle Hrom' Hsm' Hdisj.
  pose proof (smatch_swf segs _ _ _ Hsm') as Hwf'.
  destruct Hsm' as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct Hmem as (Hall & Hpd' & Hfr).
  assert (RNG : forall oR, In oR R -> obj_range rhoX oR = obj_range rho oR).
  { intros oR Hin. apply (obj_range_agree_vals n); [exact Hag|]. exact (proj1 (forallb_forall _ _) Hwf oR Hin). }
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { pose proof Hwf' as W. unfold swf in W |- *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
    repeat (apply andb_prop in W; destruct W as [W ?]).
    repeat (apply andb_true_intro; split); try assumption.
    apply forallb_forall. intros o Hin. apply in_app_or in Hin as [Hin|Hin].
    - revert o Hin. apply forallb_forall. assumption.
    - apply (obj_wf_mono n); [exact Hle|]. exact (proj1 (forallb_forall _ _) Hwf o Hin). }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  split; [|split].
  - apply Forall_app. split; [exact Hall|].
    apply Forall_forall. intros oR Hin.
    pose proof (proj1 (Forall_forall _ _) HR oR Hin) as HoR.
    pose proof (proj1 (forallb_forall _ _) Hwf oR Hin) as HwfR.
    apply (obj_holds_agree_vars segs (fun v => Pos.ltb v n) rho rhoX ms oR) in HoR;
      [| intros v Hv; apply (proj1 Hag); apply Pos.ltb_lt; exact Hv | exact (proj2 Hag) | apply obj_wf_vars_all; exact HwfR].
    eapply (obj_holds_mem_ext segs rhoX ms ms'); [exact Hrom' | | exact HoR].
    intros off Hoff.
    assert (HinR : in_ranges rho R (Z_to_bv 64 (bv_unsigned (eval rhoX (ob_base oR)) + off))).
    { exists oR. split; [exact Hin|]. rewrite <- (RNG oR Hin). unfold obj_range. cbn [fst snd].
      pose proof (proj1 HoR) as HB. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia). lia. }
    rewrite Hfr.
    + apply Hrm. exact HinR.
    + apply Forall_forall. intros o' Hin'. lazy beta zeta. intros Hr.
      pose proof (Hdisj o' oR Hin' Hin) as D. rewrite <- (RNG oR Hin) in D.
      unfold ranges_disjoint, obj_range in D. cbn [fst snd] in D.
      unfold obj_range in Hr. cbn [fst snd] in Hr.
      pose proof (proj1 HoR) as HB. rewrite Z_to_bv_unsigned, bv_wrap_small in Hr by (rewrite two64; lia). lia.
  - apply pairwise_disjoint_app; [exact Hpd' | |].
    + apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd.
      erewrite map_ext_in; [exact Hpd|]. intros o Ho. apply RNG. exact Ho.
    + intros o1 o2 Hin1 Hin2. rewrite (RNG o2 Hin2). apply Hdisj; assumption.
  - intros a Ha. apply Hfr. apply outside_all_app_iff in Ha as [Ha _]. exact Ha.
Qed.

Lemma new_objs_spec : ltac2:(tb__ "0|0|
S1S1S3S61S3R1SaR2A1A3S2fS2bS33S63S3S70R2A1SaR4A1A3S35A3S61S3R2S52R4R3A2A3A2F_;Fo;FL;FPre;").
Proof using .
  intros Pre L o Hin. destruct (existsb (same_frame o) (ss_objs Pre)) eqn:E; [left; reflexivity|].
  right. unfold new_objs. apply List.filter_In. split; [exact Hin|]. rewrite E. reflexivity.
Qed.

Lemma import_post_linkP : ltac2:(tb__ "0|3|
S1S1S56S34S3A1M0S34S1A1S0S34S47A1M1S48S46G1S48S46S1S0S2bS38G0A1S89ReRdRcA3S3aG0RbA2A3S2bS33S4eRfReRdRcRbA5S35A3S4Vsegs;RbR10S36G1S65RaS66R9R8A2A4M2A4S61S1R5RdA3S68S2R11A1S55S57RdRfRbA3R10A2R5A3S4Vsegs;R6R7G2A4S51RfRdR11R12R13R8R7A7S2dS0S0S2cS4dR11RfR13R14R15R16RaR1R9A9S4Vsegs;R1S6bR14S2R15A1RaS2R16A1R13A5S36G1S65RdS66RcRbA2A4A4A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;FrhoL;FL;Fmd';Fms';Ftr';Fmd;Fms;Ftr;Frho;FPosts;FR;Fs;FPre;FC;").
Proof using .
  intros C Pre s R Posts rho tr ms md tr' ms' md' L rhoL He Hchk Hsm HinL HagL HsmL [Hkept Hnew].
  unfold call_checkP in Hchk.
  apply andb_prop in Hchk as [Hchk Hposts]. apply andb_prop in Hchk as [Hchk Hg]. apply andb_prop in Hchk as [Hsb Hdom].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & HR & HpdR & HwfR & HinR).
  set (rhoA := rho_absorb rho R ms) in *. set (rho1 := rho_sub rhoA s) in *.
  set (nf := ss_next Pre) in *. set (nc := ss_next C) in *.
  set (cnt := fresh_count nf L).
  set (rhoX := rho_join rho rhoL nc nf cnt (rm rhoL)).
  pose proof (proj1 (forallb_forall _ _) Hposts L HinL) as HP. cbn beta in HP. unfold post_okP in HP.
  apply andb_prop in HP as [HP HswfI]. apply andb_prop in HP as [HP HswfL]. apply andb_prop in HP as [Hle Hpv].
  apply Pos.leb_le in Hle.
  assert (HAGv : agree_vals nc rho rhoX).
  { split; cbn; [|intros l; reflexivity]. intros i Hi. unfold rhoX, rho_join. cbn. rewrite join_rw_below by exact Hi. reflexivity. }
  exists rhoX. split.
  { split; [exact HAGv|]. split; [intros a; reflexivity|]. split; [exact HagL|].
    intros v Hv1 Hv2. unfold rhoX, cnt.
    exact (import_agree rho rhoA rhoL s nf nc L (rm rhoL) Hsb Hdom ltac:(lia) eq_refl eq_refl HagL v Hv1 Hv2). }
  set (s' := import_sub s nf L nc). set (nc' := import_next nf L nc).

  assert (STEP1 : smatch segs (rho_sub rhoX s') L (tr', mkCfg ms' md')).
  { pose proof (state_vars_all_and _ _ Hpv HswfL) as VARS.
    eapply (smatch_agree_vars segs _ rhoL (rho_sub rhoX s')); [ | | | exact VARS | exact HsmL].
    - intros v Hv. cbn beta in Hv. apply andb_prop in Hv as [Hv1 Hv2]. apply Pos.ltb_lt in Hv2.
      unfold rhoX, s', cnt.
      exact (import_agree rho rhoA rhoL s nf nc L (rm rhoL) Hsb Hdom ltac:(lia) eq_refl eq_refl HagL v Hv1 ltac:(lia)).
    - destruct HagL as [_ AL]. cbn in AL |- *. intros l. rewrite <- AL. reflexivity.
    - cbn. reflexivity. }

  assert (HswfS : swf (subst_state s' L nc') = true).
  { unfold import_post in HswfI. fold nf s' nc' in HswfI.
    unfold swf in HswfI |- *. cbn [set_objs ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in HswfI.
    repeat (apply andb_prop in HswfI; destruct HswfI as [HswfI ?]).
    rewrite forallb_app in H0. apply andb_prop in H0 as [H0 _].
    repeat (apply andb_true_intro; split); assumption. }
  pose proof (smatch_subst_intro segs rhoX s' L nc' _ HswfS STEP1) as STEP2.

  assert (E1 : forall oL, In oL (ss_objs L) -> obj_range (rho_sub rhoX s') oL = obj_range rhoL oL).
  { intros oL HinL'.
    pose proof (state_vars_all_and _ _ Hpv HswfL) as VARS. unfold state_vars_all in VARS.
    apply andb_prop in VARS as [VARS _]. apply andb_prop in VARS as [_ VOB].
    apply (obj_range_agree_vars (fun v => (negb (v <? nf)%positive || wsub_bound s v || (v <? nc)%positive) && (v <? ss_next L)%positive)).
    - intros v Hv. apply andb_prop in Hv as [Hv1 Hv2]. apply Pos.ltb_lt in Hv2.
      unfold rhoX, s', cnt.
      exact (import_agree rho rhoA rhoL s nf nc L (rm rhoL) Hsb Hdom ltac:(lia) eq_refl eq_refl HagL v Hv1 ltac:(lia)).
    - destruct HagL as [_ AL]. cbn in AL |- *. intros l. rewrite <- AL. reflexivity.
    - exact (proj1 (forallb_forall _ _) VOB oL HinL'). }
  assert (STEP3 : smatch segs rhoX (set_objs (subst_state s' L nc') (ss_objs (subst_state s' L nc') ++ R)) (tr', mkCfg ms' md')).
  { apply (smatch_frame_outP rho rhoX R nc _ ms tr' ms' md' HR HpdR HwfR); [ | | | | exact STEP2 | ].
    - split; cbn; [|intros l; reflexivity].
      intros i Hi. unfold rhoX, rho_join. cbn. rewrite join_rw_below by exact Hi. reflexivity.
    - intros a Ha. unfold rhoX, rho_join. cbn [rm]. rewrite (Hkept a Ha). apply rm_absorb_in. exact Ha.
    - cbn. apply pos_add_nat_ge.
    - intros a.
      assert (R1 : rom_ok segs ms) by (destruct Hsm as (_ & _ & _ & _ & X & _); exact X).
      assert (R2 : rom_ok segs ms') by (destruct HsmL as (_ & _ & _ & _ & X & _); exact X).
      rewrite R1, R2. reflexivity.
    - intros o' oR Hin' HinR'. cbn in Hin'. apply in_map_iff in Hin' as (oL & <- & HinL').
      rewrite obj_range_subst, (E1 oL HinL').
      destruct (new_objs_spec Pre L oL HinL') as [FR|NEW].
      + apply existsb_exists in FR as (oP & HinP & SF).
        rewrite (same_frame_range rhoL oL oP SF).
        assert (E2 : obj_range rhoL oP = obj_range rho1 oP).
        { apply (obj_range_agree_vals nf); [exact HagL|].
          pose proof (smatch_swf segs _ _ _ HsmPre) as W. exact (proj1 (forallb_forall _ _) (swf_objs _ W) oP HinP). }
        rewrite E2. unfold rho1, rhoA. eapply entails_fr_ranges; eauto.
      + exact (Hnew oL oR NEW HinR'). }
  unfold import_post. fold nf s' nc'. exact STEP3.
Qed.

Definition J_ofP (JL : jpost) (rho1 rhoL : valuation) : jpred := ltac2:(tb__ "0|0|
S0S34S47A1S46VJL;Vrho1;VrhoL;R2R1A4Lm;Lt;L_;").

Lemma stableJ_ofP : ltac2:(tb__ "0|0|
S31S4bS0S0S60R4S4fR3R2R1A3A2FrhoL;Frho1;FJL;Fn;").
Proof using . intros n JL rho1 rhoL r r' t m _ H. exact H. Qed.

Theorem call_soundP : ltac2:(tb__ "0|3|
S7cOF_;S5bS5bS1S1S56S34S3A1M0S34S39S1S4bA2M1A1S80S0S2bS38G0A1S89R7R6R5A3S3aG0R4A2A3S2bS33S4eR8R7R6R5S8aG1S1S3eS1S4bA2R4A4A5S35A3S0S7eVsegs;RdS5cVsegs;RbR9R1A4S4cS2R9A1R1R6A3A4Frho1;S34S47A1M2S48S46S4Vsegs;R7RdS36G2S65R3S66R2R1A2A4A4R10R8R4R2A3R10S55S57R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S1S4bG2S48S46S0G2S48S46S61G1S36S1S4bR9R8A4R10A3S4Vsegs;RfR15S36G2S65R8S66R7R6A2A4A4R18R10R9R7A3S68S2R16A1S55S57R11R14R9A3R15A2R7A3S4Vsegs;R8RdS36G2S65R7S66R6R5A2A4A4RdS55S57R13R16RbA3R17A2R9R8R6A4S2cS51R14RcR17R18R19RfRaA7S0S4dR15RdR18R19R1aR1bR10R1RbA9S7eVsegs;R1fS5cVsegs;S4fR10S55S57R16R19ReA3R1aA2RcA3S6bR1aS2R1bA1R11S2R1cA1R19A5R2A4R17A4F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;S7eVsegs;RfS5cVsegs;ReRcR6A4R7A4F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJp;FJ;Fok;").
Proof using .
  intros ok J Jp C Pre s R Posts Q rho He Hchk Hsum Hin Hout.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R ms) s) n); [|split; [exact HsmPre|exact (Hin tr ms md Hsm Hk)]].
  intros w' (L & JL & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (Hout L JL tr ms md rhoL tr' ms' md' HinL Hsm Hk HagL HsmL Hk') as [Hok Hcont].
  destruct (import_post_linkP C Pre s R (map fst Posts) rho tr ms md tr' ms' md' L rhoL He Hchk Hsm
              ltac:(apply in_map_iff; exists (L, JL); auto) HagL HsmL Hok) as (rho' & HLK & HSP).
  apply (Hcont rho' HLK n HgQ). split; [exact HSP|]. exact Hk'.
Qed.

Theorem call_soundNP : ltac2:(tb__ "0|3|
S7cOF_;S5bS5bS1S1S56S34S3A1M0S34S39S1S4bA2M1A1S80S0S3cS2bS38G0A1S89R8R7R6A3S3aG0R5A2A3S2bS33S4eR9R8R7R6S8aG1S1S3eS1S4bA2R5A4A5S35A3S0S7fVsegs;ReR4S5cVsegs;RcRaR1A4S4cS2RaA1R1R7A3A5Frho1;S34S47A1M2S48S46S4Vsegs;R8ReS36G2S65R3S66R2R1A2A4A4R11R9R4R2A3R11S55S57RaRdR4A3ReA2R5R3A3F_;F_;Fmd;Fms;Ftr;S1S4bG2S48S46S0G2S48S46S61G1S36S1S4bR9R8A4R11A3S4Vsegs;R10R16S36G2S65R8S66R7R6A2A4A4R19R11R9R7A3S68S2R17A1S55S57R12R15R9A3R16A2R7A3S4Vsegs;R8RdS36G2S65R7S66R6R5A2A4A4RdS55S57R14R17RbA3R18A2R9R8R6A4S2cS51R15RcR18R19R1aRfRaA7S0S4dR16RdR19R1aR1bR1cR10R1RbA9S7fVsegs;R20R16S5cVsegs;S4fR10S55S57R17R1aReA3R1bA2RcA3S6bR1bS2R1cA1R11S2R1dA1R1aA5R2A4R18A5F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;S7fVsegs;R10R6S5cVsegs;RfRdR7A4R8A5F_;F_;F_;F_;F_;Fm;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJp;FJ;Fok;").
Proof using .
  intros ok J Jp C Pre s R Posts Q rho m He Hchk Hsum Hin Hout.
  intros HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R ms) s)); [|split; [exact HsmPre|exact (Hin tr ms md Hsm Hk)]].
  intros w' (L & JL & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (Hout L JL tr ms md rhoL tr' ms' md' HinL Hsm Hk HagL HsmL Hk') as [Hok Hcont].
  destruct (import_post_linkP C Pre s R (map fst Posts) rho tr ms md tr' ms' md' L rhoL He Hchk Hsm
              ltac:(apply in_map_iff; exists (L, JL); auto) HagL HsmL Hok) as (rho' & HLK & HSP).
  apply (Hcont rho' HLK HgQ). split; [exact HSP|]. exact Hk'.
Qed.

Theorem call_completeP : ltac2:(tb__ "0|3|
S5bS5bS1S1S56S34S3A1M0S34S39S1S4bA2M1A1S7cOF_;S0S2bS38G0A1S89R7R6R5A3S3aG0R4A2A3S2bS33S4eR8R7R6R5S8aG1S1S3eS1S4bA2R4A4A5S35A3S0S7dVsegs;S5cVsegs;RbR9R1A4S4cS2R9A1R1R6A3A3Frho1;S34S47A1M2S48S46S4Vsegs;R7RdS36G2S65R3S66R2R1A2A4A4R10R8R4R2A3R10S55S57R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S1S4bG2S48S46S0G2S48S46S61G1S36S1S4bR9R8A4R10A3S4Vsegs;RfR15S36G2S65R8S66R7R6A2A4A4R18R10R9R7A3S68S2R16A1S55S57R11R14R9A3R15A2R7A3S4Vsegs;R8RdS36G2S65R7S66R6R5A2A4A4RdS55S57R13R16RbA3R17A2R9R8R6A4S2cS51R14RcR17R18R19RfRaA7S0S4dR15RdR18R19R1aR1bR10R1RbA9S7dVsegs;S5cVsegs;S4fR10S55S57R16R19ReA3R1aA2RcA3S6bR1aS2R1bA1R11S2R1cA1R19A5R2A4R17A3F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;S7dVsegs;S5cVsegs;ReRcR6A4R7A3F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Proof using .
  intros J Jp C Pre s R Posts Q rho He Hchk Hsum Hin Hout.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_fr_sound segs C Pre s R rho tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R ms) s) _ (conj HsmPre (Hin tr ms md Hsm Hk))) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & JL & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (Hout L JL tr ms md rhoL tr' ms' md' HinL Hsm Hk HagL HsmL Hk') as [Hok Hcont].
  destruct (import_post_linkP C Pre s R (map fst Posts) rho tr ms md tr' ms' md' L rhoL He Hchk Hsm
              ltac:(apply in_map_iff; exists (L, JL); auto) HagL HsmL Hok) as (rho' & HLK & HSP).
  destruct (Hcont rho' HLK _ (conj HSP Hk')) as (w'' & Hsteps' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Lemma call_linkP_rw : ltac2:(tb__ "0|0|
S0S48S34S3A1S56S1S1S1S0S0S31S4dRaR9R8R7R6R5R4R3R2A9S86R2S2R6A1A2S2bS45Q40A1S5R5R3A2S5RcR3A2A3F_;F_;Fi;FrhoL;Frho';FL;FC;FPre;Fs;FR;Fms;Frho;").
Proof using . intros rho ms R s Pre C L rho' rhoL i (A & _) Hi. symmetry. apply (proj1 A). exact Hi. Qed.

Lemma call_linkP_rl : ltac2:(tb__ "0|0|
S0S48S34S3A1S56S1S1S1S0S0S31S4dRaR9R8R7R6R5R4R3R2A9S2bS34S45Q8A1A1S7R4R2A2S7RbR2A2A3F_;Fl;FrhoL;Frho';FL;FC;FPre;Fs;FR;Fms;Frho;").
Proof using . intros rho ms R s Pre C L rho' rhoL l (A & _). symmetry. apply (proj2 A). Qed.

Lemma call_linkP_rm : ltac2:(tb__ "0|0|
S0S48S34S3A1S56S1S1S1S0S0S45Q40A1S4dRaR9R8R7R6R5R4R3R2A9S2bS38S45Q8A1A1S8R4R2A2S8R3R2A2A3F_;Fa;FrhoL;Frho';FL;FC;FPre;Fs;FR;Fms;Frho;").
Proof using . intros rho ms R s Pre C L rho' rhoL a (_ & B & _). apply B. Qed.

Lemma call_linkP_pre_var : ltac2:(tb__ "0|0|
S0S48S34S3A1S56S1S1S1S0S0S31S4dRaR9R8R7R6R5R4R3R2A9S86R2S2R7A1A2S2bS45Q40A1S5R4R3A2ScRcS58R9R3A2A2A3F_;F_;Fv;FrhoL;Frho';FL;FC;FPre;Fs;FR;Fms;Frho;").
Proof using .
  intros rho ms R s Pre C L rho' rhoL v (_ & _ & [A _] & _) Hv.
  rewrite <- (A v Hv). cbn [rho_sub rw]. apply eval_absorb.
Qed.

Lemma exit_postP : ltac2:(tb__ "0|1|
S7cOF_;S5bS31S0S34S39S1S4bA2M0A1S1S4bS80S61G0S36S1S4bR3R2A4R4A3S0S34S47A1S46RbR3R2R1A3S2cS68RbRaR4A3R7RaR4R3R2A4A2F_;Fmd;Ftr;Frho;S0S7eVsegs;RbS5cVsegs;RaR6R1A4S7cS2fR5R1A1S4cRaR9R8R1A4A2Lw;A4Frho;F_;F_;FX;FJL;FE;FPosts;Frho0;Fn;FJE;Fok;").
Proof using .
  intros ok JE n rho0 Posts E JL X Hin HJ rho.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w [Hsm Hk]. right. destruct (HJ _ _ _ Hk) as [Hag HJL]. exists E, JL, rho. auto.
Qed.

Lemma eexit_postP : ltac2:(tb__ "0|1|
S5bS31S0S34S39S1S4bA2M0A1S1S4bS7cOF_;S61G0S36S1S4bR3R2A4R4A3S0S34S47A1S46RbR3R2R1A3S2cS68RbRaR4A3R7RaR4R3R2A4A2F_;Fmd;Ftr;Frho;S0S7dVsegs;S5cVsegs;RaR6R1A4S7cS2fR5R1A1S4cRaR9R8R1A4A2Lw;A3Frho;F_;F_;FX;FJL;FE;FPosts;Frho0;Fn;FJE;").
Proof using .
  intros JE n rho0 Posts E JL X Hin HJ rho w [Hsm Hk].
  exists w. split; [apply wsteps_refl|]. right. destruct (HJ _ _ _ Hk) as [Hag HJL]. exists E, JL, rho. auto.
Qed.

Lemma post_ok_okP : ltac2:(tb__ "0|0|
S1S56S31S34S3A1S1S2bS33S78R5R4R3R2R1A5S35A3S2bS33S53R6R5R4R3R2A5S35A3F_;FL;FR;Fnc;Fs;FPre;").
Proof using .
  intros Pre s nc R L H. unfold post_ok in H. unfold post_okP.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  rewrite H0, H2, H3, H4. reflexivity.
Qed.

Lemma call_check_checkP : ltac2:(tb__ "0|0|
S1S1S56S34S3A1S34S42A1S2bS33S6cR5R4R3R2R1A5S35A3S2bS33S4eR6R5R4R3S8aS42S1S43R2A4A5S35A3F_;FPosts;FR;Fs;FPre;FC;").
Proof using .
  intros C Pre s R Posts H. unfold call_check in H. unfold call_checkP.
  apply andb_prop in H as [H HP]. rewrite H. cbn [andb].
  apply forallb_forall. intros L HL. apply in_map_iff in HL as (L0 & <- & HL0).
  apply post_ok_okP. exact (proj1 (forallb_forall _ _) HP L0 HL0).
Qed.

Lemma triple_LQJ_LQP : ltac2:(tb__ "0|2|
S7cOF_;S80S5bS31S0S34S42A1S7eVsegs;R6R5S5eVsegs;R4R3R2R1A5A4S7eVsegs;R7R6S4cR4R3S8aS42S39S1S0S0S34S47A1M0S46OFm;Ft;Fr;F_;M1A2S42S36S1G1S43R1A1S0S0G0S46RaR3R2R1A3Lm;Lt;Lr;L_;A4LL;R2A4A3A4F_;Fleaves;Frho0;Fn;FJ;FP;Fok;").
Proof using .
  intros ok P J n rho0 leaves HT. eapply triple_conseq; [intros w Hw; exact Hw | | exact HT].
  intros w Hw. apply LQJ_LQP. exact Hw.
Qed.

Lemma etriple_LQJ_LQP : ltac2:(tb__ "0|2|
S7cOF_;S5bS31S0S34S42A1S7dVsegs;R5S5eVsegs;R4R3R2R1A5A3S7dVsegs;R6S4cR4R3S8aS42S39S1S0S0S34S47A1M0S46OFm;Ft;Fr;F_;M1A2S42S36S1G1S43R1A1S0S0G0S46RaR3R2R1A3Lm;Lt;Lr;L_;A4LL;R2A4A3A3F_;Fleaves;Frho0;Fn;FJ;FP;").
Proof using .
  intros P J n rho0 leaves HT. eapply etriple_conseq; [intros w Hw; exact Hw | | exact HT].
  intros w Hw. apply LQJ_LQP. exact Hw.
Qed.

End Call.
