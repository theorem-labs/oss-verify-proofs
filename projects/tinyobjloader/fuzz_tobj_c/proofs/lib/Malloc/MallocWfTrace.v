(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "prod"; "bool"; "list"; "unit"; "pair"; "option"; "nat"; "true"; "app"; "nil"; "cons"; "tt"; "false"; "length"; "Some"; "fst"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfTrace"; "shp"; "rt"; "sq"; "ra1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "rkind"; "region"; "st_regions"; "sptr"; "mkRegion"; "rg_kind"; "rg_live"; "kreq"; "lupd"; "RkMap"; "ameta"; "mslot"; "rg_len"; "upd_region"; "PGSZ"; "RkBrk"; "alloc_slot"; "BrkCur"; "KBrkGrow"; "MUsed"; "RkMetaRes"; "account_bounce"; "activate_group"; "alloc_group"; "alloc_meta"; "area_from_brk"; "area_from_mmap"; "ask"; "askz"; "bind"; "brkst"; "decay_bounces"; "dequeue"; "dequeue_head"; "enframe"; "fail"; "find_frame"; "forget_frame"; "free"; "free_meta"; "get"; "get_links"; "getm"; "ibind"; "install_group"; "malloc"; "massert"; "mcheck"; "modify"; "new_region"; "nontrivial_free"; "open_area"; "page_round"; "put"; "queue"; "record_seq"; "release_slot"; "set_links"; "set_metas"; "st_brk"; "step_seq"; "try_avail"; "@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "regions_after"; "req_ok"; "MT"; "reqs_ok"; "same_shape_regions"; "yields"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "add"; "mul"; "@Stdlib.Lists.List"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition shp (rs : list region) : list (rkind * bool) := ltac2:(tb__ "0|0|
S5bS18S0S17S1A2S18S4S17S1S1cR1A1S1dR1A1A4Lrg;Vrs;A4").

Lemma same_shape_shp a b : ltac2:(tb__ "0|0|
S57S60Va;Vb;A2S55S2S0S17S1A2A1S12Va;A1S12Vb;A1A3A2").
Proof.
  unfold same_shape_regions, shp. split.
  - revert b. induction a as [|x a IH]; intros [|y b] [H1 H2]; cbn in *; try discriminate; [reflexivity|].
    injection H1 as E1 T1. injection H2 as E2 T2. rewrite E1, E2. f_equal. apply IH. split; assumption.
  - revert b. induction a as [|x a IH]; intros [|y b] H; cbn in *; try discriminate; [split; reflexivity|].
    injection H as E1 E2 T. destruct (IH b T) as [IH1 IH2]. rewrite E1, E2, IH1, IH2. split; reflexivity.
Qed.

Lemma shp_app a b : ltac2:(tb__ "0|1|
S55S2S0S17S1A2M0A1S12S8S18Va;Vb;A3A1S8G0S12Va;A1S12Vb;A1A3A3").
Proof. unfold shp. apply map_app. Qed.

Lemma shp_lupd l r x : ltac2:(tb__ "0|1|
S55S2S0S17S1A2M0A1S12S1fS18Vl;Vr;Vx;A4A1S1fG0S12Vl;A1Vr;S4S17S1S1cVx;A1S1dVx;A1A4A4A3").
Proof. revert r. induction l as [|y l IH]; intros [|r]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma lupd_nth_same {T} (l : list T) r (f : T -> T) d : ltac2:(tb__ "0|0|
VT;S55VT;Vf;R1A1R1A3Fx;S55S2VT;A1S1fVT;Vl;Vr;Vf;S5aVT;Vr;Vl;Vd;A4A1A4Vl;A3F_;").
Proof. intros Hf. rewrite Hf. revert r. induction l as [|y l IH]; intros [|r]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma shp_lupd_keep l r (f : region -> region) d : ltac2:(tb__ "0|1|
S18S56S55S17S1cVf;R1A1M0A1S1cR1A1A3S55S1S1dG0A1S1dR1A1A3A2Frg;S55S2S0S17S1A2A1S12S1fS18Vl;Vr;Vf;S5aS18Vr;Vl;Vd;A4A1A4A1S12Vl;A1A3F_;").
Proof.
  intros Hf. revert r. induction l as [|y l IH]; intros [|r]; cbn [lupd nth]; try reflexivity.
  - destruct (Hf y) as [E1 E2]. unfold shp. cbn [map]. rewrite E1, E2. reflexivity.
  - unfold shp in *. cbn [map]. f_equal. apply IH.
Qed.

Lemma shp_length a b : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12Va;A1S12Vb;A1A3S55S6SdS18Va;A2SdS18Vb;A2A3F_;").
Proof. intros H. rewrite <- (length_map (fun rg => (rg_kind rg, rg_live rg)) a), <- (length_map (fun rg => (rg_kind rg, rg_live rg)) b). unfold shp in H. rewrite H. reflexivity. Qed.

Definition ra1 (rs : list region) (e : kreq * Z) : list region := ltac2:(tb__ "0|7|
S0S1eS58A2S2S18A1M0Le;Ve;S1eS58S1eG0Lk;R2Vrs;S58S58G0Lnpages;R1Vrs;S59S59G0Lp;R1S59Vrs;Lp0;S59S59G0Lp0;R1S59Vrs;Lp1;M1G1S1G0L_;M2S62R4Z0M3A2Vrs;S8S18Vrs;SaS18S1bS26S64Z2S25A2S9S58A1M4S7A4S9S18A1M5A3A3X1x2X59x3Lp0;Vrs;X59x3Lp;S59Vrs;Lp;X58x3Lnpages;Vrs;S58G2S62R2G3A2M6Vrs;S8S18Vrs;SaS18S1bS20S4bR1A1G4S7A4G5A3A3X1x2Llen;S58G2G6Vrs;S8S18Vrs;SaS18S1bS2bR1G4S7A4G5A3A3X1x2Llen;S1aVrs;Lpage;S6S58S1fS18Vrs;R2S1bS20S23S5aS18R2Vrs;S1bS20G3G4ScA4A4A1G4ScA4A4Llen;Lr;S58Vrs;Lpristine;X1ex8Lz;Lk;X0x1").

Lemma regions_after_cons rs e t : ltac2:(tb__ "0|0|
S55S2S18A1S5cVrs;SaS0S1eS58A2Ve;Vt;A3A2S5cS15Vrs;Ve;A2Vt;A2A3").
Proof. destruct e as [q z]. destruct q; try reflexivity. cbn [regions_after ra1]. destruct npages as [|p|p]; try reflexivity. destruct p as [p|p|]; try reflexivity. destruct p; reflexivity. Qed.

Fixpoint rt {A : Type} (rs : list region) (t : itree astate A) (Q : list region -> A -> Prop) : Prop :=
  match t with
  | IRet a => Q rs a
  | IFail _ => True
  | IAsk q snap k => req_ok snap q -> forall z, rt (ra1 rs (q, z)) (k z) Q
  end.

Lemma rt_yields {A} rs (t : itree astate A) Q tr a : ltac2:(tb__ "0|0|
S13VA;Vrs;Vt;VQ;A4S5fVA;Vt;A2S61VA;Vt;Vtr;Va;A4VQ;S5cVrs;Vtr;A2Va;A2F_;F_;F_;").
Proof.
  revert rs tr. induction t as [a' | q sp k IH | f]; intros rs tr H RQ Y; destruct tr as [|[q' z] tr]; cbn in Y; try contradiction.
  - subst a'. exact H.
  - destruct Y as (-> & Az & Y). cbn in RQ. destruct RQ as [Rq RQ]. rewrite regions_after_cons. apply (IH z). + apply H. exact Rq. + apply RQ. exact Az. + exact Y.
Qed.

Lemma rt_conseq {A} rs (t : itree astate A) (Q Q' : list region -> A -> Prop) : ltac2:(tb__ "0|0|
S13VA;Vrs;Vt;VQ;A4S2S18A1VA;VQ;R2R1A2VQ';R3R2A2F_;Fa;Frs';S13VA;Vrs;Vt;VQ';A4F_;F_;").
Proof. revert rs. induction t as [a | q sp k IH | f]; intros rs H HQ; cbn in *; [apply HQ, H | | exact I]. intros Rq z. apply IH; [apply H; exact Rq | exact HQ]. Qed.

Lemma rt_ibind {A B} rs (x : itree astate A) (K : A -> itree astate B) Q : ltac2:(tb__ "0|0|
S13VA;Vrs;Vx;S2S18A1VA;S13VB;R2VK;R1A1VQ;A4La;Lrs';A4S13VB;Vrs;S42S16VA;VB;Vx;VK;A5VQ;A4F_;").
Proof. revert rs. induction x as [a | q sp k IH | f]; intros rs H; cbn in *; [exact H | | exact I]. intros Rq z. apply IH. apply H. exact Rq. Qed.

Section MonadRules.
  Context {A B : Type}.
  Implicit Types (s : astate) (rs : list region).

  Lemma rt_ret rs (a : A) s Q : Q rs (a, s) -> rt rs (ret a s) Q.
  Proof using . intros H. exact H. Qed.
  Lemma rt_bind rs (m : M B) (k : B -> M A) s Q : ltac2:(tb__ "0|2|
S13S0VB;S16A2M0Vrs;Vm;Vs;A1S2S18A1G0S13S0VA;S16A2M1R2Vk;SfVB;S16R1A3S11VB;S16R1A3A2VQ;A4Lr;Lrs';A4S13G1Vrs;S34VB;VA;Vm;Vk;Vs;A5VQ;A4F_;").
  Proof using . intros H. unfold bind. apply rt_ibind. eapply rt_conseq; [exact H|]. intros rs' [b s']. cbn. intros X; exact X. Qed.
  Lemma rt_fail rs f s Q : ltac2:(tb__ "0|0|
S13S0VA;S16A2Vrs;S3aVA;Vf;Vs;A3VQ;A4").
  Proof using . exact I. Qed.
  Lemma rt_get rs s (Q : list region -> astate * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;Vrs;S4S16S16Vs;Vs;A4A2S13S0S16S16A2Vrs;S3fVs;A1VQ;A4F_;").
  Proof using . intros H; exact H. Qed.
  Lemma rt_put rs s s' (Q : list region -> unit * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;Vrs;S4S3S16SbVs';A4A2S13S0S3S16A2Vrs;S4cVs';Vs;A2VQ;A4F_;").
  Proof using . intros H; exact H. Qed.
  Lemma rt_modify rs f s (Q : list region -> unit * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;Vrs;S4S3S16SbVf;Vs;A1A4A2S13S0S3S16A2Vrs;S47Vf;Vs;A2VQ;A4F_;").
  Proof using . intros H; exact H. Qed.
  Lemma rt_ask rs q s (Q : list region -> bool * astate -> Prop) : ltac2:(tb__ "0|0|
S5dVs;Vq;A2S58VQ;S15Vrs;S4S1eS58Vq;R1A4A2S4S1S16S10S62R1Z0A2A1Vs;A4A2Fz;F_;S13S0S1S16A2Vrs;S32Vq;Vs;A2VQ;A4F_;").
  Proof using . intros H Rq z. cbn. apply H. exact Rq. Qed.
  Lemma rt_askz rs q s (Q : list region -> Z * astate -> Prop) : ltac2:(tb__ "0|0|
S5dVs;Vq;A2S58VQ;S15Vrs;S4S1eS58Vq;R1A4A2S4S58S16R1Vs;A4A2Fz;F_;S13S0S58S16A2Vrs;S33Vq;Vs;A2VQ;A4F_;").
  Proof using . intros H Rq z. cbn. apply H. exact Rq. Qed.
  Lemma rt_massert rs (b : bool) i s (Q : list region -> unit * astate -> Prop) : ltac2:(tb__ "0|0|
S55S1Vb;S7A3VQ;Vrs;S4S3S16SbVs;A4A2F_;S13S0S3S16A2Vrs;S45Vb;Vi;Vs;A3VQ;A4F_;").
  Proof using . intros H. unfold massert. destruct b; [apply H; reflexivity | exact I]. Qed.
  Lemma rt_mcheck rs (b : bool) i s (Q : list region -> unit * astate -> Prop) : ltac2:(tb__ "0|0|
S55S1Vb;S7A3VQ;Vrs;S4S3S16SbVs;A4A2F_;S13S0S3S16A2Vrs;S46Vb;Vi;Vs;A3VQ;A4F_;").
  Proof using . intros H. unfold mcheck. destruct b; [apply H; reflexivity | exact I]. Qed.
End MonadRules.

Lemma rt_getm rs p s (Q : list region -> ameta * astate -> Prop) : ltac2:(tb__ "0|0|
S21S55S5S22A1S5eVs;Vp;A2SeS22S2aR1A1A2A3VQ;Vrs;S4S21S16R2Vs;A4A2F_;Fam;S13S0S21S16A2Vrs;S41Vp;Vs;A2VQ;A4F_;").
Proof.
  intros H. unfold getm. apply rt_bind. apply rt_get. cbn [fst snd]. unfold MT in H.
  destruct (mlookup (st_metas s) p) as [[| |am]|]; try exact I. apply H. reflexivity.
Qed.

Lemma rt_get_links rs p s (Q : list region -> (option sptr * option sptr) * astate -> Prop) : ltac2:(tb__ "0|2|
S0S5S1aA1M0G0A2M1VQ;Vrs;S4G1S16R1Vs;A4A2Fl;S13S0G1S16A2Vrs;S40Vp;Vs;A2VQ;A4F_;").
Proof. intros H. unfold get_links. apply rt_bind. apply rt_get. cbn [fst snd]. destruct (mlookup (st_metas s) p); [apply H | exact I]. Qed.

Lemma rt_set_links rs p pr nx s (Q : list region -> unit * astate -> Prop) : ltac2:(tb__ "0|0|
S2S0S1aS22A2A1VQ;Vrs;S4S3S16SbS51R1Vs;A2A4A2Fms;S13S0S3S16A2Vrs;S50Vp;Vpr;Vnx;Vs;A4VQ;A4F_;").
Proof. intros H. unfold set_links. apply rt_bind. apply rt_get. cbn [fst snd]. destruct (mlookup (st_metas s) p); [apply H | exact I]. Qed.

Definition sq {A} (rs : list region) (r : A * astate) : Prop := shp (st_regions (snd r)) = shp rs.

Create HintDb rt.

Ltac rq := cbn [st_regions st_metas set_init_done set_mmap_counter set_free_meta_head set_avail_meta set_avail_meta_count
               set_avail_meta_area_count set_meta_alloc_shift set_area_head set_area_tail set_avail_meta_areas
               set_active set_usage set_unmap_seq set_bounces set_seq set_brk set_metas set_regions set_areas fst snd] in *.

Ltac rtstep :=
  lazymatch goal with
  | |- rt _ (bind _ _ _) _ => apply rt_bind
  | |- rt _ (ret _ _) _ => apply rt_ret
  | |- rt _ (get _) _ => apply rt_get
  | |- rt _ (put _ _) _ => apply rt_put
  | |- rt _ (modify _ _) _ => apply rt_modify
  | |- rt _ (setm _ _ _) _ => unfold setm at 1; apply rt_modify
  | |- rt _ (setslot _ _ _) _ => unfold setslot at 1; apply rt_modify
  | |- rt _ (set_usage_of _ _ _) _ => unfold set_usage_of at 1; apply rt_modify
  | |- rt _ (set_head _ _ _) _ => unfold set_head at 1
  | |- rt _ (get_head _ _) _ => unfold get_head at 1
  | |- rt _ (getm _ _) _ => apply rt_getm; intros ? ?
  | |- rt _ (get_links _ _) _ => apply rt_get_links; intros ?
  | |- rt _ (set_links _ _ _ _) _ => apply rt_set_links; intros ?
  | |- rt _ (set_prev _ _ _) _ => unfold set_prev at 1
  | |- rt _ (set_next _ _ _) _ => unfold set_next at 1
  | |- rt _ (massert _ _ _) _ => apply rt_massert; intros _
  | |- rt _ (mcheck _ _ _) _ => apply rt_mcheck; intros ?
  | |- rt _ (ask _ _) _ => let z := fresh "z" in apply rt_ask; intros ?RQ z; cbn [ra1]; destruct (z =? 0); cbn [negb]
  | |- rt _ (askz _ _) _ => apply rt_askz; intros ?RQ ?; cbn [ra1]
  | |- rt _ (fail _ _) _ => apply rt_fail
  | |- rt _ (IFail _) _ => exact I
  | |- rt _ (IRet _) _ => cbn [rt]
  | |- rt _ (match ?x with _ => _ end _) _ => destruct x eqn:?
  | |- rt _ (match ?x with _ => _ end) _ => destruct x eqn:?
  | |- rt _ _ (fun _ _ => rt _ _ _) =>
      let HQ := fresh "HQ" in
      eapply rt_conseq; [solve [eauto 4 with rt nocore] | intros ? [? ?] HQ;
        lazymatch type of HQ with
        | _ /\ _ => let EQ := fresh "EQ" in destruct HQ as [HQ EQ]; cbn [fst snd] in EQ; try subst
        | _ => idtac
        end; unfold sq in HQ; cbn [fst snd] in HQ ]
  | |- rt _ _ _ => solve [eauto 3 with rt nocore]
  | |- sq _ _ => unfold sq; rq; solve [assumption | congruence | auto]
  | |- True => exact I
  | |- forall _, _ => intros ?
  end.
Ltac rtauto := repeat (cbn beta iota zeta delta [fst snd negb andb orb]; rtstep).

Section Fns.
  Implicit Types (s : astate) (rs : list region).

  Lemma rt_queue rs h m s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S3S16A2Vrs;S4dVh;Vm;Vs;A3S14S3A1A4F_;").
  Proof. intros E. unfold queue. rtauto. all: destruct h; rtauto. Qed.
  Hint Resolve rt_queue : rt.

  Lemma rt_dequeue rs h m s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S3S16A2Vrs;S37Vh;Vm;Vs;A3S14S3A1A4F_;").
  Proof. intros E. unfold dequeue. rtauto; destruct h; rtauto. Qed.
  Hint Resolve rt_dequeue : rt.

  Lemma rt_dequeue_head rs h s : ltac2:(tb__ "0|1|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S5S1aA1M0S16A2Vrs;S38Vh;Vs;A2S14G0A1A4F_;").
  Proof. intros E. unfold dequeue_head. destruct h; rtauto. Qed.
  Hint Resolve rt_dequeue_head : rt.

  Lemma rt_free_meta rs m s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S3S16A2Vrs;S3eVm;Vs;A2S14S3A1A4F_;").
  Proof. intros E. unfold free_meta. rtauto. Qed.
  Hint Resolve rt_free_meta : rt.

  Lemma rt_step_seq rs s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S3S16A2Vrs;S53Vs;A1S14S3A1A4F_;").
  Proof. intros E. unfold step_seq. rtauto. destruct (st_seq s =? 255); rq; exact E. Qed.
  Hint Resolve rt_step_seq : rt.

  Lemma rt_record_seq rs sc s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S3S16A2Vrs;S4eVsc;Vs;A2S14S3A1A4F_;").
  Proof. intros E. unfold record_seq. destruct (bounce_idx sc); rtauto. Qed.
  Hint Resolve rt_record_seq : rt.

  Lemma rt_account_bounce rs sc s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S3S16A2Vrs;S2cVsc;Vs;A2S14S3A1A4F_;").
  Proof. intros E. unfold account_bounce. destruct (bounce_idx sc); rtauto. destruct (negb _ && _); rq; exact E. Qed.
  Hint Resolve rt_account_bounce : rt.

  Lemma rt_decay_bounces rs sc s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S3S16A2Vrs;S36Vsc;Vs;A2S14S3A1A4F_;").
  Proof. intros E. unfold decay_bounces. destruct (bounce_idx sc); rtauto. destruct (_ =? 0); rq; exact E. Qed.
  Hint Resolve rt_decay_bounces : rt.

  Lemma rt_new_region rs k len len' s : ltac2:(tb__ "0|2|
S55S2S0S17S1A2A1S12S19Vs;A1M0A1S12Vrs;A1A3S13S0S6S16A2M1S8S18Vrs;SaS18S1bVk;Vlen';S9S58A1S7A4S9S18A1A3A3S48Vk;Vlen;Vs;A3S2S18A1G1S56S14S6R2R1A3S55S6SfS6S16R1A3SdS18G0A2A3A2Lr;Lrs';A4F_;").
  Proof. intros E. unfold new_region. rtauto. split; [|reflexivity]. unfold sq. rq. rewrite !shp_app, E. reflexivity. Qed.

  Lemma rt_upd_region_keep rs r f s : ltac2:(tb__ "0|1|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S18S56S55S17S1cVf;R1A1M0A1S1cR1A1A3S55S1S1dG0A1S1dR1A1A3A2Frg;S13S0S3S16A2Vrs;S24Vr;Vf;Vs;A3S14S3A1A4F_;F_;").
  Proof. intros E Hf. unfold upd_region. rtauto. unfold sq. rq. rewrite (shp_lupd_keep _ _ _ _ Hf). exact E. Qed.

  Lemma rt_upd_region_kill rs r len s : ltac2:(tb__ "0|1|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S3S16A2S1fS18Vrs;Vr;S1bS20Vlen;S9S58A1M0ScA4A4S24Vr;S18S1bS20S23R1A1G0ScA4Lrg;Vs;A3S14S3A1A4F_;").
  Proof. intros E. unfold upd_region. rtauto. unfold sq. rq. rewrite !shp_lupd, E. reflexivity. Qed.

  Lemma shp_lupd_nth l r x rg : ltac2:(tb__ "0|0|
S55S5S18A1S65S18Vl;Vr;A3SeS18Vrg;A2A3S55S17S1cVx;A1S1cVrg;A1A3S55S1S1dVx;A1S1dVrg;A1A3S55S2S0S17S1A2A1S12S1fS18Vl;Vr;Vx;A4A1S12Vl;A1A3F_;F_;F_;").
  Proof.
    revert r. induction l as [|y l IH]; intros [|r] Hn Hk Hl; cbn [lupd nth_error] in *; try reflexivity.
    - injection Hn as ->. unfold shp. cbn [map]. rewrite Hk, Hl. reflexivity.
    - unfold shp in *. cbn [map]. f_equal. apply IH; assumption.
  Qed.

  Lemma rt_upd_region_brk rs r pages s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S5dVs;S29Z1A1A2S55S35S52Vs;A1S28Vr;Vpages;A2A3S13S0S3S16A2Vrs;S24Vr;S18S1bS26S63S23R1A1S25A2S9S58A1S7A4Lrg;Vs;A3S14S3A1A4F_;F_;F_;").
  Proof.
    intros E RQ Hb. unfold upd_region. rtauto. unfold sq. rq.
    destruct RQ as [[H _] | (_ & r0 & p0 & rg & Hb0 & Hrg & Hk & Hl & _)]; [lia|].
    rewrite Hb in Hb0. injection Hb0 as <- <-. unfold region_of in Hrg.
    rewrite <- E. apply (shp_lupd_nth _ _ _ rg); [exact Hrg | cbn; congruence | cbn; congruence].
  Qed.

  Hint Resolve rt_new_region rt_upd_region_keep rt_upd_region_kill rt_upd_region_brk : rt.
  Hint Extern 1 (forall rg, _ = _ /\ _ = _) => intros; split; reflexivity : rt.

  Lemma rt_area_from_brk rs s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S1S16A2Vrs;S30Vs;A1S14S1A1A4F_;").
  Proof.
    intros E. unfold area_from_brk. rtauto. Qed.
  Hint Resolve rt_area_from_brk : rt.

  Lemma rt_area_from_mmap rs s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S1S16A2Vrs;S31Vs;A1S14S1A1A4F_;").
  Proof. intros E. unfold area_from_mmap. rtauto. Qed.
  Hint Resolve rt_area_from_mmap : rt.

  Lemma rt_open_area rs nu s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S1S16A2Vrs;S4aVnu;Vs;A2S14S1A1A4F_;").
  Proof. intros E. unfold open_area. rtauto. Qed.
  Hint Resolve rt_open_area : rt.

  Lemma rt_alloc_meta rs s : ltac2:(tb__ "0|1|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S5S1aA1M0S16A2Vrs;S2fVs;A1S14G0A1A4F_;").
  Proof. intros E. unfold alloc_meta. rtauto. Qed.
  Hint Resolve rt_alloc_meta : rt.

  Lemma rt_activate_group rs m s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S58S16A2Vrs;S2dVm;Vs;A2S14S58A1A4F_;").
  Proof. intros E. unfold activate_group. rtauto. Qed.
  Hint Resolve rt_activate_group : rt.

  Lemma rt_try_avail rs sc s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S58S16A2Vrs;S54Vsc;Vs;A2S14S58A1A4F_;").
  Proof. intros E. unfold try_avail. rtauto. Qed.
  Hint Resolve rt_try_avail : rt.

  Lemma rt_enframe rs g idx n ctr k s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S1aS16A2Vrs;S39Vg;Vidx;Vn;Vctr;Vk;Vs;A6S14S1aA1A4F_;").
  Proof. intros E. unfold enframe. rtauto. Qed.
  Hint Resolve rt_enframe : rt.

  Lemma rt_install_group rs m sc cnt aidx maplen mem sl s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S3S16A2Vrs;S43Vm;Vsc;Vcnt;Vaidx;Vmaplen;Vmem;Vsl;Vs;A8S14S3A1A4F_;").
  Proof. intros E. unfold install_group. rtauto. Qed.
  Hint Resolve rt_install_group : rt.

  Lemma rt_forget_frame rs g i s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S3S16A2Vrs;S3cVg;Vi;Vs;A3S14S3A1A4F_;").
  Proof. intros E. unfold forget_frame. rtauto. Qed.
  Hint Resolve rt_forget_frame : rt.

  Lemma rt_release_slot rs g i s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S3S16A2Vrs;S4fVg;Vi;Vs;A3S14S3A1A4F_;").
  Proof. intros E. unfold release_slot. rtauto. Qed.
  Hint Resolve rt_release_slot : rt.

  Lemma rt_find_frame rs p s : ltac2:(tb__ "0|1|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S0S1aS58A2M0S16A2Vrs;S3bVp;Vs;A2S14G0A1A4F_;").
  Proof. intros E. unfold find_frame. rtauto. Qed.
  Hint Resolve rt_find_frame : rt.

  Lemma rt_alloc_mutual fuel : ltac2:(tb__ "0|3|
S56S2S18A1M0S58S58S16S55S2S0S17S1A2A1S12S19R1A1A1S12R4A1A3M1S13S0S58S16A2R5S27Vfuel;R4R3R2A4S14S58A1A4F_;Fs;Freq;Fsc;Frs;G0S58S58S16G1S13S0S5S1aA1M2S16A2R5S2eVfuel;R4R3R2A4S14G2A1A4F_;Fs;Freq;Fsc;Frs;A2").
  Proof.
    induction fuel as [|f [IHs IHg]]; [split; intros; cbn; exact I|]. split.
    - intros rs sc req s E. cbn fix beta iota delta [alloc_slot]. rtauto.
    - intros rs sc req s E. cbn fix beta iota delta [alloc_group]. rtauto.
  Qed.
  Lemma rt_alloc_slot fuel rs sc req s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S58S16A2Vrs;S27Vfuel;Vsc;Vreq;Vs;A4S14S58A1A4F_;").
  Proof. apply (proj1 (rt_alloc_mutual fuel)). Qed.
  Hint Resolve rt_alloc_slot : rt.

  Lemma rt_malloc rs n s : ltac2:(tb__ "0|1|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S5S1aA1M0S16A2Vrs;S44Vn;Vs;A2S14G0A1A4F_;").
  Proof. intros E. unfold malloc. rtauto. Qed.

  Lemma rt_nontrivial_free fuel rs g i s : ltac2:(tb__ "0|1|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S5S0S6S58A2A1M0S16A2Vrs;S49Vfuel;Vg;Vi;Vs;A4S14G0A1A4F_;").
  Proof.
    revert rs g i s. induction fuel as [|f IH]; intros rs g i s E; [cbn; exact I|].
    cbn fix beta iota delta [nontrivial_free]. rtauto.
  Qed.
  Hint Resolve rt_nontrivial_free : rt.

  Lemma rt_free rs p s : ltac2:(tb__ "0|0|
S55S2S0S17S1A2A1S12S19Vs;A1A1S12Vrs;A1A3S13S0S3S16A2Vrs;S3dVp;Vs;A2S14S3A1A4F_;").
  Proof. intros E. unfold free. rtauto. Qed.
End Fns.
