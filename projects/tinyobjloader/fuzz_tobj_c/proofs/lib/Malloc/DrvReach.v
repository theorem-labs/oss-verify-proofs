(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "st_avail_meta_count"; "st_init_done"; "mslot"; "ameta"; "st_usage"; "MUsed"; "st_free_meta_head"; "slotst"; "st_metas"; "am_last"; "am_slots"; "malloc"; "new_region"; "st_active"; "alloc_meta"; "am_avail"; "am_freed"; "am_maplen"; "am_sc"; "area_from_brk"; "area_from_mmap"; "dequeue"; "free"; "initial_cnt"; "open_area"; "set_links"; "upd_region"; "METAS_PER_AREA"; "MMAP_THRESHOLD"; "account_bounce"; "activate_group"; "alloc_slot"; "decay_bounces"; "dequeue_head"; "enframe"; "find_frame"; "forget_frame"; "free_meta"; "get_links"; "mupdate"; "nontrivial_free"; "queue"; "record_seq"; "release_slot"; "set_metas"; "set_next"; "set_prev"; "step_seq"; "try_avail"; "usage_of"; "HFreeMeta"; "PGSZ"; "UNIT"; "am_set_links"; "ask"; "askz"; "bind"; "bit"; "class_size"; "fail"; "find_frame_in"; "find_in_slots"; "get"; "getm"; "ibind"; "install_group"; "lupd"; "massert"; "mcheck"; "mlookup"; "mmap_plan"; "modify"; "okay_to_free"; "ones"; "page_round"; "put"; "region"; "st_regions"; "with_links"; "@Corelib.Init.Datatypes"; "prod"; "unit"; "bool"; "option"; "pair"; "nat"; "true"; "list"; "fst"; "length"; "None"; "tt"; "S"; "Some"; "snd"; "false"; "negb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.DrvReach"; "ct"; "full_all"; "fq"; "cq"; "gfull"; "uq"; "cqd"; "cqm"; "drv_inv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "of_nat"; "to_nat"; "div"; "eqb"; "sub"; "lor"; "ltb"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "drv_reach"; "DRV_OPS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "@Stdlib.Lists.List"; "In"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "WF"; "MT"; "yields"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint ct {A : Type} (t : itree astate A) (Q : A -> Prop) : Prop :=
  match t with
  | IRet a => Q a
  | IFail _ => True
  | IAsk q snap k => forall z, ct (k z) Q
  end.

Lemma ct_yields {A} (t : itree astate A) Q tr a : ltac2:(tb__ "0|0|
S68VA;Vt;VQ;A3S83VA;Vt;Vtr;Va;A4VQ;Va;A1F_;F_;").
Proof.
  revert tr. induction t as [a' | q sp k IH | f]; intros tr H Y; destruct tr as [|[q' z] tr]; cbn in Y; try contradiction.
  - subst a'. exact H.
  - destruct Y as (-> & Az & Y). apply (IH z tr). + apply H. + exact Y.
Qed.

Lemma ct_conseq {A} (t : itree astate A) (Q Q' : A -> Prop) : ltac2:(tb__ "0|0|
S68VA;Vt;VQ;A3VA;VQ;R1A1VQ';R2A1F_;Fa;S68VA;Vt;VQ';A3F_;F_;").
Proof. induction t as [a | q sp k IH | f]; intros H HQ; cbn in *; [apply HQ, H | | exact I]. intros z. apply IH; [apply H | exact HQ]. Qed.

Lemma ct_ibind {A B} (x : itree astate A) (K : A -> itree astate B) Q : ltac2:(tb__ "0|0|
S68VA;Vx;VA;S68VB;VK;R1A1VQ;A3La;A3S68VB;S47S5VA;VB;Vx;VK;A5VQ;A3F_;").
Proof. induction x as [a | q sp k IH | f]; intros H; cbn in *; [exact H | | exact I]. intros z. apply IH. apply H. Qed.

Section MonadRules.
  Context {A B : Type}.
  Implicit Types (s : astate).

  Lemma ct_ret (a : A) s Q : Q (a, s) -> ct (ret a s) Q.
  Proof using . intros H. exact H. Qed.
  Lemma ct_bind (m : M B) (k : B -> M A) s Q : ltac2:(tb__ "0|2|
S68S56VB;S5A2M0Vm;Vs;A1G0S68S56VA;S5A2M1Vk;S5eVB;S5R1A3S64VB;S5R1A3A2VQ;A3Lr;A3S68G1S3fVB;VA;Vm;Vk;Vs;A5VQ;A3F_;").
  Proof using . intros H. unfold bind. apply ct_ibind. eapply ct_conseq; [exact H|]. intros [b s']. cbn. intros X; exact X. Qed.
  Lemma ct_fail f s Q : ltac2:(tb__ "0|0|
S68S56VA;S5A2S42VA;Vf;Vs;A3VQ;A3").
  Proof using . exact I. Qed.
  Lemma ct_get s (Q : astate * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S5aS5S5Vs;Vs;A4A1S68S56S5S5A2S45Vs;A1VQ;A3F_;").
  Proof using . intros H; exact H. Qed.
  Lemma ct_put s s' (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S5aS57S5S61Vs';A4A1S68S56S57S5A2S52Vs';Vs;A2VQ;A3F_;").
  Proof using . intros H; exact H. Qed.
  Lemma ct_modify f s (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S5aS57S5S61Vf;Vs;A1A4A1S68S56S57S5A2S4eVf;Vs;A2VQ;A3F_;").
  Proof using . intros H; exact H. Qed.
  Lemma ct_ask q s (Q : bool * astate -> Prop) : ltac2:(tb__ "0|0|
S67VQ;S5aS58S5S66S77R1Z0A2A1Vs;A4A1Fz;S68S56S58S5A2S3dVq;Vs;A2VQ;A3F_;").
  Proof using . intros H z. cbn. apply H. Qed.
  Lemma ct_askz q s (Q : Z * astate -> Prop) : ltac2:(tb__ "0|0|
S67VQ;S5aS67S5R1Vs;A4A1Fz;S68S56S67S5A2S3eVq;Vs;A2VQ;A3F_;").
  Proof using . intros H z. cbn. apply H. Qed.
  Lemma ct_massert (b : bool) i s (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
S0S58Vb;S5cA3VQ;S5aS57S5S61Vs;A4A1F_;S68S56S57S5A2S4aVb;Vi;Vs;A3VQ;A3F_;").
  Proof using . intros H. unfold massert. destruct b; [apply H; reflexivity | exact I]. Qed.
  Lemma ct_mcheck (b : bool) i s (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
S0S58Vb;S5cA3VQ;S5aS57S5S61Vs;A4A1F_;S68S56S57S5A2S4bVb;Vi;Vs;A3VQ;A3F_;").
  Proof using . intros H. unfold mcheck. destruct b; [apply H; reflexivity | exact I]. Qed.
End MonadRules.

Lemma ct_getm p s (Q : ameta * astate -> Prop) : ltac2:(tb__ "0|0|
SaS0S59S9A1S82Vs;Vp;A2S63S9ScR1A1A2A3VQ;S5aSaS5R2Vs;A4A1F_;Fam;S68S56SaS5A2S46Vp;Vs;A2VQ;A3F_;").
Proof.
  intros H. unfold getm. apply ct_bind. apply ct_get. cbn [fst snd]. unfold MT in H.
  destruct (mlookup (st_metas s) p) as [[| |am]|]; try exact I. apply H. reflexivity.
Qed.

Lemma ct_get_links p s (Q : (option sptr * option sptr) * astate -> Prop) : ltac2:(tb__ "0|2|
S56S59S6A1M0G0A2M1VQ;S5aG1S5R1Vs;A4A1Fl;S68S56G1S5A2S2dVp;Vs;A2VQ;A3F_;").
Proof. intros H. unfold get_links. apply ct_bind. apply ct_get. cbn [fst snd]. destruct (mlookup (st_metas s) p); [apply H | exact I]. Qed.

Lemma ct_set_links p pr nx s (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
S5dS56S6S9A2A1VQ;S5aS57S5S61S33R1Vs;A2A4A1Fms;S68S56S57S5A2S20Vp;Vpr;Vnx;Vs;A4VQ;A3F_;").
Proof. intros H. unfold set_links. apply ct_bind. apply ct_get. cbn [fst snd]. destruct (mlookup (st_metas s) p); [apply H | exact I]. Qed.

Definition cq {A} (c : Z) (b : bool) (r : A * astate) : Prop :=
  st_avail_meta_count (snd r) = c /\ st_init_done (snd r) = b.

Create HintDb ct.
Hint Extern 1 (_ <= _) => lia : ct.
Hint Extern 1 (st_avail_meta_count _ = _) => cbn; first [assumption | reflexivity | congruence] : ct.
Hint Extern 1 (st_init_done _ = _) => cbn; first [assumption | reflexivity | congruence] : ct.

Ltac cq_unf := cbn [st_avail_meta_count st_init_done set_init_done set_mmap_counter set_free_meta_head set_avail_meta set_avail_meta_count
               set_avail_meta_area_count set_meta_alloc_shift set_area_head set_area_tail set_avail_meta_areas
               set_active set_usage set_unmap_seq set_bounces set_seq set_brk set_metas set_regions set_areas fst snd] in *.

Ltac ct_leaf := fail.

Ltac ct_conseq_step :=
  let HQ := fresh "HQ" in
  eapply ct_conseq; [solve [eauto 4 with ct nocore] | intros [? ?] HQ;
    lazymatch type of HQ with
    | _ /\ _ = _ => let EQ := fresh "EQ" in destruct HQ as [HQ EQ]; cbn [fst snd] in EQ; try subst
    | _ => idtac
    end;
    lazymatch type of HQ with
    | cq _ _ _ => unfold cq in HQ; cbn [fst snd] in HQ; destruct HQ as [? ?]
    | _ => cbn [fst snd] in HQ
    end ].

Ltac ctstep :=
  lazymatch goal with
  | |- ct (bind _ _ _) _ => apply ct_bind
  | |- ct (ret _ _) _ => apply ct_ret
  | |- ct (get _) _ => apply ct_get
  | |- ct (put _ _) _ => apply ct_put
  | |- ct (modify _ _) _ => apply ct_modify
  | |- ct (setm _ _ _) _ => unfold setm at 1; apply ct_modify
  | |- ct (setslot _ _ _) _ => unfold setslot at 1; apply ct_modify
  | |- ct (set_usage_of _ _ _) _ => unfold set_usage_of at 1; apply ct_modify
  | |- ct (set_head _ _ _) _ => unfold set_head at 1
  | |- ct (get_head _ _) _ => unfold get_head at 1
  | |- ct (getm _ _) _ => apply ct_getm; intros ? ?
  | |- ct (get_links _ _) _ => apply ct_get_links; intros ?
  | |- ct (set_links _ _ _ _) _ => apply ct_set_links; intros ?
  | |- ct (set_prev _ _ _) _ => unfold set_prev at 1
  | |- ct (set_next _ _ _) _ => unfold set_next at 1
  | |- ct (massert _ _ _) _ => let Hm := fresh "Hm" in apply ct_massert; intros Hm; try (exfalso; discriminate Hm)
  | |- ct (mcheck _ _ _) _ => apply ct_mcheck; intros ?
  | |- ct (ask _ _) _ => let z := fresh "z" in apply ct_ask; intros z; destruct (z =? 0); cbn [negb]
  | |- ct (askz _ _) _ => apply ct_askz; intros ?
  | |- ct (fail _ _) _ => apply ct_fail
  | |- ct (IFail _) _ => exact I
  | |- ct (IRet _) _ => cbn [ct]
  | |- ct (match ?x with _ => _ end _) _ => destruct x eqn:?
  | |- ct (match ?x with _ => _ end) _ => destruct x eqn:?
  | |- ct _ (fun _ => ct _ _) => ct_conseq_step
  | |- ct _ _ => solve [eauto 4 with ct nocore]
  | |- cq _ _ _ => unfold cq; cq_unf; solve [split; first [assumption | congruence | reflexivity | auto] ]
  | |- True => exact I
  | |- forall _, _ => intros ?
  | |- _ => solve [ct_leaf]
  end.
Ltac ctauto := repeat (cbn beta iota zeta delta [fst snd negb andb orb]; ctstep).

Implicit Types (s : astate) (c : Z) (b : bool).

  Lemma ct_queue c b h m s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S57S5A2S30Vh;Vm;Vs;A3S6bS57Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold queue. ctauto. all: destruct h; ctauto. Qed.
  Hint Resolve ct_queue : ct.

  Lemma ct_dequeue c b h m s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S57S5A2S1cVh;Vm;Vs;A3S6bS57Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold dequeue. ctauto; destruct h; ctauto. Qed.
  Hint Resolve ct_dequeue : ct.

  Lemma ct_dequeue_head c b h s : ltac2:(tb__ "0|1|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S59S6A1M0S5A2S28Vh;Vs;A2S6bG0Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold dequeue_head. destruct h; ctauto. Qed.
  Hint Resolve ct_dequeue_head : ct.

  Lemma ct_free_meta c b m s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S57S5A2S2cVm;Vs;A2S6bS57Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold free_meta. ctauto. Qed.
  Hint Resolve ct_free_meta : ct.

  Lemma ct_step_seq c b s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S57S5A2S36Vs;A1S6bS57Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold step_seq. ctauto. destruct (st_seq s =? 255); cq_unf; split; assumption. Qed.
  Hint Resolve ct_step_seq : ct.

  Lemma ct_record_seq c b sc s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S57S5A2S31Vsc;Vs;A2S6bS57Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold record_seq. destruct (bounce_idx sc); ctauto. Qed.
  Hint Resolve ct_record_seq : ct.

  Lemma ct_account_bounce c b sc s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S57S5A2S24Vsc;Vs;A2S6bS57Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold account_bounce. destruct (bounce_idx sc); ctauto. destruct (negb _ && _); cq_unf; split; assumption. Qed.
  Hint Resolve ct_account_bounce : ct.

  Lemma ct_decay_bounces c b sc s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S57S5A2S27Vsc;Vs;A2S6bS57Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold decay_bounces. destruct (bounce_idx sc); ctauto. destruct (_ =? 0); cq_unf; split; assumption. Qed.
  Hint Resolve ct_decay_bounces : ct.

  Lemma ct_new_region c b k len s : ltac2:(tb__ "0|1|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S5bS5A2M0S13Vk;Vlen;Vs;A3G0S1S6bS5bVc;Vb;R1A4S0S5bS5eS5bS5R1A3S5fS53S54Vs;A1A2A3A2Lr;A3F_;F_;").
  Proof. intros E1 E2. unfold new_region. ctauto. split; [|reflexivity]. unfold cq. cq_unf. split; assumption. Qed.
  Lemma ct_new_region' c b k len s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S5bS5A2S13Vk;Vlen;Vs;A3S6bS5bVc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. eapply ct_conseq; [apply (ct_new_region c b k len s E1 E2)|]. intros a [H _]. exact H. Qed.
  Hint Resolve ct_new_region' : ct.

  Lemma ct_upd_region c b r f s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S57S5A2S21Vr;Vf;Vs;A3S6bS57Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold upd_region. ctauto. Qed.
  Hint Resolve ct_upd_region : ct.

  Lemma ct_activate_group c b m s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S67S5A2S25Vm;Vs;A2S6bS67Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold activate_group. ctauto. Qed.
  Hint Resolve ct_activate_group : ct.

  Lemma ct_try_avail c b sc s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S67S5A2S37Vsc;Vs;A2S6bS67Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold try_avail. ctauto. Qed.
  Hint Resolve ct_try_avail : ct.

  Lemma ct_enframe c b g idx n ctr k s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S6S5A2S29Vg;Vidx;Vn;Vctr;Vk;Vs;A6S6bS6Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold enframe. ctauto. Qed.
  Hint Resolve ct_enframe : ct.

  Lemma ct_install_group c b m sc cnt aidx maplen mem sl s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S57S5A2S48Vm;Vsc;Vcnt;Vaidx;Vmaplen;Vmem;Vsl;Vs;A8S6bS57Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold install_group. ctauto. Qed.
  Hint Resolve ct_install_group : ct.

  Lemma ct_forget_frame c b g i s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S57S5A2S2bVg;Vi;Vs;A3S6bS57Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold forget_frame. ctauto. Qed.
  Hint Resolve ct_forget_frame : ct.

  Lemma ct_release_slot c b g i s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S57S5A2S32Vg;Vi;Vs;A3S6bS57Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold release_slot. ctauto. Qed.
  Hint Resolve ct_release_slot : ct.

  Lemma ct_find_frame c b p s : ltac2:(tb__ "0|1|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S56S6S67A2M0S5A2S2aVp;Vs;A2S6bG0Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold find_frame. ctauto. Qed.
  Hint Resolve ct_find_frame : ct.

  Lemma ct_nontrivial_free fuel c b g i s : ltac2:(tb__ "0|1|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S59S56S5bS67A2A1M0S5A2S2fVfuel;Vg;Vi;Vs;A4S6bG0Vc;Vb;A3A3F_;F_;").
  Proof.
    revert c b g i s. induction fuel as [|f IH]; intros c b g i s E1 E2; [cbn; exact I|].
    cbn fix beta iota delta [nontrivial_free]. ctauto.
  Qed.
  Hint Resolve ct_nontrivial_free : ct.

  Theorem ct_free c b p s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S57S5A2S1dVp;Vs;A2S6bS57Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold free. ctauto. Qed.

  Definition cqm (hd : option sptr) (c : Z) (r : option sptr * astate) : Prop := ltac2:(tb__ "0|9|
S1S0S58S8S64S59S6A1M0S5Vr;A3M1A1S5cA3S1S71Z0M2S7G1A1M3A2S1S0G0S5eG0S5Vr;A3S60S6A1M4A3M5S0S67G3Vc;A3M6F_;S2G5A1S3S1S2S0G0Vhd;G4A3M7A1G6A2S3S1G7S1S72G2Vc;A2S0S67G3S78Vc;Z1M8A2A3A2A2S1G7S1S71Vc;G2A2S0S67G3S78S22G8A2A3A2A2A2A2F_;A2A2A2").

  Lemma ct_area_from_brk c b s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S58S5A2S1aVs;A1S6bS58Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold area_from_brk. ctauto. Qed.
  Hint Resolve ct_area_from_brk : ct.

  Lemma ct_area_from_mmap c b s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S58S5A2S1bVs;A1S6bS58Vc;Vb;A3A3F_;F_;").
  Proof. intros E1 E2. unfold area_from_mmap. ctauto. Qed.
  Hint Resolve ct_area_from_mmap : ct.

  Lemma ct_open_area c b nu s : ltac2:(tb__ "0|2|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S68S56S58S5A2M0S1fVnu;Vs;A2G0S1S0S58S5eS58S5R1A3M1S5cA3S6bS58S22Vb;R2A4F_;S0S58G1S65A3S6bS58Vc;Vb;R2A4F_;A2Lr;A3F_;F_;").
  Proof.
    intros E1 E2. unfold open_area. ctauto.
    all: try (split; [intros _ | intros; discriminate]); try (split; [intros; discriminate | intros _]);
         unfold cq; cq_unf; split; first [assumption | reflexivity | congruence].
  Qed.

  Theorem ct_alloc_meta c b s : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1Vb;A3S71Z0Vc;A2S68S56S59S6A1S5A2S15Vs;A1S6fSdVs;A1Vc;A2A3F_;F_;F_;").
  Proof.
    intros E1 E2 Hc. unfold alloc_meta, dequeue_head. ctauto; cbn [st_free_meta_head st_avail_meta_count set_init_done] in Heqo.
    -
      unfold cqm. cq_unf. split; [assumption|]. split; [lia|]. split; [intros; discriminate|].
      intros _. left. split; [congruence | assumption].
    -
      cbn [st_avail_meta_count set_init_done] in Heqb0. apply Z.ltb_lt in Heqb0.
      unfold cqm. cq_unf. split; [reflexivity|]. split; [lia|]. split; [intros; discriminate|].
      intros _. right. left. split; [assumption | split; [lia | lia]].
    -
      cbn [st_avail_meta_count set_init_done] in Heqb0. apply Z.ltb_ge in Heqb0.
      eapply ct_conseq; [apply (ct_open_area c true b0 a0); assumption|].
      intros [ok s2] [OK KO]. cbn [fst snd] in *. destruct ok; cbn [negb].
      + destruct (OK eq_refl) as [C2 I2]. cbn [fst snd] in C2, I2. ctauto.
        unfold cqm. cq_unf. rewrite C2. split; [assumption|]. split; [unfold METAS_PER_AREA; lia|]. split; [intros; discriminate|].
        intros _. right. right. split; [assumption | split; [lia | reflexivity]].
      + destruct (KO eq_refl) as [C2 I2]. cbn [fst snd] in C2, I2. ctauto.
        unfold cqm. cq_unf. split; [assumption|]. split; [lia|]. split; [intros _; assumption|]. intros X. exfalso. apply X. reflexivity.
    -
      unfold cqm. cq_unf. split; [assumption|]. split; [lia|]. split; [intros _; assumption|]. intros X. exfalso. apply X. reflexivity.
  Qed.
  Hint Resolve ct_alloc_meta : ct.

  Definition cqd {A} (c : Z) (r : A * astate) : Prop :=
    st_init_done (snd r) = true /\ 0 <= st_avail_meta_count (snd r) /\ c - 1 <= st_avail_meta_count (snd r).

  Theorem ct_malloc_direct c s n : ltac2:(tb__ "0|1|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1S5cA3S71Z0Vc;A2S71S23Vn;A2S68S56S59S6A1M0S5A2S12Vn;Vs;A2S6eG0Vc;A2A3F_;F_;F_;F_;").
  Proof.
    intros E1 E2 Hc Hn. unfold malloc.
    destruct (size_overflows n) eqn:Eov.
    { apply ct_ret. unfold cqd. cq_unf. rewrite E1, E2. repeat split; [lia|lia]. }
    rewrite (proj2 (Z.leb_le _ _) Hn). ctauto.
    all: unfold cqd; cq_unf; cbn [fst snd] in *; rewrite ?E1, ?E2.
    1: repeat split; lia.
    all: match goal with H : cqm _ _ _ |- _ => destruct H as (I1 & C1 & N1 & S1); cbn [fst snd] in I1, C1, N1, S1 end.
    1: destruct (S1 ltac:(discriminate)) as [[_ E]|[(_ & _ & E)|(_ & Hc0 & E)]]; unfold METAS_PER_AREA in *; repeat split; first [congruence | lia].
    all: specialize (N1 eq_refl); repeat split; first [congruence | lia].
  Qed.

  Theorem ct_free_d c s p : ltac2:(tb__ "0|0|
S0S67S7Vs;A1Vc;A3S0S58S8Vs;A1S5cA3S71Z0Vc;A2S68S56S57S5A2S1dVp;Vs;A2S6eS57S73Vc;Z1A2A2A3F_;F_;F_;").
  Proof.
    intros E1 E2 Hc. eapply ct_conseq; [apply (ct_free c true p s E1 E2)|].
    intros [[] s'] [C I]. unfold cqd. cbn [fst snd] in *. rewrite C, I. repeat split; lia.
  Qed.

Ltac evalc x := let v := eval vm_compute in x in change x with v.

Lemma initial_cnt_44 u : ltac2:(tb__ "0|1|
S3S0S67S1eZ2cVu;A2M0ZeA3S0S67G0Z7A3A2").
Proof.
  unfold initial_cnt. change (44 <? 9) with false. cbn iota.
  change (znth (Z.land 44 3) med_cnt_tab) with 28.
  unfold halve_while_even.
  change (Z.even 28) with true. cbn [andb].
  destruct (u <? 4 * 28).
  - change (28 / 2) with 14. change (Z.even 14) with true. cbn [andb].
    destruct (u <? 4 * 14).
    + change (14 / 2) with 7. change (Z.even 7) with false. cbn [andb].
      right. vm_compute. reflexivity.
    + left. vm_compute. reflexivity.
  - left. vm_compute. reflexivity.
Qed.

Lemma group_44_big u : ltac2:(tb__ "0|1|
S0S58S7aS76S3aZ2A2S73S7bS41Z2cM0A1S1eG0Vu;A2A2S3bA2A2S5cA3").
Proof. destruct (initial_cnt_44 u) as [E|E]; rewrite E; vm_compute; reflexivity. Qed.

Lemma ct_init_slot f s : ltac2:(tb__ "0|5|
S0S67S7Vs;A1Z0M0A3S0S59S6A1M1SdVs;A1S60S6A1M2A3S0G1S80G1S75Z2cM3A1S14Vs;A1G2A4G2A3S68S56S67S5A2M4S26S62S62Vf;A1A1G3Z10000Vs;A4G4S71G0S5eS67S5R1A3A2S6bS67Z64S5cR2A4F_;Lr;A3F_;F_;F_;").
Proof.
  intros Hc Hhd H44.
  cbn fix beta iota delta [alloc_slot].
  apply ct_bind. unfold try_avail, get_head. apply ct_bind. apply ct_bind. apply ct_get. cbn beta iota delta [fst snd].
  apply ct_ret. cbn beta iota delta [fst snd]. rewrite H44. apply ct_ret. cbn beta iota zeta delta [fst snd negb Z.eqb].
  ctauto. cbn fix beta iota delta [alloc_group]. ctauto.
  all: cbn [fst snd] in *.
  all: try (exfalso; lia).
  all: try match goal with H : (PGSZ / 2 <? _) = false |- _ => rewrite group_44_big in H; discriminate H end.
  all: unfold cqm in *; cbn [fst snd] in *.
  all: try (exfalso; lia).
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : Some _ <> None -> _ |- _ =>
    destruct (H ltac:(discriminate)) as [[X _]|[(_ & X & _)|(_ & _ & CX)]];
    [exfalso; exact (X Hhd) | exfalso; lia | unfold METAS_PER_AREA in CX; unfold cq; cbn [fst snd]; split; [lia | congruence]] end.
Qed.

Lemma ct_malloc_first s : ltac2:(tb__ "0|3|
S0S67S7Vs;A1Z0A3S0S59S6A1M0SdVs;A1S60S6A1M1A3S0G0S80G0S75Z2cA1S14Vs;A1G1A4G1A3S68S56G0S5A2M2S12Z10000Vs;A2G2S2S0G0S5eG0S5R1A3G1A3A1S6bG0Z64S5cR2A4F_;Lr;A3F_;F_;F_;").
Proof.
  intros Hc Hhd H44.
  unfold malloc. evalc (size_overflows 65536). evalc (MMAP_THRESHOLD <=? 65536). cbn iota.
  apply ct_bind. apply ct_get. cbn beta iota zeta delta [fst snd].
  evalc (size_to_class 65536). rewrite !H44. evalc (4 <=? 44). evalc (44 <? 32). cbn beta iota zeta delta [andb osptr_eqb].
  rewrite !H44. change NEST_FUEL with (S (S 62%nat)).
  apply ct_bind. apply ct_ret. cbn beta iota zeta delta [fst snd]. apply ct_bind. apply ct_bind.
  eapply ct_conseq; [apply (ct_init_slot 62 s Hc Hhd H44)|].
  intros [idx s1] HP. cbn beta iota zeta delta [fst snd] in *.
  destruct (idx <? 0) eqn:Hidx.
  - ctauto.
  - apply Z.ltb_ge in Hidx. destruct (HP Hidx) as [C1 I1]. cbn [fst snd] in C1, I1. ctauto.
Qed.

Definition gfull (am : ameta) : Prop := ltac2:(tb__ "0|2|
S1S0S67S16Vam;A1Z0M0A3S1S0S67S17Vam;A1G0A3S1S0S67S10Vam;A1G0A3S1S0S5bS5fSeS11Vam;A1A2U1A3S1S2S0S67S18Vam;A1G0A3A1S3S0S67S19Vam;A1M1Z2cA3S0S67G1Z3fA3A2A2A2A2A2A2").
Definition full_all (s : astate) : Prop := ltac2:(tb__ "0|0|
S6SaS7fS56S6S9A2S5aS6S9R2ScR1A1A4SfVs;A1A3S6cR2A1F_;Fam;Fg;").
Definition fq {A} (r : A * astate) : Prop := full_all (snd r).

Lemma In_mupdate_weak l p x e : ltac2:(tb__ "0|1|
S7fS56S6S9A2M0Ve;S2eVl;Vp;Vx;A3A3S3S0G0Ve;S5aS6S9Vp;Vx;A4A3S7fG0Ve;Vl;A3A2F_;").
Proof.
  induction l as [|[q y] t IH]; cbn.
  - intros [H|[]]. left. symmetry. exact H.
  - destruct (sptr_eqb p q) eqn:E; cbn.
    + apply sptr_eqb_eq in E. subst q. intros [H|H]; [left; symmetry; exact H | right; right; exact H].
    + intros [H|H]; [right; left; exact H|]. destruct (IH H) as [H'|H']; [left; exact H' | right; right; exact H'].
Qed.

Lemma mlookup_In l p x : ltac2:(tb__ "0|0|
S0S59S9A1S4cVl;Vp;A2S63S9Vx;A2A3S7fS56S6S9A2S5aS6S9Vp;Vx;A4Vl;A3F_;").
Proof.
  induction l as [|[q y] t IH]; cbn; [discriminate|].
  destruct (sptr_eqb p q) eqn:E; intros H.
  - apply sptr_eqb_eq in E. injection H as <-. subst. left. reflexivity.
  - right. apply IH, H.
Qed.

Lemma full_all_upd s p x : ltac2:(tb__ "0|0|
S69Vs;A1SaS0S9Vx;ScR1A1A3S6cR2A1F_;Fam;S69S33S2eSfVs;A1Vp;Vx;A3Vs;A2A1F_;F_;").
Proof.
  intros F Hx g am Hin. cbn in Hin. destruct (In_mupdate_weak _ _ _ _ Hin) as [E|H].
  - injection E as -> E2. apply Hx. symmetry. exact E2.
  - exact (F g am H).
Qed.

Lemma gfull_links pr nx am : ltac2:(tb__ "0|0|
S6cVam;A1S6cS3cVpr;Vnx;Vam;A3A1F_;").
Proof. intros G. destruct am. exact G. Qed.
Lemma gfull_with_links x pr nx am : ltac2:(tb__ "0|0|
SaS0S9Vx;ScR1A1A3S6cR2A1F_;Fam0;S0S9S55Vx;Vpr;Vnx;A3ScVam;A1A3S6cVam;A1F_;F_;").
Proof.
  intros Hx E. destruct x as [| |am0]; cbn in E; try discriminate. injection E as <-. apply gfull_links. apply Hx. reflexivity.
Qed.

Definition unMUsed (x : mslot) (d : ameta) : ameta := match x with MUsed a => a | _ => d end.
Lemma MUsed_inj am am' : ltac2:(tb__ "0|0|
S0S9ScVam;A1ScVam';A1A3S0SaVam;Vam';A3F_;").
Proof. intros E. exact (f_equal (fun x => unMUsed x am) E). Qed.

Lemma gfull_mod am am' : ltac2:(tb__ "0|1|
S6cVam;A1S0S67S16Vam';A1Z0M0A3S0S67S17Vam';A1G0A3S0S67S10Vam';A1S10Vam;A1A3S0S5bS5fSeS11Vam';A1A2S5fSeS11Vam;A1A2A3S0S67S18Vam';A1S18Vam;A1A3S0S67S19Vam';A1S19Vam;A1A3S6cVam';A1F_;F_;F_;F_;F_;F_;F_;").
Proof. intros (G1 & G2 & G3 & G4 & G5 & G6) E1 E2 E3 E4 E5 E6. unfold gfull. rewrite E1, E2, E3, E4, E5, E6. repeat split; assumption. Qed.

Lemma length_lupd {T} (l : list T) i v : ltac2:(tb__ "0|0|
S0S5bS5fVT;S49VT;Vl;Vi;Vv;A4A2S5fVT;Vl;A2A3").
Proof. revert i. induction l as [|x t IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Ltac am_cbn := cbn [am_avail am_freed am_last am_slots am_maplen am_sc am_prev am_next am_mem am_aidx
                    am_set_aidx am_set_avail am_set_freed am_set_links am_set_prev am_set_next am_set_slots upd_slot].
Ltac gfull_solve Gpf :=
  let G := fresh "G" in pose proof Gpf as G;
  apply (gfull_mod _ _ G); am_cbn; rewrite ?(proj1 G), ?(proj1 (proj2 G)); cbn [Z.land Z.ldiff];
  first [reflexivity | congruence | lia | apply length_lupd].

Lemma full_all_same s s' : ltac2:(tb__ "0|0|
S0S5dS56S6S9A2A1SfVs';A1SfVs;A1A3S69Vs;A1S69Vs';A1F_;F_;").
Proof. intros E F g am Hin. rewrite E in Hin. exact (F g am Hin). Qed.

Lemma page_round_pages_ne0 x : ltac2:(tb__ "0|1|
S72Z0M0Vx;A2S2S0S67S76S51Vx;A1Z1000A2G0A3A1F_;").
Proof.
  intros Hx. unfold page_round, PGSZ. rewrite Z.div_mul by lia.
  assert (1 <= (x + 4096 - 1) / 4096) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Ltac fq_new :=
  let am' := fresh "am'" in let E := fresh "E" in intros am' E;
  first [ discriminate E
        | apply MUsed_inj in E; subst am';
          first [ unfold gfull; cbn -[page_round Z.add Z.mul Z.div Z.sub];
                  repeat split; first [lia | reflexivity | apply page_round_pages_ne0; unfold IB, UNIT; lia | (right; reflexivity) | (left; reflexivity)]
                | match goal with
                  | F : full_all ?s0, H : MT _ ?g = Some (MUsed ?am) |- gfull _ => gfull_solve (F g am (mlookup_In _ _ _ H))
                  | F : full_all ?s0, H : In (?g, MUsed ?am) _ |- gfull _ => gfull_solve (F g am H)
                  end ] ].

Ltac fq_full :=
  first [ assumption
        | apply full_all_upd; [assumption | fq_new]
        | match goal with |- full_all (_ _ ?S) =>
            apply (full_all_same S); [reflexivity | first [assumption | apply full_all_upd; [assumption | fq_new]]] end ].

Ltac fq_leaf := unfold fq; cbn [fst snd]; fq_full.

Create HintDb ft.
Hint Extern 2 (full_all _) => fq_full : ft.

Ltac ft_conseq_step :=
  let HQ := fresh "HQ" in
  eapply ct_conseq; [solve [eauto 4 with ft nocore] | intros [? ?] HQ;
    lazymatch type of HQ with
    | _ /\ _ = _ => let EQ := fresh "EQ" in destruct HQ as [HQ EQ]; cbn [fst snd] in EQ; try subst
    | _ => idtac
    end;
    lazymatch type of HQ with
    | cq _ _ _ => unfold cq in HQ; cbn [fst snd] in HQ; destruct HQ as [? ?]
    | _ => try unfold fq in HQ; cbn [fst snd] in HQ
    end ].

Ltac ftstep :=
  lazymatch goal with
  | |- ct (bind _ _ _) _ => apply ct_bind
  | |- ct (ret _ _) _ => apply ct_ret
  | |- ct (get _) _ => apply ct_get
  | |- ct (put _ _) _ => apply ct_put
  | |- ct (modify _ _) _ => apply ct_modify
  | |- ct (setm _ _ _) _ => unfold setm at 1; apply ct_modify
  | |- ct (setslot _ _ _) _ => unfold setslot at 1; apply ct_modify
  | |- ct (set_usage_of _ _ _) _ => unfold set_usage_of at 1; apply ct_modify
  | |- ct (set_head _ _ _) _ => unfold set_head at 1
  | |- ct (get_head _ _) _ => unfold get_head at 1
  | |- ct (getm _ _) _ => apply ct_getm; intros ? ?
  | |- ct (get_links _ _) _ => apply ct_get_links; intros ?
  | |- ct (set_links _ _ _ _) (fun _ => ct _ _) => first [ft_conseq_step | apply ct_set_links; intros ?]
  | |- ct (set_links _ _ _ _) _ => first [solve [eauto 4 with ft nocore] | apply ct_set_links; intros ?]
  | |- ct (set_prev _ _ _) _ => unfold set_prev at 1
  | |- ct (set_next _ _ _) _ => unfold set_next at 1
  | |- ct (massert _ _ _) _ => let Hm := fresh "Hm" in apply ct_massert; intros Hm; try (exfalso; discriminate Hm)
  | |- ct (mcheck _ _ _) _ => apply ct_mcheck; intros ?
  | |- ct (ask _ _) _ => let z := fresh "z" in apply ct_ask; intros z; destruct (z =? 0); cbn [negb]
  | |- ct (askz _ _) _ => apply ct_askz; intros ?
  | |- ct (fail _ _) _ => apply ct_fail
  | |- ct (IFail _) _ => exact I
  | |- ct (IRet _) _ => cbn [ct]
  | |- ct (match ?x with _ => _ end _) _ => destruct x eqn:?
  | |- ct (match ?x with _ => _ end) _ => destruct x eqn:?
  | |- ct _ (fun _ => ct _ _) => ft_conseq_step
  | |- ct _ _ => solve [eauto 4 with ft nocore]
  | |- cq _ _ _ => unfold cq; cq_unf; solve [split; first [assumption | congruence | reflexivity | auto] ]
  | |- True => exact I
  | |- forall _, _ => intros ?
  | |- _ => solve [fq_leaf]
  end.
Ltac ftauto := repeat (cbn beta iota zeta delta [fst snd negb andb orb]; ftstep).

Lemma ft_get_links_used p s (Q : (option sptr * option sptr) * astate -> Prop) : ltac2:(tb__ "0|2|
S56S59S6A1M0G0A2M1VQ;S5aG1S5R1Vs;A4A1Fl;S68S56G1S5A2S2dVp;Vs;A2VQ;A3F_;").
Proof. apply ct_get_links. Qed.

Lemma ft_set_links p pr nx s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S20Vp;Vpr;Vnx;Vs;A4S6aS57A1A3F_;").
Proof.
  intros F. unfold set_links. apply ct_bind. apply ct_get. cbn [fst snd].
  destruct (mlookup (st_metas s) p) as [x|] eqn:M; [|exact I].
  unfold setslot. apply ct_modify. unfold fq. cbn [fst snd]. apply full_all_upd; [exact F|].
  intros am E. apply (gfull_with_links x pr nx am); [|exact E]. intros am0 ->. exact (F p am0 (mlookup_In _ _ _ M)).
Qed.
Hint Resolve ft_set_links : ft.

Lemma ft_set_prev p pr s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S35Vp;Vpr;Vs;A3S6aS57A1A3F_;").
Proof. intros F. unfold set_prev. ftauto. Qed.
Lemma ft_set_next p nx s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S34Vp;Vnx;Vs;A3S6aS57A1A3F_;").
Proof. intros F. unfold set_next. ftauto. Qed.
Hint Resolve ft_set_prev ft_set_next : ft.

Lemma ft_queue h m s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S30Vh;Vm;Vs;A3S6aS57A1A3F_;").
Proof. intros F. unfold queue. ftauto. all: destruct h; ftauto. Qed.
Hint Resolve ft_queue : ft.

Lemma ft_dequeue h m s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S1cVh;Vm;Vs;A3S6aS57A1A3F_;").
Proof. intros F. unfold dequeue. ftauto; destruct h; ftauto. Qed.
Hint Resolve ft_dequeue : ft.

Lemma ft_dequeue_head h s : ltac2:(tb__ "0|1|
S69Vs;A1S68S56S59S6A1M0S5A2S28Vh;Vs;A2S6aG0A1A3F_;").
Proof. intros F. unfold dequeue_head. destruct h; ftauto. Qed.
Hint Resolve ft_dequeue_head : ft.

Lemma ft_free_meta m s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S2cVm;Vs;A2S6aS57A1A3F_;").
Proof. intros F. unfold free_meta. ftauto. Qed.
Hint Resolve ft_free_meta : ft.

Lemma ft_step_seq s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S36Vs;A1S6aS57A1A3F_;").
Proof. intros F. unfold step_seq. ftauto. destruct (st_seq s =? 255); exact F. Qed.
Hint Resolve ft_step_seq : ft.

Lemma ft_record_seq sc s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S31Vsc;Vs;A2S6aS57A1A3F_;").
Proof. intros F. unfold record_seq. destruct (bounce_idx sc); ftauto. Qed.
Hint Resolve ft_record_seq : ft.

Lemma ft_account_bounce sc s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S24Vsc;Vs;A2S6aS57A1A3F_;").
Proof. intros F. unfold account_bounce. destruct (bounce_idx sc); ftauto. destruct (negb _ && _); exact F. Qed.
Hint Resolve ft_account_bounce : ft.

Lemma ft_decay_bounces sc s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S27Vsc;Vs;A2S6aS57A1A3F_;").
Proof. intros F. unfold decay_bounces. destruct (bounce_idx sc); ftauto. destruct (_ =? 0); exact F. Qed.
Hint Resolve ft_decay_bounces : ft.

Lemma ft_new_region k len s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S5bS5A2S13Vk;Vlen;Vs;A3S6aS5bA1A3F_;").
Proof. intros F. unfold new_region. ftauto. Qed.
Hint Resolve ft_new_region : ft.

Lemma ft_upd_region r f s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S21Vr;Vf;Vs;A3S6aS57A1A3F_;").
Proof. intros F. unfold upd_region. ftauto. Qed.
Hint Resolve ft_upd_region : ft.

Lemma ft_activate_group m s : ltac2:(tb__ "0|1|
S69Vs;A1S68S56S67S5A2M0S25Vm;Vs;A2G0S1S6aS67R1A2S0S67S5eS67S5R1A3Z0A3A2Lr;A3F_;").
Proof.
  intros F. unfold activate_group. ftauto.
  match goal with H : MT _ ?g = Some (MUsed ?am) |- _ => pose proof (F g am (mlookup_In _ _ _ H)) as G end.
  split; [fq_leaf|]. cbn [fst]. rewrite (proj1 (proj2 G)). reflexivity.
Qed.
Hint Resolve ft_activate_group : ft.

Lemma ft_try_avail sc s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S67S5A2S37Vsc;Vs;A2S6aS67A1A3F_;").
Proof. intros F. unfold try_avail. ftauto. Qed.
Hint Resolve ft_try_avail : ft.

Lemma ft_enframe g idx n ctr k s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S6S5A2S29Vg;Vidx;Vn;Vctr;Vk;Vs;A6S6aS6A1A3F_;").
Proof.
  intros F. unfold enframe. ftauto.
Qed.
Hint Resolve ft_enframe : ft.

Lemma ft_forget_frame g i s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S2bVg;Vi;Vs;A3S6aS57A1A3F_;").
Proof.
  intros F. unfold forget_frame. ftauto.
Qed.
Hint Resolve ft_forget_frame : ft.

Lemma ft_release_slot g i s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S32Vg;Vi;Vs;A3S6aS57A1A3F_;").
Proof.
  intros F. unfold release_slot. ftauto.
Qed.
Hint Resolve ft_release_slot : ft.

Lemma find_in_slots_range sl base st i0 p i : ltac2:(tb__ "0|0|
S0S59S67A1S44Vsl;Vbase;Vst;Vi0;Vp;A5S63S67Vi;A2A3S1S71Vi0;Vi;A2S72Vi;S73Vi0;S74S5fSeVsl;A2A1A2A2A2F_;").
Proof.
  revert i0. induction sl as [|x t IH]; intros i0 H; cbn in H; [discriminate|].
  cbn [length]. rewrite Nat2Z.inj_succ.
  destruct (ss_fr x) as [fr|].
  - destruct (sptr_eqb _ _); [injection H as <-; lia|]. specialize (IH _ H). lia.
  - specialize (IH _ H). lia.
Qed.

Lemma find_frame_in_facts l p g i : ltac2:(tb__ "0|1|
S0S59S56S6S67A2M0A1S43Vl;Vp;A2S63G0S5aS6S67Vg;Vi;A4A2A3S4SaSaS1S7fS56S6S9A2S5aS6S9Vg;ScR1A1A4Vl;A3S1S71Z0Vi;A2S72Vi;S74S5fSeS11R1A1A2A1A2A2A2Lam;A2F_;").
Proof.
  induction l as [|[q x] t IH]; cbn; intros H; [discriminate|].
  destruct x as [pr nx| |am].
  - destruct (IH H) as (am & Hin & Hi). exists am. split; [right; exact Hin | exact Hi].
  - destruct (IH H) as (am & Hin & Hi). exists am. split; [right; exact Hin | exact Hi].
  - destruct (find_in_slots (am_slots am) (padd (am_mem am) UNIT) (stride_of am) 0 p) as [j|] eqn:E.
    + injection H as <- <-. exists am. split; [left; reflexivity|]. pose proof (find_in_slots_range _ _ _ _ _ _ E). lia.
    + destruct (IH H) as (am' & Hin & Hi). exists am'. split; [right; exact Hin | exact Hi].
Qed.

Lemma ft_find_frame p s : ltac2:(tb__ "0|2|
S69Vs;A1S68S56S56S6S67A2M0S5A2M1S2aVp;Vs;A2G1S1S6aG0R1A2S1S0S5S64G0S5R1A3Vs;A3S1S4SaSaS7fS56S6S9A2S5aS6S9S5eS6S67S5eG0S5R2A3A3ScR1A1A4SfVs;A1A3Lam;A2S0S67S64S6S67S5eG0S5R1A3A3Z0A3A2A2A2Lr;A3F_;").
Proof.
  intros F. unfold find_frame. apply ct_bind. apply ct_get. cbn [fst snd].
  destruct (find_frame_in (st_metas s) p) as [[g i]|] eqn:E; [|exact I].
  apply ct_ret. cbn [fst snd]. destruct (find_frame_in_facts _ _ _ _ E) as (am & Hin & Hi).
  pose proof (F g am Hin) as (_ & _ & _ & Hlen & _). rewrite Hlen in Hi. cbn in Hi.
  split; [exact F|]. split; [reflexivity|]. split; [exists am; exact Hin | lia].
Qed.

Lemma mask_full am : ltac2:(tb__ "0|0|
S6cVam;A1S0S58S77S73S79S17Vam;A1S16Vam;A1A2S40Z0A1A2S50S10Vam;A1A1A2S5cA3F_;").
Proof. intros (G1 & G2 & G3 & _). rewrite G1, G2, G3. reflexivity. Qed.
Lemma okay_to_free_full s g am : ltac2:(tb__ "0|0|
S6cVam;A1S0S58S4fVs;Vg;Vam;A3S5cA3F_;").
Proof.
  intros (G1 & G2 & G3 & G4 & G5 & [G6|G6]); unfold okay_to_free; rewrite G6; [|reflexivity].
  cbn [Z.leb orb]. destruct (stride_of am <? class_size 44); [reflexivity|].
  destruct (am_maplen am =? 0); [reflexivity|]. destruct (negb (osptr_eqb (am_next am) (Some g))); [reflexivity|]. reflexivity.
Qed.

Ltac pose_gfulls := repeat match goal with
  | F : full_all _, H : MT _ ?g = Some (MUsed ?am) |- _ =>
      lazymatch goal with
      | G : gfull am |- _ => fail
      | _ => pose proof (F g am (mlookup_In _ _ _ H))
      end
  end.

Lemma ft_nontrivial_free fuel g s : ltac2:(tb__ "0|1|
S69Vs;A1S68S56S59S56S5bS67A2A1M0S5A2S2fVfuel;Vg;Z0Vs;A4S6aG0A1A3F_;").
Proof.
  intros F. destruct fuel as [|f]; [exact I|].
  cbn fix beta iota delta [nontrivial_free]. ftauto.
  all: pose_gfulls.

  all: try match goal with Hb : negb (am_maplen ?am =? 0) = false, G : gfull ?am |- _ =>
         exfalso; apply (proj1 (proj2 (proj2 (proj2 (proj2 G))))); apply Z.eqb_eq; destruct (am_maplen am =? 0); [reflexivity | discriminate Hb] end.

  all: try match goal with Hb : (_ && okay_to_free _ _ ?am)%bool = false, G : gfull ?am |- _ =>
         exfalso; rewrite (mask_full am G), (okay_to_free_full _ _ am G) in Hb; discriminate Hb end.
Qed.
Hint Resolve ft_nontrivial_free : ft.

Theorem ft_free p s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S57S5A2S1dVp;Vs;A2S6aS57A1A3F_;").
Proof.
  intros F. unfold free. destruct p as [p|]; [|apply ct_ret; exact F].
  apply ct_bind. eapply ct_conseq; [apply (ft_find_frame p s F)|].
  intros [[g i] s'] (F' & Es & (am & Hin) & Hi). cbn [fst snd] in *. subst s' i.
  pose proof (F g am Hin) as G.
  ftauto.
  all: pose_gfulls.
  all: try match goal with Hb : (negb (am_freed ?am =? 0) && _)%bool = true, G : gfull ?am |- _ =>
         exfalso; rewrite (proj1 (proj2 G)) in Hb; discriminate Hb end.
Qed.

Lemma ft_area_from_brk s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S58S5A2S1aVs;A1S6aS58A1A3F_;").
Proof. intros F. unfold area_from_brk. ftauto. Qed.
Lemma ft_area_from_mmap s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S58S5A2S1bVs;A1S6aS58A1A3F_;").
Proof. intros F. unfold area_from_mmap. ftauto. Qed.
Lemma ft_open_area nu s : ltac2:(tb__ "0|0|
S69Vs;A1S68S56S58S5A2S1fVnu;Vs;A2S6aS58A1A3F_;").
Proof. intros F. unfold open_area. ftauto. Qed.
Hint Resolve ft_area_from_brk ft_area_from_mmap ft_open_area : ft.
Lemma ft_alloc_meta s : ltac2:(tb__ "0|1|
S69Vs;A1S68S56S59S6A1M0S5A2S15Vs;A1S6aG0A1A3F_;").
Proof. intros F. unfold alloc_meta. ftauto. Qed.
Hint Resolve ft_alloc_meta : ft.

Theorem ft_malloc_direct s n : ltac2:(tb__ "0|1|
S69Vs;A1S71S23Vn;A2S68S56S59S6A1M0S5A2S12Vn;Vs;A2S6aG0A1A3F_;F_;").
Proof.
  intros F Hn. unfold malloc.
  destruct (size_overflows n) eqn:Eov; [apply ct_ret; exact F|].
  rewrite (proj2 (Z.leb_le _ _) Hn). unfold MMAP_THRESHOLD in Hn. ftauto.
Qed.

Definition uq (u0 : list Z) {A} (r : A * astate) : Prop := st_usage (snd r) = u0.
Ltac uq_leaf := unfold uq; cbn [snd st_usage set_init_done set_mmap_counter set_free_meta_head set_avail_meta set_avail_meta_count
               set_avail_meta_area_count set_meta_alloc_shift set_area_head set_area_tail set_avail_meta_areas
               set_active set_usage set_unmap_seq set_bounces set_seq set_brk set_metas set_regions set_areas]; first [assumption | congruence].
Create HintDb ut.
Hint Extern 1 (st_usage _ = _) => uq_leaf : ut.

Ltac ut_conseq_step :=
  let HQ := fresh "HQ" in
  eapply ct_conseq; [solve [eauto 4 with ut nocore] | intros [? ?] HQ;
    lazymatch type of HQ with
    | _ /\ _ = _ => let EQ := fresh "EQ" in destruct HQ as [HQ EQ]; cbn [fst snd] in EQ; try subst
    | _ => idtac
    end;
    lazymatch type of HQ with
    | cq _ _ _ => unfold cq in HQ; cbn [fst snd] in HQ; destruct HQ as [? ?]
    | _ => try unfold uq in HQ; cbn [fst snd] in HQ
    end ].

Ltac utstep :=
  lazymatch goal with
  | |- ct (bind _ _ _) _ => apply ct_bind
  | |- ct (ret _ _) _ => apply ct_ret
  | |- ct (get _) _ => apply ct_get
  | |- ct (put _ _) _ => apply ct_put
  | |- ct (modify _ _) _ => apply ct_modify
  | |- ct (setm _ _ _) _ => unfold setm at 1; apply ct_modify
  | |- ct (setslot _ _ _) _ => unfold setslot at 1; apply ct_modify
  | |- ct (set_usage_of _ _ _) _ => unfold set_usage_of at 1; apply ct_modify
  | |- ct (set_head _ _ _) _ => unfold set_head at 1
  | |- ct (get_head _ _) _ => unfold get_head at 1
  | |- ct (getm _ _) _ => apply ct_getm; intros ? ?
  | |- ct (get_links _ _) _ => apply ct_get_links; intros ?
  | |- ct (set_links _ _ _ _) (fun _ => ct _ _) => first [ut_conseq_step | apply ct_set_links; intros ?]
  | |- ct (set_links _ _ _ _) _ => first [solve [eauto 4 with ut nocore] | apply ct_set_links; intros ?]
  | |- ct (set_prev _ _ _) _ => unfold set_prev at 1
  | |- ct (set_next _ _ _) _ => unfold set_next at 1
  | |- ct (massert _ _ _) _ => let Hm := fresh "Hm" in apply ct_massert; intros Hm; try (exfalso; discriminate Hm)
  | |- ct (mcheck _ _ _) _ => apply ct_mcheck; intros ?
  | |- ct (ask _ _) _ => let z := fresh "z" in apply ct_ask; intros z; destruct (z =? 0); cbn [negb]
  | |- ct (askz _ _) _ => apply ct_askz; intros ?
  | |- ct (fail _ _) _ => apply ct_fail
  | |- ct (IFail _) _ => exact I
  | |- ct (IRet _) _ => cbn [ct]
  | |- ct (match ?x with _ => _ end _) _ => destruct x eqn:?
  | |- ct (match ?x with _ => _ end) _ => destruct x eqn:?
  | |- ct _ (fun _ => ct _ _) => ut_conseq_step
  | |- ct _ _ => solve [eauto 4 with ut nocore]
  | |- cq _ _ _ => unfold cq; cq_unf; solve [split; first [assumption | congruence | reflexivity | auto] ]
  | |- True => exact I
  | |- forall _, _ => intros ?
  | |- _ => solve [uq_leaf]
  end.
Ltac utauto := repeat (cbn beta iota zeta delta [fst snd negb andb orb]; utstep).

Section Usage.
  Variable u0 : list Z.
  Lemma ut_set_links p pr nx s : ltac2:(tb__ "0|0|
S0S5dS67A1SbVs;A1Vu0;A3S68S56S57S5A2S20Vp;Vpr;Vnx;Vs;A4S6dVu0;S57A2A3F_;").
  Proof using . intros E. unfold set_links, setslot. utauto. Qed.
  Hint Resolve ut_set_links : ut.
  Lemma ut_set_prev p pr s : ltac2:(tb__ "0|0|
S0S5dS67A1SbVs;A1Vu0;A3S68S56S57S5A2S35Vp;Vpr;Vs;A3S6dVu0;S57A2A3F_;").
  Proof using . intros E. unfold set_prev. utauto. Qed.
  Lemma ut_set_next p nx s : ltac2:(tb__ "0|0|
S0S5dS67A1SbVs;A1Vu0;A3S68S56S57S5A2S34Vp;Vnx;Vs;A3S6dVu0;S57A2A3F_;").
  Proof using . intros E. unfold set_next. utauto. Qed.
  Hint Resolve ut_set_prev ut_set_next : ut.
  Lemma ut_dequeue_fm m s : ltac2:(tb__ "0|0|
S0S5dS67A1SbVs;A1Vu0;A3S68S56S57S5A2S1cS39Vm;Vs;A3S6dVu0;S57A2A3F_;").
  Proof using . intros E. unfold dequeue. utauto. Qed.
  Hint Resolve ut_dequeue_fm : ut.
  Lemma ut_new_region k len s : ltac2:(tb__ "0|0|
S0S5dS67A1SbVs;A1Vu0;A3S68S56S5bS5A2S13Vk;Vlen;Vs;A3S6dVu0;S5bA2A3F_;").
  Proof using . intros E. unfold new_region. utauto. Qed.
  Lemma ut_upd_region r f s : ltac2:(tb__ "0|0|
S0S5dS67A1SbVs;A1Vu0;A3S68S56S57S5A2S21Vr;Vf;Vs;A3S6dVu0;S57A2A3F_;").
  Proof using . intros E. unfold upd_region. utauto. Qed.
  Hint Resolve ut_new_region ut_upd_region : ut.
  Lemma ut_area_from_brk s : ltac2:(tb__ "0|0|
S0S5dS67A1SbVs;A1Vu0;A3S68S56S58S5A2S1aVs;A1S6dVu0;S58A2A3F_;").
  Proof using . intros E. unfold area_from_brk. utauto. Qed.
  Lemma ut_area_from_mmap s : ltac2:(tb__ "0|0|
S0S5dS67A1SbVs;A1Vu0;A3S68S56S58S5A2S1bVs;A1S6dVu0;S58A2A3F_;").
  Proof using . intros E. unfold area_from_mmap. utauto. Qed.
  Lemma ut_open_area nu s : ltac2:(tb__ "0|0|
S0S5dS67A1SbVs;A1Vu0;A3S68S56S58S5A2S1fVnu;Vs;A2S6dVu0;S58A2A3F_;").
  Proof using . intros E. unfold open_area. utauto. Qed.
  Hint Resolve ut_area_from_brk ut_area_from_mmap ut_open_area : ut.
  Theorem ut_alloc_meta s : ltac2:(tb__ "0|1|
S0S5dS67A1SbVs;A1Vu0;A3S68S56S59S6A1M0S5A2S15Vs;A1S6dVu0;G0A2A3F_;").
  Proof using . intros E. unfold alloc_meta, dequeue_head. utauto. Qed.
End Usage.

Lemma ct_and {A} (t : itree astate A) (Q1 Q2 : A -> Prop) : ltac2:(tb__ "0|0|
S68VA;Vt;VQ1;A3S68VA;Vt;VQ2;A3S68VA;Vt;VA;S1VQ1;R1A1VQ2;R1A1A2La;A3F_;F_;").
Proof. induction t as [a | q sp k IH | f]; cbn; intros H1 H2; [split; assumption | | exact I]. intros z. apply IH; [apply H1 | apply H2]. Qed.

Lemma plan_44 s1 : ltac2:(tb__ "0|2|
S0S56S67S67A2S4dVs1;Z2cM0Z10000S1eG0Z0M1A2G1A5S5aS67S67Z1Z11000A4A3").
Proof. unfold mmap_plan, is_bouncing. evalc (bounce_idx 44). evalc (initial_cnt 44 0). cbn -[usage_of]. reflexivity. Qed.

Lemma ft_init_slot f s : ltac2:(tb__ "0|4|
S69Vs;A1S0S67S7Vs;A1Z0M0A3S0S59S6A1M1SdVs;A1S60S6A1M2A3S0G1S80G1S75Z2cM3A1S14Vs;A1G2A4G2A3S0S67S38Vs;G3A2G0A3S68S56S67S5A2S26S62S62Vf;A1A1G3Z10000Vs;A4S6aS67A1A3F_;F_;F_;F_;F_;").
Proof.
  intros F Hc Hhd H44 Hu.
  cbn fix beta iota delta [alloc_slot].
  apply ct_bind. unfold try_avail, get_head. apply ct_bind. apply ct_bind. apply ct_get. cbn beta iota delta [fst snd].
  apply ct_ret. cbn beta iota delta [fst snd]. rewrite H44. apply ct_ret. cbn beta iota zeta delta [fst snd negb Z.eqb].
  apply ct_bind. cbn fix beta iota delta [alloc_group]. apply ct_bind.
  eapply ct_conseq; [exact (ct_and _ _ _ (ft_alloc_meta s F) (ut_alloc_meta (st_usage s) s eq_refl))|].
  intros [om s1] [F1 U1]. unfold fq, uq in F1, U1. cbn [fst snd] in F1, U1.
  destruct om as [m|]; cbn iota; [|ftauto].
  apply ct_bind. apply ct_get. cbn beta iota delta [fst snd].
  assert (Hu1 : usage_of s1 44 = 0) by (unfold usage_of in *; rewrite U1; exact Hu).
  cbn zeta. rewrite Hu1, group_44_big, plan_44. cbn [fst snd].
  match goal with |- context [install_group _ _ _ ?ai ?ml _ _] => evalc ai; evalc ml end.
  evalc (page_round 69632).
  unfold install_group. ftauto.
Qed.

Lemma ft_malloc_first s : ltac2:(tb__ "0|4|
S69Vs;A1S0S67S7Vs;A1Z0M0A3S0S59S6A1M1SdVs;A1S60S6A1M2A3S0G1S80G1S75Z2cM3A1S14Vs;A1G2A4G2A3S0S67S38Vs;G3A2G0A3S68S56G1S5A2S12Z10000Vs;A2S6aG1A1A3F_;F_;F_;F_;F_;").
Proof.
  intros F Hc Hhd H44 Hu.
  unfold malloc. evalc (size_overflows 65536). evalc (MMAP_THRESHOLD <=? 65536). cbn iota.
  apply ct_bind. apply ct_get. cbn beta iota zeta delta [fst snd].
  evalc (size_to_class 65536). rewrite !H44. evalc (4 <=? 44). evalc (44 <? 32). cbn beta iota zeta delta [andb osptr_eqb].
  rewrite !H44. change NEST_FUEL with (S (S 62%nat)).
  apply ct_bind. apply ct_ret. cbn beta iota zeta delta [fst snd]. apply ct_bind. apply ct_bind.
  eapply ct_conseq; [apply (ft_init_slot 62 s F Hc Hhd H44 Hu)|].
  intros [idx s1] F1. unfold fq in F1. cbn beta iota zeta delta [fst snd] in *.
  ftauto.
Qed.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout MallocIface ContractDrv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition drv_inv (j : nat) (s : astate) : Prop := ltac2:(tb__ "0|1|
S1S81Vs;A1S1S0S58S8Vs;A1S5cA3S1S71Z0S7Vs;A1M0A2S1S71Z64S73G0S74Vj;A1A2A2S69Vs;A1A2A2A2A2").

Theorem drv_reach_inv C j A : ltac2:(tb__ "0|0|
S7cVC;Vj;VA;A3S70Vj;S7eVA;A1A2F_;").
Proof.
  induction 1 as [brk0 tr p A' HM Hp | j A n tr p A' HR IH Hn HM | j A b tr A' HR IH HF].
  - pose proof (malloc_rel_WF _ 65536 _ _ _ (MA_init_WF C brk0) ltac:(lia) HM) as HW'.
    destruct HM as (q & HY & _ & Hres & _). cbn [ma_s MA_init] in HY.
    assert (F0 : full_all init_state) by (intros g am []).
    pose proof (ct_yields _ _ tr (q, ma_s A') (ct_malloc_first init_state eq_refl eq_refl eq_refl) HY) as HQ.
    pose proof (ct_yields _ _ tr (q, ma_s A') (ft_malloc_first init_state F0 eq_refl eq_refl eq_refl eq_refl) HY) as HF.
    unfold fq in HF. cbn [fst snd] in HQ, HF. destruct q as [q|]; [|exfalso; apply Hp; exact Hres].
    destruct (HQ ltac:(discriminate)) as [C1 I1]. cbn [fst snd] in C1, I1. unfold drv_inv. rewrite C1, I1. split; [exact HW'|]. split; [reflexivity|]. split; [lia|]. split; [cbn; lia | exact HF].
  - pose proof (malloc_rel_WF _ n _ _ _ (proj1 IH) ltac:(unfold MMAP_THRESHOLD in Hn; lia) HM) as HW'.
    destruct IH as (HW & HI & H0 & HJ & HFa). destruct HM as (q & HY & _).
    pose proof (ct_yields _ _ tr (q, ma_s A') (ct_malloc_direct _ _ n eq_refl HI H0 (proj1 Hn)) HY) as (I1 & C0 & C1).
    pose proof (ct_yields _ _ tr (q, ma_s A') (ft_malloc_direct _ n HFa (proj1 Hn)) HY) as HF. unfold fq in HF.
    cbn [fst snd] in I1, C0, C1, HF. unfold drv_inv. rewrite Nat2Z.inj_succ. split; [exact HW'|]. split; [exact I1|]. split; [exact C0|]. split; [lia | exact HF].
  - pose proof (free_rel_WF _ _ _ _ (proj1 IH) HF) as HW'.
    destruct IH as (HW & HI & H0 & HJ & HFa). unfold drv_inv. rewrite Nat2Z.inj_succ.
    destruct HF as [(_ & -> & _) | (p & n & _ & _ & HY & _)].
    + split; [exact HW|]. split; [exact HI|]. split; [exact H0|]. split; [lia | exact HFa].
    + pose proof (ct_yields _ _ tr (tt, ma_s A') (ct_free _ _ (Some p) _ eq_refl eq_refl) HY) as [C1 I1].
      pose proof (ct_yields _ _ tr (tt, ma_s A') (ft_free (Some p) _ HFa) HY) as HF'. unfold fq in HF'.
      cbn [fst snd] in C1, I1, HF'. rewrite C1, I1. split; [exact HW'|]. split; [exact HI|]. split; [exact H0|]. split; [lia | exact HF'].
Qed.

Theorem drv_reach_inited C j A : ltac2:(tb__ "0|0|
S7cVC;Vj;VA;A3S0S58S8S7eVA;A1A1S5cA3F_;").
Proof. intros H. exact (proj1 (proj2 (drv_reach_inv C j A H))). Qed.

Theorem drv_reach_meta_avail C j A : ltac2:(tb__ "0|1|
S7cVC;Vj;VA;A3S72S74Vj;A1S7dA2S3S2S0S59S6A1SdS7eVA;A1M0A1S60S6A1A3A1S72Z0S7G0A1A2A2F_;F_;").
Proof. intros H Hj. pose proof (drv_reach_inv C j A H) as (_ & _ & _ & HJ & _). unfold DRV_OPS in Hj. right. lia. Qed.

Theorem drv_reach_meta_count C j A : ltac2:(tb__ "0|0|
S7cVC;Vj;VA;A3S72S74Vj;A1S7dA2S72Z3cS7S7eVA;A1A1A2F_;F_;").
Proof. intros H Hj. pose proof (drv_reach_inv C j A H) as (_ & _ & _ & HJ & _). unfold DRV_OPS in Hj. lia. Qed.

Theorem drv_reach_full C j A : ltac2:(tb__ "0|0|
S7cVC;Vj;VA;A3S69S7eVA;A1A1F_;").
Proof. intros H. exact (proj2 (proj2 (proj2 (proj2 (drv_reach_inv C j A H))))). Qed.

Theorem drv_reach_WF C j A : ltac2:(tb__ "0|0|
S7cVC;Vj;VA;A3S81S7eVA;A1A1F_;").
Proof. intros H. exact (proj1 (drv_reach_inv C j A H)). Qed.

