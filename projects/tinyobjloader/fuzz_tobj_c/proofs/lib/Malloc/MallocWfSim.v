(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "False"; "True"; "iff"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "slotst"; "mslot"; "ameta"; "MUsed"; "st_metas"; "nth_slot"; "mkAMeta"; "frame"; "slot_is_group"; "IAsk"; "bind"; "mcheck"; "mupdate"; "ibind"; "set_metas"; "ss_hdr"; "KJunk"; "alloc_slot"; "ask"; "find_frame_in"; "fkind"; "get"; "getm"; "massert"; "mkSlot"; "mlookup"; "modify"; "put"; "ret"; "slot_junk"; "st_active"; "st_area_head"; "st_area_tail"; "st_areas"; "st_avail_meta"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_avail_meta_count"; "st_bounces"; "st_brk"; "st_free_meta_head"; "st_init_done"; "st_meta_alloc_shift"; "st_mmap_counter"; "st_regions"; "st_seq"; "st_unmap_seq"; "st_usage"; "FGroup"; "UNIT"; "find_in_slots"; "fr_off"; "ss_fr"; "IFail"; "IRet"; "account_bounce"; "activate_group"; "alloc_group"; "alloc_meta"; "am_avail"; "am_freed"; "am_slots"; "area_from_brk"; "area_from_mmap"; "askz"; "brkst"; "decay_bounces"; "dequeue"; "dequeue_head"; "enframe"; "fail"; "find_frame"; "forget_frame"; "fr_kind"; "fr_n"; "free"; "free_meta"; "get_head"; "get_links"; "install_group"; "is_bouncing"; "kreq"; "links_of"; "lupd"; "malloc"; "mkA"; "mkFrame"; "mmap_plan"; "new_region"; "nontrivial_free"; "open_area"; "padd"; "queue"; "record_seq"; "region"; "release_slot"; "set_active"; "set_area_head"; "set_area_tail"; "set_areas"; "set_avail_meta"; "set_avail_meta_area_count"; "set_avail_meta_areas"; "set_avail_meta_count"; "set_bounces"; "set_brk"; "set_free_meta_head"; "set_head"; "set_init_done"; "set_links"; "set_meta_alloc_shift"; "set_mmap_counter"; "set_next"; "set_prev"; "set_regions"; "set_seq"; "set_unmap_seq"; "set_usage"; "set_usage_of"; "setm"; "setslot"; "step_seq"; "stride_of"; "try_avail"; "upd_region"; "upd_slot"; "usage_of"; "with_links"; "FUser"; "IB"; "am_aidx"; "am_last"; "am_maplen"; "am_mem"; "am_next"; "am_prev"; "am_sc"; "am_set_slots"; "class_size"; "slot_start"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSim"; "sheq"; "rsim"; "eqr"; "mrel"; "is_junk"; "hdr_known_at"; "ef"; "enr"; "chk"; "orel"; "amr"; "ffr"; "mres"; "stride_flds"; "@Corelib.Init.Datatypes"; "prod"; "unit"; "option"; "bool"; "pair"; "list"; "Some"; "true"; "snd"; "false"; "fst"; "tt"; "nat"; "None"; "andb"; "cons"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "erase_slot"; "erase_meta"; "MT"; "tsim"; "shape_eq"; "keys"; "active_hd"; "erase"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@Stdlib.ZArith.BinInt.Z"; "le"; "eqb"; "lt"; "mul"; "sub"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase"; "itok"; "@Stdlib.Lists.List"; "NoDup"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition is_junk (q : kreq) : bool := match q with KJunk _ => true | _ => false end.

Lemma tsim_ask_inv {A B} (R : A -> B -> Prop) q sp k q' sp' k' : ltac2:(tb__ "0|2|
SbaVA;VB;VR;S13S8VA;Vq;Vsp;Vk;A5S13S8VB;Vq';Vsp';Vk';A5A5S3S1S0Sa8S9bVq;A1M0SacA3S1S0Sa8S9bVq';A1SacA3S96S96S1Sc1Z0R2A2Sc3R2Z100A2A2M1G1SbaVA;VB;VR;Vk;R4A1Vk';R3A1A5F_;F_;Fz';Fz;A2A2S1S0Sa8G0SaeA3S1S0S5bVq;Vq';A3S96SbaVA;VB;VR;Vk;R1A1Vk';R1A1A5Fz;A2A2A2F_;").
Proof. intros H. destruct q, q'; cbn in H; first [right; split; [reflexivity|exact H] | left; split; [reflexivity|split; [reflexivity|exact H]] | destruct H as [H _]; discriminate]. Qed.

Lemma tsim_ask_intro {A B} (R : A -> B -> Prop) q sp k q' sp' k' : ltac2:(tb__ "0|2|
S3S1S0Sa8S9bVq;A1M0SacA3S1S0Sa8S9bVq';A1SacA3S96S96S1Sc1Z0R2A2Sc3R2Z100A2A2M1G1SbaVA;VB;VR;Vk;R4A1Vk';R3A1A5F_;F_;Fz';Fz;A2A2S1S0Sa8G0SaeA3S1S0S5bVq;Vq';A3S96SbaVA;VB;VR;Vk;R1A1Vk';R1A1A5Fz;A2A2A2SbaVA;VB;VR;S13S8VA;Vq;Vsp;Vk;A5S13S8VB;Vq';Vsp';Vk';A5A5F_;").
Proof.
  intros [(J & J' & H) | (J & <- & H)].
  - destruct q, q'; cbn in J, J'; try discriminate. exact H.
  - destruct q; cbn in J; try discriminate; cbn; (split; [reflexivity|exact H]).
Qed.

Lemma tsim_mono {A B} (R R' : A -> B -> Prop) (x : itree astate A) (y : itree astate B) : ltac2:(tb__ "0|0|
VA;VB;VR;R2R1A2VR';R3R2A2F_;Fb;Fa;SbaVA;VB;VR;Vx;Vy;A5SbaVA;VB;VR';Vx;Vy;A5F_;F_;").
Proof.
  intros HR. revert y. induction x as [a | q sp k IH | f]; intros y H; destruct y as [b | q' sp' k' | f'];
    try (cbn in H; first [contradiction | destruct q; contradiction]).
  - exact (HR _ _ H).
  - apply tsim_ask_inv in H. apply tsim_ask_intro. destruct H as [(J & J' & H) | (J & E & H)].
    + left. split; [exact J|]. split; [exact J'|]. intros z z' Hz Hz'. apply IH. apply H; assumption.
    + right. split; [exact J|]. split; [exact E|]. intros z. apply IH. apply H.
  - exact I.
Qed.

Lemma tsim_ibind {A B C D} (R1 : A -> B -> Prop) (R2 : C -> D -> Prop)
      (x : itree astate A) (y : itree astate B) (K : A -> itree astate C) (K' : B -> itree astate D) : ltac2:(tb__ "0|0|
SbaVA;VB;VR1;Vx;Vy;A5VA;VB;VR1;R2R1A2SbaVC;VD;VR2;VK;R3A1VK';R2A1A5F_;Fb;Fa;SbaVC;VD;VR2;S17S8VA;VC;Vx;VK;A5S17S8VB;VD;Vy;VK';A5A5F_;F_;").
Proof.
  intros H HK. revert y H. induction x as [a | q sp k IH | f]; intros y H; destruct y as [b | q' sp' k' | f'];
    try (cbn in H; first [contradiction | destruct q; contradiction]).
  - cbn. apply HK, H.
  - cbn [ibind]. apply tsim_ask_inv in H. apply tsim_ask_intro. destruct H as [(J & J' & H) | (J & E & H)].
    + left. split; [exact J|]. split; [exact J'|]. intros z z' Hz Hz'. apply IH. apply H; assumption.
    + right. split; [exact J|]. split; [exact E|]. intros z. apply IH. apply H.
  - exact I.
Qed.

Lemma itok_unbind {A B} (x : itree astate A) (K : A -> itree astate B) Q : ltac2:(tb__ "0|0|
Sc7VB;S17S8VA;VB;Vx;VK;A5VQ;A3Sc7VA;Vx;VA;Sc7VB;VK;R1A1VQ;A3La;A3F_;").
Proof.
  induction x as [a | q sp k IH | f]; cbn; intros H; [exact H | | exact H].
  destruct H as [Hq H]. split; [exact Hq|]. intros z Hz. apply IH. apply H, Hz.
Qed.

Definition rsim {A B} (R : A -> B -> Prop) (x : itree astate A) (y : itree astate B) : Prop :=
  forall P P', itok x P -> itok y P' -> tsim (fun a b => R a b /\ P a /\ P' b) x y.

Lemma rsim_tsim {A B} (R : A -> B -> Prop) x y P P' : ltac2:(tb__ "0|0|
S98VA;VB;VR;Vx;Vy;A5Sc7VA;Vx;VP;A3Sc7VB;Vy;VP';A3SbaVA;VB;VA;VB;S1VR;R2R1A2S1VP;R2A1VP';R1A1A2A2Lb;La;Vx;Vy;A5F_;F_;F_;").
Proof. intros H Hx Hy. exact (H P P' Hx Hy). Qed.

Lemma rsim_mono {A B} (R R' : A -> B -> Prop) (x : itree astate A) (y : itree astate B) : ltac2:(tb__ "0|0|
VA;VB;VR;R2R1A2VR';R3R2A2F_;Fb;Fa;S98VA;VB;VR;Vx;Vy;A5S98VA;VB;VR';Vx;Vy;A5F_;F_;").
Proof.
  intros HR H P P' Hx Hy. eapply tsim_mono; [|exact (H P P' Hx Hy)]. intros a b (H1 & H2 & H3). auto.
Qed.

Lemma rsim_iret {A B} (R : A -> B -> Prop) a b : ltac2:(tb__ "0|0|
VR;Va;Vb;A2S98VA;VB;VR;S40S8VA;Va;A3S40S8VB;Vb;A3A5F_;").
Proof. intros H P P' Hx Hy. cbn in *. auto. Qed.

Lemma rsim_ifail_l {A B} (R : A -> B -> Prop) f (y : itree astate B) : ltac2:(tb__ "0|0|
S98VA;VB;VR;S3fS8VA;Vf;A3Vy;A5").
Proof. intros P P' Hx Hy. destruct Hx. Qed.

Lemma rsim_ifail_r {A B} (R : A -> B -> Prop) (x : itree astate A) f : ltac2:(tb__ "0|0|
S98VA;VB;VR;Vx;S3fS8VB;Vf;A3A5").
Proof. intros P P' Hx Hy. destruct Hy. Qed.

Lemma rsim_ibind {A B C D} (R1 : A -> B -> Prop) (R2 : C -> D -> Prop)
      (x : itree astate A) (y : itree astate B) (K : A -> itree astate C) (K' : B -> itree astate D) : ltac2:(tb__ "0|0|
S98VA;VB;VR1;Vx;Vy;A5VA;VB;VR1;R2R1A2S98VC;VD;VR2;VK;R3A1VK';R2A1A5F_;Fb;Fa;S98VC;VD;VR2;S17S8VA;VC;Vx;VK;A5S17S8VB;VD;Vy;VK';A5A5F_;F_;").
Proof.
  intros H HK P P' Hx Hy. apply itok_unbind in Hx. apply itok_unbind in Hy.
  eapply tsim_ibind; [exact (H _ _ Hx Hy)|]. intros a b (H1 & H2 & H3). exact (HK a b H1 P P' H2 H3).
Qed.

Lemma rsim_iask {A B} (R : A -> B -> Prop) q sp sp' k k' : ltac2:(tb__ "0|0|
S0Sa8S9bVq;A1SaeA3S96S98VA;VB;VR;Vk;R1A1Vk';R1A1A5Fz;S98VA;VB;VR;S13S8VA;Vq;Vsp;Vk;A5S13S8VB;Vq;Vsp';Vk';A5A5F_;F_;").
Proof.
  intros J H P P' Hx Hy. cbn in Hx, Hy. destruct Hx as [_ Hx], Hy as [_ Hy].
  apply tsim_ask_intro. right. split; [exact J|]. split; [reflexivity|]. intros z.
  assert (Az : answer_ok q z) by (destruct q; cbn in J |- *; first [exact I | discriminate]).
  exact (H z P P' (Hx z Az) (Hy z Az)).
Qed.

Lemma rsim_iask_junk {A B} (R : A -> B -> Prop) c c' sp sp' k k' : ltac2:(tb__ "0|1|
S96S96S1Sc1Z0R2A2Sc3R2Z100A2A2M0G0S98VA;VB;VR;Vk;R4A1Vk';R3A1A5F_;F_;Fz';Fz;S98VA;VB;VR;S13S8VA;S1aVc;A1Vsp;Vk;A5S13S8VB;S1aVc';A1Vsp';Vk';A5A5F_;").
Proof.
  intros H P P' Hx Hy. cbn in Hx, Hy. destruct Hx as [_ Hx], Hy as [_ Hy].
  cbn. intros z z' Hz Hz'. exact (H z z' Hz Hz' P P' (Hx z Hz) (Hy z' Hz')).
Qed.

Section MonadRules.
  Context {A B : Type}.
  Implicit Types (s t : astate).

  Lemma rsim_ret (R : A * astate -> A * astate -> Prop) (a b : A) s t : ltac2:(tb__ "0|1|
VR;Sa9VA;S8Va;Vs;A4Sa9VA;S8Vb;Vt;A4A2S98Sa5VA;S8A2M0G0VR;S26VA;Va;Vs;A3S26VA;Vb;Vt;A3A5F_;").
  Proof using . intros H. apply rsim_iret. exact H. Qed.

  Lemma rsim_bind (R1 : B * astate -> B * astate -> Prop) (R2 : A * astate -> A * astate -> Prop)
        (m m' : M B) (k k' : B -> M A) s t : ltac2:(tb__ "0|2|
S98Sa5VB;S8A2M0G0VR1;Vm;Vs;A1Vm';Vt;A1A5VB;S8VB;S8VR1;Sa9VB;S8R4R3A4Sa9VB;S8R2R1A4A2S98Sa5VA;S8A2M1G1VR2;Vk;R5R4A2Vk';R3R2A2A5F_;Ft1;Fb';Fs1;Fb;S98G1G1VR2;S14VB;VA;Vm;Vk;Vs;A5S14VB;VA;Vm';Vk';Vt;A5A5F_;F_;").
  Proof using .
    intros H HK. unfold bind. eapply rsim_ibind; [exact H|]. intros [b s1] [b' t1] Hb. exact (HK _ _ _ _ Hb).
  Qed.

  Lemma rsim_fail_l R f s (y : itree astate (A * astate)) : ltac2:(tb__ "0|1|
S98Sa5VA;S8A2M0G0VR;S50VA;Vf;Vs;A3Vy;A5").
  Proof using . apply rsim_ifail_l. Qed.
  Lemma rsim_fail_r R (x : itree astate (A * astate)) f t : ltac2:(tb__ "0|1|
S98Sa5VA;S8A2M0G0VR;Vx;S50VA;Vf;Vt;A3A5").
  Proof using . apply rsim_ifail_r. Qed.

  Lemma rsim_get (R : astate * astate -> astate * astate -> Prop) s t : ltac2:(tb__ "0|1|
VR;Sa9S8S8Vs;Vs;A4Sa9S8S8Vt;Vt;A4A2S98Sa5S8S8A2M0G0VR;S1fVs;A1S1fVt;A1A5F_;").
  Proof using . intros H. apply rsim_iret. exact H. Qed.

  Lemma rsim_put (R : unit * astate -> unit * astate -> Prop) s1 t1 s t : ltac2:(tb__ "0|1|
VR;Sa9Sa6S8Sb0Vs1;A4Sa9Sa6S8Sb0Vt1;A4A2S98Sa5Sa6S8A2M0G0VR;S25Vs1;Vs;A2S25Vt1;Vt;A2A5F_;").
  Proof using . intros H. apply rsim_iret. exact H. Qed.

  Lemma rsim_modify (R : unit * astate -> unit * astate -> Prop) f f' s t : ltac2:(tb__ "0|1|
VR;Sa9Sa6S8Sb0Vf;Vs;A1A4Sa9Sa6S8Sb0Vf';Vt;A1A4A2S98Sa5Sa6S8A2M0G0VR;S24Vf;Vs;A2S24Vf';Vt;A2A5F_;").
  Proof using . intros H. apply rsim_iret. exact H. Qed.

  Lemma rsim_ask (R : bool * astate -> bool * astate -> Prop) q s t : ltac2:(tb__ "0|1|
S0Sa8S9bVq;A1SaeA3Sa8VR;Sa9Sa8S8R1Vs;A4Sa9Sa8S8R1Vt;A4A2Fb;S98Sa5Sa8S8A2M0G0VR;S1cVq;Vs;A2S1cVq;Vt;A2A5F_;F_;").
  Proof using . intros J H. unfold ask. apply rsim_iask; [exact J|]. intros z. apply rsim_iret. apply H. Qed.

  Lemma rsim_askz_junk (R : Z * astate -> Z * astate -> Prop) c c' s t : ltac2:(tb__ "0|2|
S96S96S1Sc1Z0R2A2Sc3R2Z100A2A2M0G0VR;Sa9S96S8R4Vs;A4Sa9S96S8R3Vt;A4A2F_;F_;Fz';Fz;S98Sa5S96S8A2M1G1VR;S4aS1aVc;A1Vs;A2S4aS1aVc';A1Vt;A2A5F_;").
  Proof using . intros H. unfold askz. apply rsim_iask_junk. intros z z' Hz Hz'. apply rsim_iret. apply H; assumption. Qed.
End MonadRules.

  Lemma rsim_massert (R : unit * astate -> unit * astate -> Prop) b b' i i' s t : ltac2:(tb__ "0|1|
S0Sa8Vb;SacA3S0Sa8Vb';SacA3VR;Sa9Sa6S8Sb0Vs;A4Sa9Sa6S8Sb0Vt;A4A2F_;F_;S98Sa5Sa6S8A2M0G0VR;S21Vb;Vi;Vs;A3S21Vb';Vi';Vt;A3A5F_;").
  Proof.
    intros H. unfold massert. destruct b; [|apply rsim_ifail_l]. destruct b'; [|apply rsim_ifail_r].
    apply rsim_ret. apply H; reflexivity.
  Qed.

  Lemma rsim_mcheck (R : unit * astate -> unit * astate -> Prop) b b' i i' s t : ltac2:(tb__ "0|1|
S0Sa8Vb;SacA3S0Sa8Vb';SacA3VR;Sa9Sa6S8Sb0Vs;A4Sa9Sa6S8Sb0Vt;A4A2F_;F_;S98Sa5Sa6S8A2M0G0VR;S15Vb;Vi;Vs;A3S15Vb';Vi';Vt;A3A5F_;").
  Proof.
    intros H. unfold mcheck. destruct b; [|apply rsim_ifail_l]. destruct b'; [|apply rsim_ifail_r].
    apply rsim_ret. apply H; reflexivity.
  Qed.

Definition erase_am (am : ameta) : ameta := ltac2:(tb__ "0|0|
S93SbfSaSaSb7S47Vam;A1A4Vam;A2").
Definition ef (e : sptr * mslot) : sptr * mslot := ltac2:(tb__ "0|0|
Sa9S9SbSafS9SbVe;A3Sb8SadS9SbVe;A3A1A4").
Definition mrel (ms mt : list (sptr * mslot)) : Prop := ltac2:(tb__ "0|1|
S0SaaSa5S9SbA2M0A1SbfG0G0S9dVms;A4SbfG0G0S9dVmt;A4A3").

Lemma erase_unfold s : ltac2:(tb__ "0|1|
S0S8SbeVs;A1S18SbfSa5S9SbA2M0G0S9dSeVs;A1A4Vs;A2A3").
Proof. reflexivity. Qed.

Definition sheq (s t : astate) : Prop := ltac2:(tb__ "0|0|
S1SbbVs;Vt;A2Sc8S9SbcVs;A1A2A2").

Lemma sheq_shape s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2SbbVs;Vt;A2F_;").
Proof. intros [H _]; exact H. Qed.

Lemma sq_metas s t : ltac2:(tb__ "0|0|
SbbVs;Vt;A2S9aSeVs;A1SeVt;A1A2F_;").
Proof. intros H. exact (f_equal st_metas H). Qed.
Lemma sheq_metas s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S9aSeVs;A1SeVt;A1A2F_;").
Proof. intros [H _]. apply sq_metas, H. Qed.

Lemma mrel_keys ms mt : ltac2:(tb__ "0|2|
S9aVms;Vmt;A2S0SaaS9A1SbfSa5S9SbA2M0S9SafS9SbA2M1Vms;A4SbfG0S9G1Vmt;A4A3F_;").
Proof.
  intros H. transitivity (map fst (map ef ms)); [rewrite map_map; reflexivity|].
  unfold mrel in H. rewrite H, map_map. reflexivity.
Qed.

Lemma sheq_nodup_l s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2Sc8S9SbcVs;A1A2F_;").
Proof. intros [_ H]; exact H. Qed.
Lemma sheq_nodup_r s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2Sc8S9SbcVt;A1A2F_;").
Proof. intros [H ND]. unfold keys in *. rewrite <- (mrel_keys _ _ (sq_metas _ _ H)). exact ND. Qed.

Lemma sq_init_done s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0Sa8S33Vt;A1S33Vs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_init_done H). Qed.
Lemma sq_mmap_counter s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0S96S35Vt;A1S35Vs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_mmap_counter H). Qed.
Lemma sq_free_meta_head s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0Sa7S9A1S32Vt;A1S32Vs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_free_meta_head H). Qed.
Lemma sq_avail_meta s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0S9S2cVt;A1S2cVs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_avail_meta H). Qed.
Lemma sq_avail_meta_count s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0S96S2fVt;A1S2fVs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_avail_meta_count H). Qed.
Lemma sq_avail_meta_area_count s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0S96S2dVt;A1S2dVs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_avail_meta_area_count H). Qed.
Lemma sq_meta_alloc_shift s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0S96S34Vt;A1S34Vs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_meta_alloc_shift H). Qed.
Lemma sq_area_head s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0Sa7S9A1S29Vt;A1S29Vs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_area_head H). Qed.
Lemma sq_area_tail s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0Sa7S9A1S2aVt;A1S2aVs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_area_tail H). Qed.
Lemma sq_avail_meta_areas s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0S9S2eVt;A1S2eVs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_avail_meta_areas H). Qed.
Lemma sq_active s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0SaaSa7S9A1A1S28Vt;A1S28Vs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_active H). Qed.
Lemma sq_usage s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0SaaS96A1S39Vt;A1S39Vs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_usage H). Qed.
Lemma sq_unmap_seq s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0SaaS96A1S38Vt;A1S38Vs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_unmap_seq H). Qed.
Lemma sq_bounces s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0SaaS96A1S30Vt;A1S30Vs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_bounces H). Qed.
Lemma sq_seq s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0S96S37Vt;A1S37Vs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_seq H). Qed.
Lemma sq_brk s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0S4bS31Vt;A1S31Vs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_brk H). Qed.
Lemma sq_regions s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0SaaS68A1S36Vt;A1S36Vs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_regions H). Qed.
Lemma sq_areas s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0SaaS9A1S2bVt;A1S2bVs;A1A3F_;").
Proof. intros [H _]. symmetry. exact (f_equal st_areas H). Qed.
Lemma sq_is_bouncing s t sc : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0Sa8S5aVt;Vsc;A2S5aVs;Vsc;A2A3F_;").
Proof. intros H. unfold is_bouncing. rewrite (sq_bounces _ _ H). reflexivity. Qed.
Lemma sq_usage_of s t sc : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0S96S88Vt;Vsc;A2S88Vs;Vsc;A2A3F_;").
Proof. intros H. unfold usage_of. rewrite (sq_usage _ _ H). reflexivity. Qed.
Lemma sq_active_hd s t sc : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0Sa7S9A1SbdVt;Vsc;A2SbdVs;Vsc;A2A3F_;").
Proof. intros H. unfold active_hd. rewrite (sq_active _ _ H). reflexivity. Qed.
Lemma sq_mmap_plan s t sc req c u : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0Sa5S96S96A2S61Vt;Vsc;Vreq;Vc;Vu;A5S61Vs;Vsc;Vreq;Vc;Vu;A5A3F_;").
Proof. intros H. unfold mmap_plan. rewrite !(sq_is_bouncing _ _ _ H), !(sq_usage_of _ _ _ H). reflexivity. Qed.

Ltac shrw H := rewrite ?(sq_mmap_plan _ _ _ _ _ _ H), ?(sq_is_bouncing _ _ _ H), ?(sq_usage_of _ _ _ H), ?(sq_active_hd _ _ _ H), ?(sq_init_done _ _ H), ?(sq_mmap_counter _ _ H), ?(sq_free_meta_head _ _ H), ?(sq_avail_meta _ _ H), ?(sq_avail_meta_count _ _ H), ?(sq_avail_meta_area_count _ _ H), ?(sq_meta_alloc_shift _ _ H), ?(sq_area_head _ _ H), ?(sq_area_tail _ _ H), ?(sq_avail_meta_areas _ _ H), ?(sq_active _ _ H), ?(sq_usage _ _ H), ?(sq_unmap_seq _ _ H), ?(sq_bounces _ _ H), ?(sq_seq _ _ H), ?(sq_brk _ _ H), ?(sq_regions _ _ H), ?(sq_areas _ _ H) in *.
Ltac shrwg H := rewrite ?(sq_mmap_plan _ _ _ _ _ _ H), ?(sq_is_bouncing _ _ _ H), ?(sq_usage_of _ _ _ H), ?(sq_active_hd _ _ _ H), ?(sq_init_done _ _ H), ?(sq_mmap_counter _ _ H), ?(sq_free_meta_head _ _ H), ?(sq_avail_meta _ _ H), ?(sq_avail_meta_count _ _ H), ?(sq_avail_meta_area_count _ _ H), ?(sq_meta_alloc_shift _ _ H), ?(sq_area_head _ _ H), ?(sq_area_tail _ _ H), ?(sq_avail_meta_areas _ _ H), ?(sq_active _ _ H), ?(sq_usage _ _ H), ?(sq_unmap_seq _ _ H), ?(sq_bounces _ _ H), ?(sq_seq _ _ H), ?(sq_brk _ _ H), ?(sq_regions _ _ H), ?(sq_areas _ _ H).

Lemma sq_mk x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 ms mt : ltac2:(tb__ "0|0|
S9aVms;Vmt;A2SbbS5fVx0;Vx1;Vx2;Vx3;Vx4;Vx5;Vx6;Vx7;Vx8;Vx9;Vx10;Vx11;Vx12;Vx13;Vx14;Vx15;Vms;Vx17;Vx18;A13S5fVx0;Vx1;Vx2;Vx3;Vx4;Vx5;Vx6;Vx7;Vx8;Vx9;Vx10;Vx11;Vx12;Vx13;Vx14;Vx15;Vmt;Vx17;Vx18;A13A2F_;").
Proof. intros H. unfold shape_eq. rewrite !erase_unfold. cbn. unfold mrel in H. rewrite H. reflexivity. Qed.

Lemma sq_fields s t : ltac2:(tb__ "0|2|
S6SbbVs;Vt;A2S1S0Sa8S33Vs;A1S33Vt;A1A3S1S0S96S35Vs;A1S35Vt;A1A3S1S0Sa7S9A1M0S32Vs;A1S32Vt;A1A3S1S0S9S2cVs;A1S2cVt;A1A3S1S0S96S2fVs;A1S2fVt;A1A3S1S0S96S2dVs;A1S2dVt;A1A3S1S0S96S34Vs;A1S34Vt;A1A3S1S0G0S29Vs;A1S29Vt;A1A3S1S0G0S2aVs;A1S2aVt;A1A3S1S0S9S2eVs;A1S2eVt;A1A3S1S0SaaG0A1S28Vs;A1S28Vt;A1A3S1S0SaaS96A1M1S39Vs;A1S39Vt;A1A3S1S0G1S38Vs;A1S38Vt;A1A3S1S0G1S30Vs;A1S30Vt;A1A3S1S0S96S37Vs;A1S37Vt;A1A3S1S0S4bS31Vs;A1S31Vt;A1A3S1S0SaaS68A1S36Vs;A1S36Vt;A1A3S1S0SaaS9A1S2bVs;A1S2bVt;A1A3S9aSeVs;A1SeVt;A1A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  split.
  - intros H. repeat match goal with |- _ /\ _ => split end;
      match goal with
      | |- mrel _ _ => exact (f_equal st_metas H)
      | |- ?p s = ?p t => pose proof (f_equal p H) as E; cbn in E; exact E
      end.
  - destruct s as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19], t as [b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19]. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas].
    intros (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM). subst. unfold shape_eq. rewrite !erase_unfold. unfold set_metas.
    cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. unfold mrel in EM. rewrite EM. reflexivity.
Qed.
Lemma sheq_set_init_done v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S76Vv;Vs;A2S76Vv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_init_done. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_mmap_counter v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S79Vv;Vs;A2S79Vv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_mmap_counter. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_free_meta_head v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S74Vv;Vs;A2S74Vv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_free_meta_head. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_avail_meta v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S6eVv;Vs;A2S6eVv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_avail_meta. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_avail_meta_count v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S71Vv;Vs;A2S71Vv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_avail_meta_count. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_avail_meta_area_count v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S6fVv;Vs;A2S6fVv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_avail_meta_area_count. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_meta_alloc_shift v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S78Vv;Vs;A2S78Vv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_meta_alloc_shift. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_area_head v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S6bVv;Vs;A2S6bVv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_area_head. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_area_tail v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S6cVv;Vs;A2S6cVv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_area_tail. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_avail_meta_areas v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S70Vv;Vs;A2S70Vv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_avail_meta_areas. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_active v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S6aVv;Vs;A2S6aVv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_active. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_usage v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S7fVv;Vs;A2S7fVv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_usage. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_unmap_seq v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S7eVv;Vs;A2S7eVv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_unmap_seq. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_bounces v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S72Vv;Vs;A2S72Vv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_bounces. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_seq v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S7dVv;Vs;A2S7dVv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_seq. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_brk v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S73Vv;Vs;A2S73Vv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_brk. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_regions v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S7cVv;Vs;A2S7cVv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_regions. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_areas v s t : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S97S6dVv;Vs;A2S6dVv;Vt;A2A2F_;").
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_areas. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.

Lemma mrel_mupdate ms mt p x x' : ltac2:(tb__ "0|0|
S9aVms;Vmt;A2S0SbSb8Vx;A1Sb8Vx';A1A3S9aS16Vms;Vp;Vx;A3S16Vmt;Vp;Vx';A3A2F_;F_;").
Proof.
  unfold mrel. revert mt. induction ms as [|[q y] ms IH]; intros [|[q' y'] mt] H Ex; cbn [mupdate map] in *; try discriminate.
  - unfold ef. cbn [fst snd]. rewrite Ex. reflexivity.
  - unfold ef in H at 1 3. cbn [fst snd] in H. injection H as Eq Ey Et. subst q'. destruct (sptr_eqb p q); cbn [map].
    + unfold ef at 1 3. cbn [fst snd]. rewrite Ex, Et. reflexivity.
    + unfold ef at 1 3. cbn [fst snd]. rewrite Ey. f_equal. apply IH; assumption.
Qed.

Definition orel (o o' : option mslot) : Prop := ltac2:(tb__ "0|2|
Sa7SbA1M0OLo;Vo;SbG0OLo';M1Vo';SbS0SbSb8R2A1Sb8R1A1A3Lx';S4Xa7x2Lx;G1Vo';SbS4Lm;S5Xa7x2Xa7x2").

Lemma mrel_mlookup ms mt p : ltac2:(tb__ "0|0|
S9aVms;Vmt;A2Sa0S23Vms;Vp;A2S23Vmt;Vp;A2A2F_;").
Proof.
  unfold mrel. revert mt. induction ms as [|[q y] ms IH]; intros [|[q' y'] mt] H; cbn [mlookup map] in *; try discriminate; [exact I|].
  unfold ef in H at 1 3. cbn [fst snd] in H. injection H as Eq Ey Et. subst q'. destruct (sptr_eqb p q); [exact Ey|]. apply IH. exact Et.
Qed.

Lemma sheq_MT s t p : ltac2:(tb__ "0|0|
S97Vs;Vt;A2Sa0Sb9Vs;Vp;A2Sb9Vt;Vp;A2A2F_;").
Proof. intros H. unfold MT. apply mrel_mlookup. apply sheq_metas, H. Qed.

Lemma erase_meta_inv x x' : ltac2:(tb__ "0|3|
S0SbSb8Vx;A1Sb8Vx';A1A3SbOLx;Vx;Sa7S9A1M0G0S0SbVx';Vx;A3M1Lnext;Lprev;G1ScS2SaaSaA1M2G2S1S0SbVx';SdS10S91R2A1S90R2A1S8fR2A1S45R2A1S46R2A1S8dR2A1S92R2A1S8eR2A1S8cR2A1R1AaA1A3S0G2SbfSaSaSb7S47R2A1A4SbfSaSaSb7R1A4A3A2Lsl';A2Lam;Xbx3F_;").
Proof.
  destruct x as [pr nx| |am], x' as [pr' nx'| |am']; cbn; intros E; try discriminate; try congruence.
  destruct am, am'. cbn in E |- *. injection E as -> -> -> -> -> -> -> -> -> Esl. eexists. split; [reflexivity | exact Esl].
Qed.

Lemma erase_am_mk pr nx mem av frd la sc ml ai sl sl' : ltac2:(tb__ "0|0|
S0SaaSaA1SbfSaSaSb7Vsl;A4SbfSaSaSb7Vsl';A4A3S0SbSb8SdS10Vpr;Vnx;Vmem;Vav;Vfrd;Vla;Vsc;Vml;Vai;Vsl;AaA1A1Sb8SdS10Vpr;Vnx;Vmem;Vav;Vfrd;Vla;Vsc;Vml;Vai;Vsl';AaA1A1A3F_;").
Proof. intros H. cbn. rewrite H. reflexivity. Qed.

Lemma links_of_erase x x' : ltac2:(tb__ "0|1|
S0SbSb8Vx;A1Sb8Vx';A1A3S0Sa5Sa7S9A1M0G0A2S5cVx';A1S5cVx;A1A3F_;").
Proof. intros E. apply erase_meta_inv in E. destruct x; subst; try reflexivity. destruct E as (sl' & -> & _). destruct m; reflexivity. Qed.

Lemma with_links_erase x x' pr nx : ltac2:(tb__ "0|0|
S0SbSb8Vx;A1Sb8Vx';A1A3S0SbSb8S89Vx;Vpr;Vnx;A3A1Sb8S89Vx';Vpr;Vnx;A3A1A3F_;").
Proof. intros E. pose proof (erase_meta_inv _ _ E) as E'. destruct x; subst; try reflexivity. destruct E' as (sl' & -> & Es). destruct m. cbn in Es |- *. rewrite Es. reflexivity. Qed.

Lemma cons_inj {T} (a b : T) (l m : list T) : ltac2:(tb__ "0|1|
S0SaaVT;A1M0Sb4VT;Va;Vl;A3Sb4VT;Vb;Vm;A3A3S1S0VT;Va;Vb;A3S0G0Vl;Vm;A3A2F_;").
Proof. intros H. injection H as -> ->. split; reflexivity. Qed.

Lemma map_erase_nth sl sl' i : ltac2:(tb__ "0|0|
S0SaaSaA1SbfSaSaSb7Vsl;A4SbfSaSaSb7Vsl';A4A3S0SaSb7Sc0SaVi;Vsl;S27A4A1Sb7Sc0SaVi;Vsl';S27A4A1A3F_;").
Proof.
  revert sl' i. induction sl as [|x sl IH]; intros [|x' sl'] i H; cbn [map] in H; try discriminate; [reflexivity|].
  apply cons_inj in H as [Ex Et]. destruct i; cbn [nth]; [exact Ex | apply IH; exact Et].
Qed.

Lemma map_erase_lupd sl sl' i x x' : ltac2:(tb__ "0|1|
S0SaaSaA1M0SbfSaSaSb7Vsl;A4SbfSaSaSb7Vsl';A4A3S0SaSb7Vx;A1Sb7Vx';A1A3S0G0SbfSaSaSb7S5dSaVsl;Vi;Vx;A4A4SbfSaSaSb7S5dSaVsl';Vi;Vx';A4A4A3F_;F_;").
Proof.
  revert sl' i. induction sl as [|y sl IH]; intros [|y' sl'] i H Ex; cbn [map] in H; try discriminate; [reflexivity|].
  apply cons_inj in H as [Ey Et]. destruct i; cbn [lupd map]; [congruence|]. rewrite Ey. f_equal. apply IH; assumption.
Qed.

Lemma map_erase_length sl sl' : ltac2:(tb__ "0|0|
S0SaaSaA1SbfSaSaSb7Vsl;A4SbfSaSaSb7Vsl';A4A3S0Sb1Sb5SaVsl';A2Sb5SaVsl;A2A3F_;").
Proof. intros H. rewrite <- (length_map erase_slot sl), <- (length_map erase_slot sl'), H. reflexivity. Qed.

Lemma erase_slot_inv x x' : ltac2:(tb__ "0|6|
S0SaSb7Vx;A1Sb7Vx';A1A3S1S6S0Sa7Sa5S96S96A2M0A1M1S19Vx;A1Sb2G0A1M2A3S0G1S19Vx';A1G2A3A2Sa7S11A1OLx;M3S3eVx;A1S11G3S3eVx';A1M4S11S1S0S96S54R1A1S54R2A1A3S1S0S1eS53R1A1S53R2A1M5A3S0S1eG5S3aA3S0S96S3dR2A1S3dR3A1A3F_;A2A2Lfr';S4Xa7x2Lfr;G3G4S11S4Lf;S5Xa7x2Xa7x2A2F_;").
Proof.
  destruct x as [h f], x' as [h' f']. unfold erase_slot. cbn [ss_hdr ss_fr]. intros E. injection E as Eh Ef. split.
  - destruct h, h'; split; intros; congruence.
  - destruct f as [fr|], f' as [fr'|]; try discriminate; [|exact I]. injection Ef as Eo En Ek.
    split; [congruence|]. split; [congruence|]. intros K. rewrite K in Eo. rewrite <- Ek, K in Eo. congruence.
Qed.

Lemma erase_slot_rehdr x x' f : ltac2:(tb__ "0|0|
S0SaSb7Vx;A1Sb7Vx';A1A3S0SaSb7S22S19Vx;A1Vf;A2A1Sb7S22S19Vx';A1Vf;A2A1A3F_;").
Proof. intros E. unfold erase_slot in *. cbn [ss_hdr ss_fr] in *. injection E as Eh Ef. rewrite Eh. reflexivity. Qed.

Lemma map_erase_nth_slot pr nx mem av frd la sc ml ai sl pr' nx' mem' av' frd' la' sc' ml' ai' sl' i : ltac2:(tb__ "0|0|
S0SaaSaA1SbfSaSaSb7Vsl;A4SbfSaSaSb7Vsl';A4A3S0SaSb7SfS10Vpr;Vnx;Vmem;Vav;Vfrd;Vla;Vsc;Vml;Vai;Vsl;AaVi;A2A1Sb7SfS10Vpr';Vnx';Vmem';Vav';Vfrd';Vla';Vsc';Vml';Vai';Vsl';AaVi;A2A1A3F_;").
Proof. intros H. unfold nth_slot. cbn [am_slots]. apply map_erase_nth. exact H. Qed.

Lemma sheq_set_metas s t p x x' : ltac2:(tb__ "0|0|
S97Vs;Vt;A2S0SbSb8Vx;A1Sb8Vx';A1A3S97S18S16SeVs;A1Vp;Vx;A3Vs;A2S18S16SeVt;A1Vp;Vx';A3Vt;A2A2F_;F_;").
Proof.
  intros [H ND] Ex. split.
  - pose proof (mrel_mupdate _ _ p x x' (sq_metas _ _ H) Ex) as M.
    apply sq_fields in H. apply (proj2 (sq_fields _ _)). unfold set_metas.
    cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
    repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
  - unfold keys. cbn [st_metas set_metas]. apply NoDup_keys_mupdate. exact ND.
Qed.

Create HintDb sheq.
Hint Resolve sheq_set_init_done sheq_set_mmap_counter sheq_set_free_meta_head sheq_set_avail_meta
  sheq_set_avail_meta_count sheq_set_avail_meta_area_count sheq_set_meta_alloc_shift sheq_set_area_head
  sheq_set_area_tail sheq_set_avail_meta_areas sheq_set_active sheq_set_usage sheq_set_unmap_seq
  sheq_set_bounces sheq_set_seq sheq_set_brk sheq_set_regions sheq_set_areas sheq_set_metas : sheq.

Definition stride_flds (la ml sc : Z) : Z := ltac2:(tb__ "0|1|
Sa8S96L_;Sb3Sc2Vla;Z0M0A2Sb6Sc2Vml;G0A2A1A2Sc5Sc4Vml;Z1000A2S3bA2S94Vsc;A1Xa8x2").
Lemma stride_of_mk pr nx mem av frd la sc ml ai sl : ltac2:(tb__ "0|0|
S0S96S84S10Vpr;Vnx;Vmem;Vav;Vfrd;Vla;Vsc;Vml;Vai;Vsl;AaA1Sa4Vla;Vml;Vsc;A3A3").
Proof. reflexivity. Qed.

Ltac amsimp := cbn [am_set_slots am_set_avail am_set_freed am_set_aidx am_set_links am_set_prev am_set_next upd_slot
                    am_prev am_next am_mem am_avail am_freed am_last am_sc am_maplen am_aidx am_slots]; rewrite ?stride_of_mk.
Ltac eam :=
  amsimp;
  first [ reflexivity | assumption
        | apply erase_am_mk;
          first [ assumption
                | apply map_erase_lupd;
                  first [ assumption | reflexivity
                        | apply erase_slot_rehdr; first [assumption | apply map_erase_nth_slot; assumption | apply map_erase_nth; assumption] ] ]
        | apply with_links_erase; assumption
        | congruence ].
Hint Extern 1 (erase_meta _ = erase_meta _) => eam : sheq.

Ltac sheq_tac :=
  match goal with H : sheq ?s ?t |- _ => shrwg H; solve [eauto 20 with sheq] end.

Definition eqr {A} (r r' : A * astate) : Prop := fst r = fst r' /\ sheq (snd r) (snd r').

Definition amr (p : sptr) (s t : astate) (r r' : ameta * astate) : Prop := ltac2:(tb__ "0|5|
S2Sa7S9A1M0G0S2G0G0S2S9S9S2S96S96S2S96S96S2S96S96S2S96S96S2S96S96S2S96S96S2SaaSaA1M1G1S2G1G1S1S0ScSafScS8Vr;A3M2S10RbRaR9R8R7R6R5R4R3R2AaA3S1S0ScSafScS8Vr';A3M3S10RbRaR9R8R7R6R5R4R3R1AaA3S1S0G1SbfSaSaSb7R2A4SbfSaSaSb7R1A4A3S1S0Sa7SbA1M4Sb9Vs;Vp;A2SabSbSdG2A1A2A3S1S0G4Sb9Vt;Vp;A2SabSbSdG3A1A2A3S1S0S8SadScS8Vr;A3Vs;A3S0S8SadScS8Vr';A3Vt;A3A2A2A2A2A2A2Lsl';A2Lsl;A2Lai;A2Lml;A2Lsc;A2Lla;A2Lfrd;A2Lav;A2Lmem;A2Lnx;A2Lpr;A2").

Section Prims.
  Context {A : Type}.
  Implicit Types (s t : astate).

  Lemma rsim_ret_eq (a : A) s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5VA;S8A2M0G0S99VA;A1S26VA;Va;Vs;A3S26VA;Va;Vt;A3A5F_;").
  Proof using . intros H. apply rsim_ret. split; [reflexivity | exact H]. Qed.

  Lemma rsim_get_eq s t : ltac2:(tb__ "0|1|
S98Sa5S8S8A2M0G0G0G0S1S0G0R2Sa9S8S8Vs;Vs;A4A3S0G0R1Sa9S8S8Vt;Vt;A4A3A2Lr';Lr;S1fVs;A1S1fVt;A1A5").
  Proof using . apply rsim_get. split; reflexivity. Qed.

  Lemma rsim_modify_eq f f' s t : ltac2:(tb__ "0|1|
S97Vf;Vs;A1Vf';Vt;A1A2S98Sa5Sa6S8A2M0G0S99Sa6A1S24Vf;Vs;A2S24Vf';Vt;A2A5F_;").
  Proof using . intros H. apply rsim_modify. split; [reflexivity | exact H]. Qed.

  Lemma rsim_put_eq s1 t1 s t : ltac2:(tb__ "0|1|
S97Vs1;Vt1;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S25Vs1;Vs;A2S25Vt1;Vt;A2A5F_;").
  Proof using . intros H. apply rsim_put. split; [reflexivity | exact H]. Qed.

  Lemma rsim_ask_eq q s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S0Sa8S9bVq;A1SaeA3S98Sa5Sa8S8A2M0G0S99Sa8A1S1cVq;Vs;A2S1cVq;Vt;A2A5F_;F_;").
  Proof using . intros H J. apply rsim_ask; [exact J|]. intros b. split; [reflexivity | exact H]. Qed.

End Prims.

Definition chk (b b' : bool) (s t : astate) (r r' : unit * astate) : Prop := ltac2:(tb__ "0|0|
S1S0Sa8Vb;SacA3S1S0Sa8Vb';SacA3S1S0S8SadSa6S8Vr;A3Vs;A3S0S8SadSa6S8Vr';A3Vt;A3A2A2A2").

Lemma rsim_massert_chk b b' i i' s t : ltac2:(tb__ "0|1|
S98Sa5Sa6S8A2M0G0S9fVb;Vb';Vs;Vt;A4S21Vb;Vi;Vs;A3S21Vb';Vi';Vt;A3A5").
Proof. apply rsim_massert. intros B B'. split; [exact B|]. split; [exact B'|]. split; reflexivity. Qed.

Lemma rsim_mcheck_chk b b' i i' s t : ltac2:(tb__ "0|1|
S98Sa5Sa6S8A2M0G0S9fVb;Vb';Vs;Vt;A4S15Vb;Vi;Vs;A3S15Vb';Vi';Vt;A3A5").
Proof. apply rsim_mcheck. intros B B'. split; [exact B|]. split; [exact B'|]. split; reflexivity. Qed.

Lemma rsim_getm p s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5ScS8A2M0G0Sa1Vp;Vs;Vt;A3S20Vp;Vs;A2S20Vp;Vt;A2A5F_;").
Proof.
  intros H. unfold getm. eapply rsim_bind; [apply rsim_get_eq|]. intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->.
  pose proof (sheq_MT s t p H) as OR. unfold MT in OR.
  destruct (mlookup (st_metas s) p) as [x|] eqn:Ms, (mlookup (st_metas t) p) as [x'|] eqn:Mt; cbn in OR; try contradiction; [|apply rsim_ifail_l].
  pose proof (erase_meta_inv _ _ OR) as INV. destruct x as [pr0 nx0| |am]; [subst x'; apply rsim_ifail_l .. |].
  destruct INV as (sl' & -> & ES). apply rsim_ret. destruct am as [pr nx mem av frd la sc ml ai sl]. cbn in ES.
  exists pr, nx, mem, av, frd, la, sc, ml, ai, sl, sl'. unfold MT. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | exact ES | exact Ms | exact Mt].
Qed.

Lemma rsim_setm p am am' s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S0SbSb8SdVam;A1A1Sb8SdVam';A1A1A3S98Sa5Sa6S8A2M0G0S99Sa6A1S81Vp;Vam;Vs;A3S81Vp;Vam';Vt;A3A5F_;F_;").
Proof. intros H E. unfold setm. apply rsim_modify_eq. apply sheq_set_metas; assumption. Qed.

Lemma rsim_setslot p x x' s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S0SbSb8Vx;A1Sb8Vx';A1A3S98Sa5Sa6S8A2M0G0S99Sa6A1S82Vp;Vx;Vs;A3S82Vp;Vx';Vt;A3A5F_;F_;").
Proof. intros H E. unfold setslot. apply rsim_modify_eq. apply sheq_set_metas; assumption. Qed.

Lemma rsim_get_links p s t : ltac2:(tb__ "0|3|
S97Vs;Vt;A2S98Sa5Sa5Sa7S9A1M0G0A2M1S8A2M2G2S99G1A1S58Vp;Vs;A2S58Vp;Vt;A2A5F_;").
Proof.
  intros H. unfold get_links. eapply rsim_bind; [apply rsim_get_eq|]. intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->.
  pose proof (sheq_MT s t p H) as OR. unfold MT in OR.
  destruct (mlookup (st_metas s) p) as [x|], (mlookup (st_metas t) p) as [x'|]; cbn in OR; try contradiction; [|apply rsim_ifail_l].
  apply rsim_ret. split; [cbn [fst]; symmetry; apply links_of_erase; exact OR | exact H].
Qed.

Lemma rsim_set_links p pr nx s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S77Vp;Vpr;Vnx;Vs;A4S77Vp;Vpr;Vnx;Vt;A4A5F_;").
Proof.
  intros H. unfold set_links. eapply rsim_bind; [apply rsim_get_eq|]. intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->.
  pose proof (sheq_MT s t p H) as OR. unfold MT in OR.
  destruct (mlookup (st_metas s) p) as [x|], (mlookup (st_metas t) p) as [x'|]; cbn in OR; try contradiction; [|apply rsim_ifail_l].
  apply rsim_setslot; [exact H|]. apply with_links_erase. exact OR.
Qed.

Lemma rsim_set_prev p pr s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S7bVp;Vpr;Vs;A3S7bVp;Vpr;Vt;A3A5F_;").
Proof.
  intros H. unfold set_prev. eapply rsim_bind; [apply rsim_get_links; exact H|].
  intros l s1 l' t1 [E HS]; cbn [fst snd] in E, HS; subst l'. apply rsim_set_links. exact HS.
Qed.

Lemma rsim_set_next p nx s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S7aVp;Vnx;Vs;A3S7aVp;Vnx;Vt;A3A5F_;").
Proof.
  intros H. unfold set_next. eapply rsim_bind; [apply rsim_get_links; exact H|].
  intros l s1 l' t1 [E HS]; cbn [fst snd] in E, HS; subst l'. apply rsim_set_links. exact HS.
Qed.

Lemma rsim_get_head h s t : ltac2:(tb__ "0|2|
S97Vs;Vt;A2S98Sa5Sa7S9A1M0S8A2M1G1S99G0A1S57Vh;Vs;A2S57Vh;Vt;A2A5F_;").
Proof.
  intros H. unfold get_head. eapply rsim_bind; [apply rsim_get_eq|]. intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->.
  destruct h; apply rsim_ret; (split; [cbn [fst]; shrwg H; reflexivity | exact H]).
Qed.

Lemma rsim_set_head h v s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S75Vh;Vv;Vs;A3S75Vh;Vv;Vt;A3A5F_;").
Proof. intros H. unfold set_head. destruct h; apply rsim_modify_eq; shrwg H; auto with sheq. Qed.

Ltac shall := repeat match goal with H : sheq _ _ |- _ => progress (shrwg H) end.

Create HintDb rsim.

Ltac rhead :=
  lazymatch goal with
  | |- rsim _ (get _) (get _) => apply rsim_get_eq
  | |- rsim _ (ret _ _) (ret _ _) => apply rsim_ret_eq; assumption
  | |- rsim _ (modify _ _) (modify _ _) => apply rsim_modify_eq; sheq_tac
  | |- rsim _ (put _ _) (put _ _) => apply rsim_put_eq; sheq_tac
  | |- rsim _ (getm _ _) (getm _ _) => apply rsim_getm; assumption
  | |- rsim _ (setm _ _ _) (setm _ _ _) => apply rsim_setm; [assumption | eam]
  | |- rsim _ (setslot _ _ _) (setslot _ _ _) => apply rsim_setslot; [assumption | eam]
  | |- rsim _ (get_links _ _) (get_links _ _) => apply rsim_get_links; assumption
  | |- rsim _ (set_links _ _ _ _) (set_links _ _ _ _) => apply rsim_set_links; assumption
  | |- rsim _ (set_prev _ _ _) (set_prev _ _ _) => apply rsim_set_prev; assumption
  | |- rsim _ (set_next _ _ _) (set_next _ _ _) => apply rsim_set_next; assumption
  | |- rsim _ (get_head _ _) (get_head _ _) => apply rsim_get_head; assumption
  | |- rsim _ (set_head _ _ _) (set_head _ _ _) => apply rsim_set_head; assumption
  | |- rsim _ (massert _ _ _) (massert _ _ _) => apply rsim_massert_chk
  | |- rsim _ (mcheck _ _ _) (mcheck _ _ _) => apply rsim_mcheck_chk
  | |- rsim _ (ask _ _) (ask _ _) => apply rsim_ask_eq; [assumption | reflexivity]
  | |- rsim _ (fail _ _) _ => apply rsim_ifail_l
  | |- rsim _ _ (fail _ _) => apply rsim_ifail_r
  | |- rsim _ _ _ => solve [eauto 3 with rsim nocore]
  end.

Ltac rintro :=
  let a := fresh "a" in let s1 := fresh "s" in let a' := fresh "a'" in let t1 := fresh "t" in
  let HR := fresh "HR" in
  intros a s1 a' t1 HR; cbn beta in HR;
  lazymatch type of HR with
  | eqr _ _ =>
      let E := fresh "E" in let HS := fresh "HS" in
      destruct HR as [E HS]; cbn [fst snd] in E, HS; subst a'
  | chk _ _ _ _ _ _ =>
      let B1 := fresh "CHK" in let B2 := fresh "CHK'" in let E1 := fresh "E" in let E2 := fresh "E" in
      destruct HR as (B1 & B2 & E1 & E2); cbn [fst snd] in E1, E2; subst s1 t1; destruct a, a'
  | _ = _ /\ _ = _ =>
      let E1 := fresh "E" in let E2 := fresh "E" in
      destruct HR as [E1 E2]; injection E1 as -> ->; injection E2 as -> ->
  | amr _ _ _ _ _ =>
      let pr := fresh "pr" in let nx := fresh "nx" in let mem := fresh "mem" in let av := fresh "av" in
      let frd := fresh "frd" in let la := fresh "la" in let sc := fresh "sc" in let ml := fresh "ml" in
      let ai := fresh "ai" in let sl := fresh "sl" in let sl' := fresh "sl'" in
      let E1 := fresh "E" in let E2 := fresh "E" in let ES := fresh "ES" in
      let M1 := fresh "Ms" in let M2 := fresh "Mt" in let E3 := fresh "E" in let E4 := fresh "E" in
      destruct HR as (pr & nx & mem & av & frd & la & sc & ml & ai & sl & sl' & E1 & E2 & ES & M1 & M2 & E3 & E4);
      cbn [fst snd] in E1, E2, M1, M2, E3, E4; subst a a' s1 t1
  | _ => idtac
  end; cbn beta iota zeta delta [fst snd].

Ltac rauto :=
  shall; amsimp;
  first
  [ lazymatch goal with
    | |- rsim _ (bind _ _ _) (bind _ _ _) => eapply rsim_bind; [solve [rauto] | rintro; rauto]
    | |- rsim _ (match ?x with _ => _ end _) (match ?x with _ => _ end _) => destruct x eqn:?; rauto
    | |- rsim _ (match ?x with _ => _ end) (match ?x with _ => _ end) => destruct x eqn:?; rauto
    | |- rsim _ _ _ => rhead
    end
  | idtac ].

Ltac rstep := shall; amsimp; eapply rsim_bind; [rhead | rintro].
Ltac rbind tac := shall; amsimp; eapply rsim_bind; [tac | rintro].
Ltac rcase :=
  shall; amsimp;
  lazymatch goal with
  | |- rsim _ (match ?x with _ => _ end _) _ => destruct x eqn:?
  | |- rsim _ (match ?x with _ => _ end) _ => destruct x eqn:?
  end.

Lemma rsim_queue h m s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S66Vh;Vm;Vs;A3S66Vh;Vm;Vt;A3A5F_;").
Proof. intros H. unfold queue. rauto. Qed.
Global Hint Resolve rsim_queue : rsim.

Lemma rsim_dequeue h m s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S4dVh;Vm;Vs;A3S4dVh;Vm;Vt;A3A5F_;").
Proof. intros H. unfold dequeue. rauto. Qed.
Global Hint Resolve rsim_dequeue : rsim.

Lemma rsim_dequeue_head h s t : ltac2:(tb__ "0|2|
S97Vs;Vt;A2S98Sa5Sa7S9A1M0S8A2M1G1S99G0A1S4eVh;Vs;A2S4eVh;Vt;A2A5F_;").
Proof. intros H. unfold dequeue_head. rauto. Qed.
Global Hint Resolve rsim_dequeue_head : rsim.

Lemma rsim_free_meta m s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S56Vm;Vs;A2S56Vm;Vt;A2A5F_;").
Proof. intros H. unfold free_meta. rauto. Qed.
Global Hint Resolve rsim_free_meta : rsim.

Lemma rsim_set_usage_of sc v s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S80Vsc;Vv;Vs;A3S80Vsc;Vv;Vt;A3A5F_;").
Proof. intros H. unfold set_usage_of. rauto. Qed.
Global Hint Resolve rsim_set_usage_of : rsim.

Lemma rsim_step_seq s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S83Vs;A1S83Vt;A1A5F_;").
Proof. intros H. unfold step_seq. apply rsim_modify_eq. shrwg H. destruct (st_seq s =? 255); auto with sheq. Qed.
Global Hint Resolve rsim_step_seq : rsim.

Lemma rsim_record_seq sc s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S67Vsc;Vs;A2S67Vsc;Vt;A2A5F_;").
Proof. intros H. unfold record_seq. destruct (bounce_idx sc); rauto. Qed.
Global Hint Resolve rsim_record_seq : rsim.

Lemma rsim_account_bounce sc s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S41Vsc;Vs;A2S41Vsc;Vt;A2A5F_;").
Proof.
  intros H. unfold account_bounce. destruct (bounce_idx sc); [|rauto].
  apply rsim_modify_eq. shrwg H. destruct (negb _ && _); auto with sheq.
Qed.
Global Hint Resolve rsim_account_bounce : rsim.

Lemma rsim_decay_bounces sc s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S4cVsc;Vs;A2S4cVsc;Vt;A2A5F_;").
Proof.
  intros H. unfold decay_bounces. destruct (bounce_idx sc); [|rauto].
  apply rsim_modify_eq. shrwg H. destruct (_ =? 0); auto with sheq.
Qed.
Global Hint Resolve rsim_decay_bounces : rsim.

Lemma rsim_new_region k len s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sb1S8A2M0G0S99Sb1A1S62Vk;Vlen;Vs;A3S62Vk;Vlen;Vt;A3A5F_;").
Proof. intros H. unfold new_region. rauto. Qed.
Global Hint Resolve rsim_new_region : rsim.

Lemma rsim_upd_region r f s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S86Vr;Vf;Vs;A3S86Vr;Vf;Vt;A3A5F_;").
Proof. intros H. unfold upd_region. rauto. Qed.
Global Hint Resolve rsim_upd_region : rsim.

Lemma rsim_area_from_brk s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa8S8A2M0G0S99Sa8A1S48Vs;A1S48Vt;A1A5F_;").
Proof. intros H. unfold area_from_brk. rauto. Qed.
Global Hint Resolve rsim_area_from_brk : rsim.

Lemma rsim_area_from_mmap s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa8S8A2M0G0S99Sa8A1S49Vs;A1S49Vt;A1A5F_;").
Proof. intros H. unfold area_from_mmap. rauto. Qed.
Global Hint Resolve rsim_area_from_mmap : rsim.

Lemma rsim_open_area nu s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa8S8A2M0G0S99Sa8A1S64Vnu;Vs;A2S64Vnu;Vt;A2A5F_;").
Proof. intros H. unfold open_area. rauto. Qed.
Global Hint Resolve rsim_open_area : rsim.

Lemma rsim_alloc_meta s t : ltac2:(tb__ "0|2|
S97Vs;Vt;A2S98Sa5Sa7S9A1M0S8A2M1G1S99G0A1S44Vs;A1S44Vt;A1A5F_;").
Proof. intros H. unfold alloc_meta. rauto. Qed.
Global Hint Resolve rsim_alloc_meta : rsim.

Lemma rsim_activate_group m s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5S96S8A2M0G0S99S96A1S42Vm;Vs;A2S42Vm;Vt;A2A5F_;").
Proof. intros H. unfold activate_group. rauto. Qed.
Global Hint Resolve rsim_activate_group : rsim.

Lemma rsim_install_group m sc cnt aidx maplen mem sl s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S59Vm;Vsc;Vcnt;Vaidx;Vmaplen;Vmem;Vsl;Vs;A8S59Vm;Vsc;Vcnt;Vaidx;Vmaplen;Vmem;Vsl;Vt;A8A5F_;").
Proof. intros H. unfold install_group. rauto. Qed.
Global Hint Resolve rsim_install_group : rsim.

Lemma rsim_forget_frame g i s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa6S8A2M0G0S99Sa6A1S52Vg;Vi;Vs;A3S52Vg;Vi;Vt;A3A5F_;").
Proof. intros H. unfold forget_frame. rauto. Qed.
Global Hint Resolve rsim_forget_frame : rsim.

Lemma rsim_try_avail sc s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5S96S8A2M0G0S99S96A1S85Vsc;Vs;A2S85Vsc;Vt;A2A5F_;").
Proof. intros H. unfold try_avail. rauto. Qed.
Global Hint Resolve rsim_try_avail : rsim.

Definition enr (g : sptr) (idx n : Z) (k : fkind) (s t : astate) (r r' : sptr * astate) : Prop := ltac2:(tb__ "0|8|
S2Sa7S9A1M0G0S2G0G0S2S9S9S2S96S96S2S96S96S2S96S96S2S96S96S2S96S96S2S96S96S2SaaSaA1M1G1S2G1G1S2S96S96S2S96S96S2Sa5S96S96A2M2G2S2G2G2S10RfReRdRcRbRaR9R8R7R6AaScS10R10RfReRdRcRbRaR9R8R6AaScS1S0Sa7SbA1M3Sb9Vs;Vg;A2SabSbSdR2A1A2A3S1S0G3Sb9Vt;Vg;A2SabSbSdR1A1A2A3S1S0G1SbfSaSaSb7R8A4SbfSaSaSb7R7A4A3S1S1Sc1Z0M4Vidx;A2Sc1Vidx;RcA2A2S1S0S8SadS9S8Vr;A3M5S18S16SeVs;A1Vg;SdS87R2Vidx;S22SabG2R4A2SabS11S60R6Vn;Vk;A3A2A2A3A1A3Vs;A2A3S1S0S8SadS9S8Vr';A3M6S18S16SeVt;A1Vg;SdS87R1Vidx;S22SabG2R3A2SabS11S60R5Vn;Vk;A3A2A2A3A1A3Vt;A2A3S1S0S9SafS9S8Vr;A3S65S95R2Vidx;A2M7Sc4S3bR6A2A2A3S1S0S9SafS9S8Vr';A3S65G7Sc4S3bR5A2A2A3S1S0S1eVk;S3aA3S1S0S96R7G4A3S0S96R6G4A3A2F_;S97G5G6A2A2A2A2A2A2A2A2A2A2Tam';Tam;Lhdr';A2Lhdr;A2Loff';A2Loff;A2Lsl';A2Lsl;A2Lai;A2Lml;A2Lsc;A2Lla;A2Lfrd;A2Lav;A2Lmem;A2Lnx;A2Lpr;A2").

Lemma rsim_enframe g idx n ctr k s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S0S1eVk;S3aA3S2ScScS1S0Sa7SbA1Sb9Vs;Vg;A2SabSbSdR1A1A2A3S0S96Vn;Sc5S84R1A1S8bA2A3A2Lam;A2F_;S98Sa5S9S8A2M0G0S9eVg;Vidx;Vn;Vk;Vs;Vt;A6S4fVg;Vidx;Vn;Vctr;Vk;Vs;A6S4fVg;Vidx;Vn;Vctr;Vk;Vt;A6A5F_;F_;").
Proof.
  intros H HG. unfold enframe. rstep. rstep.
  set (am := mkAMeta pr nx mem av frd la sc ml ai sl) in *. set (am' := mkAMeta pr nx mem av frd la sc ml ai sl') in *.
  set (slack := (stride_flds la ml sc - IB - n) / UNIT).
  assert (EN : erase_slot (nth_slot am idx) = erase_slot (nth_slot am' idx)) by (apply map_erase_nth_slot; exact ES).
  apply erase_slot_inv in EN as [EH _].
  eapply (rsim_bind (fun r r' => snd r = s /\ snd r' = t /\ (slack = 0 -> fst r = 0 /\ fst r' = 0))).
  { destruct (slack =? 0) eqn:Es0.
    - apply rsim_ret. cbn [fst snd]. auto.
    - apply Z.eqb_neq in Es0.
      destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|] eqn:Eh, (ss_hdr (nth_slot am' idx)) as [[h3' h16']|] eqn:Eh';
        [| exfalso; pose proof (proj2 EH eq_refl); congruence | exfalso; pose proof (proj1 EH eq_refl); congruence |].
      + apply rsim_ret. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. intros; lia.
      + eapply (rsim_bind (fun r r' => snd r = s /\ snd r' = t)).
        * apply rsim_askz_junk. intros; split; reflexivity.
        * intros z s1 z' t1 [E1 E2]. cbn [fst snd] in E1, E2. subst s1 t1. apply rsim_ret. cbn [fst snd].
          split; [reflexivity|]. split; [reflexivity|]. intros; lia. }
  intros off0 s1 off0' t1 (E1 & E2 & Z0). cbn [fst snd] in E1, E2, Z0. subst s1 t1.
  rstep.
  unfold bind, setm, modify, ret. cbn [ibind]. apply rsim_iret.
  match goal with |- enr _ _ _ _ _ _ (padd _ (UNIT * ?o), _) (padd _ (UNIT * ?o'), _) => set (off := o); set (off' := o') end.
  assert (HG0 : k = FGroup -> off = 0 /\ off' = 0).
  { intros Hk. destruct (HG Hk) as (am0 & M0 & En). rewrite Ms in M0. injection M0 as <-. subst am. rewrite stride_of_mk in En.
    assert (S0 : slack = 0).
    { subst slack. rewrite En. replace (stride_flds la ml sc - IB - (stride_flds la ml sc - IB)) with 0 by lia. reflexivity. }
    destruct (Z0 S0) as [-> ->]. subst off off'. rewrite S0. cbn. split; reflexivity. }
  unfold enr. exists pr, nx, mem, av, frd, la, sc, ml, ai, sl, sl', off, off'. eexists. eexists. cbn [fst snd]. fold am am'.
  split; [exact Ms|]. split; [exact Mt|]. split; [exact ES|].
  split; [apply andb_prop in CHK as [B1 B2]; apply Z.leb_le in B1; apply Z.leb_le in B2; lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HG0|].
  apply sheq_set_metas; [exact H|]. subst am am'. unfold upd_slot. amsimp. apply erase_am_mk. apply map_erase_lupd; [exact ES|].
  destruct k; [reflexivity|]. destruct (HG0 eq_refl) as [-> ->]. reflexivity.
Qed.

Ltac enr_intro HR :=
  destruct HR as (?pr & ?nx & ?mem & ?av & ?frd & ?la & ?sc & ?ml & ?ai & ?sl & ?sl' & ?off & ?off' & ?hdr & ?hdr' &
                  ?Ms & ?Mt & ?ES & ?Hidx & ?E1 & ?E2 & ?P1 & ?P2 & ?HG0 & ?HS); cbn [fst snd] in Ms, Mt, E1, E2, P1, P2, HS.

Lemma rsim_alloc_mutual fuel : ltac2:(tb__ "0|4|
S1S96S96S8S8S97R2R1A2M0S98Sa5S96S8A2M1G1S99S96A1S1bVfuel;R5R4R3A4S1bVfuel;R5R4R2A4A5F_;Ft;Fs;Freq;Fsc;S96S96S8S8G0S98Sa5Sa7S9A1M2S8A2M3G3S99G2A1S43Vfuel;R5R4R3A4S43Vfuel;R5R4R2A4A5F_;Ft;Fs;Freq;Fsc;A2").
Proof.
  induction fuel as [|f [IHs IHg]].
  { split; intros; cbn; apply rsim_ifail_l. }
  split.
  - intros sc req s t H. cbn fix beta iota delta [alloc_slot]. rauto.
  - intros sc req s t H. cbn fix beta iota delta [alloc_group]. rauto.

    rbind ltac:(apply rsim_enframe; [assumption | intros _; eexists; split; [eassumption | apply Z.eqb_eq in CHK; rewrite <- CHK; reflexivity]]).
    enr_intro HR. subst. destruct (HG0 eq_refl) as [-> ->]. rauto.
Qed.

Lemma rsim_alloc_slot fuel sc req s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5S96S8A2M0G0S99S96A1S1bVfuel;Vsc;Vreq;Vs;A4S1bVfuel;Vsc;Vreq;Vt;A4A5F_;").
Proof. apply (proj1 (rsim_alloc_mutual fuel)). Qed.
Global Hint Resolve rsim_alloc_slot : rsim.

Definition mres (n : Z) (r r' : option sptr * astate) : Prop := ltac2:(tb__ "0|5|
S1S97SadSa7S9A1M0S8Vr;A3M1SadG0S8Vr';A3M2A2G0OLx;M3SafG0S8Vr;A3S9G3SafG0S8Vr';A3M4S9S2S9S9S2S96S96S2S8S8S2S8S8S9eR4R3Vn;S8aR2R1Sa9S9S8R6G1A4Sa9S9S8R5G2A4A8Lt0;A2Ls0;A2Lidx;A2Lg;A2Lp';S4Xa7x2Lp;G3G4S9S4Ls;S5Xa7x2Xa7x2A2").

Lemma sq_head_full s t h : ltac2:(tb__ "0|4|
S97Vs;Vt;A2S0Sa8Sa7SbA1Sa8Lx;M0S23SeVt;A1Vh;A2SbSbSa8Lm;R1Sa7S9A1M1G1SacLnext;Lprev;SacScSb3Sc2S45R1A1Z0M2A2Sc2S46R1A1G2A2A2Lam;Xbx3Lm;M3SacXa7x2G0S23SeVs;A1Vh;A2G3SacXa7x2A3F_;").
Proof.
  intros H. pose proof (sheq_MT s t h H) as OR. unfold MT in OR.
  destruct (mlookup (st_metas s) h) as [x|], (mlookup (st_metas t) h) as [x'|]; cbn in OR; try contradiction; [|reflexivity].
  pose proof (erase_meta_inv _ _ OR) as INV. destruct x; [subst x'; reflexivity .. |]. destruct INV as (sl' & -> & _). reflexivity.
Qed.

Lemma enr_sheq g idx n k s t p s1 p' t1 : ltac2:(tb__ "0|0|
S9eVg;Vidx;Vn;Vk;Vs;Vt;Sa9S9S8Vp;Vs1;A4Sa9S9S8Vp';Vt1;A4A8S97Vs1;Vt1;A2F_;").
Proof. intros HR. enr_intro HR. exact HS. Qed.

Ltac mres_leaf :=
  apply rsim_ret; split; [ first [assumption | eapply enr_sheq; eassumption] | cbn [fst snd]; first [exact I | do 4 eexists; eassumption] ].

Lemma rsim_malloc n s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa7S9A1S8A2M0G0Sa3Vn;A1S5eVn;Vs;A2S5eVn;Vt;A2A5F_;").
Proof.
  intros H. unfold malloc. destruct (size_overflows n); [mres_leaf|].
  destruct (MMAP_THRESHOLD <=? n).
  -
    rauto; try mres_leaf.
    rbind ltac:(apply rsim_enframe; [assumption | intros; discriminate]). mres_leaf.
  -
    rstep. shall. destruct (nth (Z.to_nat (size_to_class n + 1)) (st_active s) None) as [h|];
      [rewrite (sq_head_full s t h H)|].
    all: match goal with |- rsim _ (bind (match nth (Z.to_nat ?x) _ _ with _ => _ end) _ _) _ => set (sc := x) end.
    all: rauto; try mres_leaf.
    all: rbind ltac:(apply rsim_enframe; [assumption | intros; discriminate]); mres_leaf.
Qed.

Lemma find_in_slots_ge sl base stride i p k : ltac2:(tb__ "0|0|
S0Sa7S96A1S3cVsl;Vbase;Vstride;Vi;Vp;A5SabS96Vk;A2A3Sc1Vi;Vk;A2F_;").
Proof.
  revert i. induction sl as [|x sl IH]; intros i H; cbn [find_in_slots] in H; [discriminate|].
  destruct (ss_fr x) as [fr|]; [destruct (sptr_eqb _ p); [injection H as <-; lia|]|]; apply IH in H; lia.
Qed.

Lemma find_in_slots_rel sl sl' base stride i p : ltac2:(tb__ "0|6|
S0SaaSaA1SbfSaSaSb7Vsl;A4SbfSaSaSb7Vsl';A4A3S3S0Sa7S96A1M0S3cVsl;Vbase;Vstride;Vi;Vp;A5M1S3cVsl';Vbase;Vstride;Vi;Vp;A5M2A3S3S2S96S96S1S0G0G1SabS96R1A2M3A3S1Sc1Vi;R1A2M4S0Sa8S12Sc0SaSc6Sc5R1Vi;A2A1M5Vsl;S27A4A1SaeA3A2A2Lk;A2S2S96S96S1S0G0G2G3A3S1G4S0Sa8S12Sc0SaG5Vsl';S27A4A1SaeA3A2A2Lk;A2A2A2F_;").
Proof.
  revert sl' i. induction sl as [|x sl IH]; intros [|x' sl'] i H; cbn [map] in H; try discriminate; [left; reflexivity|].
  apply cons_inj in H as [Ex Et]. pose proof (erase_slot_inv _ _ Ex) as [_ FR]. cbn [find_in_slots].
  assert (SH : forall y l k, i + 1 <= k -> nth (Z.to_nat (k - i)) (y :: l) slot_junk = nth (Z.to_nat (k - (i + 1))) l slot_junk).
  { intros y l k Hk. replace (Z.to_nat (k - i)) with (S (Z.to_nat (k - (i + 1)))) by lia. reflexivity. }
  assert (REC : find_in_slots sl base stride (i + 1) p = find_in_slots sl' base stride (i + 1) p
    \/ (exists k, find_in_slots sl base stride (i + 1) p = Some k /\ i <= k /\ slot_is_group (nth (Z.to_nat (k - i)) (x :: sl) slot_junk) = false)
    \/ (exists k, find_in_slots sl' base stride (i + 1) p = Some k /\ i <= k /\ slot_is_group (nth (Z.to_nat (k - i)) (x' :: sl') slot_junk) = false)).
  { destruct (IH sl' (i + 1) Et) as [E | [(k & Hk & Hik & Hg) | (k & Hk & Hik & Hg)]]; [left; exact E | right; left | right; right];
      exists k; rewrite SH by lia; repeat split; auto; lia. }
  assert (G0 : forall y : slotst, forall fr, ss_fr y = Some fr -> fr_kind fr = FUser -> slot_is_group (nth (Z.to_nat (i - i)) (y :: sl) slot_junk) = false).
  { intros y fr Hy Hk. rewrite Z.sub_diag. cbn [Z.to_nat nth]. unfold slot_is_group. rewrite Hy, Hk. reflexivity. }
  assert (G0' : forall y : slotst, forall fr, ss_fr y = Some fr -> fr_kind fr = FUser -> slot_is_group (nth (Z.to_nat (i - i)) (y :: sl') slot_junk) = false).
  { intros y fr Hy Hk. rewrite Z.sub_diag. cbn [Z.to_nat nth]. unfold slot_is_group. rewrite Hy, Hk. reflexivity. }
  destruct (ss_fr x) as [fr|] eqn:Fx, (ss_fr x') as [fr'|] eqn:Fx'; try contradiction; [|exact REC].
  destruct FR as (En & Ek & Eo).
  destruct (fr_kind fr) eqn:K.
  -
    destruct (sptr_eqb (padd base (stride * i + UNIT * fr_off fr)) p).
    + right; left. exists i. split; [reflexivity|]. split; [lia|]. eapply G0; [exact Fx | exact K].
    + destruct (sptr_eqb (padd base (stride * i + UNIT * fr_off fr')) p).
      * right; right. exists i. split; [reflexivity|]. split; [lia|]. eapply G0'; [exact Fx' | exact Ek].
      * exact REC.
  -
    rewrite (Eo eq_refl). destruct (sptr_eqb _ p); [left; reflexivity | exact REC].
Qed.

Lemma find_frame_in_rel ms mt p : ltac2:(tb__ "0|8|
S9aVms;Vmt;A2S3S0Sa7Sa5S9S96A2M0A1M1S1dVms;Vp;A2M2S1dVmt;Vp;A2M3A3S3S2S9S9S2S96S96S2ScScS1S0G1G2SabG0Sa9S9S96R3R2A4A2M4A3S1Sc9Sa5S9SbA2M5Sa9S9SbR3SdR1A1A4M6Vms;A3S0Sa8S12SfR1R2A2A1SaeA3M7A2A2Lam;A2Lk;A2Lm;A2S2S9S9S2S96S96S2ScScS1S0G1G3G4A3S1Sc9G5G6Vmt;A3G7A2A2Lam';A2Lk;A2Lm;A2A2A2F_;").
Proof.
  unfold mrel. revert mt. induction ms as [|[q x] ms IH]; intros [|[q' x'] mt] H; cbn [map] in H; try discriminate; [left; reflexivity|].
  apply cons_inj in H as [Eqx Et]. unfold ef in Eqx. cbn [fst snd] in Eqx. injection Eqx as Eq Ex. subst q'.
  assert (REC : find_frame_in ms p = find_frame_in mt p
    \/ (exists m k am, find_frame_in ms p = Some (m, k) /\ In (m, MUsed am) ((q, x) :: ms) /\ slot_is_group (nth_slot am k) = false)
    \/ (exists m k am', find_frame_in mt p = Some (m, k) /\ In (m, MUsed am') ((q, x') :: mt) /\ slot_is_group (nth_slot am' k) = false)).
  { destruct (IH mt Et) as [E | [(m & k & am & Hf & Hin & Hg) | (m & k & am & Hf & Hin & Hg)]]; [left; exact E | right; left | right; right];
      exists m, k, am; repeat split; auto; right; exact Hin. }
  pose proof (erase_meta_inv _ _ Ex) as INV. cbn [find_frame_in].
  destruct x as [pr0 nx0| |am]; [subst x'; exact REC .. |]. destruct INV as (sl' & -> & ES).
  destruct am as [pr nx mem av frd la sc ml ai sl]. unfold stride_of. cbn [am_slots am_mem am_prev am_next am_avail am_freed am_last am_sc am_maplen am_aidx] in ES |- *.
  match goal with |- context [find_in_slots sl ?b ?st 0 p] =>
    destruct (find_in_slots_rel sl sl' b st 0 p ES) as [E | [(k & Hk & _ & Hg) | (k & Hk & _ & Hg)]] end.
  - rewrite E. destruct (find_in_slots sl' _ _ 0 p); [left; reflexivity | exact REC].
  - right; left. rewrite Hk. eexists q, k, _. split; [reflexivity|]. split; [left; reflexivity|]. unfold nth_slot. cbn [am_slots]. rewrite Z.sub_0_r in Hg. exact Hg.
  - right; right. rewrite Hk. eexists q, k, _. split; [reflexivity|]. split; [left; reflexivity|]. unfold nth_slot. cbn [am_slots]. rewrite Z.sub_0_r in Hg. exact Hg.
Qed.

Definition ffr (s t : astate) (r r' : (sptr * Z) * astate) : Prop := ltac2:(tb__ "0|5|
S1S0S8SadSa5S9S96A2M0S8Vr;A3Vs;A3S1S0S8SadG0S8Vr';A3Vt;A3S3S0G0SafG0S8Vr;A3M1SafG0S8Vr';A3M2A3S3S2ScScS1S0Sa7SbA1M3Sb9Vs;SafS9S96G1A3A2SabSbSdR1A1A2M4A3S0Sa8S12SfR1SadS9S96G1A3A2A1SaeA3A2Lam;A2S2ScScS1S0G3Sb9Vt;SafS9S96G2A3A2G4A3S0Sa8S12SfR1SadS9S96G2A3A2A1SaeA3A2Lam';A2A2A2A2A2").

Lemma rsim_find_frame p s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S98Sa5Sa5S9S96A2S8A2M0G0Sa2Vs;Vt;A2S51Vp;Vs;A2S51Vp;Vt;A2A5F_;").
Proof.
  intros H. unfold find_frame. rstep.
  destruct (find_frame_in_rel _ _ p (sheq_metas _ _ H)) as [E | [(m & k & am & Hf & Hin & Hg) | (m & k & am & Hf & Hin & Hg)]].
  - rewrite <- E. destruct (find_frame_in (st_metas s) p); [|apply rsim_ifail_l]. apply rsim_ret. split; [reflexivity|]. split; [reflexivity|]. left. reflexivity.
  - rewrite Hf. destruct (find_frame_in (st_metas t) p); [|apply rsim_ifail_r]. apply rsim_ret. split; [reflexivity|]. split; [reflexivity|].
    right; left. exists am. cbn [fst snd]. split; [|exact Hg]. unfold MT. apply mlookup_of_In; [exact (sheq_nodup_l _ _ H) | exact Hin].
  - rewrite Hf. destruct (find_frame_in (st_metas s) p); [|apply rsim_ifail_l]. apply rsim_ret. split; [reflexivity|]. split; [reflexivity|].
    right; right. exists am. cbn [fst snd]. split; [|exact Hg]. unfold MT. apply mlookup_of_In; [exact (sheq_nodup_r _ _ H) | exact Hin].
Qed.

Lemma rsim_parent_check_fail_l {B C} (R : C * astate -> B -> Prop) m k am s (K : unit -> M C) (y : itree astate B) : ltac2:(tb__ "0|0|
S0Sa7SbA1Sb9Vs;Vm;A2SabSbSdVam;A1A2A3S0Sa8S12SfVam;Vk;A2A1SaeA3S98Sa5VC;S8A2VB;VR;S14ScVC;S20Vm;A1ScS14Sa6VC;S15S12SfR1Vk;A2A1ZaA2VK;A4Lamp;Vs;A5Vy;A5F_;F_;").
Proof.
  intros Hm Hg. unfold bind at 1. unfold getm, bind, get. cbn [ibind]. unfold MT in Hm. rewrite Hm. cbn [ibind ret].
  unfold mcheck. rewrite Hg. cbn. apply rsim_ifail_l.
Qed.

Lemma rsim_parent_check_fail_r {A C} (R : A -> C * astate -> Prop) m k am t (K : unit -> M C) (x : itree astate A) : ltac2:(tb__ "0|0|
S0Sa7SbA1Sb9Vt;Vm;A2SabSbSdVam;A1A2A3S0Sa8S12SfVam;Vk;A2A1SaeA3S98VA;Sa5VC;S8A2VR;Vx;S14ScVC;S20Vm;A1ScS14Sa6VC;S15S12SfR1Vk;A2A1ZaA2VK;A4Lamp;Vt;A5A5F_;F_;").
Proof.
  intros Hm Hg. unfold bind at 1. unfold getm, bind, get. cbn [ibind]. unfold MT in Hm. rewrite Hm. cbn [ibind ret].
  unfold mcheck. rewrite Hg. cbn. apply rsim_ifail_r.
Qed.

Definition hdr_known_at (s : astate) (g : sptr) (i : Z) : Prop := ltac2:(tb__ "0|1|
ScS11S0Sa7SbA1Sb9Vs;Vg;A2SabSbSdR2A1A2A3S0Sa7S11A1S3eSfR3Vi;A2A1SabS11R2A2A3S0S96S3dR3A1Z0A3S7S0Sa7Sa5S96S96A2M0A1S19SfR5Vi;A2A1Sb2G0A1A3A1F_;F_;F_;Ffr;Fam;").

Lemma rsim_release_slot g i s t : ltac2:(tb__ "0|1|
S97Vs;Vt;A2S9cVs;Vg;Vi;A3S9cVt;Vg;Vi;A3S98Sa5Sa6S8A2M0G0S99Sa6A1S69Vg;Vi;Vs;A3S69Vg;Vi;Vt;A3A5F_;F_;F_;").
Proof.
  intros H H0s H0t. unfold release_slot. rstep.
  set (am := mkAMeta pr nx mem av frd la sc ml ai sl) in *. set (am' := mkAMeta pr nx mem av frd la sc ml ai sl') in *.
  assert (EN : erase_slot (nth_slot am i) = erase_slot (nth_slot am' i)) by (apply map_erase_nth_slot; exact ES).
  pose proof (erase_slot_inv _ _ EN) as [EH FR].
  apply rsim_setm; [exact H|]. subst am am'. unfold upd_slot. amsimp. apply erase_am_mk. apply map_erase_lupd; [exact ES|].
  match goal with |- erase_slot (match ss_fr ?x with _ => _ end) = erase_slot (match ss_fr ?x' with _ => _ end) =>
    set (sx := x) in *; set (sx' := x') in * end.
  destruct (ss_fr sx) as [fr|] eqn:F, (ss_fr sx') as [fr'|] eqn:F'; try contradiction; [|exact EN].
  destruct FR as (En & Ek & Eo).
  destruct (fr_off fr =? 0) eqn:O, (fr_off fr' =? 0) eqn:O'.
  - reflexivity.
  - apply Z.eqb_eq in O. specialize (H0s _ fr Ms F O). destruct (ss_hdr sx') eqn:Eh'; [reflexivity|]. exfalso. apply H0s. apply (proj2 EH). reflexivity.
  - apply Z.eqb_eq in O'. specialize (H0t _ fr' Mt F' O'). destruct (ss_hdr sx) eqn:Eh; [reflexivity|]. exfalso. apply H0t. apply (proj1 EH). reflexivity.
  - apply erase_slot_rehdr. exact EN.
Qed.

Lemma rsim_nontrivial_free fuel g i s t : ltac2:(tb__ "0|2|
S97Vs;Vt;A2S98Sa5Sa7Sa5Sb1S96A2A1M0S8A2M1G1S99G0A1S63Vfuel;Vg;Vi;Vs;A4S63Vfuel;Vg;Vi;Vt;A4A5F_;").
Proof.
  revert g i s t. induction fuel as [|f IH]; intros g i s t H; [cbn; apply rsim_ifail_l|].
  cbn fix beta iota delta [nontrivial_free]. unfold okay_to_free. rauto.

  eapply rsim_bind.
  { rcase; [rauto|].
    rbind ltac:(apply rsim_find_frame; assumption).
    destruct HR as (E1 & E2 & CASES); cbn [fst snd] in E1, E2, CASES; subst.
    destruct CASES as [<- | [(am0 & M0 & G0) | (am0 & M0 & G0)]].
    - rauto.
    - eapply rsim_parent_check_fail_l; eassumption.
    - eapply rsim_parent_check_fail_r; eassumption. }
  rintro; rauto.
Qed.
Global Hint Resolve rsim_nontrivial_free : rsim.

Lemma rsim_free p p' g i s t : ltac2:(tb__ "0|4|
S97Vs;Vt;A2S0Sa7Sa5S9S96A2M0A1M1S1dSeVs;A1Vp;A2SabG0Sa9S9S96Vg;Vi;A4A2M2A3S0G1S1dSeVt;A1Vp';A2G2A3S9cVs;Vg;Vi;A3S9cVt;Vg;Vi;A3S98Sa5Sa6S8A2M3G3S99Sa6A1S55SabS9Vp;A2Vs;A2S55SabS9Vp';A2Vt;A2A5F_;F_;F_;F_;F_;").
Proof.
  intros H Fs Ft H0s H0t. unfold free.
  eapply (rsim_bind (fun r r' => r = ((g, i), s) /\ r' = ((g, i), t))).
  { unfold find_frame. rstep. rewrite Fs, Ft. apply rsim_ret. split; reflexivity. }
  intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->. cbn beta iota zeta delta [fst snd].
  rstep. rbind ltac:(apply rsim_release_slot; assumption). rauto.
Qed.
