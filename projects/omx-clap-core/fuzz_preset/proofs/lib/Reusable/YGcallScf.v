(* Theorem Labs, 2026-10: the generic-to-cf BRIDGE for the frame-area rules of YGcallSx.v (aj_stack_malloc_at_x,
   aj_flag_store_x). Every Section hypothesis of those rules is discharged here, PROVED, at the walks' relation
     ARxs := fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S   (YGcallcf.v; YG0ncf.v).
   1. The model (any relation ARx; the relation premise is not read):
      - SMX : stack_malloc_x_any. The progress half is cgif YG05.v:70 stack_malloc_progress, whose proof never reads its
        Wf premise, restated without it (stack_malloc_progress_any); the post half comes from stack_malloc's
        definition (YG00.v:570-579) and YG05.v's fs_probe_some (stack_malloc_apath_post).
      - SFX : stack_free_x_any. cgif reads it from Wf's NoDup through YG05.v:118 del_pos_spec; del_pos removes the
        FIRST occurrence, so the split exists without NoDup (del_pos_split).
   2. The callee text: astack_malloc_realizes_x_conj lifts FCiface's text from ARx to ARx /\ P for any P that set_fs
      keeps (a frame-area malloc changes only st_fs: stack_malloc_apath_set_fs); xs_placed_cf is such a P
      (xs_placed_cf_set_fs: it reads ly, st_secs, st_chunks and errb_e only, so the proof is conversion).
      astack_malloc_realizes_cf_x: the cf text YG0dcf.v astack_malloc_realizes_cf IS the generic text at ARcf;
      astack_malloc_realizes_cf_xs: the cf text gives the text at ARxs.
   3. The flag store's laws at ARxs:
      - ASFX : astack_free_x_xs, from h-asan-init-2's astack_free_law_ok_cf (YG0tcf.v:476) and xs_placed_cf kept by
        stack_free_state (a set_fs);
      - FFLX : frame_flag_x_xs, from AR_flag_law_ok_cf and AR_client_img_law_ok_cf (YG0scf.v): the flag byte is
        runtime-owned, an application address, and off the image. No image premise.
   Numerals: 0, 10 (the frame classes, cgif's range: DERIVED). No ADDRESS. Uses the shared cf classes CfImg /
   CfParams only; no preset name, no ledger. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0scf YG0tcf FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The model's frame-area malloc and free.                                     *)

(* del_pos removes the first occurrence: the split needs no NoDup (cgif YG05.v:118 del_pos_spec takes one). *)
Lemma del_pos_split : forall l cid pos, In (cid, pos) l ->
exists l1 l2, l = l1 ++ (cid, pos) :: l2 /\ del_pos l cid pos = l1 ++ l2.
Proof.
induction l as [|[c p] t IH]; intros cid pos Hin; [destruct Hin|]. cbn [del_pos].
destruct (andb (c =? cid) (p =? pos)) eqn:E.
- apply Bool.andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst. exists [], t. split; reflexivity.
- destruct Hin as [Heq|Hin]; [injection Heq as -> ->; rewrite !Z.eqb_refl in E; discriminate|].
  destruct (IH cid pos Hin) as (l1 & l2 & -> & E2). exists ((c, p) :: l1), l2. rewrite E2. split; reflexivity.
Qed.

Lemma stack_free_frames : forall S cid pos, In (cid, pos) (frames S) ->
exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Proof. intros S cid pos Hin. exact (del_pos_split (frames S) cid pos Hin). Qed.

(* cgif YG05.v:70 stack_malloc_progress without its Wf premise, which its proof never reads. *)
Lemma stack_malloc_progress_any : forall S cid, 0 <= cid <= 10 -> count_cid cid (frames S) < fs_frames cid ->
exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S').
Proof.
intros s cid Hc Hcnt. pose proof (YG05.fs_frames_pos cid Hc) as HN.
unfold stack_malloc, YG00.bind, YG00.get, YG00.put, YG00.ret. cbn [ibind].
destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs s)) cid (znth 0 cid (fs_hint (st_fs s)))) as [[pos hint']|] eqn:EP.
- cbn [ibind]. exists pos. eexists. reflexivity.
- exfalso. set (N := fs_frames cid) in *. set (hint := znth 0 cid (fs_hint (st_fs s))) in *.
  pose proof (YG05.fs_probe_none _ _ _ _ EP) as ALL.
  pose proof (YG05.count_cid_ge cid (fs_live (st_fs s)) (map (fun j => (hint + Z.of_nat j) mod N) (seq 0 (Z.to_nat N)))
    (YG05.mod_window_nodup N hint (Z.to_nat N) HN ltac:(lia))) as GE.
  rewrite length_map, length_seq in GE. unfold frames in Hcnt.
  specialize (GE ltac:(apply Forall_forall; intros p Hp; apply in_map_iff in Hp as (j & <- & Hj); apply in_seq in Hj;
    apply YG05.mem_pos_spec; apply ALL; lia)). lia.
Qed.

(* A frame-area malloc's result state differs from its entry state in st_fs only. *)
Lemma stack_malloc_apath_set_fs : forall S cid pos S',
apath (stack_malloc cid S) [] (PFake cid pos, S') -> exists f, S' = set_fs f S.
Proof.
intros S cid pos S'. unfold stack_malloc, YG00.bind, YG00.get, YG00.put, YG00.ret. cbn [ibind].
destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S)))) as [[pos0 hint']|];
cbn [ibind apath]; intros Hpath.
- apply pair_equal_spec in Hpath as [_ E]. eexists. symmetry. exact E.
- apply pair_equal_spec in Hpath as [E _]. discriminate E.
Qed.

(* cgif's stack_malloc_post (YG01.v:462) at a PFake result, from the definition: the frame pushed is fresh. *)
Lemma stack_malloc_apath_post : forall S cid pos S', 0 <= cid <= 10 ->
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
(exists f, S' = set_fs f S) /\ frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
Proof.
intros S cid pos S' Hc. pose proof (YG05.fs_frames_pos cid Hc) as HN.
unfold stack_malloc, YG00.bind, YG00.get, YG00.put, YG00.ret. cbn [ibind].
destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S)))) as [[pos0 hint']|] eqn:EP;
cbn [ibind apath]; intros Hpath.
- apply pair_equal_spec in Hpath as [E1 E2]. assert (pos0 = pos) as <- by congruence. subst S'.
  split; [eexists; reflexivity|]. split; [reflexivity|].
  destruct (YG05.fs_probe_some _ _ _ _ _ _ HN EP) as (h & _ & _ & _ & Hm). exact (YG05.mem_pos_false _ _ _ Hm).
- apply pair_equal_spec in Hpath as [E _]. discriminate E.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* YGcallSx.v's SMX, at any relation ARx. *)
Lemma stack_malloc_x_any : forall segs (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
count_cid cid (frames S) < fs_frames cid ->
exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
Proof.
intros segs ARx ly S Hp W mem md cid _ Hc Hcnt.
destruct (stack_malloc_progress_any S cid Hc Hcnt) as (pos & S' & Hpath).
exists pos, S'. split; [exact Hpath | exact (stack_malloc_apath_post S cid pos S' Hc Hpath)].
Qed.

(* YGcallSx.v's SFX, at any relation ARx. *)
Lemma stack_free_x_any : forall segs (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Proof. intros segs ARx ly S Hp W mem md cid pos _ Hin. exact (stack_free_frames S cid pos Hin). Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. FCiface's frame-area text, lifted to ARx /\ P for a P that set_fs keeps.    *)
Lemma astack_malloc_realizes_x_conj : forall segs B
(ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
(P : alayout -> astate -> Prop) cid,
(forall ly S f, P ly S -> P ly (set_fs f S)) ->
astack_malloc_realizes_x segs B ARx cid ->
astack_malloc_realizes_x segs B (fun ly S Hp W mem md => ARx ly S Hp W mem md /\ P ly S) cid.
Proof.
intros segs B ARx P cid HPk ASM ly S Hp W regs mem md pos S' ((HAR & HP) & R) Hcnt Hpath.
destruct (stack_malloc_apath_set_fs S cid pos S' Hpath) as (f & ES').
assert (HP' : P ly S') by (rewrite ES'; exact (HPk ly S f HP)).
eapply SRr_mono; [exact (ASM ly S Hp W regs mem md pos S' (conj HAR R) Hcnt Hpath)|].
cbv beta. intros W2 c2 _ (-> & regs' & mem' & md' & Hc & HAR' & Rest).
split; [reflexivity|]. exists regs', mem', md'. split; [exact Hc|]. split; [exact (conj HAR' HP') | exact Rest].
Qed.
End a.

(* ---------------------------------------------------------------------------- *)
(* 3. The cf instance.                                                            *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Lemma xs_placed_cf_set_fs : forall ly S f, xs_placed_cf ly S -> xs_placed_cf ly (set_fs f S).
Proof. intros ly S f H. exact H. Qed.

Lemma xs_placed_cf_stack_free : forall ly S cid pos, xs_placed_cf ly S -> xs_placed_cf ly (stack_free_state cid pos S).
Proof. intros ly S cid pos H. exact (xs_placed_cf_set_fs ly S _ H). Qed.

Variable segs : list Segment.
Variable B : asyms.

Lemma astack_malloc_realizes_cf_x : forall cid,
astack_malloc_realizes_cf segs B cid = astack_malloc_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) cid.
Proof. reflexivity. Qed.

Lemma astack_malloc_realizes_cf_xs : forall cid, astack_malloc_realizes_cf segs B cid ->
astack_malloc_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S) cid.
Proof.
intros cid H.
exact (astack_malloc_realizes_x_conj segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) xs_placed_cf cid
  xs_placed_cf_set_fs H).
Qed.

(* YGcallSx.v's ASFX at ARxs. *)
Lemma astack_free_x_xs : forall ly S Hp W mem md mem' md' cid pos,
ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S -> In (cid, pos) (frames S) ->
aview segs (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARcf segs B ly (stack_free_state cid pos S) Hp W mem' md' /\ xs_placed_cf ly (stack_free_state cid pos S).
Proof.
intros ly S Hp W mem md mem' md' cid pos [HAR HX] Hin H0 H1 H2 H3 H4 H5 H6.
exact (conj (astack_free_law_ok_cf segs B ly S Hp W mem md mem' md' cid pos HAR Hin H0 H1 H2 H3 H4 H5 H6)
  (xs_placed_cf_stack_free ly S cid pos HX)).
Qed.

(* YGcallSx.v's FFLX at ARxs: the flag byte is runtime-owned and an application address (AR_flag_law_ok_cf), and
   off the image (AR_client_img_law_ok_cf, the flag arm). *)
Lemma frame_flag_x_xs : forall ly S Hp (W : world segs) mem md cid pos,
ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S -> In (cid, pos) (frames S) ->
aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img segs (flag_addr ly cid pos)).
Proof.
intros ly S Hp W mem md cid pos [HAR _] Hin.
destruct (AR_flag_law_ok_cf segs B ly S Hp W mem md cid pos HAR Hin) as (_ & Hown & Hia & _).
destruct (AR_client_img_law_ok_cf segs B ly S Hp W mem md (flag_addr ly cid pos) HAR
  (or_intror (or_intror (ex_intro _ cid (ex_intro _ pos (conj Hin eq_refl)))))) as [_ Himg].
split; [exact Hown|]. split; [apply (in_app_addr _ _ _ Hia); lia | exact Himg].
Qed.
End c.
