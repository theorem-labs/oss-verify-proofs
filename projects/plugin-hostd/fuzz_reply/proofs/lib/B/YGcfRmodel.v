(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfRmodel.v, sha256 bf58f1888240282196dbac88eb4ce83e0d073c4157cb1191884767c8a5f6c2a1 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
   Modules that are per image in this tree (lane W's AllocG / DeallocG / DMspec / DMiface / ImgBaseDG / DGif0, the F1 core's
   YGcfRehidePost / YGcfRecStep, and the per-image cf files of this carry) name lib/B; a sentence is split at a directory
   change, the module order kept.
*)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the text is otherwise unchanged. *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the model obligations of
   c-asan's realloc composition.
   The obligations are a Theorem Labs lane's RGtop.rmodel_ok itself (RGtop.v:227, the c5 form; RGtop.v is a by-path copy of
   478a815d97c). Its section closes over the variables its body uses, in their declaration order: U mt ft AOX rpre
   nmax lmax rU rpreA rpreD. gflag is YG0d.gflag, as in RGtop.
   The instance: U := rU := admits (as_universe B) (the P'' trace premise, YG01.v:156; a Theorem Labs lane 22:05Z), mt := malloc_cf,
   ft := free_cf, nmax := cf_malloc_max, lmax := LIVE_MAX, AOX := cgif's aowned (YG0n.v:236-242) or the live
   error-buffer extent xs_cf (YG0ncf.v:341). The two U conclusions (U tr S1 after the entry step, q <> PNull ->
   U tr S2 after the inner malloc) follow from the entry premise rU tr S by admits_keep (YG01.v:222): free_cf PNull
   keeps the depot (cfr_null_state), and malloc_cf keeps it or appends tr (YGcfAmx.v dep_malloc_cf_apath).
   rpre cannot be True: the inner malloc's post (the new block live, the old blocks kept, the new base fresh)
   is malloc_post_cf, which holds only from a Wf_cf state with the three input-driven room facts (ROOM_cf,
   YGcfRoomPre.v); rmodel_ok's premises give no allocator relation to read them from. So rpre_cfr is
   universe_ok, Wf_cf and ROOM_cf at the entry state. The entry step free_cf PNull is a tick and the
   internal-init flag alone (cfr_null_state), so it keeps the chunks, the secondaries, the frames, the regions
   and the secondary array, hence the blocks, the live bytes, ROOM_cf (YGcfAmx2.ROOM_cf_nfr) and AOX.
   rmodel_ok_cf_wf: the strongest form, with rpreA := rpre_cfr (the entry facts hold again after free_cf PNull)
   and rpreD := universe_ok and Wf_cf after the inner malloc; rmodel_ok_cf: the form with rpreA := rpreD := True
   (AllocG.v's shared-instance rpre), by rmodel_ok_mono. No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YG06bcf YG07cf YGcfRoomPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG03cf YG03dcf YGcfAmx YGcfAmx2 YGcfApath.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RGtop.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. A Theorem Labs lane's rmodel_ok: RGtop.rmodel_ok. rpreA and rpreD occur only in conclusions. *)
Lemma rmodel_ok_mono : forall U mt ft AOX rpre nmax lmax rU (rpreA rpreD rpreA' rpreD' : astate -> Z -> Prop),
(forall S n, rpreA S n -> rpreA' S n) -> (forall S n, rpreD S n -> rpreD' S n) ->
RGtop.rmodel_ok U mt ft AOX rpre nmax lmax rU rpreA rpreD -> RGtop.rmodel_ok U mt ft AOX rpre nmax lmax rU rpreA' rpreD'.
Proof.
intros U mt ft AOX rpre nmax lmax rU rpreA rpreD rpreA' rpreD' HA HD H. unfold RGtop.rmodel_ok in *. destruct H as [H1 H2]. split.
- intros S n tr trc S1 R N L T P G. destruct (H1 S n tr trc S1 R N L T P G) as (U1 & A & K).
exact (conj U1 (conj (HA _ _ A) K)).
- intros S n tr trc1 S1 trc2 q S2 R N L T P1 G1 P2 G2.
destruct (H2 S n tr trc1 S1 trc2 q S2 R N L T P1 G1 P2 G2) as (U2 & Q & K). split; [exact U2|]. split; [exact Q|].
intros p n_old Hin. destruct (K p n_old Hin) as (Hi & D & E). split; [exact Hi|]. split; [|exact E].
intros Hq. exact (HD _ _ (D Hq)).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The instance's premises.                                                    *)
(* With the driver's hull admission at the call LAST (field round 3, Main 2026-10-30: the same route as
   rpreD_free_cf; rpre_cfr_of_pre takes it from acall_pre_cf's conjunct). *)
Definition rpre_cfr {ci : CfImg} {cp : CfParams} (B : asyms) (S : astate) (n : Z) : Prop :=
universe_ok (as_universe B) /\ Wf_cf (as_universe B) S /\ ROOM_cf S /\ cf_hull_ok S.

Definition rpreD_cfr {cp : CfParams} (B : asyms) (S : astate) (n : Z) : Prop :=
universe_ok (as_universe B) /\ Wf_cf (as_universe B) S.

(* ---------------------------------------------------------------------------- *)
(* 3. The entry step free_cf PNull: a tick and the internal-init flag set (it was set already, or it is set). *)
Lemma cfr_null_state {ci : CfImg} : forall tr S trc S1, apath (free_cf PNull tr S) trc (tt, S1) ->
S1 = set_internal_inited true (set_nev (st_nev S + 1) S).
Proof.
intros tr S trc S1 H. unfold free_cf, tick, bind, get, modify, ret in H. cbn in H.
destruct (st_internal_inited S) eqn:Ei; cbn in H; (destruct trc as [|e trc]; [|destruct H]);
apply (f_equal snd) in H; cbn [snd] in H; subst S1; unfold set_internal_inited, set_nev; cbn;
try rewrite Ei; reflexivity.
Qed.

Lemma cfr_null_keep {ci : CfImg} : forall tr S trc S1, apath (free_cf PNull tr S) trc (tt, S1) ->
nfr S S1 /\ blocks S1 = blocks S /\ blocks_bytes S1 = blocks_bytes S /\ st_secs S1 = st_secs S /\
(forall B ly a, aowned B ly S1 a \/ Exists (in_zr a) (xs_cf ly S1) -> aowned B ly S a \/ Exists (in_zr a) (xs_cf ly S)).
Proof.
intros tr S trc S1 H. rewrite (cfr_null_state tr S trc S1 H).
(split; [unfold nfr; split; [reflexivity | split; reflexivity]|]);
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; intros B ly a Ha; exact Ha.
Qed.

(* Wf_cf after free_cf PNull, from ml_free_cf on the path. *)
Lemma cfr_null_wf {ci : CfImg} {cp : CfParams} : forall U tr S trc S1, universe_ok U -> Wf_cf U S -> batch_room_cf S ->
admits U tr S -> apath (free_cf PNull tr S) trc (tt, S1) -> Wf_cf U S1.
Proof.
intros U tr S trc S1 HU HW HB Htr Hp.
assert (A : atok_cf true (free_cf PNull tr S) (free_post_ycf U S PNull 0)).
{ eapply ml_free_cf; eauto. }
destruct (atok_cf_apath _ _ _ trc (tt, S1) A Hp) as [ns F].
unfold free_post_ycf in F. cbn [snd] in F. exact (proj1 F).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. rmodel_ok at the cf instance.                                               *)
Theorem rmodel_ok_cf_wf {ci : CfImg} {cp : CfParams} : forall B,
RGtop.rmodel_ok (admits (as_universe B)) malloc_cf free_cf
(fun ly S a => aowned B ly S a \/ Exists (in_zr a) (xs_cf ly S))
(rpre_cfr B) cf_malloc_max LIVE_MAX (admits (as_universe B)) (rpre_cfr B) (rpreD_cfr B).
Proof.
intros B. unfold RGtop.rmodel_ok. split.
- intros S n tr trc S1 (HU & HW & HR & HO) Hn Hl Htr Hp _.
destruct (cfr_null_keep tr S trc S1 Hp) as (N1 & B1 & BB1 & X1 & A1).
pose proof HR as (_ & _ & HB).
(* U tr S1: free(NULL) keeps the depot, so the entry premise carries over (admits_keep). *)
split; [apply (admits_keep _ tr S S1 Htr); left; rewrite (cfr_null_state tr S trc S1 Hp); reflexivity|].
split; [| split; [rewrite BB1; exact Hl|]; split; [exact B1|]; split; [rewrite X1; apply Nat.le_refl | exact (A1 B)]].
split; [exact HU|]. split; [exact (cfr_null_wf _ tr S trc S1 HU HW HB Htr Hp)|].
split; [exact (ROOM_cf_nfr S S1 N1 HR)|].
(* the admission: free_cf PNull keeps st_secs, so both meters (CfParams.cf_hull_counts) *)
rewrite (cfr_null_state tr S trc S1 Hp).
exact (cf_hull_counts (set_internal_inited true (set_nev (st_nev S + 1) S)) S eq_refl eq_refl HO).
- intros S n tr trc1 S1 trc2 q S2 (HU & HW & HR & _) Hn Hl Htr Hp1 _ Hp2 _.
(* U tr S1 and U tr S2: free(NULL) keeps the depot; malloc_cf keeps it or appends tr (dep_malloc_cf_apath). *)
assert (Htr1 : admits (as_universe B) tr S1)
  by (apply (admits_keep _ tr S S1 Htr); left; rewrite (cfr_null_state tr S trc1 S1 Hp1); reflexivity).
assert (Htr2 : admits (as_universe B) tr S2).
{ apply (admits_keep _ tr S1 S2 Htr1). pose proof (dep_malloc_cf_apath n tr S1 trc2 (q, S2) Hp2) as D. cbn [snd] in D. exact D. }
split; [intros _; exact Htr2|].
destruct (cfr_null_keep tr S trc1 S1 Hp1) as (N1 & B1 & BB1 & _ & _).
pose proof HR as (_ & _ & HB).
pose proof (cfr_null_wf _ tr S trc1 S1 HU HW HB Htr Hp1) as W1.
destruct (ROOM_cf_nfr S S1 N1 HR) as (HS1 & HE1 & HB1).
assert (Hl1 : blocks_bytes S1 + n <= LIVE_MAX) by (rewrite BB1; exact Hl).
pose proof (malloc_cf_apath_post (as_universe B) S1 n tr trc2 (q, S2) HU W1 ltac:(lia) Hl1 Htr1 HS1 HE1 HB1 Hp2) as M2.
unfold malloc_post_cf in M2. destruct M2 as (W2 & _ & _ & _ & Bl2 & _).
assert (BL : (q = PNull /\ blocks S2 = blocks S1) \/
(q <> PNull /\ blocks S2 = blocks S1 ++ [(q, n)] /\ ~ In q (map fst (blocks S1)))).
{ destruct q as [|qo|qr qo|qc qp]; [left; split; [reflexivity | exact Bl2] | ..];
right; (split; [discriminate|]); exact Bl2. }
rewrite B1 in BL. destruct BL as [(Eq & E2) | (Hq & E2 & Hf)].
+ subst q. split; [intros C; exfalso; apply C; reflexivity|].
intros p n_old Hin. split; [rewrite E2; exact Hin|]. split; intros C; exfalso; apply C; reflexivity.
+ split; [intros _; rewrite E2; apply in_or_app; right; left; reflexivity|].
intros p n_old Hin. split; [rewrite E2; apply in_or_app; left; exact Hin|].
split; [intros _; exact (conj HU W2)|].
intros _ Ep. subst p. apply Hf. apply in_map_iff. exists (q, n_old). split; [reflexivity | exact Hin].
Qed.

(* The form with AllocG.v's shared-instance premises: rpreA := rpreD := True. *)
Theorem rmodel_ok_cf {ci : CfImg} {cp : CfParams} : forall B,
RGtop.rmodel_ok (admits (as_universe B)) malloc_cf free_cf
(fun ly S a => aowned B ly S a \/ Exists (in_zr a) (xs_cf ly S))
(rpre_cfr B) cf_malloc_max LIVE_MAX (admits (as_universe B)) (fun _ _ => True) (fun _ _ => True).
Proof.
intros B. eapply rmodel_ok_mono; [| | exact (rmodel_ok_cf_wf B)]; intros S n _; exact I.
Qed.
