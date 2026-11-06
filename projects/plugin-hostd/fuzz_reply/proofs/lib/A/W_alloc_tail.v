(* ALLOC_TAIL as a theorem of AR, for every allocator instance B: the rest of a live block's last 8-byte granule is
   visible (aview <> None) in every AR state.  Proof by a Theorem Labs lane (zz_alloc_tail_gen, its gs_scan placement probe):
   In_ablocks -> chunk_facts -> ck_extent mod 8 = 0 -> the granule tail lies in chunk_junk's last range -> am_junk
   makes it visible.  The drain walks stated this as a Section hypothesis "asked of the allocator instance"; it is
   not an instance obligation, so W_drain_pb.v discharges it from here and pb_drain no longer takes it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0s.
Import ListNotations.
Open Scope Z_scope.

Lemma at_in_zseq : forall lo n a, lo <= a < lo + n -> In a (YG0n.zseq lo n).
Proof.
intros lo n a H. unfold YG0n.zseq. apply in_map_iff. exists (Z.to_nat (a - lo)). split.
- rewrite Z2Nat.id by lia. lia.
- apply in_seq. lia.
Qed.

Lemma at_cls8 : forall c, 1 <= c <= 30 -> class_size c mod 8 = 0.
Proof.
intros c Hc.
assert (A : forallb (fun c => class_size c mod 8 =? 0) (YG0n.zseq 1 30) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in A. apply Z.eqb_eq. apply A. apply at_in_zseq. lia.
Qed.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma at_ext8 : forall (B : asyms) ly S k, YG0s.cfacts B ly S k -> ck_extent k mod 8 = 0.
Proof.
intros B ly S k (_ & _ & _ & _ & _ & _ & _ & _ & G9).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct G9].
- cbv beta iota zeta in G9. destruct G9 as (Hc & _ & _ & He & _). rewrite He. apply at_cls8. exact Hc.
- cbv beta iota in G9. destruct G9 as (_ & _ & _ & He & _). rewrite He. unfold sec_map_size, round_up, kPage.
  assert (E : forall q, (q * 4096 + 4096 - 4096) mod 8 = 0)
    by (intros q; replace (q * 4096 + 4096 - 4096) with (q * 512 * 8) by lia; apply Z.mod_mul; lia).
  apply E.
Qed.

Lemma alloc_tail : forall (segs : list Segment) (B : asyms) ly S (W : world segs) mem md p n a,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview segs (w_H W) mem a <> None.
Proof.
intros segs B ly S W mem md p n a HAR Hin Ha.
destruct HAR as (HM & _).
apply YG0s.In_ablocks in Hin as (k & Hk & Hst & Hu & Hr).
pose proof (YG0s.chunk_facts B ly S _ k HM Hk) as CF.
pose proof (at_ext8 B ly S k CF) as E8.
destruct CF as (_ & _ & G3 & G4 & _ & _ & _ & G8 & _).
assert (HJ : In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S)).
{ unfold ajunk. right. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|]. unfold chunk_junk.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ HM) _ HJ) as V.
unfold range_vis in V. cbn [fst snd] in V.
rewrite aeval_aoff in V by (intros e' Ee; destruct (ck_beg k); cbn in Ee; discriminate Ee).
change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
unfold ck_n in V. rewrite <- Hu, G4, <- Hr in Ha.
pose proof (Z.div_mod (ck_base B ly k) 16 ltac:(lia)) as D1.
pose proof (Z.div_mod (ck_extent k) 8 ltac:(lia)) as D2.
pose proof (Z.div_mod (ck_base B ly k + ck_rz k + req_size (ck_req k) - 1) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (ck_base B ly k + ck_rz k + req_size (ck_req k) - 1) 8 ltac:(lia)) as D4.
specialize (V (a - (ck_base B ly k + (ck_rz k + req_size (ck_req k))))).
replace (ck_base B ly k + (ck_rz k + req_size (ck_req k)) + (a - (ck_base B ly k + (ck_rz k + req_size (ck_req k)))))
  with a in V by lia.
apply V. lia.
Qed.
End t.
