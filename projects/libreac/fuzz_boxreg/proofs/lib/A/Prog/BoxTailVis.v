(* libreac/fuzz_boxreg: proof of asn_blk_tail_vis (lib/A/Rt/SnprintfDef.v) and of its B twin absn_blk_tail_vis
   (lib/B/Rt/SnprintfDefB.v), which has the same text. Both are proved from one lemma over the core's AR,
   ar_blk_tail_vis: in every AR state, the bytes of a heap block (p, n) from p + n up to p + round_up n 8 are readable.
   Why: the block is the user part of an allocated chunk k (ablocks over YG01.blocks), so p = ck_base k + ck_rz k and
   n = ck_req k. If n = 0 the range is empty. Else ck_n k = n, and AR's am_junk (lib/Reusable/YG0n.v:219) keeps every
   range of chunk_junk k visible, the last of which is (ck_base k + ck_rz k + n, ck_extent k - ck_rz k - n)
   (YG0n.v:60). That range covers the bytes because round_up n 8 <= ck_extent k - ck_rz k: n <= ck_extent k - ck_rz k
   (cfacts, lib/Reusable/YG0s.v:229) and ck_extent k - ck_rz k is a multiple of 8 (ck_rz k mod 16 = 0, YG0s.v:228; a
   primary chunk's extent is class_size c with class_size c mod 32 = 0, YG0a.v:28-30; a secondary chunk's extent is
   sec_map_size n - kPage with sec_map_size n mod kPage = 0, YG0a.v:112).
   Rule 24 (record): proof-index snprintf (exit 0, index main@e966c513ee6 / recipes@566eb6ffa5d) lists no
   heap-tail lemma; git grep of blk_tail_vis / chunk_junk_vis / junk_tail over main, ossv/recipes, ossv/candidates and
   release/pau-projects-recipes: none. Cold refs: PROVISIONAL, a full (an internal command) search is
   running (a Theorem Labs lane, 2026-10-29); if it finds an equivalent lemma this file is replaced by it or cites it. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require SnprintfDefB.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* The last range of chunk_junk k is a range of the state's junk. *)
Lemma chunk_tail_in_ajunk : forall ly S k, In k (st_chunks S) ->
In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S).
Proof.
intros ly S k Hk. unfold ajunk. right. right.
apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
apply in_flat_map. exists k. split; [exact Hk|].
unfold chunk_junk. cbv zeta.
apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.
(* A chunk's extent minus its left redzone is a multiple of 8. *)
Lemma chunk_room_mod8 : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) -> (ck_extent k - ck_rz k) mod 8 = 0.
Proof.
intros ly S rd k M Hk.
pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & RZ & _ & _ & G).
assert (EX : ck_extent k mod 8 = 0).
{ destruct (ck_beg k) as [|off|r o|c q]; try solve [destruct G].
  - cbv zeta in G. destruct G as (Gc & _ & _ & Gext & _).
    pose proof (class_ok (prim_class off) ltac:(lia)) as (_ & K2 & _). rewrite Gext.
    apply Z.mod_divide in K2 as [q K2]; [|lia]. rewrite K2. replace (q * 32) with ((q * 4) * 8) by lia. apply Z.mod_mul. lia.
  - destruct G as (_ & Hp & _ & Gext & _). pose proof (secondary_geometry (ck_req k)) as SG.
    pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & _ & Hn & _).
    destruct (SG ltac:(lia) Hp) as (_ & _ & _ & _ & S5 & _). rewrite Gext.
    apply Z.mod_divide in S5 as [q S5]; [|unfold kPage; lia]. rewrite S5. unfold kPage.
    replace (q * 4096 - 4096) with ((q * 512 - 512) * 8) by lia. apply Z.mod_mul. lia. }
apply Z.mod_divide in EX as [a EX]; [|lia]. apply Z.mod_divide in RZ as [b RZ]; [|lia].
rewrite EX, RZ. replace (a * 8 - b * 16) with ((a - 2 * b) * 8) by lia. apply Z.mod_mul. lia.
Qed.
(* In every AR state, a heap block's bytes past its requested size, up to the next multiple of 8 of that size, are
   readable. *)
Lemma ar_blk_tail_vis : forall ly S (W : world segs) mem md p n a, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + n <= a < p + round_up n 8 -> aview segs (w_H W) mem a <> None.
Proof.
intros ly S W mem md p n a (M & _) Hb Ha.
unfold ablocks, blocks in Hb. apply in_map_iff in Hb as ([u r] & Eb & Hb). cbn [fst snd] in Eb. injection Eb as Ep En.
apply in_map_iff in Hb as (k & Ek & Hk). injection Ek as Eu Er. subst u r.
apply filter_In in Hk as [Hk _].
pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & UA & _ & _ & Hn & HX & _).
pose proof (chunk_room_mod8 ly S _ k M Hk) as R8.
(* the range is empty when n = 0 *)
assert (N1 : 1 <= n).
{ destruct (Z.eq_dec n 0) as [->|]; [|lia]. unfold round_up in Ha. cbn in Ha. lia. }
assert (CN : ck_n k = n) by (unfold ck_n, req_size; destruct (Z.eqb_spec (ck_req k) 0); lia).
assert (RU : round_up n 8 <= ck_extent k - ck_rz k).
{ apply round_up_le; [lia | | exact R8]. unfold ck_n in CN. lia. }
pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ (chunk_tail_in_ajunk ly S k Hk)) as V.
unfold range_vis in V. cbn [fst snd] in V. rewrite CN in V.
rewrite aeval_aoff in V by (intros e'; destruct (ck_beg k); cbn; discriminate).
change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
replace a with (ck_base B ly k + (ck_rz k + n) + (a - (ck_base B ly k + (ck_rz k + n)))) by lia.
apply V. rewrite <- Ep, UA in Ha. lia.
Qed.
Lemma asn_blk_tail_vis_ok : SnprintfDef.asn_blk_tail_vis segs B.
Proof. exact ar_blk_tail_vis. Qed.
Lemma absn_blk_tail_vis_ok : SnprintfDefB.absn_blk_tail_vis segs B.
Proof. exact ar_blk_tail_vis. Qed.
End c.
End b.
