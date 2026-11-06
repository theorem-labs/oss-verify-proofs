From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* The bytes of a live heap block's chunk past its requested size: the chunk_junk tail
   (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) of YG0n.v is
   visible by am_junk, and the chunk end is 8-aligned, so the rest of the aligned 8-byte word
   holding a block's last byte is visible (mapped, not hidden by w_H). *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Lemma ck_extent_mod8 : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) -> ck_extent k mod 8 = 0.
Proof.
intros ly S rd k M Hk.
pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
destruct (ck_beg k) as [|off|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & _).
pose proof (class_ok (prim_class off) ltac:(lia)) as (_ & K2 & _).
rewrite Gext. apply Z.mod_divide in K2 as [q Hq]; [|lia]. rewrite Hq.
replace (q * 32) with ((q * 4) * 8) by lia. apply Z.mod_mul. lia.
- destruct GG as (_ & Hp & _ & Gext & _).
pose proof (secondary_geometry (ck_req k) ltac:(lia) Hp) as (_ & _ & _ & _ & S5 & _).
rewrite Gext. unfold kPage in *. apply Z.mod_divide in S5 as [q Hq]; [|lia]. rewrite Hq.
replace (q * 4096 - 4096) with ((q * 512 - 512) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma AR_block_tail_vis : forall ly S W mem md p n a,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n <= a < round_up (p + req_size n) 8 ->
aview segs (w_H W) mem a <> None.
Proof.
intros ly S W mem md p n a (M & _) Hin Ha.
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hr). subst p n.
pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & G3 & G4 & _ & G6 & G7 & G8 & _).
pose proof (ck_extent_mod8 ly S _ k M Hk) as E8.
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M)
(aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k)) as V.
specialize (V ltac:(unfold ajunk; right; right; rewrite !in_app_iff; do 2 right; left; apply in_flat_map;
exists k; split; [exact Hk|]; unfold chunk_junk; rewrite !in_app_iff; do 3 right; left; reflexivity)).
unfold range_vis in V. cbn [fst snd] in V.
assert (EA : aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k)) = ck_base B ly k + ck_rz k + ck_n k).
{ unfold ck_base, sptr_addr. rewrite aeval_aoff; [lia|]. destruct (ck_beg k); intros e' He'; cbn in He'; discriminate He'. }
rewrite EA in V. unfold ck_n in V. rewrite G4 in Ha. unfold round_up in Ha.
pose proof (Z.mul_div_le (ck_base B ly k + ck_rz k + req_size (ck_req k) + 8 - 1) 8 ltac:(lia)) as D.
apply Z.mod_divide in G3 as [qb Hqb]; [|lia]. apply Z.mod_divide in G6 as [qr Hqr]; [|lia].
apply Z.mod_divide in E8 as [qe Hqe]; [|lia].
replace a with (ck_base B ly k + ck_rz k + req_size (ck_req k) + (a - (ck_base B ly k + ck_rz k + req_size (ck_req k)))) by lia.
apply V. lia.
Qed.
Lemma AR_block_word_vis : forall ly S W mem md p n j a,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p <= j < p + req_size n -> j <= a < j - j mod 8 + 8 ->
aview segs (w_H W) mem a <> None.
Proof.
intros ly S W mem md p n j a HAR Hin Hj Ha.
destruct (Z_lt_le_dec a (p + req_size n)) as [Hblk|Htail].
- destruct HAR as (M & _). apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hr). subst p n.
pose proof (proj1 (Forall_forall _ _) (am_client _ _ _ _ M) (sptr_exp (ck_user k), ck_n k)) as V. unfold aclient in V.
specialize (V ltac:(apply in_app_iff; left; apply in_flat_map; exists k; split; [exact Hk | unfold chunk_user; rewrite Hst; left; reflexivity])).
unfold range_vis in V. cbn [fst snd] in V. fold (sptr_addr B ly (ck_user k)) in V.
replace a with (sptr_addr B ly (ck_user k) + (a - sptr_addr B ly (ck_user k))) by lia.
apply V. unfold ck_n. lia.
- apply (AR_block_tail_vis ly S W mem md p n a HAR Hin). split; [exact Htail|]. unfold round_up.
pose proof (Z.div_mod j 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound j 8 ltac:(lia)) as B1.
pose proof (Z.div_mod (p + req_size n + 8 - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + req_size n + 8 - 1) 8 ltac:(lia)) as B2.
lia.
Qed.
End t.
