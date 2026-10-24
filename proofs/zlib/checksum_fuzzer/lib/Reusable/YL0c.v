(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP0l YP06 YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YL07 YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.
Lemma mem_ok_cons : forall E m r rs,
mem_ok segs E m rs -> region_wf r = true -> region_ok segs E m r ->
(forall r', In r' rs -> extent_disjoint E r r') ->
mem_ok segs E m (r :: rs).
Proof.
intros E m r rs (Hwf & Hok & Hpd) Hr Hro Hd. split; [| split].
- cbn. rewrite Hr, Hwf. reflexivity.
- constructor; assumption.
- split; [| exact Hpd]. clear -Hd. induction rs as [|x rs IH]; cbn; [exact I|].
split; [apply Hd; left; reflexivity | apply IH; intros r' H; apply Hd; right; exact H].
Qed.
Definition sep_check (G : facts) (rs : smem) : bool := block_sep_check B G [] rs.
Lemma sep_check_disjoint : forall E m G L A md p sz rs (r : YP09.region) n,
facts_ok E G -> stack_anchored E G   -> MR L A m md -> In (p, sz) (user_blocks A) ->
r_base r = Some n -> r_lo r < r_hi r ->
ptr_addr L p <= bv_unsigned (ew E n) + r_lo r -> bv_unsigned (ew E n) + r_hi r <= ptr_addr L p + sz ->
ms_segs B <> [] ->
sep_check G rs = true ->
forall r', In r' rs -> extent_disjoint E r r'.
Proof.
intros E m G L A md p sz rs r n HG HSA HMR Hin Hb Hlohi Hlo Hhi Hne Hsep r' Hr'.
pose proof (forallb_In _ _ r' Hsep Hr') as H. cbn beta in H.
pose proof (mr_blocks B MR LAWS L A m md p sz 0 HMR Hin ltac:(lia)) as (_ & Hplo & Hphi & _).
unfold extent_disjoint. rewrite Hb. cbn [base_val].
destruct (r_base r') as [k|] eqn:Hb'; cbn [base_val].
- cbn [blk_size] in H. destruct (anch_lo G k) as [K|] eqn:HK; [|discriminate]. apply Z.leb_le in H.
pose proof (stack_anchored_sound E G k K HSA HK).
pose proof YM05.alloc_ceiling_val. lia.
- apply andb_prop in H as [Hnz H]. apply Z.ltb_lt in Hnz.
apply existsb_In in H as (sg & Hsg & H). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct (Z_le_dec (bv_unsigned (ew E n) + r_hi r) (0 + r_lo r')) as [|C1]; [lia|].
destruct (Z_le_dec (0 + r_hi r') (bv_unsigned (ew E n) + r_lo r)) as [|C2]; [lia|].
exfalso.
destruct (Z_le_dec (r_lo r') (bv_unsigned (ew E n) + r_lo r)) as [C3|C3].
+ apply (ax_blocks_img AX L A m md p sz (bv_unsigned (ew E n) + r_lo r - ptr_addr L p) HMR Hin ltac:(lia)).
apply (in_img_of_reserved B sg); [exact Hsg | lia | exact Hne].
+ apply (ax_blocks_img AX L A m md p sz (r_lo r' - ptr_addr L p) HMR Hin ltac:(lia)).
apply (in_img_of_reserved B sg); [exact Hsg | lia | exact Hne].
Qed.
Lemma mem_ok_head_replace : forall E m r r' rs,
mem_ok segs E m (r :: rs) ->
r_base r' = r_base r -> r_lo r <= r_lo r' -> r_hi r' <= r_hi r -> r_lo r' <= r_hi r' -> r_whi r' <= r_wlo r' ->
forallb (chunk_inside r') (r_chunks r') = true ->
Forall (chunk_ok segs E m (base_val E (r_base r'))) (r_chunks r') ->
mem_ok segs E m (r' :: rs).
Proof.
intros E m r r' rs (Hwf & Hok & Hpd) Hb Hlo Hhi Hlohi Hro Hci Hcs.
cbn in Hwf. apply andb_prop in Hwf as [Hr Hwf]. cbn in Hpd. destruct Hpd as [Hall Hpd].
inversion Hok as [|r0 rs0 Hr0 Hrs]; subst.
split; [| split].
- cbn. rewrite Hwf, andb_true_r. unfold region_wf. rewrite Hci.
rewrite (proj2 (Z.leb_le _ _) Hlohi), (proj2 (Z.leb_le _ _) Hro). reflexivity.
- constructor; [| exact Hrs]. destruct Hr0 as (A1 & A2 & A3 & A4).
unfold region_ok. rewrite Hb in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact Hcs].
- split; [| exact Hpd]. clear -Hall Hb Hlo Hhi. induction rs as [|x rs IH]; cbn in *; [exact I|].
destruct Hall as [H1 H2]. split; [| apply IH; exact H2].
unfold extent_disjoint in *. rewrite Hb. lia.
Qed.
Lemma chunk_ok_cdata0 : forall E m base d len bs,
ed E d = bs -> len <= Z.of_nat (length bs) ->
(forall i, 0 <= i < len -> mbyte segs m (base + i) = nth_error bs (Z.to_nat i)) ->
chunk_ok segs E m base (mkChunk 0 (CData d 0 len)).
Proof.
intros E m base d len bs Hd Hlen Hb. eapply (chunk_ok_cdata B); [exact Hd | lia | lia |].
intros i Hi. rewrite Z.add_0_l. apply Hb. exact Hi.
Qed.
End b.
End a.
