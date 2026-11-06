(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1by X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1r3 X1og X1oh X1oi X1pe X1r9 X1or.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Common Require X1ad.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Definition BMAX : Z := 4357000000.

Definition RQ (L : mled) (e : ev) (B : Z) : Prop :=
match e with
| EMmap a len prot flags => a = 0 -> flags = MAPF ->
mmap_len len <= 2^22 \/ (mmap_len len <= 2^27 /\ gm L + BB L + mmap_len len <= B)
| _ => True
end.

Lemma RQ_mono L e B B' : B <= B' -> RQ L e B -> RQ L e B'.
Proof.
intros HB H. destruct e; cbn in *; auto. intros E1 E2. destruct (H E1 E2) as [H1|[H1 H2]]; [left; exact H1| right; split; [exact H1| lia]].
Qed.

Lemma PGE_count mo : PGE mo -> 4096 * Z.of_nat (length (vm_maps (m_vmmaps mo))) <= vm_live_bytes (m_vmmaps mo).
Proof.
intros H. unfold vm_live_bytes. rewrite <- X1ad.zsumf_esz_live. apply X1ad.count_le_bytes. intros e He. exact (H e He).
Qed.

Theorem gap_of_counts : forall L pbrk mo nZ,
KL L pbrk mo -> LI L mo -> 0 <= nZ ->
2^40 + vm_live_bytes (m_vmmaps mo) + Z.of_nat (length (vm_maps (m_vmmaps mo))) * (nZ + 4095) + nZ <= alloc_ceiling_lo ->
vm_gap_available (m_vmmaps mo) nZ = true.
Proof.
intros L pbrk mo nZ HK HL HnZ Hroom.
set (h := m_vmmaps mo) in *.
pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). fold h in S1, S2, S3, S4.
pose proof (proj1 (LI_sbk _ _ HL)) as SB. fold h in SB.
pose proof (kl_ceil _ _ _ HK) as [Htop [Hlo _]]. fold h in Htop.
set (sb := bv_unsigned (vm_start_brk h)) in *.
apply (X1ad.vm_gap_available_of_sum_from h nZ sb HnZ); [unfold PGSZ in *; lia| unfold PGSZ in *; exact S2| |].
- intros e He. pose proof (kl_resv_top _ _ _ HK e He) as T. fold h sb in T. unfold ehi in T. unfold X1ad.elo, X1ad.esz. lia.
- rewrite X1ad.zsumf_jcost, X1ad.zsumf_esz_live. unfold vm_live_bytes in Hroom. lia.
Qed.

Lemma maps_count_le mo x : PGE mo -> vm_live_bytes (m_vmmaps mo) <= x ->
4096 * Z.of_nat (length (vm_maps (m_vmmaps mo))) <= x.
Proof. intros H Hx. pose proof (PGE_count mo H). lia. Qed.

Lemma answer_ok_of_free : forall L pbrk mo len a,
KL L pbrk mo -> 0 < len ->
let h := m_vmmaps mo in let n := mmap_len len in
0 < a -> a mod 4096 = 0 -> a + n <= alloc_top h ->
region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
mmap_answer_ok (ld_ceil L) (lranges L) len a = true.
Proof.
intros L pbrk mo len a HK Hlen h n Ha A1 Htop Hrf.
pose proof (ld_ceil_lt _ _ _ HK) as Hcl. pose proof (proj1 (kl_ceil _ _ _ HK)) as Hc. fold h in Hc.
pose proof (mmap_len_ge len Hlen) as Hn1. pose proof (mmap_len_pos_pg len Hlen) as Hn2. fold n in Hn1, Hn2.
assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
assert (Hround : round_up_pg len = n) by (subst n; apply round_up_pg_eq).
assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
a + n <= b0 \/ b0 + mmap_len l0 <= a).
{ intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. exact D. }
assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
{ intros b0 l0 E. pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ua, Un in D. exact D. }
unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb].
unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
enough (a + n <= lo \/ lo + m <= a) as D.
{ destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
- rewrite (kl_resv _ _ _ HK) in H.
apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
pose proof (region_free_disj _ _ _ (e, sz) Hrf (in_or_app _ _ _ (or_introl H))) as D. unfold elo, ehi in D. cbn [fst snd] in D. rewrite Ua, Un in D. exact D.
- injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. left; exact H.
- injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. right; exists k; exact H.
- injection E as -> ->. pose proof (kl_brkreg _ _ _ HK b0 l0 H) as (R1 & R2 & R3 & R4 & R5 & _).
rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b0 l0 H). lia.
Qed.

Lemma errno_answer_ok L len prot : answer_ok L (EMmap 0 len prot MAPF) (TWO64 - ENOMEM) = true.
Proof. reflexivity. Qed.

Lemma post_err L len prot : event_post L (EMmap 0 len prot MAPF) (TWO64 - ENOMEM) = L.
Proof. reflexivity. Qed.

Lemma post_grant L len prot a : prot = PROT_NONE \/ prot = PROT_RW -> is_err a = false ->
gm (event_post L (EMmap 0 len prot MAPF) a) = gm L + mmap_len len /\ BB (event_post L (EMmap 0 len prot MAPF) a) = BB L.
Proof.
intros Hp He. change (event_post L (EMmap 0 len prot MAPF) a)
with (if is_err a then L else if prot =? PROT_NONE then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L).
rewrite He. destruct Hp as [-> | ->]; cbn [Z.eqb PROT_NONE PROT_RW Pos.eqb].
- rewrite gm_add_meta, BB_set_metas. split; reflexivity.
- rewrite gm_add_group, BB_set_groups. split; reflexivity.
Qed.

Definition BOUNDB (L : mled) (e : ev) (B : Z) : Prop :=
forall z, answer_ok L e z = true -> gm (event_post L e z) + BB (event_post L e z) <= B.

Theorem nroom_of_ledger : forall B L pbrk mo len prot,
KL L pbrk mo -> LI L mo -> 0 < len < LEN_MAX -> (prot = PROT_NONE \/ prot = PROT_RW) ->
B <= BMAX -> BOUNDB L (EMmap 0 len prot MAPF) B -> RQ L (EMmap 0 len prot MAPF) B ->
nroom B (NMmap 0 len prot MAPF) mo.
Proof.
intros B L pbrk mo len prot HK HL Hlen Hp HB HBd HRQ. cbn [nroom]. intros _ _.
set (h := m_vmmaps mo) in *. set (n := mmap_len len).
pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
pose proof (ld_ceil_lt _ _ _ HK) as Hcl. unfold LEN_MAX in Hlen.
pose proof (LI_elim _ _ HL) as Hlive. fold h in Hlive.
pose proof (HBd _ (errno_answer_ok L len prot)) as Hpre. rewrite post_err in Hpre.
pose proof (maps_count_le mo (vm_live_bytes h) (LI_pge _ _ HL) (Z.le_refl _)) as Hk. fold h in Hk.
set (k := Z.of_nat (length (vm_maps h))) in *.
pose proof (live_bytes_nonneg (vm_maps h)) as Hnn. unfold vm_live_bytes in *.
assert (Hfloor : alloc_ceiling_lo = 0x7fff7f800000) by reflexivity. unfold BMAX in HB.
destruct (HRQ eq_refl eq_refl) as [Hsmall|[Hbig Hroom]]; fold n in Hsmall || fold n in Hbig, Hroom.
-
assert (Hgap : vm_gap_available h n = true).
{ apply (gap_of_counts L pbrk mo n); [exact HK| exact HL| lia|].
fold h k. unfold vm_live_bytes. rewrite Hfloor.
assert (k * (n + 4095) <= k * (2^22 + 4095)) by (apply Z.mul_le_mono_nonneg_l; lia). nia. }
split; [| exact Hgap].
destruct (vm_gap_available_find h n Hgap) as [aw Hfind].
destruct (vm_find_base_sound h n aw Hfind) as (F1 & F2 & F3 & F4).
pose proof (alloc_top_room h) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
assert (Hans : answer_ok L (EMmap 0 len prot MAPF) (bv_unsigned aw) = true).
{ change (answer_ok L (EMmap 0 len prot MAPF) (bv_unsigned aw)) with (mmap_answer_ok (ld_ceil L) (lranges L) len (bv_unsigned aw)).
apply (answer_ok_of_free L pbrk mo len (bv_unsigned aw) HK ltac:(lia)); fold h n; [lia| change page_size with 4096 in F1; exact F1| exact F3|].
rewrite Z_to_bv_bv_unsigned. exact F4. }
pose proof (HBd _ Hans) as Hpost.
assert (Herr : is_err (bv_unsigned aw) = false) by (unfold is_err, TWO64; apply Z.ltb_ge; lia).
destruct (post_grant L len prot (bv_unsigned aw) Hp Herr) as [G1 G2]. rewrite G1, G2 in Hpost. fold n in Hpost. lia.
-
split; [lia|].
apply (gap_of_counts L pbrk mo n HK HL ltac:(lia)). fold h k. unfold vm_live_bytes. rewrite Hfloor.
assert (E1 : 4096 * (k * (n + 4095)) <= (BMAX - n) * (n + 4095)).
{ unfold BMAX. assert (4096 * k <= 4357000000 - n) by lia. nia. }
assert (E2 : (BMAX - n) * (n + 4095) <= (BMAX - 2^27) * (2^27 + 4095)).
{ unfold BMAX. assert (0 <= (2^27 - n) * (4357000000 - 2^27 - n - 4095)) by (apply Z.mul_nonneg_nonneg; lia). nia. }
unfold BMAX in E1, E2. lia.
Qed.
