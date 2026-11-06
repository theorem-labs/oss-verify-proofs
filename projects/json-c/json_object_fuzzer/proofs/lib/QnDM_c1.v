(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 QZAi QUZl Q7S0 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition CTX : Z := 0x1a188.
Definition MLOCK : Z := 0x1a0d0.
Definition LIBC : Z := 0x1a120.
Definition NEED_LOCKS : Z := 0x1a123.
Definition PAGE_SIZE_A : Z := 0x1a150.
Definition SIZE_CLASSES : Z := 0x18170.
Definition DEBRUIJN : Z := 0x18130.

Definition get_meta_entry : Z := 0x15970.
Definition malloc_entry : Z := 0x16c7c.
Definition free_entry : Z := 0x15e70.
Definition alloc_meta_entry : Z := 0x15fd4.
Definition alloc_slot_entry : Z := 0x162e0.
Definition nontrivial_free_entry : Z := 0x15a6c.
Definition mmap_entry : Z := 0x172d4.
Definition munmap_entry : Z := 0x173e4.
Definition mprotect_entry : Z := 0x1739c.
Definition unlock_entry : Z := 0x17b14.

Definition agent_reserved : list (Z * Z) := [(0x10000, 0x9000); (0x19000, 0x2000)].

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition b8 (z : Z) : byte := Z_to_bv 8 z.

Definition pw (st : mstate) (p : optr) : word := wz (oconc st p).

Definition meta_word (mr : meta) : Z :=
m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr.

Definition meta_cells (st : mstate) (mr : meta) : list cell :=
[C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (pw st (m_mem mr));
C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr))].

Definition brk_word (st : mstate) : Z :=
match c_brk (ctx st) with
| BrkUntried => 0
| BrkDead => 2^64 - 1
| BrkLive rid off => conc st (rid, off)
end.

Definition ctx_head_cells (st : mstate) : list cell :=
let c := ctx st in
[C8 (wz (c_secret c)); C4 (wz (c_init_done c)); C4 (wz (c_mmap_counter c));
C8 (pw st (c_free_meta_head c)); C8 (pw st (c_avail_meta c));
C8 (wz (c_avail_meta_count c)); C8 (wz (c_avail_meta_area_count c)); C8 (wz (c_meta_alloc_shift c));
C8 (pw st (c_meta_area_head c)); C8 (pw st (c_meta_area_tail c)); C8 (pw st (c_avail_meta_areas c))].

Definition actives (st : mstate) : list word := map (fun i => pw st (active st (Z.of_nat i))) (seq 0 48).
Definition usages (st : mstate) : list word := map (fun i => wz (usage st (Z.of_nat i))) (seq 0 48).
Definition unmap_seqs (st : mstate) : list byte := map (fun i => b8 (unmap_seq st (Z.of_nat i))) (seq 0 32).
Definition bouncess (st : mstate) : list byte := map (fun i => b8 (bounces st (Z.of_nat i))) (seq 0 32).
Definition zeros (n : nat) : list byte := repeat (b8 0) n.
Definition ctx_tail_cells (st : mstate) : list cell :=
[C1 (b8 (c_seq (ctx st))); CB 7 (zeros 7); C8 (wz (brk_word st))].

Definition lr_lo (r : region) : Z :=
match r_kind r with RKBrk => r_base r + 4096 | _ => r_base r end.

#[using="Type"] Lemma lr_lo_ge r : r_base r <= lr_lo r.
Proof. unfold lr_lo. destruct (r_kind r); lia. Qed.
#[using="Type"] Lemma lr_lo_group r : r_kind r = RKGroup -> lr_lo r = r_base r.
Proof. unfold lr_lo. intros ->. reflexivity. Qed.
#[using="Type"] Lemma lr_lo_nbrk r : r_kind r <> RKBrk -> lr_lo r = r_base r.
Proof. unfold lr_lo. destruct (r_kind r); congruence. Qed.

Section MREP.
Variable st : mstate.
Variable m : word -> option byte.

Definition regions_wf : Prop :=
s_reserved st = agent_reserved
/\ (forall rid r, (s_regions st) !! rid = Some r ->
0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= r_len r
/\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ ranges_free agent_reserved (r_base r) (round_up_pg (r_len r)) = true)
/\ (forall rid1 r1 rid2 r2, (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= lr_lo r1)

/\ (forall a ar, (s_areas st) !! a = Some ar ->
exists r, (s_regions st) !! (fst a) = Some r /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0
/\ r_kind r <> RKGroup /\ lr_lo r <= r_base r + snd a)
/\ (forall b gh, (s_groups st) !! b = Some gh ->
exists r, (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0).

End MREP.

Definition mrep_W (st : mstate) : list (Z * Z) :=
(CTX, CTX + 928)
:: map (fun kr : N * region => (r_base (snd kr), r_base (snd kr) + round_up_pg (r_len (snd kr)))) (map_to_list (s_regions st)).

Definition blocks_preserved (L : list (Z * Z)) (m m' : word -> option byte) : Prop :=
forall a, (exists bl, In bl L /\ fst bl <= a < fst bl + snd bl) -> m' (wa a) = m (wa a).

#[using="Type"] Lemma conc_aadd : forall st p d,
is_Some ((s_regions st) !! (fst p)) -> conc st (aadd p d) = conc st p + d.
Proof.
intros st [rid off] d [r Hr]. unfold conc, aadd, get_region. cbn. rewrite Hr. lia.
Qed.

#[using="Type"] Lemma conc_region : forall st rid off r,
(s_regions st) !! rid = Some r -> conc st (rid, off) = r_base r + off.
Proof. intros. unfold conc, get_region. cbn. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros. unfold round_up_pg, PGSZ. assert (0 <= Z.land (-x) (4096 - 1)) by (apply Z.land_nonneg; right; lia). lia. Qed.

#[using="Type"] Lemma wz_unsigned x : 0 <= x < 2^64 -> bv_unsigned (wz x) = x.
Proof. intros. unfold wz. apply unsigned_lit. lia. Qed.
#[using="Type"] Lemma b8_unsigned x : 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof. intros. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma zxb_b8 x : 0 <= x < 256 -> zxb (b8 x) = wz x.
Proof. intros. unfold zxb, wz. rewrite b8_unsigned by lia. reflexivity. Qed.
#[using="Type"] Lemma zx16_wz x : 0 <= x < 65536 -> zx16 (wz x) = wz x.
Proof. intros. unfold zx16, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
#[using="Type"] Lemma sx32_wz x : 0 <= x < 2^31 -> sx32 (wz x) = wz x.
Proof. intros. unfold sx32, wz. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

#[using="Type"] Lemma land_ldiff_distr x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

#[using="Type"] Lemma land_pgmask x : 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
intros Hx.
assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
rewrite land_ldiff_distr. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^12) with 4096. pose proof (Z.div_mod x 4096). lia.
Qed.

#[using="Type"] Lemma mod_mod_pow2 z a b : 0 <= a <= b -> (z mod 2^b) mod 2^a = z mod 2^a.
Proof. intros. apply Z.mod_mod_divide. exists (2^(b-a)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

#[using="Type"] Lemma swrap32_mod32 z : (bv_swrap 32 z) mod 2^32 = z mod 2^32.
Proof.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
replace (z + 2^31 - 2^31) with z by lia. reflexivity.
Qed.

#[using="Type"] Lemma wrap32_sx32_wz a : 0 <= a < 2^32 -> bv_wrap 32 (bv_unsigned (sx32 (wz a))) = a.
Proof.
intros Ha. unfold sx32, wz. rewrite (unsigned_lit a) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2^64). change (2 ^ Z.of_N 32) with (2^32).
rewrite (mod_mod_pow2 _ 32 64) by lia. rewrite swrap32_mod32. apply Z.mod_small. lia.
Qed.

#[using="Type"] Lemma bit_test_form a i : 0 <= a -> 0 <= i ->
Z.land (bv_swrap 32 (Z.shiftr a i) mod 2^64) 1 = Z.b2z (Z.testbit a i).
Proof.
intros Ha Hi. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia.
rewrite Z.testbit_spec' by lia. rewrite <- Z.shiftr_div_pow2 by lia.
rewrite (mod_mod_pow2 _ 1 64) by lia.
rewrite <- (mod_mod_pow2 (bv_swrap 32 (a ≫ i)) 1 32) by lia. rewrite swrap32_mod32.
rewrite (mod_mod_pow2 _ 1 32) by lia. reflexivity.
Qed.

#[using="Type"] Lemma signed_wz_small x : 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
intros. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
End RC__1.

Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma size_class_range sc : 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
intros H. unfold size_class.
assert (F : Forall (fun x => 1 <= x <= 8191) size_classes).
{ unfold size_classes. repeat (constructor; [lia|]). constructor. }
apply (Forall_nth (fun x => 1 <= x <= 8191) size_classes); [exact F|]. cbn. lia.
Qed.

#[using="Type"] Lemma conc_region' : forall st (q : aptr) r,
(s_regions st) !! (fst q) = Some r -> conc st q = r_base r + snd q.
Proof. intros st [rid off] r H. apply conc_region. exact H. Qed.

Definition meta_slot (st : mstate) (g : aptr) : Prop :=
exists a ar k, (s_areas st) !! a = Some ar /\ 0 <= k < NSLOTS /\ g = aadd a (AREA_HDR + META_SIZE * k).

#[using="Type"] Lemma le2_lohi : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> le2 (wz (lo + 256 * hi)) = [b8 lo; b8 hi].
Proof.
intros lo hi Hl Hh. unfold le2, wz, b8. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
f_equal; [apply Z_to_bv8_mod; rewrite <- Zplus_mod_idemp_r; replace (256 * hi) with (hi * 2^8) by lia; rewrite Z_mod_mult; rewrite Z.add_0_r; reflexivity|].
f_equal. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
replace (lo + 256 * hi) with (lo + hi * 256) by lia. rewrite Z.div_add, Z.div_small by lia. reflexivity.
Qed.

Definition ticks_ok (st : mstate) : Prop :=
(forall rid sh u hl ch, (s_shadow st) !! rid = Some sh -> (r_hav sh) !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
/\ (forall rid sh pg t, (s_shadow st) !! rid = Some sh -> (r_havp sh) !! pg = Some t -> (t <= s_tick st)%N).

#[using="Type"] Lemma reserved_disjoint : forall b n, ranges_free agent_reserved b n = true ->
(b + n <= 0x10000 \/ 0x19000 <= b) /\ (b + n <= 0x19000 \/ 0x1b000 <= b).
Proof.
intros b n H. unfold ranges_free, agent_reserved in H. cbn [forallb fst snd] in H.
unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.

Definition wr_in (st : mstate) (rid : N) (a len : Z) : Prop :=
exists r, (s_regions st) !! rid = Some r /\ lr_lo r <= a /\ a + len <= r_base r + round_up_pg (r_len r) /\ 0 <= len.

#[using="Type"] Lemma wr_in_image : forall st rid a len,
regions_wf st -> wr_in st rid a len ->
(a + len <= 0x19000 \/ 0x1b000 <= a) /\ 0 <= a /\ a + len <= 2^64.
Proof.
intros st rid a len (_ & WR & _) (r & Hr & H1 & H2 & H3).
destruct (WR rid r Hr) as (B0 & _ & L0 & BC & RF). unfold alloc_ceiling in BC.
destruct (reserved_disjoint _ _ RF) as [_ D2]. pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r). lia.
Qed.

#[using="Type"] Lemma wr_in_other : forall st rid a len rid' r',
regions_wf st -> wr_in st rid a len -> (s_regions st) !! rid' = Some r' -> rid' <> rid ->
a + len <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= a.
Proof.
intros st rid a len rid' r' (_ & _ & DJ & _) (r & Hr & H1 & H2 & H3) Hr' Hne.
destruct (DJ rid r rid' r' Hr Hr' ltac:(congruence)); lia.
Qed.

#[using="Type"] Lemma area_lr_lo : forall st a ar r, regions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
lr_lo r <= r_base r + snd a.
Proof.
intros st a ar r (_ & _ & _ & WA & _) Ha Hr. destruct (WA a ar Ha) as (r0 & Hr0 & _ & _ & _ & _ & LO).
rewrite Hr in Hr0. inversion Hr0; subst. exact LO.
Qed.

#[using="Type"] Lemma regions_disjoint_full : forall st rid1 r1 rid2 r2,
regions_wf st -> (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
r_kind r1 <> RKBrk -> r_kind r2 <> RKBrk ->
r_base r1 + round_up_pg (r_len r1) <= r_base r2 \/ r_base r2 + round_up_pg (r_len r2) <= r_base r1.
Proof.
intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1 K2.
pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_nbrk r1 K1), (lr_lo_nbrk r2 K2) in X. exact X.
Qed.

#[using="Type"] Lemma regions_disjoint_grp : forall st rid1 r1 rid2 r2,
regions_wf st -> (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
r_kind r1 = RKGroup ->
r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= r_base r1.
Proof.
intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1.
pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_group r1 K1) in X. exact X.
Qed.

#[using="Type"] Lemma area_conc : forall st a ar, regions_wf st -> (s_areas st) !! a = Some ar ->
exists r, (s_regions st) !! (fst a) = Some r /\ conc st a = r_base r + snd a
/\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0 /\ r_kind r <> RKGroup
/\ 0 < r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling.
Proof.
intros st a ar (_ & WR & _ & WA & _) Ha. destruct (WA a ar Ha) as (r & Hr & A0 & A1 & AL & NK & _).
destruct (WR _ r Hr) as (B0 & BAL & _ & BC & _).
exists r. rewrite (conc_region' st a r Hr). repeat split; auto.
Qed.

#[using="Type"] Lemma group_conc : forall st b gh, regions_wf st -> (s_groups st) !! b = Some gh ->
exists r, (s_regions st) !! (fst b) = Some r /\ conc st b = r_base r + snd b
/\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0
/\ 0 < r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling.
Proof.
intros st b gh (_ & WR & _ & _ & WG) Hb. destruct (WG b gh Hb) as (r & Hr & K & B0 & B1 & AL).
destruct (WR _ r Hr) as (R0 & _ & _ & RC & _).
exists r. rewrite (conc_region' st b r Hr). repeat split; auto.
Qed.

#[using="Type"] Lemma s_shadow_wr8 : forall st p v,
s_shadow (wr8 p v st) =
<[fst p := mkShadow (<[snd p := (Z.land v 255, s_tick st)]> (r_cells (get_shadow st (fst p)))) (r_hav (get_shadow st (fst p))) (r_havp (get_shadow st (fst p)))]> (s_shadow st).
Proof. intros. reflexivity. Qed.

#[using="Type"] Lemma get_shadow_unfold : forall st rid, get_shadow st rid = default shadow0 ((s_shadow st) !! rid).
Proof. reflexivity. Qed.

#[using="Type"] Lemma get_shadow_wr8_same : forall st p v,
get_shadow (wr8 p v st) (fst p) =
mkShadow (<[snd p := (Z.land v 255, s_tick st)]> (r_cells (get_shadow st (fst p)))) (r_hav (get_shadow st (fst p))) (r_havp (get_shadow st (fst p))).
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_eq. reflexivity. Qed.

#[using="Type"] Lemma get_shadow_wr8_other : forall st p v rid, rid <> fst p ->
get_shadow (wr8 p v st) rid = get_shadow st rid.
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_ne by congruence. reflexivity. Qed.

#[using="Type"] Lemma cell_read_wr8_other : forall st p v o, o <> snd p ->
cell_read (get_shadow (wr8 p v st) (fst p)) o = cell_read (get_shadow st (fst p)) o.
Proof. intros. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

#[using="Type"] Lemma cell_read_wr8_same : forall st p v,
ticks_ok st -> 0 <= v < 256 ->
cell_read (get_shadow (wr8 p v st) (fst p)) (snd p) = Known v.
Proof.
intros st p v [T1 T2] Hv. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_eq.
replace (Z.land v 255) with v by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
unfold get_shadow. destruct (s_shadow st !! fst p) as [sh|] eqn:E; cbn.
- assert (SP : stale_pg (r_havp sh !! (snd p `div` 4096)) (Some (s_tick st)) = false).
{ unfold stale_pg. destruct (r_havp sh !! (snd p `div` 4096)) eqn:E2; [|reflexivity].
apply N.ltb_ge. eapply T2; eauto. }
assert (SU : stale (default [] (r_hav sh !! (snd p `div` 16))) (snd p `mod` 16) (Some (s_tick st)) = false).
{ unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. intros ([cov t] & Hin & Hb).
destruct (r_hav sh !! (snd p `div` 16)) eqn:E3; cbn in Hin; [|contradiction].
apply Bool.andb_true_iff in Hb. destruct Hb as [_ Hb]. apply N.ltb_lt in Hb.
pose proof (T1 _ _ _ _ _ E E3 Hin) as HT. cbn [snd] in HT. exfalso. apply (N.lt_irrefl t). eapply N.le_lt_trans; [exact HT | exact Hb]. }
rewrite SP, SU. reflexivity.
- rewrite lookup_empty. cbn. reflexivity.
Qed.

#[using="Type"] Lemma ticks_ok_wr8 : forall st p v, ticks_ok st -> ticks_ok (wr8 p v st).
Proof.
intros st p v [T1 T2]. split.
- intros rid sh u hl ch Hs Hu Hin. cbn [s_tick wr8 upd_shadow set_shadow] in *.
rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
+ rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hu.
unfold get_shadow in Hu. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hu.
* eapply T1; eauto.
* rewrite lookup_empty in Hu. discriminate.
+ rewrite lookup_insert_ne in Hs by congruence. eapply T1; eauto.
- intros rid sh pg t Hs Hp. cbn [s_tick wr8 upd_shadow set_shadow] in *.
rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
+ rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hp.
unfold get_shadow in Hp. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hp.
* eapply T2; eauto.
* rewrite lookup_empty in Hp. discriminate.
+ rewrite lookup_insert_ne in Hs by congruence. eapply T2; eauto.
Qed.

#[using="Type"] Lemma wr8_mod : forall st p v, wr8 p v st = wr8 p (v mod 256) st.
Proof.
intros. unfold wr8, upd_shadow. cbn beta.
replace (Z.land (v mod 256) 255) with (Z.land v 255); [reflexivity|].
change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

#[using="Type"] Lemma le2_split : forall v, 0 <= v < 65536 -> le2 (wz v) = [b8 (v mod 256); b8 (v / 256)].
Proof.
intros v Hv. replace v with (v mod 256 + 256 * (v / 256)) at 1 by (pose proof (Z.div_mod v 256); lia).
rewrite le2_lohi; [reflexivity| |]; [pose proof (Z.mod_pos_bound v 256); lia | split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]].
Qed.

#[using="Type"] Lemma get_meta_rec_upd : forall st g f g',
get_meta_rec (upd_meta g f st) g' = if aptr_eqb g' g then f (get_meta_rec st g) else get_meta_rec st g'.
Proof.
intros. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn [s_metas set_metas].
unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

#[using="Type"] Lemma aptr_eqb_refl : forall g, aptr_eqb g g = true.
Proof. intros [a b]. unfold aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma map_seq_upd : forall {X} (f g : nat -> X) (j : nat) (x : X) n s,
(forall i, (s <= i < s + n)%nat -> g i = if Nat.eqb i j then x else f i) ->
(s <= j)%nat ->
map g (seq s n) = upd (map f (seq s n)) (j - s) x.
Proof.
intros X f g j x n. induction n as [|n IH]; intros s Hg Hj; [reflexivity|].
cbn [seq map]. destruct (Nat.eq_dec j s) as [->|NE].
- rewrite Nat.sub_diag. cbn [upd]. rewrite Hg by lia. rewrite Nat.eqb_refl. f_equal.
apply map_ext_in. intros i Hi. apply in_seq in Hi. rewrite Hg by lia.
destruct (Nat.eqb_spec i s); [lia|reflexivity].
- replace (j - s)%nat with (S (j - S s)) by lia. cbn [upd]. f_equal.
+ rewrite Hg by lia. destruct (Nat.eqb_spec s j); [lia|reflexivity].
+ apply IH; [intros; apply Hg; lia|lia].
Qed.

#[using="Type"] Lemma active_set_active : forall st sc v i,
active (set_active sc v st) i = if Z.eqb i sc then v else active st i.
Proof.
intros. unfold active, set_active, upd_ctx. cbn [ctx s_ctx c_active set_active_map].
destruct v as [p|]; destruct (Z.eqb_spec i sc); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
- rewrite lookup_delete_eq. reflexivity.
- rewrite lookup_delete_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma actives_set_active : forall st sc v, 0 <= sc < 48 ->
actives (set_active sc v st) = upd (actives st) (Z.to_nat sc) (pw st v).
Proof.
intros st sc v Hsc. unfold actives.
replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
apply (map_seq_upd (fun i => pw st (active st (Z.of_nat i))) (fun i => pw (set_active sc v st) (active (set_active sc v st) (Z.of_nat i)))); [|lia].
intros i Hi. rewrite active_set_active.
assert (Hpw : forall q, pw (set_active sc v st) q = pw st q) by (intros [q|]; reflexivity).
rewrite Hpw. destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.

Definition sh_ticks (sh : shadow) (t : N) : Prop :=
(forall u hl ch, (r_hav sh) !! u = Some hl -> In ch hl -> (snd ch <= t)%N)
/\ (forall pg t', (r_havp sh) !! pg = Some t' -> (t' <= t)%N).

Definition shadow_le (sh sh' : shadow) : Prop :=
r_cells sh' = r_cells sh /\ forall o v, cell_read sh' o = Known v -> cell_read sh o = Known v.

#[using="Type"] Lemma shadow_le_refl : forall sh, shadow_le sh sh. Proof. intros; split; auto. Qed.
#[using="Type"] Lemma shadow_le_trans : forall a b c, shadow_le a b -> shadow_le b c -> shadow_le a c.
Proof. intros a b c [E1 H1] [E2 H2]. split; [congruence|]. eauto. Qed.

#[using="Type"] Lemma In_filter_bool : forall {A} (f : A -> bool) (l : list A) x,
In x (filter (fun y => f y) l) <-> In x l /\ f x = true.
Proof.
intros A f l x. rewrite <- !list_elem_of_In. rewrite list_elem_of_filter.
unfold Is_true. destruct (f x); intuition congruence.
Qed.

#[using="Type"] Lemma stale_hav_add : forall hl cov t b tc,
(forall ch, In ch hl -> (snd ch <= t)%N) ->
stale (hav_add cov t hl) b tc = false -> stale hl b tc = false.
Proof.
intros hl cov t b tc Ht Hs. unfold stale in *.
apply Bool.not_true_iff_false. apply Bool.not_true_iff_false in Hs. rewrite existsb_exists in *.
intros ([c' h'] & Hin & Hb). apply Hs. cbn [fst snd] in Hb.
apply Bool.andb_true_iff in Hb. destruct Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1.
destruct (Z.ltb_spec cov c').
- exists (c', h'). split; [|cbn [fst snd]; rewrite (proj2 (Z.ltb_lt _ _) Hb1), Hb2; reflexivity].
unfold hav_add. right. apply In_filter_bool. split; [exact Hin|]. cbn. apply Z.ltb_lt. assumption.
- exists (cov, t). split; [unfold hav_add; left; reflexivity|]. cbn [fst snd].
rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
destruct tc as [tc|]; [|reflexivity]. apply N.ltb_lt. apply N.ltb_lt in Hb2.
pose proof (Ht _ Hin) as Hh. cbn [snd] in Hh. eapply N.lt_le_trans; [exact Hb2|exact Hh].
Qed.

#[using="Type"] Lemma hav_unit_step : forall cells hav havp u cov t,
sh_ticks (mkShadow cells hav havp) t ->
shadow_le (mkShadow cells hav havp) (mkShadow cells (<[u := hav_add cov t (default [] (hav !! u))]> hav) havp)
/\ sh_ticks (mkShadow cells (<[u := hav_add cov t (default [] (hav !! u))]> hav) havp) t.
Proof.
intros cells hav havp u cov t [T1 T2]. cbn [r_hav r_havp] in T1, T2.
assert (Hl : forall ch, In ch (default [] (hav !! u)) -> (snd ch <= t)%N).
{ intros ch Hin. destruct (hav !! u) eqn:E2; cbn in Hin; [eapply T1; eauto| contradiction]. }
split.
- split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
destruct (Z.eq_dec (o / 16) u) as [E|NE].
+ rewrite E, lookup_insert_eq in Hc. cbn [default from_option id] in Hc. rewrite E.
destruct (cells !! o) as [[v0 tc]|].
* destruct (stale_pg (havp !! (o / 4096)) (Some tc)) eqn:SP; [cbn in Hc; discriminate|].
destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) (Some tc)) eqn:SU; [cbn in Hc; discriminate|].
rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
* destruct (stale_pg (havp !! (o / 4096)) None) eqn:SP; [cbn in Hc; discriminate|].
destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) None) eqn:SU; [cbn in Hc; discriminate|].
rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
+ rewrite lookup_insert_ne in Hc by congruence. exact Hc.
- split; cbn [r_hav r_havp]; [|exact T2].
intros u' hl ch Hu Hin. destruct (Z.eq_dec u' u) as [->|NE].
+ rewrite lookup_insert_eq in Hu. inversion Hu; subst hl. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
apply In_filter_bool in Hin. destruct Hin as [Hin _]. apply Hl. exact Hin.
+ rewrite lookup_insert_ne in Hu by congruence. eapply T1; eauto.
Qed.

#[using="Type"] Lemma hav_page_step : forall cells hav havp pg t,
sh_ticks (mkShadow cells hav havp) t ->
shadow_le (mkShadow cells hav havp) (mkShadow cells hav (<[pg := t]> havp))
/\ sh_ticks (mkShadow cells hav (<[pg := t]> havp)) t.
Proof.
intros cells hav havp pg t [T1 T2]. cbn [r_hav r_havp] in T1, T2. split.
- split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
destruct (Z.eq_dec (o / 4096) pg) as [E|NE].
+ rewrite E, lookup_insert_eq in Hc. rewrite E.
destruct (cells !! o) as [[v0 tc]|]; cbn [stale_pg orb] in Hc.
* destruct (N.ltb_spec tc t); [discriminate|].
destruct (havp !! pg) as [h|] eqn:E2; cbn [stale_pg].
-- pose proof (T2 _ _ E2). replace (tc <? h)%N with false by (symmetry; apply N.ltb_ge; lia). exact Hc.
-- exact Hc.
* discriminate.
+ rewrite lookup_insert_ne in Hc by congruence. exact Hc.
- split; cbn [r_hav r_havp]; [exact T1|].
intros pg' t' Hp. destruct (Z.eq_dec pg' pg) as [->|NE].
+ rewrite lookup_insert_eq in Hp. inversion Hp; subst. lia.
+ rewrite lookup_insert_ne in Hp by congruence. eapply T2; eauto.
Qed.

#[using="Type"] Lemma Z_iter_invariant : forall {A} (f : A -> A) (Inv : A -> Prop) n x,
(forall y, Inv y -> Inv (f y)) -> Inv x -> Inv (Z.iter n f x).
Proof.
intros A f Inv n x Hf Hx. destruct n; cbn; auto. apply Pos.iter_invariant; auto.
Qed.

#[using="Type"] Lemma havoc_units_le : forall cells hav havp x y t,
sh_ticks (mkShadow cells hav havp) t ->
shadow_le (mkShadow cells hav havp) (mkShadow cells (havoc_units x y t hav) havp)
/\ sh_ticks (mkShadow cells (havoc_units x y t hav) havp) t.
Proof.
intros cells hav havp x y t T. unfold havoc_units.
set (f := fun acc : Z * gmap Z (list (Z * N)) => _).
apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells (snd acc) havp)
/\ sh_ticks (mkShadow cells (snd acc) havp) t)).
- intros [u h] [HL HT]. unfold f. cbn [fst snd].
destruct (hav_unit_step cells h havp u (if u =? (y - 1) / 16 then (let r := y mod 16 in if r =? 0 then 16 else r) else 16) t HT) as [HL2 HT2].
split; [eapply shadow_le_trans; eauto| exact HT2].
- cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.

#[using="Type"] Lemma havoc_pages_le : forall cells hav havp p0 p1 t,
sh_ticks (mkShadow cells hav havp) t ->
shadow_le (mkShadow cells hav havp) (mkShadow cells hav (havoc_pages p0 p1 t havp))
/\ sh_ticks (mkShadow cells hav (havoc_pages p0 p1 t havp)) t.
Proof.
intros cells hav havp p0 p1 t T. unfold havoc_pages.
set (f := fun acc : Z * gmap Z N => _).
apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells hav (snd acc))
/\ sh_ticks (mkShadow cells hav (snd acc)) t)).
- intros [pg h] [HL HT]. unfold f. cbn [fst snd].
destruct (hav_page_step cells hav h pg t HT) as [HL2 HT2].
split; [eapply shadow_le_trans; eauto| exact HT2].
- cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.

#[using="Type"] Lemma sh_ticks_of_ticks_ok : forall st rid, ticks_ok st -> sh_ticks (get_shadow st rid) (s_tick st).
Proof.
intros st rid [T1 T2]. unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn.
- split; [intros; eapply T1; eauto | intros; eapply T2; eauto].
- split; cbn; intros; rewrite lookup_empty in *; discriminate.
Qed.

Definition W_high (W : list (Z * Z)) : Prop := forall lo hi, In (lo, hi) W -> alloc_ceiling <= lo.

#[using="Type"] Lemma W_high_disjoint : forall W a n, W_high W -> a + n <= alloc_ceiling -> disjoint_from W a n.
Proof.
induction W as [|[lo hi] W IH]; intros a n HW Hn; cbn; [exact I|].
split. { left. pose proof (HW lo hi ltac:(left; reflexivity)). lia. }
apply IH; [| exact Hn]. intros lo' hi' Hin. apply (HW lo' hi'). right; exact Hin.
Qed.

#[using="Type"] Lemma ticks_ok_set_tick : forall st t, (s_tick st <= t)%N -> ticks_ok st -> ticks_ok (set_tick t st).
Proof.
intros st t Ht [T1 T2]. split; cbn.
- intros rid sh u hl ch H1 H2 H3. pose proof (T1 rid sh u hl ch H1 H2 H3). lia.
- intros rid sh pg t' H1 H2. pose proof (T2 rid sh pg t' H1 H2). lia.
Qed.

#[using="Type"] Lemma malloc_impl_spec_statement : True. Proof. exact I. Qed.

#[using="Type"] Lemma free_trivial_spec_statement : True. Proof. exact I. Qed.

#[using="Type"] Lemma wrappers_spec_statement : True. Proof. exact I. Qed.

End RC__2.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Q9A7.Mq1.
Import ListNotations. Unset Keyed Unification.
Local Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Lemma zb_land_pow2_bit0 : forall x k, 0 <= k -> Z.testbit x k = false -> Z.land x (2^k) = 0.
Proof.
intros x k Hk Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity| apply Bool.andb_false_r].
Qed.

Lemma zb_lxor_pow2 : forall x k, 0 <= k ->
Z.lxor x (2^k) = x + 2^k - 2 * 2^k * ((x / 2^k) mod 2).
Proof.
intros x k Hk.
destruct (Z.testbit x k) eqn:Hb.
- pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm.
set (y := Z.lxor x (2^k)).
assert (Hy : Z.testbit y k = false).
{ subst y. rewrite Z.lxor_spec, Hb, Z.pow2_bits_true by lia. reflexivity. }
assert (E : Z.lxor y (2^k) = y + 2^k).
{ symmetry. apply Z.add_nocarry_lxor. apply zb_land_pow2_bit0; assumption. }
subst y. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r in E. lia.
- pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm.
rewrite <- Z.add_nocarry_lxor by (apply zb_land_pow2_bit0; assumption). lia.
Qed.

Lemma zb_lxor_b31 : forall x, Z.lxor x 2147483648 = x + 2147483648 - 4294967296 * ((x / 2147483648) mod 2).
Proof. intros x. change 2147483648 with (2^31). rewrite zb_lxor_pow2 by lia. lia. Qed.

Lemma bv_wrap32_eq : forall z, bv_wrap 32 z = z mod 4294967296.
Proof. reflexivity. Qed.

Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.

Lemma swrap32_small : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

Lemma sext32_eq : forall z, sext32 z = ((z + 2147483648) mod 4294967296 - 2147483648) mod 18446744073709551616.
Proof.
intros z. unfold sext32, sub64, M32. rewrite wrap64_mod. change (2^64) with 18446744073709551616. f_equal.
change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. change 2147483648 with (2^31).
rewrite zb_lxor_pow2 by lia. change 4294967296 with (2^32).
Z.div_mod_to_equations. nia.
Qed.

Lemma land_swrap32_sext32 : forall z, Z.land (bv_swrap 32 z) 18446744073709551615 = sext32 z.
Proof. intros z. rewrite land_W64, sext32_eq, swrap32_eq. reflexivity. Qed.

Lemma mod_swrap32_sext32 : forall z, (bv_swrap 32 z) mod 18446744073709551616 = sext32 z.
Proof. intros z. rewrite sext32_eq, swrap32_eq. reflexivity. Qed.

Lemma Z_to_bv_swrap32 : forall z, Z_to_bv 64 (bv_swrap 32 z) = Z_to_bv 64 (sext32 z).
Proof. intros z. rewrite <- land_swrap32_sext32. symmetry. apply Z_to_bv_land64. Qed.

Lemma sext32_range : forall z, 0 <= sext32 z < 18446744073709551616.
Proof. intros z. rewrite sext32_eq. apply Z.mod_pos_bound. lia. Qed.

Lemma sext32_small : forall z, 0 <= z < 2147483648 -> sext32 z = z.
Proof. intros z Hz. rewrite sext32_eq. rewrite (Z.mod_small (z + _)) by lia. rewrite Z.mod_small by lia. lia. Qed.

Lemma sext32_mod32 : forall z, sext32 (z mod 4294967296) = sext32 z.
Proof.
intros z. rewrite !sext32_eq. f_equal. f_equal.
rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma sext32_land64 : forall z, sext32 (Z.land z 18446744073709551615) = sext32 z.
Proof.
intros z. rewrite land_W64, <- (sext32_mod32 (z mod 2^64)), <- (sext32_mod32 z). f_equal.
change (2^64) with (4294967296 * 4294967296). rewrite Z.rem_mul_r by lia.
rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma sext32_landM32 : forall z, sext32 (Z.land z 4294967295) = sext32 z.
Proof.
intros z. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. apply sext32_mod32.
Qed.

Lemma sext32_low : forall z, (sext32 z) mod 4294967296 = z mod 4294967296.
Proof.
intros z. rewrite sext32_eq. change 18446744073709551616 with (4294967296 * 4294967296).
rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia.
Z.div_mod_to_equations. lia.
Qed.

Lemma zext32_eq : forall z, zext32 z = z mod 4294967296.
Proof. intros z. unfold zext32, M32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma zext32_small : forall z, 0 <= z < 4294967296 -> zext32 z = z.
Proof. intros z Hz. rewrite zext32_eq. apply Z.mod_small. lia. Qed.

Lemma zext32_sext32 : forall z, zext32 (sext32 z) = z mod 4294967296.
Proof. intros z. rewrite zext32_eq. apply sext32_low. Qed.

Lemma srliw_pos : forall x k, 0 < k -> srliw x k = Z.shiftr (x mod 4294967296) k.
Proof.
intros x k Hk. unfold srliw. unfold M32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia.
change (2^32) with 4294967296.
apply sext32_small. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma walk_srliw : forall x k, 0 < k -> 0 <= x ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 x) k) = Z.shiftr (x mod 4294967296) k.
Proof.
intros x k Hk Hx. rewrite bv_wrap32_eq. apply swrap32_small.
pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.le_trans with 0; [lia|]. apply Z.div_pos; lia. }
apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma land_mask_small : forall x k, 0 <= k -> 0 <= x < 2^k -> Z.land x (2^k - 1) = x.
Proof. intros x k Hk Hx. rewrite zb_land_mask by lia. apply Z.mod_small. lia. Qed.

Lemma land_W64_small : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (2^64 - 1). apply land_mask_small; [lia|]. change (2^64) with 18446744073709551616. lia. Qed.

Lemma land_M32_small : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (2^32 - 1). apply land_mask_small; [lia|]. change (2^32) with 4294967296. lia. Qed.

Lemma land63_small : forall x, 0 <= x < 64 -> Z.land x 63 = x.
Proof. intros x Hx. change 63 with (2^6 - 1). apply land_mask_small; [lia|]. change (2^6) with 64. lia. Qed.

Lemma land63_64_128 : forall x, 64 <= x < 128 -> Z.land x 63 = x - 64.
Proof.
intros x Hx. change 63 with (2^6 - 1). rewrite zb_land_mask by lia. change (2^6) with 64.
rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma shiftr63_small : forall x, 0 <= x < 9223372036854775808 -> Z.shiftr x 63 = 0.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. change (2^63) with 9223372036854775808. lia. Qed.

Lemma shiftr_bound : forall x k, 0 <= x < 18446744073709551616 -> 0 <= k <= 64 ->
0 <= Z.shiftr x k < 2^(64 - k).
Proof.
intros x k Hx Hk. rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (64 - k)) with 64 by lia.
change (2^64) with 18446744073709551616. lia.
Qed.

Lemma sext32_gcc : forall v, sext32 (Z.lxor v 2147483648 - 2147483648) = sext32 v.
Proof.
intros v. rewrite <- (sext32_mod32 (Z.lxor v _ - _)), <- (sext32_mod32 v). f_equal.
rewrite zb_lxor_b31. Z.div_mod_to_equations. lia.
Qed.

Lemma gcc_sext_low32 : forall v, (Z.lxor v 2147483648 - 2147483648) mod 4294967296 = v mod 4294967296.
Proof. intros v. rewrite zb_lxor_b31. Z.div_mod_to_equations. lia. Qed.

Lemma gcc_sext_low6 : forall v, Z.land (Z.lxor v 2147483648 - 2147483648) 63 = Z.land v 63.
Proof.
intros v. change 63 with (2^6 - 1). rewrite !zb_land_mask by lia. rewrite zb_lxor_b31.
change (2^6) with 64. Z.div_mod_to_equations. lia.
Qed.

Lemma gcc_sext_small : forall v, 0 <= v < 2147483648 ->
Z.land (Z.lxor v 2147483648 - 2147483648) 18446744073709551615 = v.
Proof.
intros v Hv. rewrite zb_lxor_b31, (Z.div_small v) by lia. change (0 mod 2) with 0.
rewrite land_W64. rewrite Z.mod_small; lia.
Qed.

Lemma shiftr_mod32_bound : forall x k, 0 < k -> 0 <= Z.shiftr (x mod 4294967296) k < 2147483648.
Proof.
intros x k Hk. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma lxor31_sub_small : forall v, 0 <= v < 2147483648 -> Z.lxor v 2147483648 - 2147483648 = v.
Proof. intros v Hv. rewrite zb_lxor_b31, (Z.div_small v) by lia. change (0 mod 2) with 0. lia. Qed.

Ltac fix32 :=
repeat first
[ rewrite walk_srliw by (first [lia | zrange_nonneg])
| match goal with
| |- context [Z.lxor (Z.shiftr (?x mod 4294967296) ?k) 2147483648 - 2147483648] =>
rewrite (lxor31_sub_small (Z.shiftr (x mod 4294967296) k)) by (apply shiftr_mod32_bound; lia)
| |- context [Z.land (Z.lxor (Z.shiftr (?x mod 4294967296) ?k) 2147483648 - 2147483648) 18446744073709551615] =>
rewrite (gcc_sext_small (Z.shiftr (x mod 4294967296) k)) by (apply shiftr_mod32_bound; lia)
end ].
Ltac wstep := zstep; fix32.

Lemma clz32_mirror_range : forall r, 0 <= clz32_mirror r < 18446744073709551616.
Proof. intros r. unfold clz32_mirror. cbv zeta. unfold srliw at 1. apply sext32_range. Qed.

Lemma land63_mod : forall x, Z.land x 63 = x mod 64.
Proof. intros. change 63 with (2^6 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma land63_congr32 : forall x y, x mod 4294967296 = y mod 4294967296 -> Z.land x 63 = Z.land y 63.
Proof.
intros x y H. rewrite !land63_mod.
rewrite <- (Z.mod_mod_divide x 4294967296 64), <- (Z.mod_mod_divide y 4294967296 64) by (exists 67108864; reflexivity).
now rewrite H.
Qed.

Lemma land63_sext32 : forall x, Z.land (sext32 x) 63 = Z.land x 63.
Proof. intros. apply land63_congr32. apply sext32_low. Qed.

Lemma land63_zext32 : forall x, Z.land (zext32 x) 63 = Z.land x 63.
Proof. intros. apply land63_congr32. rewrite zext32_eq. apply Z.mod_mod. lia. Qed.

Lemma land63_gcc : forall x,
Z.land (Z.land (Z.lxor x 2147483648 - 2147483648) 18446744073709551615) 63 = Z.land x 63.
Proof.
intros. apply land63_congr32. rewrite land_W64. change (2^64) with 18446744073709551616.
rewrite Z.mod_mod_divide by (exists 4294967296; reflexivity).
apply gcc_sext_low32.
Qed.

Lemma landM32_gcc : forall x,
Z.land (Z.land (Z.lxor x 2147483648 - 2147483648) 18446744073709551615) 4294967295 = zext32 (sext32 x).
Proof.
intros. rewrite zext32_sext32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask, land_W64 by lia.
change (2^32) with 4294967296. change (2^64) with 18446744073709551616.
rewrite Z.mod_mod_divide by (exists 4294967296; reflexivity).
apply gcc_sext_low32.
Qed.

Lemma land63_not_congr : forall x y, 0 <= x < 18446744073709551616 -> 0 <= y < 18446744073709551616 ->
x mod 4294967296 = y mod 4294967296 ->
Z.land (Z.lxor x 18446744073709551615) 63 = Z.land (Z.lxor y 18446744073709551615) 63.
Proof.
intros x y Hx Hy H. rewrite !zb_lxor_ones by lia. apply land63_congr32.
Z.div_mod_to_equations. lia.
Qed.

Lemma shl48_congr : forall x y, x mod 4294967296 = y mod 4294967296 ->
Z.land (Z.shiftl x 48) 18446744073709551615 = Z.land (Z.shiftl y 48) 18446744073709551615.
Proof.
intros x y H. rewrite !land_W64, !Z.shiftl_mul_pow2 by lia.
change (2^64) with (65536 * 2^48). rewrite !Z.mul_mod_distr_r by lia. f_equal.
rewrite <- (Z.mod_mod_divide x 4294967296 65536), <- (Z.mod_mod_divide y 4294967296 65536) by (exists 65536; reflexivity).
now rewrite H.
Qed.

Lemma shl48_sext32 : forall x,
Z.land (Z.shiftl (sext32 x) 48) 18446744073709551615 = Z.land (Z.shiftl x 48) 18446744073709551615.
Proof. intros. apply shl48_congr. apply sext32_low. Qed.

Lemma srai63_word : forall x, 0 <= x < 18446744073709551616 ->
Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 x)) 63) = Z_to_bv 64 (if 9223372036854775808 <=? x then 18446744073709551615 else 0).
Proof.
intros x Hx. rewrite zb_signed, unsigned_lit by (change (2^64) with 18446744073709551616; lia).
change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616.
destruct (Z.ltb_spec0 x 9223372036854775808); destruct (Z.leb_spec0 9223372036854775808 x); try (exfalso; lia).
- rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
- apply Z_to_bv_eqm. rewrite Z.shiftr_div_pow2 by lia. change (2^63) with 9223372036854775808.
Z.div_mod_to_equations. lia.
Qed.

Lemma half_land : forall x, 0 <= x -> Z.land (Z.shiftr x 1) 2147483647 = Z.shiftr (x mod 4294967296) 1.
Proof.
intros x Hx. change 2147483647 with (2^31 - 1). rewrite zb_land_mask, !Z.shiftr_div_pow2 by lia.
change (2^31) with 2147483648. change (2^1) with 2. Z.div_mod_to_equations. lia.
Qed.

Ltac name_as_by_tac X e tac :=
set (X := e) in *;
let RX := fresh "R" X in
assert (RX : 0 <= X < 18446744073709551616) by (subst X; tac).
Tactic Notation "name_as_by" ident(X) constr(e) tactic3(tac) := name_as_by_tac X e tac.

Lemma sext32_cases : forall u, 0 <= sext32 u < 2147483648 \/ 18446744071562067968 <= sext32 u < 18446744073709551616.
Proof. intros u. rewrite sext32_eq. Z.div_mod_to_equations. lia. Qed.

Lemma shiftr_const : forall x k c, 0 <= k -> c * 2^k <= x < (c + 1) * 2^k -> Z.shiftr x k = c.
Proof.
intros x k c Hk Hx. rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
apply Z.le_antisymm.
- apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_comm. lia.
- apply Z.div_le_lower_bound; [lia|]. rewrite Z.mul_comm. lia.
Qed.

Lemma land_signmask_shl : forall x, 0 <= x < 18446744073709551616 ->
Z.land x 18446744071562067968 = Z.shiftl (Z.shiftr x 31) 31.
Proof.
intros x Hx. change 18446744071562067968 with (Z.shiftl (Z.ones 33) 31).
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.lt_ge_cases i 31).
- rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
- rewrite !Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 31 + 31) with i by lia.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
+ rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry.
destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [|lia].
apply Z.log2_lt_pow2; [lia|]. change (2^64) with 18446744073709551616. lia.
Qed.

Lemma land_signmask : forall x, 0 <= x < 18446744073709551616 ->
Z.land x 18446744071562067968 = x - x mod 2147483648.
Proof.
intros x Hx. rewrite land_signmask_shl, zb_shr_shl by lia. reflexivity.
Qed.

Lemma srai63_var : forall a : bv 64,
Z_to_bv 64 (Z.shiftr (bv_signed a) 63) = Z_to_bv 64 (if 9223372036854775808 <=? bv_unsigned a then 18446744073709551615 else 0).
Proof.
intros a. rewrite <- srai63_word by (pose proof (zr_word a) as H; unfold inr64 in H; change (2^64) with 18446744073709551616 in H; lia).
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma signhi_pos : forall x, 0 <= x < 2147483648 ->
Z.land (Z.shiftl (Z.land x 18446744071562067968) 32) 18446744073709551615 = 0.
Proof.
intros x Hx. rewrite land_signmask, Z.mod_small by lia. rewrite Z.sub_diag. reflexivity.
Qed.

Lemma signhi_neg : forall x, 18446744071562067968 <= x < 18446744073709551616 ->
Z.land (Z.shiftl (Z.land x 18446744071562067968) 32) 18446744073709551615 = 9223372036854775808.
Proof.
intros x Hx. rewrite land_signmask by lia.
replace (x - x mod 2147483648) with 18446744071562067968 by (Z.div_mod_to_equations; lia).
reflexivity.
Qed.

Lemma negabs_model : forall x, 0 <= x < 18446744073709551616 ->
Z.land (Z.lxor x 18446744073709551615 - 18446744073709551615) 18446744073709551615 = (18446744073709551616 - x) mod 18446744073709551616.
Proof.
intros x Hx. rewrite zb_lxor_ones, land_W64 by lia. change (2^64) with 18446744073709551616.
Z.div_mod_to_equations. lia.
Qed.

Lemma negabs_code : forall x, 0 <= x < 18446744073709551616 ->
Z.lxor 18446744073709551615 x + 1 = 18446744073709551616 - x.
Proof. intros x Hx. rewrite Z.lxor_comm, zb_lxor_ones by lia. lia. Qed.

Lemma sraiw31_word : forall x, 0 <= x < 18446744073709551616 ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 x) 31)) =
Z_to_bv 64 (Z.land (0 - Z.land (Z.shiftr x 31) 1) 18446744073709551615).
Proof.
intros x Hx. apply Z_to_bv_eqm. rewrite land_W64, !swrap32_eq, land_1, !Z.shiftr_div_pow2 by lia.
change (2^31)%Z with 2147483648%Z. change (2^64)%Z with 18446744073709551616%Z.
Z.div_mod_to_equations. lia.
Qed.

Ltac model_reg_w_tac n X mexpr :=
let w := getreg n in
lazymatch w with
| Z_to_bv 64 ?e =>
replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
by (rewrite ?srliw_pos by lia; first [ f_equal; zeq | rewrite Z_to_bv_land64; f_equal; zeq ]);
set (X := mexpr) in *;
let RX := fresh "R" X in
assert (RX : 0 <= X < 18446744073709551616) by (subst X; rewrite ?srliw_pos by lia; zrange)
| _ => fail "model_reg_w: register" n "holds" w
end.
Tactic Notation "model_reg_w" constr(n) ident(X) constr(mexpr) := model_reg_w_tac n X mexpr.

Lemma clz64_mirror_range : forall x, 0 <= clz64_mirror x < 18446744073709551616.
Proof.
intros x. unfold clz64_mirror. cbv zeta. unfold mul64.
match goal with |- context [Z.shiftr (wrap64 ?p) 56] =>
pose proof (wrap64_range p) as Hr; rewrite (Z.shiftr_div_pow2 (wrap64 p)) by lia end.
change (2^64) with 18446744073709551616 in Hr.
split. { apply Z.div_pos; lia. } apply Z.div_lt_upper_bound; lia.
Qed.

Lemma zb_land_pow2 : forall x k, 0 <= k -> Z.land x (2^k) = 2^k * ((x / 2^k) mod 2).
Proof.
intros x k Hk. destruct (Z.testbit x k) eqn:Hb.
- pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm, Z.mul_1_r.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity | apply Bool.andb_false_r].
- pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm, Z.mul_0_r.
apply zb_land_pow2_bit0; assumption.
Qed.

Lemma signbit63 : forall x, 0 <= x < 18446744073709551616 ->
Z.land (Z.shiftl (Z.shiftr x 63) 63) 18446744073709551615 = Z.land 9223372036854775808 x.
Proof.
intros x Hx. rewrite zb_shr_shl, land_W64 by lia. rewrite Z.land_comm.
change 9223372036854775808 with (2^63). rewrite zb_land_pow2 by lia.
change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616.
Z.div_mod_to_equations. lia.
Qed.

Lemma lor_rot_asx : forall a s x, Z.lor (Z.lor a s) x = Z.lor (Z.lor x a) s.
Proof.
intros. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
destruct (Z.testbit a i), (Z.testbit s i), (Z.testbit x i); reflexivity.
Qed.
Lemma lor_rot_dsg : forall d s g, Z.lor (Z.lor d s) g = Z.lor (Z.lor d g) s.
Proof.
intros. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
destruct (Z.testbit d i), (Z.testbit s i), (Z.testbit g i); reflexivity.
Qed.

Ltac reg_rewrite n lem :=
let w := getreg n in
lazymatch w with
| Z_to_bv 64 ?e =>
let e' := fresh "e" in let E := fresh "E" in
remember e as e' eqn:E in |- *;
rewrite lem in E; subst e'
end.

Lemma sra63_leb : forall x, 0 <= x < 18446744073709551616 ->
(if negb (Z.shiftr x 63 =? 0) then 18446744073709551615 else 0) =
(if 9223372036854775808 <=? x then 18446744073709551615 else 0).
Proof.
intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2^63) with 9223372036854775808.
destruct (Z.leb_spec0 9223372036854775808 x).
- rewrite (proj2 (Z.eqb_neq _ _)); [reflexivity|]. Z.div_mod_to_equations. lia.
- rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma ltb1_eqb0 : forall x, 0 <= x -> (x <? 1) = (x =? 0).
Proof. intros x Hx. destruct (Z.ltb_spec0 x 1); destruct (Z.eqb_spec x 0); try reflexivity; exfalso; lia. Qed.

Lemma sext32_congr : forall x y, x mod 4294967296 = y mod 4294967296 -> sext32 x = sext32 y.
Proof. intros x y H. rewrite <- (sext32_mod32 x), <- (sext32_mod32 y), H. reflexivity. Qed.

Lemma nez_sub_lxor : forall a b, 0 <= a < 18446744073709551616 -> 0 <= b < 18446744073709551616 ->
(0 <? Z.land (a - b) 18446744073709551615) = (0 <? Z.lxor b a).
Proof.
intros a b Ha Hb. rewrite land_W64. change (2^64) with 18446744073709551616.
assert (Hn : 0 <= Z.lxor b a) by (apply Z.lxor_nonneg; split; intros; lia).
destruct (Z.eq_dec a b) as [->|Hne].
- rewrite Z.sub_diag, Z.lxor_nilpotent. reflexivity.
- assert (Z.lxor b a <> 0) by (intros E; apply (proj1 (Z.lxor_eq_0_iff b a)) in E; lia).
apply eq_true_iff_eq. rewrite !Z.ltb_lt. split; intros _; [lia|]. Z.div_mod_to_equations. lia.
Qed.

Lemma land63_lxor63 : forall x, Z.land (Z.lxor x 63) 63 = Z.land (Z.lxor x 18446744073709551615) 63.
Proof.
intros x. change 63 with (Z.ones 6). change 18446744073709551615 with (Z.ones 64).
apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, !Z.lxor_spec.
destruct (Z.lt_ge_cases i 6).
- rewrite !Z.ones_spec_low by lia. reflexivity.
- rewrite (Z.ones_spec_high 6) by lia. rewrite !Bool.andb_false_r. reflexivity.
Qed.

Lemma exp0_gcc : forall s, Z_to_bv 64 (s + -15360) =
Z_to_bv 64 (Z.land (Z.land (s + 18446744073709536255) 18446744073709551615 + 1) 18446744073709551615).
Proof.
intros s. apply Z_to_bv_eqm. rewrite !land_W64. change (2^64) with 18446744073709551616.
Z.div_mod_to_equations. lia.
Qed.

Definition to_d_pack (dE dS a_hi : Z) : Z := Z.lor (Z.lor (shl64 dE 52) (shl64 (shr64 a_hi 63) 63)) dS.

Definition to_d_normD (sig1 exp0 : Z) : Z * Z :=
let carry := shr64 sig1 52 in (add64 carry exp0, Z.land (sub64 carry 1) sig1).

Definition to_d_normal (a_lo sigHi candM1 : Z) : Z * Z :=
let sig0 := Z.lor (shr64 a_lo 60) (shl64 sigHi 4) in
let roundBits := shr64 (shl64 a_lo 4) 4 in
let exp0 := add64 candM1 1 in
let sig1 := trunc_round sig0 roundBits in
to_d_normD sig1 exp0.

Definition to_d_subD (sig1 : Z) : Z * Z :=
let carry := nez64 (shr64 sig1 52) in (carry, Z.lxor sig1 (shl64 carry 52)).

Definition to_d_subC (srLo sigHi1 shift mM64 sticky : Z) : Z * Z :=
let srHi0 := shr64 sigHi1 (Z.land shift 63) in
let srHi := Z.land (sra63 mM64) srHi0 in
let sig0 := Z.lor (shr64 srLo 60) (shl64 srHi 4) in
let roundBits := Z.lor (shr64 (shl64 srLo 4) 4) sticky in
let sig1 := trunc_round sig0 roundBits in
to_d_subD sig1.

Definition to_d_subB (a_lo sigHi1 shift shNZ slLo slHi : Z) : Z * Z :=
let stickySrc := Z.lor slLo slHi in
let m := zext32 shift in
let sticky0 := nez64 stickySrc in
let mM64 := sub64 m 64 in
let sticky := Z.land shNZ sticky0 in
let srLo := if negb (is_neg64 mM64) then shr64 sigHi1 (Z.land m 63)
else Z.lor (shr64 a_lo (Z.land shift 63)) (shl64 (shl64 sigHi1 1) (Z.land (not64 m) 63)) in
to_d_subC srLo sigHi1 shift mM64 sticky.

Definition to_d_subA (a_lo sigHi srcExp k shift : Z) : Z * Z :=
let expNZ := nez64 srcExp in
let shNZ0 := Z.lxor k srcExp in
let negsh := sext32 (sub64 0 shift) in
let implicit := shl64 expNZ 48 in
let shNZ := nez64 shNZ0 in
let nW := sext32 (sub64 128 shift) in
let t0 := shl64 a_lo (Z.land negsh 63) in
let sigHi1 := Z.lor sigHi implicit in
let n := zext32 nW in
let nM64 := sub64 n 64 in
let slLo := Z.land (sra63 nM64) t0 in
let slHi := if negb (is_neg64 nM64) then shl64 a_lo (Z.land n 63)
else Z.lor (shl64 sigHi1 (Z.land negsh 63)) (shr64 (shr64 a_lo 1) (Z.land (not64 n) 63)) in
to_d_subB a_lo sigHi1 shift shNZ slLo slHi.

Definition to_d_range (a_lo sigHi srcExp : Z) : Z * Z :=
if negb (srcExp <=? 0x43fe) then (2047, 0)
else
let expZ := eqz64 srcExp in
let k := Z.lxor expZ 0x3c01 in
let shift := sub64 k srcExp in
if lt_s64 112 shift then (0, 0)
else to_d_subA a_lo sigHi srcExp k shift.

Definition to_d_core (a_lo a_hi : Z) : Z * Z :=
let srcExp := shr64 (shl64 a_hi 1) 49 in
let sigHi := shr64 (shl64 a_hi 16) 16 in
let candM1 := add64 srcExp 0xffffffffffffc3ff in
if negb (2045 <? candM1) then to_d_normal a_lo sigHi candM1
else
let isNaN := if Z.lor a_lo sigHi =? 0 then false else negb (negb (srcExp =? 0x7fff)) in
if isNaN then (2047, Z.lor (Z.lor (shr64 a_lo 60) DQUIET) (shl64 sigHi 4))
else to_d_range a_lo sigHi srcExp.

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
intros lo hi H. unfold lo64. rewrite wrap64_mod.
rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

Lemma f128_to_d_split : forall a_lo a_hi, (0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z ->
f128_to_d (a_lo + 2^64 * a_hi) = (let '(dE, dS) := to_d_core a_lo a_hi in to_d_pack dE dS a_hi).
Proof. intros. unfold f128_to_d. rewrite lo64_words, hi64_words by lia. reflexivity. Qed.

Definition to_d_pack_g (dE dS sgn : Z) : Z := Z.lor (shl64 dE 52) (Z.lor dS sgn).

Lemma f128_to_d_split_g : forall a_lo a_hi, (0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z ->
f128_to_d (a_lo + 2^64 * a_hi) =
(let '(dE, dS) := to_d_core a_lo a_hi in to_d_pack_g dE dS (Z.land a_hi 9223372036854775808)).
Proof.
intros a_lo a_hi Hl Hh. rewrite f128_to_d_split by assumption.
destruct (to_d_core a_lo a_hi) as [dE dS]. unfold to_d_pack, to_d_pack_g.
unfold shl64 at 2. rewrite wrap64_mod. change (2^64) with 18446744073709551616.
rewrite <- land_W64, signbit63 by (change (2^64) with 18446744073709551616 in Hh; lia).
rewrite (Z.land_comm 9223372036854775808 a_hi).
apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
destruct (Z.testbit (shl64 dE 52) i), (Z.testbit dS i), (Z.testbit (Z.land a_hi 9223372036854775808) i); reflexivity.
Qed.

Lemma round_even_g : forall x, 0 <= x ->
Z_to_bv 64 (Z.land (Z.land (x + 1) 18446744073709551615) 18446744073709551614) =
Z_to_bv 64 (Z.land (Z.land x 1 + x) 18446744073709551615).
Proof.
intros x Hx. apply Z_to_bv_eqm. rewrite land_even_mask, !land_W64, !land_1.
change (2^64) with 18446744073709551616.
rewrite (Z.mod_mod_divide (x + 1) 18446744073709551616 2) by (exists 9223372036854775808; reflexivity).
Z.div_mod_to_equations. lia.
Qed.

Lemma to_d_shift_facts : forall srcExp, 0 <= srcExp <= 15360 ->
Z.lxor (Z.land (Z.lxor (Z.b2z (srcExp =? 0)) 15361 - srcExp) 18446744073709551615) 9223372036854775808
<= 9223372036854775920 ->
Z.b2z (srcExp =? 0) = 0 /\ Z.land (Z.lxor (Z.b2z (srcExp =? 0)) 15361 - srcExp) 18446744073709551615 = 15361 - srcExp
/\ 1 <= 15361 - srcExp <= 112.
Proof.
intros srcExp Hs. destruct (Z.eqb_spec srcExp 0) as [E|E].
- subst srcExp. intros K. exfalso. apply K. vm_compute. reflexivity.
- cbn [Z.b2z]. change (Z.lxor 0 15361) with 15361.
rewrite land_W64_small by lia. change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2 by lia.
rewrite (Z.div_small (15361 - srcExp)) by lia. change (2^63) with 9223372036854775808. change (0 mod 2) with 0. lia.
Qed.

Lemma lxor1_b2z : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. intros [|]; reflexivity. Qed.

Lemma landM32_swrap_land64 : forall x,
Z.land (Z.land (bv_swrap 32 x) 18446744073709551615) 4294967295 = Z.land (Z.land x 18446744073709551615) 4294967295.
Proof.
intros x. rewrite land_swrap32_sext32. change 4294967295 with (2^32 - 1). rewrite !zb_land_mask, land_W64 by lia.
change (2^32) with 4294967296. rewrite sext32_low. change (2^64) with 18446744073709551616.
rewrite Z.mod_mod_divide by (exists 4294967296; reflexivity). reflexivity.
Qed.

Lemma shl13_shr16 : forall x, 0 <= x < 18446744073709551616 ->
Z.shiftr (Z.land (Z.shiftl x 13) 18446744073709551615) 16 = Z.land (Z.shiftr x 3) 281474976710655.
Proof.
intros x Hx. rewrite land_W64, Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
change 281474976710655 with (2^48 - 1). rewrite zb_land_mask by lia.
change (2^64) with (2251799813685248 * 8192). change (2^13) with 8192. change (2^16) with (8192 * 8).
change (2^3) with 8. change (2^48) with 281474976710656.
rewrite Z.mul_mod_distr_r by lia.
rewrite <- Z.div_div, Z.div_mul by lia.
Z.div_mod_to_equations. lia.
Qed.

Lemma lor_rot_bsa : forall b s a, Z.lor (Z.lor b s) a = Z.lor (Z.lor a s) b.
Proof.
intros. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
destruct (Z.testbit b i), (Z.testbit s i), (Z.testbit a i); reflexivity.
Qed.

Lemma b2z_ltb1 : forall b, (Z.b2z b <? 1) = negb b.
Proof. intros [|]; reflexivity. Qed.

Lemma signbit63' : forall x, 0 <= x < 18446744073709551616 ->
Z.land (Z.shiftl (Z.shiftr x 63) 63) 18446744073709551615 = Z.land x 9223372036854775808.
Proof. intros. rewrite signbit63 by assumption. apply Z.land_comm. Qed.

