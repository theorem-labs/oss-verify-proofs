(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YM06 YP09 YM05 YK15 YM02.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO16 YL01.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK1j.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO10 YO0s YO0u YO15 YN03 YN2b YN33.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YI04.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma blocks_map_stable : forall (L L' : layout) (A A' : astate) l,
(forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ptr_addr L' p = ptr_addr L p) ->
incl l (user_blocks A) -> incl l (user_blocks A') ->
map (fun b : sptr * Z => (ptr_addr L' (fst b), snd b)) l = map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l.
Proof using.
intros L L' A A' l Hs. induction l as [|[q k] l IH]; intros H1 H2; cbn [map fst snd]; [reflexivity|].
rewrite (Hs q k (H1 _ (or_introl eq_refl)) (H2 _ (or_introl eq_refl))).
rewrite IH; [reflexivity | intros x Hx; apply H1; right; exact Hx | intros x Hx; apply H2; right; exact Hx].
Qed.
Lemma blocks_add : forall (L L' : layout) (A A' : astate) q n l1 l2,
(forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A') -> ptr_addr L' p = ptr_addr L p) ->
user_blocks A' = l1 ++ (q, n) :: l2 -> user_blocks A = l1 ++ l2 ->
exists b1 b2, blocks L' A' = b1 ++ (ptr_addr L' q, n) :: b2 /\ blocks L A = b1 ++ b2.
Proof using.
intros L L' A A' q n l1 l2 Hs E1 E2.
assert (S1 : incl l1 (user_blocks A) /\ incl l1 (user_blocks A')).
{ rewrite E1, E2. split; intros x Hx; apply in_app_iff; left; exact Hx. }
assert (S2 : incl l2 (user_blocks A) /\ incl l2 (user_blocks A')).
{ rewrite E1, E2. split; intros x Hx; apply in_app_iff; right; [exact Hx | right; exact Hx]. }
exists (map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l1), (map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l2).
unfold blocks. rewrite E1, E2, !map_app. cbn [map fst snd].
rewrite (blocks_map_stable L L' A A' l1 Hs (proj1 S1) (proj2 S1)).
rewrite (blocks_map_stable L L' A A' l2 Hs (proj1 S2) (proj2 S2)).
split; reflexivity.
Qed.
Lemma blocks_del : forall (L L' : layout) (A A' : astate) p n l1 l2,
(forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A') -> ptr_addr L' q = ptr_addr L q) ->
user_blocks A = l1 ++ (p, n) :: l2 -> user_blocks A' = l1 ++ l2 ->
exists b1 b2, blocks L A = b1 ++ (ptr_addr L p, n) :: b2 /\ blocks L' A' = b1 ++ b2.
Proof using.
intros L L' A A' p n l1 l2 Hs E1 E2.
assert (S1 : incl l1 (user_blocks A) /\ incl l1 (user_blocks A')).
{ rewrite E1, E2. split; intros x Hx; apply in_app_iff; left; exact Hx. }
assert (S2 : incl l2 (user_blocks A) /\ incl l2 (user_blocks A')).
{ rewrite E1, E2. split; intros x Hx; apply in_app_iff; right; [right; exact Hx | exact Hx]. }
exists (map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l1), (map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l2).
unfold blocks. rewrite E1, E2, !map_app. cbn [map fst snd].
rewrite (blocks_map_stable L L' A A' l1 Hs (proj1 S1) (proj2 S1)).
rewrite (blocks_map_stable L L' A A' l2 Hs (proj1 S2) (proj2 S2)).
split; reflexivity.
Qed.
Lemma regions_after_len : forall tr rs, (length rs <= length (regions_after rs tr))%nat.
Proof using.
induction tr as [|e t IH]; intros rs; [cbn; lia|].
rewrite regions_after_cons. etransitivity; [|apply IH].
destruct e as [q z]. destruct q; cbn [ra1];
repeat match goal with
| |- context [if ?b then _ else _] => destruct b
| |- context [match ?x with _ => _ end] => destruct x
end; rewrite ?length_lupd, ?length_app; cbn [length]; lia.
Qed.
Lemma regions_grow_malloc : forall s n tr p s', WF s -> 0 <= n -> cpath04 (malloc n s) tr (p, s') ->
(length (st_regions s) <= length (st_regions s'))%nat.
Proof using.
intros s n tr p s' HW Hn Hp.
pose proof (malloc_regions s n tr p s' HW Hn (cpath04_yields _ _ _ Hp)) as H.
apply same_shape_shp, shp_length in H. rewrite H. apply regions_after_len.
Qed.
Lemma regions_grow_free : forall s p n tr s', WF s -> In (p, n) (user_blocks s) -> cpath04 (free (Some p) s) tr (tt, s') ->
(length (st_regions s) <= length (st_regions s'))%nat.
Proof using.
intros s p n tr s' HW Hin Hp.
pose proof (free_regions s p n tr s' HW Hin (cpath04_yields _ _ _ Hp)) as H.
apply same_shape_shp, shp_length in H. rewrite H. apply regions_after_len.
Qed.
Lemma kept_of_post : forall (B : malloc_syms) (L : layout) (A A' : astate) mem mem' (gone : Z -> Prop),
(forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n ->
mbyte (ms_segs B) mem' (ptr_addr L p + i) = mbyte (ms_segs B) mem (ptr_addr L p + i)) ->
(forall p n, In (p, n) (user_blocks A) -> ~ gone (ptr_addr L p) -> In (p, n) (user_blocks A')) ->
blocks_kept B L A mem mem' gone.
Proof using.
intros B L A A' mem mem' gone Hk Hs a k i Hin Hg Hi.
apply YI04.blocks_In in Hin as (p & <- & Hin).
exact (Hk p k i Hin (Hs p k Hin Hg) Hi).
Qed.
Definition rw_ivl (B : malloc_syms) : list (Z * Z) :=
[ (ms_lock B, ms_lock B + 4); (ms_libc B + 3, ms_libc B + 4); (ms_libc B + 8, ms_libc B + 16);
(ms_libc B + 48, ms_libc B + 56); (ms_guard B, ms_guard B + 8);
(ms_ctx B, ms_ctx B + CTX_SIZE); (errno_addr B, errno_addr B + 4); (vml_lo B, vml_lo B + vml_len B) ].
Definition ro_apart_b (B : malloc_syms) : bool :=
forallb (fun s => seg_writable s ||
((Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? CEIL_MIN) &&
forallb (ivl_disjoint (Z.of_N (seg_base s), Z.of_N (seg_base s) + Z.of_N (seg_size s))) (rw_ivl B)))
(ms_segs B).
Lemma ro_apart_sound : forall B a, ro_apart_b B = true -> 0 <= a < 2 ^ 64 ->
Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true ->
in_img B a /\ a < CEIL_MIN /\ forall p, In p (rw_ivl B) -> ~ (fst p <= a < snd p).
Proof using.
intros B a H Ha Hro. unfold Mem.ro_addr in Hro.
rewrite Z_to_bv_unsigned, bv_wrap_small in Hro by (change (bv_modulus 64) with (2 ^ 64); lia).
destruct (find_segment (ms_segs B) a 1) as [s|] eqn:F; [|discriminate].
apply negb_true_iff in Hro.
pose proof (find_segment_in _ _ _ _ F) as Hin. destruct (find_segment_range _ _ _ _ F) as [R1 R2].
unfold ro_apart_b in H. rewrite forallb_forall in H. specialize (H s Hin). rewrite Hro in H. cbn [orb] in H.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. rewrite forallb_forall in H2.
assert (CM : CEIL_MIN < 2 ^ 63) by lia.
split; [|split; [lia|]].
- split; [intros E; rewrite E in Hin; destruct Hin|].
exists (segment_reservation s). split; [apply in_map; exact Hin|].
unfold segment_reservation, page_round_down_Z, page_round_up_Z, page_size. cbn [fst snd].
set (lo := Z.of_N (seg_base s)) in *. set (hi := lo + Z.of_N (seg_size s)) in *.
assert (L0 : 0 <= lo) by (unfold lo; lia).
pose proof (Z.div_mod lo 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)) as M1.
pose proof (Z.div_mod (hi + 4096 - 1) 4096 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (hi + 4096 - 1) 4096 ltac:(lia)) as M2.
rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
- intros p Hp Hx. specialize (H2 p Hp). unfold ivl_disjoint in H2. cbn [fst snd] in H2.
apply orb_prop in H2 as [E|E]; apply Z.leb_le in E; lia.
Qed.
Lemma rw_facts : forall B a, (forall p, In p (rw_ivl B) -> ~ (fst p <= a < snd p)) ->
~ (ms_lock B <= a < ms_lock B + 4) /\ a <> ms_libc B + 3 /\ ~ (ms_libc B + 8 <= a < ms_libc B + 16) /\
~ (ms_libc B + 48 <= a < ms_libc B + 56) /\ ~ (ms_guard B <= a < ms_guard B + 8) /\
~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4) /\
~ (vml_lo B <= a < vml_lo B + vml_len B).
Proof using.
intros B a H. unfold rw_ivl in H.
repeat split; intro X; [ apply (H _ (or_introl eq_refl))
| apply (H _ (or_intror (or_introl eq_refl)))
| apply (H _ (or_intror (or_intror (or_introl eq_refl))))
| apply (H _ (or_intror (or_intror (or_intror (or_introl eq_refl)))))
| apply (H _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))
| apply (H _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))
| apply (H _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))
| apply (H _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) ];
cbn [fst snd]; lia.
Qed.
Lemma ro_agree_post : forall (B : malloc_syms) (MR : MR_t) stk L A regs mem md E L' A' regs' mem' md',
AllocExtra B MR -> ro_apart_b B = true -> alloc_ceiling + stk <= spZ regs -> MR L A mem md ->
(forall a, E a -> exists p n, In (p, n) (user_blocks A) /\ ptr_addr L p <= a < ptr_addr L p + n) ->
call_post_k B MR stk L A regs mem md E L' A' regs' mem' md' ->
ro_agree (ms_segs B) mem -> ro_agree (ms_segs B) mem'.
Proof using.
intros B MR stk L A regs mem md E L' A' regs' mem' md' AX HB Hsp HMR HE Hpost Hro a Ha.
pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
assert (Ea : a = Z_to_bv 64 (bv_unsigned a)) by (symmetry; apply Z_to_bv_bv_unsigned).
set (z := bv_unsigned a) in *. rewrite Ea in Ha |- *.
destruct (ro_apart_sound B z HB Hr Ha) as (Himg & Hlow & Hrw).
destruct (rw_facts B z Hrw) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
pose proof (Hro (Z_to_bv 64 z) Ha) as Hm.
destruct Hpost as (HMR' & _ & _ & _ & _ & _ & _ & HF & _ & _).
pose proof (@alloc_ceiling_value rc) as AC.
assert (Ht : (ms_debruijn B - 108 <= z < ms_debruijn B + Z.max 32 (ms_debruijn_len B) \/ ms_size_classes B <= z < ms_size_classes B + 96 \/
ms_small_cnt B <= z < ms_small_cnt B + 27 \/ ms_med_cnt B <= z < ms_med_cnt B + 4) \/
~ (ms_debruijn B - 108 <= z < ms_debruijn B + Z.max 32 (ms_debruijn_len B) \/ ms_size_classes B <= z < ms_size_classes B + 96 \/
ms_small_cnt B <= z < ms_small_cnt B + 27 \/ ms_med_cnt B <= z < ms_med_cnt B + 4)) by lia.
destruct Ht as [Ht|Ht].
{ exact (ax_tables AX L' A' mem' md' z HMR' Ht). }
assert (Hg : ms_got_guard B <= z < ms_got_guard B + 8 \/ ~ (ms_got_guard B <= z < ms_got_guard B + 8)) by lia.
destruct Hg as [Hg|Hg].
{ destruct (ax_statics AX L A mem md HMR) as (G1 & _). destruct (ax_statics AX L' A' mem' md' HMR') as (G2 & _).
assert (Hb : mbyte (ms_segs B) mem' z = mbyte (ms_segs B) mem z).
{ replace z with (ms_got_guard B + Z.of_nat (Z.to_nat (z - ms_got_guard B))) by lia.
rewrite (G1 (Z.to_nat (z - ms_got_guard B))), (G2 (Z.to_nat (z - ms_got_guard B))) by lia. reflexivity. }
exact (eq_trans Hb Hm). }
assert (NO : forall L0 A0 mem0 md0, MR L0 A0 mem0 md0 -> ~ owned B L0 A0 z).
{ intros L0 A0 mem0 md0 H0 [Ho|Ho].
- pose proof (ax_img AX L0 A0 mem0 md0 z H0 Himg Ho). lia.
- unfold static_owned in Ho. lia. }
assert (NS : ~ scratch_k B stk regs z) by (unfold scratch_k; lia).
assert (NE : ~ E z).
{ intros He. destruct (HE z He) as (p & n & Hin & Hz').
apply (ax_blocks_img AX L A mem md p n (z - ptr_addr L p) HMR Hin ltac:(lia)).
replace (ptr_addr L p + (z - ptr_addr L p)) with z by lia. exact Himg. }
destruct (HF z (or_intror Himg) (NO L A mem md HMR) (NO L' A' mem' md' HMR') NS NE) as [Hb _].
exact (eq_trans Hb Hm).
Qed.
Lemma guard_kept_post : forall (B : malloc_syms) (MR : MR_t) L A mem md L' A' mem' md',
AllocExtra B MR -> MR L A mem md -> MR L' A' mem' md' -> guard_kept B mem mem'.
Proof using.
intros B MR L A mem md L' A' mem' md' AX H1 H2 i Hi.
destruct (ax_statics AX L A mem md H1) as (G1 & _). destruct (ax_statics AX L' A' mem' md' H2) as (G2 & _).
replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (G1 (Z.to_nat i)), (G2 (Z.to_nat i)) by lia. reflexivity.
Qed.
Lemma block_slack_region : forall A p n, WF A -> In (p, n) (user_blocks A) ->
exists rg, region_of A (prid p) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
poff p mod 16 = 0 /\ 0 <= poff p /\ 0 <= n /\ 8 * ((poff p + n + 7) / 8) <= rg_len rg.
Proof using.
intros A p n HW Hin.
destruct (user_blocks_frame A p n HW Hin) as (g & am & idx & fr & Hu & Hidx & Hfr & Hk & Hn & ->).
destruct (used_group_region [] None U0 A g am HW Hu) as (rg & Hrg & Hkind & Hlive & Ho & Hext & _).
pose proof (inv_groups HW g am Hu) as G.
pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof G as ((Glast & _) & _ & Gsl & _).
pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
pose proof (stride_mod16 _ _ _ _ _ _ HW Hu) as Hs16.
pose proof (used_group_aligned [] None U0 A HW _ g am Hu (Nat.le_refl _)) as Ha16.
exists rg. unfold frame_ptr, slot_start. destruct (am_mem am) as [k o] eqn:Emem.
rewrite ?Emem in Hrg, Ho, Hext, Ha16. cbn [padd prid poff] in *. subst n.
unfold group_extent, UNIT, IB in *.
assert (Hsi : stride_of am * idx <= stride_of am * am_last am) by (apply Z.mul_le_mono_nonneg_l; lia).
assert (M16 : (o + 16 + stride_of am * idx + 16 * fr_off fr) mod 16 = 0).
{ replace (o + 16 + stride_of am * idx + 16 * fr_off fr) with (o + stride_of am * idx + (1 + fr_off fr) * 16) by lia.
rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
rewrite Z.add_mod, Ha16, Z.add_0_l, Z.mod_mod by lia.
rewrite Z.mul_mod, Hs16, Z.mul_0_l, Z.mod_0_l by lia. reflexivity. }
assert (ME : (o + 16 + stride_of am * (idx + 1)) mod 8 = 0).
{ replace (o + 16 + stride_of am * (idx + 1)) with (o + stride_of am * (idx + 1) + 2 * 8) by lia.
rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
assert (Ho8 : o mod 8 = 0).
{ rewrite (Z.div_mod o 16 ltac:(lia)), Ha16, Z.add_0_r.
replace (16 * (o / 16)) with ((2 * (o / 16)) * 8) by lia. apply Z_mod_mult. }
assert (Hs8 : stride_of am mod 8 = 0).
{ rewrite (Z.div_mod (stride_of am) 16 ltac:(lia)), Hs16, Z.add_0_r.
replace (16 * (stride_of am / 16)) with ((2 * (stride_of am / 16)) * 8) by lia. apply Z_mod_mult. }
rewrite Z.add_mod, Ho8, Z.add_0_l, Z.mod_mod by lia.
rewrite Z.mul_mod, Hs8, Z.mul_0_l, Z.mod_0_l by lia. reflexivity. }
split; [exact Hrg|]. split; [exact Hkind|]. split; [exact Hlive|].
split; [match goal with |- ?x mod 16 = 0 =>
replace x with (o + 16 + stride_of am * idx + 16 * fr_off fr) by lia; exact M16 end|].
split; [nia|]. split; [lia|].
match goal with |- 8 * ((?x + _ + 7) / 8) <= _ =>
replace x with (o + 16 + stride_of am * idx + 16 * fr_off fr) by lia end.
assert (VE : o + 16 + stride_of am * idx + 16 * fr_off fr + fr_n fr <= o + 16 + stride_of am * (idx + 1) - 4) by nia.
assert (ER : o + 16 + stride_of am * (idx + 1) <= rg_len rg) by nia.
pose proof (Z.div_mod (o + 16 + stride_of am * (idx + 1)) 8 ltac:(lia)) as DE. rewrite ME, Z.add_0_r in DE.
pose proof (Z.div_mod (o + 16 + stride_of am * idx + 16 * fr_off fr + fr_n fr + 7) 8 ltac:(lia)) as DV.
pose proof (Z.mod_pos_bound (o + 16 + stride_of am * idx + 16 * fr_off fr + fr_n fr + 7) 8 ltac:(lia)) as MV.
lia.
Qed.
Lemma MRx_block_slack : forall B L A mem md p n a, MRx B L A mem md -> In (p, n) (blocks L A) ->
p + n <= a < 8 * ((p + n + 7) / 8) -> present mem a.
Proof using.
intros B L A mem md p n a M Hin Ha. pose proof (MRx_MRc B L A mem md M) as Mc.
apply YI04.blocks_In in Hin as (q & <- & Hq).
destruct (block_slack_region A q n (mc_wf _ _ _ _ _ Mc) Hq) as (rg & Hrg & Hkind & Hlive & Hal & Ho & Hn & Hle).
pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ Mc) _ (map_region_in_footprint A (prid q) rg Hrg Hkind Hlive))
as Hfo.
cbn [foot_ok fst snd] in Hfo. apply Hfo.
pose proof (proj1 (proj2 (mc_layout _ _ _ _ _ Mc)) (prid q) rg Hrg Hlive) as Hb.
unfold ptr_addr in Ha. destruct q as [k o]. cbn [loc_addr prid poff] in *. unfold PGSZ in Hb.
pose proof (Z.div_mod (ly_reg L k) 4096 ltac:(lia)) as DB. rewrite Hb, Z.add_0_r in DB.
pose proof (Z.div_mod (ly_reg L k + o + n + 7) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (ly_reg L k + o + n + 7) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (o + n + 7) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (o + n + 7) 8 ltac:(lia)) as M2.
lia.
Qed.
Lemma MRx_ctx_owned : forall B L A mem md a, MRx B L A mem md -> ms_ctx B <= a < ms_ctx B + CTX_SIZE ->
owned B L A a.
Proof using.
intros B L A mem md a M Ha. pose proof (MRx_MRc B L A mem md M) as Mc. left. split.
- exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd loc_addr].
rewrite (mc_ctx _ _ _ _ _ Mc). lia.
- intros ([q k] & Hq & Hx). cbn [fst snd] in Hx.
apply (MRc_blocks_img B L A mem md q k (a - ptr_addr L q) Mc Hq ltac:(unfold ptr_addr; lia)).
replace (ptr_addr L q + (a - ptr_addr L q)) with a by lia.
exact (so_ctx_img _ (mc_syms _ _ _ _ _ Mc) a Ha).
Qed.
Definition seg_wbyte (segs : list Segment) (a : word) : option byte :=
match find_segment segs (bv_unsigned a) 1 with
| Some seg => if seg_writable seg
then segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))
else None
| None => None
end.
Definition guard_seg_b (B : malloc_syms) : bool :=
forallb (fun i => match seg_wbyte (ms_segs B) (Z_to_bv 64 (ms_got_guard B + i)),
seg_wbyte (ms_segs B) (Z_to_bv 64 (ms_guard B + i)) with
| Some _, Some _ => true
| _, _ => false
end) [0; 1; 2; 3; 4; 5; 6; 7].
Lemma writable_of_seg : forall segs m a b, seg_wbyte segs (Z_to_bv 64 a) = Some b -> writable_at segs m a.
Proof using.
intros segs m a b H. unfold writable_at, wview. destruct (m (Z_to_bv 64 a)); [discriminate|].
change (seg_wbyte segs (Z_to_bv 64 a) <> None). rewrite H. discriminate.
Qed.
Section c.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.
Theorem malloc_contract_ok : AllocExtra B MR -> ro_apart_b B = true -> malloc_contract B API.
Proof using.
intros AX HB L A regs mem md n b Hpre Hro Hn HR HRm.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
assert (Hn0 : 0 <= n) by (destruct HRm as (R0 & _); exact R0).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
eapply SR_mono.
{ exact (malloc_SR_slots B MR (aa_malloc API) L A regs mem md n b Hpre Hn HR HRm). }
intros c' (p & A' & tr & Hp & (L' & regs' & mem' & md' & -> & Hpost & Ha0 & Hnz & (l1 & l2 & E1 & E2) & _) & HRA').
cbn [fst snd] in *.
assert (Hin : In (p, n) (user_blocks A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')).
{ intros q k Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
[left; exact Hq | right; right; exact Hq]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
pose proof (proj1 (call_post_k_alloc B MR L A regs mem md _ L' A' regs' mem' md') Hpost) as Hpk.
unfold malloc_ret. exists L', A', regs', mem', md', (ptr_addr L' p).
split; [reflexivity|].
split; [exact Hpk|].
split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin)|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin) as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin Hi). }
split; [exact (blocks_add L L' A A' p n l1 l2 Hstab E1 E2)|].
split; [apply (kept_of_post B L A A' mem mem'); [exact Hkeep | intros q k Hq _; exact (Hsub q k Hq)]|].
split; [exact (ro_agree_post B MR ALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a (F : False) => match F with end) Hpk Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [exact (YI04.init_done_of_block A' (p, n) HW' Hin)|].
split; [exact (regions_grow_malloc A n tr (Some p) A' HW Hn0 Hp)|].
exact HRA'.
Qed.
Theorem free_contract_ok : AllocExtra B MR -> ro_apart_b B = true -> free_contract B API.
Proof using.
intros AX HB L A regs mem md p n b Hpre Hro Hin Hp HR.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
eapply SR_mono.
{ exact (free_SR_slots B MR (aa_free API) L A regs mem md p n b Hpre Hin Hp HR). }
intros c' (A' & tr & Hcp & (L' & regs' & mem' & md' & -> & Hpost & (l1 & l2 & E1 & E2)) & HRA').
cbn [fst snd] in *.
assert (Hsub : forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')).
{ intros q k Hq Hne. rewrite E1 in Hq. rewrite E2. apply in_app_iff in Hq as [Hq|[Hq|Hq]]; apply in_app_iff;
[left; exact Hq | injection Hq as -> _; exfalso; exact (Hne eq_refl) | right; exact Hq]. }
pose proof Hpost as (HMR & _ & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
pose proof (proj1 (call_post_k_alloc B MR L A regs mem md _ L' A' regs' mem' md') Hpost) as Hpk.
exists L', A', regs', mem', md'. split; [reflexivity|]. split; [exact Hpost|].
split; [exact (blocks_del L L' A A' p n l1 l2 Hstab E1 E2)|].
split.
{ apply (kept_of_post B L A A' mem mem'); [exact Hkeep|]. intros q k Hq Hg. apply Hsub; [exact Hq|]. intros ->. exact (Hg eq_refl). }
split; [exact (ro_agree_post B MR ALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a Ha => ex_intro _ p (ex_intro _ n (conj Hin Ha))) Hpk Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [intros Hd; exact (free_keeps_init_done (Some p) A tr tt A' Hd (cpath04_yields _ _ _ Hcp))|].
split; [exact (regions_grow_free A p n tr A' HW Hin Hcp)|].
exact HRA'.
Qed.
Theorem free_null_contract_ok : free_null_contract B.
Proof using API B fx rc segs. exact (aa_free_null API). Qed.
Theorem calloc_contract_ok : AllocExtra B MR -> ro_apart_b B = true -> forall pc, calloc_contract B API pc.
Proof using.
intros AX HB pc L A regs mem md m n b Hpre Hro Hm Hn Hrm Hrn Hsm Hpc HR HRm.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
eapply SR_mono.
{ apply (mreal_SR04 segs _ _ _ (aa_calloc API pc L A regs mem md m n Hpc Hpre Hm Hn Hrm Hrn Hsm Hro)).
- apply malloc_safe; [exact HW | nia].
- exact (malloc_slots_ok04 A b (m * n) HW HR HRm). }
intros c' ([r A'] & tr & Hp & HL).
destruct (malloc_slots_step A b (m * n) tr r A' HW HR HRm Hp) as [[q ->] HRA'].
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & Ha0 & Hnz & (l1 & l2 & E1 & E2) & Hz). cbn [fst snd] in *.
assert (Hin : In (q, m * n) (user_blocks A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')).
{ intros p k Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
[left; exact Hq | right; right; exact Hq]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
split.
- unfold malloc_ret. exists L', A', regs', mem', md', (ptr_addr L' q).
split; [reflexivity|]. split; [exact Hpost|]. split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin)|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin) as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin Hi). }
split; [exact (blocks_add L L' A A' q (m * n) l1 l2 Hstab E1 E2)|].
split; [apply (kept_of_post B L A A' mem mem'); [exact Hkeep | intros p k Hq _; exact (Hsub p k Hq)]|].
split; [exact (ro_agree_post B MR CALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a (F : False) => match F with end) Hpost Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [exact (YI04.init_done_of_block A' (q, m * n) HW' Hin)|].
split; [exact (regions_grow_malloc A (m * n) tr (Some q) A' HW ltac:(nia) Hp)|].
exact HRA'.
- exists (mkst regs' (getr regs 1) mem' (seg_rom segs)), md'. split; [reflexivity|].
intros i Hi. cbn [ms_mem ms_regs mkst]. rewrite Ha0.
pose proof alloc_ceiling_lt as AC.
assert (Hq : 4096 <= ptr_addr L' q /\ ptr_addr L' q + m * n <= alloc_ceiling)
by exact (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin).
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
apply Hz. exact Hi.
Qed.
Theorem realloc_null_contract_ok : AllocExtra B MR -> ro_apart_b B = true -> realloc_null_realizes B MR ->
forall pc, ms_realloc B = Some pc -> realloc_null_contract B API pc.
Proof using.
intros AX HB HRz pc Hpc L A regs mem md n b Hpre Hro H10 H11 HR HRm.
destruct (room_slots_n b n HRm) as [Hn _].
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
eapply SR_mono.
{ apply (mreal_SR04 segs _ _ _ (HRz pc L A regs mem md n Hpc Hpre H10 H11 Hn)).
- exact (malloc_safe A n HW ltac:(lia)).
- exact (malloc_slots_ok04 A b n HW HR HRm). }
intros c' ([r A'] & tr & Hp & HL).
destruct (malloc_slots_step A b n tr r A' HW HR HRm Hp) as [[q ->] HRA'].
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & Ha0 & Hnz & (l1 & l2 & E1 & E2)). cbn [fst snd] in *.
assert (Hin : In (q, n) (user_blocks A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')).
{ intros p k Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
[left; exact Hq | right; right; exact Hq]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
unfold malloc_ret. exists L', A', regs', mem', md', (ptr_addr L' q).
split; [reflexivity|]. split; [exact Hpost|]. split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin)|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin) as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin Hi). }
split; [exact (blocks_add L L' A A' q n l1 l2 Hstab E1 E2)|].
split; [apply (kept_of_post B L A A' mem mem'); [exact Hkeep | intros p k Hq _; exact (Hsub p k Hq)]|].
split; [exact (ro_agree_post B MR REALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a (F : False) => match F with end) Hpost Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [exact (YI04.init_done_of_block A' (q, n) HW' Hin)|].
split; [exact (regions_grow_malloc A n tr (Some q) A' HW ltac:(lia) Hp)|].
exact HRA'.
Qed.
Theorem blocks_low_ok : blocks_low B API.
Proof using.
intros L A mem md p n HM Hin. apply YI04.blocks_In in Hin as (q & <- & Hq).
exact (proj1 (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HM Hq)).
Qed.
Theorem blocks_writable_ok : blocks_writable B API.
Proof using.
intros L A mem md p n i HM Hin Hi. apply YI04.blocks_In in Hin as (q & <- & Hq).
apply YL01.present_writable. exact (proj1 (mr_blocks B MR (aa_laws API) L A mem md q n i HM Hq Hi)).
Qed.
Theorem libc_no_locks_ok : AllocExtra B MR -> libc_no_locks B API.
Proof using.
intros AX L A mem md HM. exact (proj2 (proj2 (ax_statics AX L A mem md HM))).
Qed.
Theorem errno_unowned_ok : AllocExtra B MR -> errno_check B = true -> errno_unowned B API.
Proof using.
intros AX HE L A mem md a HM Ha. destruct (errno_check_sound B a HE Ha) as (Himg & Hst & Hctx).
intros [Ho|Ho]; [exact (Hctx (ax_img AX L A mem md a HM Himg Ho)) | exact (Hst Ho)].
Qed.
Theorem ctx_owned_ok : (forall L A mem md, MR L A mem md -> MRx B L A mem md) -> ctx_owned B API.
Proof using.
intros HX L A mem md a HM Ha. exact (MRx_ctx_owned B L A mem md a (HX L A mem md HM) Ha).
Qed.
Theorem block_slack_present_ok : (forall L A mem md, MR L A mem md -> MRx B L A mem md) -> block_slack_present B API.
Proof using.
intros HX L A mem md p n a HM Hin Ha. exact (MRx_block_slack B L A mem md p n a (HX L A mem md HM) Hin Ha).
Qed.
Theorem guard_rw_ok : guard_seg_b B = true -> guard_rw B API.
Proof using.
intros HG L A mem md i HM Hi. unfold guard_seg_b in HG. rewrite forallb_forall in HG.
assert (Hin : In i [0; 1; 2; 3; 4; 5; 6; 7]) by (cbn; lia).
specialize (HG i Hin).
destruct (seg_wbyte (ms_segs B) (Z_to_bv 64 (ms_got_guard B + i))) as [b1|] eqn:E1; [|discriminate].
destruct (seg_wbyte (ms_segs B) (Z_to_bv 64 (ms_guard B + i))) as [b2|] eqn:E2; [|discriminate].
split; [exact (writable_of_seg _ mem _ b1 E1) | exact (writable_of_seg _ mem _ b2 E2)].
Qed.
End c.
End a.
