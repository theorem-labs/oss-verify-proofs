(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the journal of fuzz_reply's ASan program walks.  It is the donor's
   journal (Reusable/YCbq.v:351 ajournal) with two extensions the donor's programs never needed, and the
   run chain of Reusable/YC80.v restated over it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_journal.v, with its module paths and module names changed; 240 of its 350 lines of code are new or changed and 785 lines of the source are left out. *)
(* Theorem Labs, 2026-10: fuzz_preset literal, asan / asan-ubsan program walks: the image-free part (the running-journal spec tliteral_leafX over YCbqG's ajournal_x, and list / frame helpers). *)
(* amem_range8 premise: the strlen wrapper's premise in the engine of record (YGcallMx.v 40d986309feb aj_strlen_at_x), what the caller supplies; the cstr_ok states it as YGcfStr.amem_range8 w (len cw + 1) (kit cc19dfc36d7 PRH_Base.v 7b94fd8b64fe), so the bridge discharges it from the text. *)
(* read-only premise (2026-10-29): PresetRodata.arodata_okP segs rlo rhi B (aview segs (w_H W) memc) (lib/Spec/PresetRodata.v 4eb7e95e7e93, the ONE home of in_roP / arodata_okP at the kit of record decff67d721f; PRH_Base.v 3004a98fe2d9 re-exports it as a Notation), the owned-static-excluding form the fpre gives (at rlo := pa_relro_lo, rhi := pa_relro_hi) and the strlen rules YGcallMxmn.aj_strlen_at_xro / aj_strlen_at_xrom take (YGcallMxmn.v b47cf7942c3d, which Requires PresetRodata and defines neither name). It replaces rom_view segs W memc (every in_rom byte), which the bridges bought with pal_rom_ok, FALSE at TfibB on both images (68059ec877b). literal reads no read-only byte itself; the fact goes only to the strlen call, so no owned-static premise is needed. lit_rod_keep carries it across literal's own stores. *)
(* image-bounds premise (#102): the cursor q lies off the image, as YCbq.off_img_at ilo itop q 16 at the CALLER'S image bounds (Section variables ilo itop; each walk passes its leaf instance's pa_lo / pa_hi). The old-pin text said YCbq.off_img q 16, whose body is image A's YImgTop.IMG_LO / IMG_TOP: right for A, not B' (IMG_TOP_B 0x601000 at this tree's YImgTop.v d2a97d3111ce, IMG_TOP 0x600000); off_img q n = off_img_at IMG_LO IMG_TOP q n is YCbq.off_img_A. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variables rlo rhi : Z.
Variables ilo itop : Z.
Definition LIT_STK : Z := 80 + 2 * ESTACK.
Definition tliteral_leaf_postX (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (Hpc : list Z) (W : world segs)
(memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (q v ty p text : Z) (txt cw : list Z)
: world segs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regs regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LIT_STK <= a < spZ regs) -> ~ (q <= a < q + 8) -> ~ (v <= a < v + 4) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memc a) /\
((PjGrammar.prefixb cw (skipn (Z.to_nat (p - text)) txt) = true /\ getr regs2 10 = w64 0 /\
val_mem segs (mrestrict (w_H W) mem2) q 8 (p + Z.of_nat (length cw)) /\
val_mem segs (mrestrict (w_H W) mem2) v 4 ty) \/
(PjGrammar.prefixb cw (skipn (Z.to_nat (p - text)) txt) = false /\ getr regs2 10 = w64 (-1) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LIT_STK <= a < spZ regs) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memc a))).
Definition tliteral_leafX (VRA a : Z) : Prop :=
forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word)
(q w ty v p text len : Z) (txt cw slack : list Z),
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 q -> getr regs 11 = w64 w -> getr regs 12 = w64 ty -> getr regs 13 = w64 v ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LIT_STK -> spZ regs <= sp0 ->
q mod 8 = 0 -> 4096 <= q -> amem_range q 16 -> off_img_at ilo itop q 16 -> (spZ regs <= q \/ q + 16 <= spZ regs - LIT_STK) ->
(forall x, q <= x < q + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
val_mem segs (mrestrict (w_H W) memc) q 8 p -> val_mem segs (mrestrict (w_H W) memc) (q + 8) 8 (text + len) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF q 16 ->
0 < text -> text <= p <= text + len -> text + len < 2 ^ 62 -> Z.of_nat (length txt) = len ->
garr8 segs (mrestrict (w_H W) memc) text txt ->
amem_range text len -> range_addressable (aview segs (w_H W) memc) SHADOW_OFF text len ->
(0 < len -> shadow_hull_vis (aview segs (w_H W) memc) text len) ->
(spZ regs <= text \/ text + len <= spZ regs - LIT_STK) ->
0 < w -> Z.of_nat (length cw) + 1 < 2 ^ 32 -> w + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= 2 ^ 63 ->
garr8 segs (mrestrict (w_H W) memc) w (cw ++ 0 :: slack) ->
~ In 0 cw -> (- (w + Z.of_nat (length cw) + 1)) mod 8 <= Z.of_nat (length slack) ->
amem_range w (Z.of_nat (length cw) + 1) ->
amem_range8 w (Z.of_nat (length cw) + 1) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF w (Z.of_nat (length cw) + 1) ->
shadow_hull_vis (aview segs (w_H W) memc) w (Z.of_nat (length cw) + 1) ->
(spZ regs <= w \/ w + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= spZ regs - LIT_STK) ->
PresetRodata.arodata_okP segs rlo rhi B (aview segs (w_H W) memc) ->
0 <= ty <= 2 -> v mod 8 = 0 -> 4096 <= v -> amem_range v 4 -> (forall x, v <= x < v + 4 -> ~ in_img segs x) ->
(spZ regs <= v \/ v + 4 <= spZ regs - LIT_STK) ->
(forall x, v <= x < v + 4 ->
  (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x \/ wr_fp_frame FP S lyc x) /\ apresent (w_H W) memc x) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF v VRA ->
(q + 16 <= v \/ v + 4 <= q) ->
SRr segs W (cfg_at segs a regs memc mdc)
(tliteral_leaf_postX STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc k regs q v ty p text txt cw).
End a.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Lemma lit_nth_skipn : forall (l : list Z) k i, nth i (skipn k l) 0 = nth (k + i) l 0.
Proof.
induction l as [|x l IH]; intros k i; destruct k as [|k]; cbn [skipn].
- reflexivity. - destruct i; reflexivity. - reflexivity. - cbn [Nat.add nth]. apply IH.
Qed.
Lemma lit_prefixb_nth : forall (w x : list Z),
PjGrammar.prefixb w x = true <-> ((length w <= length x)%nat /\ forall i, (i < length w)%nat -> nth i x 0 = nth i w 0).
Proof.
induction w as [|a w IH]; intros x; cbn [PjGrammar.prefixb].
- split; intros _; [split; [cbn; lia | intros i Hi; cbn in Hi; lia] | reflexivity].
- destruct x as [|b x].
+ split; [discriminate | intros [Hl _]; cbn in Hl; lia].
+ rewrite andb_true_iff, Z.eqb_eq, IH. cbn [length]. split.
* intros (-> & Hl & Hn). split; [lia|]. intros [|i] Hi; cbn [nth]; [reflexivity | apply Hn; lia].
* intros (Hl & Hn). pose proof (Hn 0%nat ltac:(lia)) as H0. cbn [nth] in H0.
split; [lia|]. split; [lia|]. intros i Hi. exact (Hn (S i) ltac:(lia)).
Qed.
Lemma lit_aview_frame : forall H E rs (m m' : word -> option byte) (X : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, in_wrange E rs a -> X a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview segs H m' a = aview segs H m a.
Proof.
intros H E rs m m' X Hfr HX a Ha Hn. apply (aview_eq_of segs). apply Hfr. rewrite unsigned_lit_small by lia.
intros Hw. exact (Hn (HX a Hw)).
Qed.
Lemma lit_garr8_aview : forall H m a (l : list Z) j,
garr8 segs (mrestrict H m) a l -> (j < length l)%nat -> aview segs H m (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m a l j G Hj. pose proof (proj2 (G j Hj)) as Hr.
unfold aview. cbv beta. rewrite (garr8_mbyte segs _ _ _ j G Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small; lia.
Qed.
Lemma lit_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44.
Proof. intros x Hx. unfold shadow_of_addr, SHADOW_OFF. lia. Qed.
Lemma lit_ra_keep : forall H m m' lo hi x n,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview segs H m' a = aview segs H m a) ->
SHADOW_OFF + 2 ^ 44 <= lo -> 0 <= x -> x + n <= 2 ^ 47 ->
range_addressable (aview segs H m) SHADOW_OFF x n -> range_addressable (aview segs H m') SHADOW_OFF x n.
Proof.
intros H m m' lo hi x n K Hlo Hx Hxn R. apply (range_addressable_agree (aview segs H m)); [|exact R].
intros y Hy. pose proof (lit_shadow_low y ltac:(lia)) as Hs. unfold SHADOW_OFF in *. apply K; lia.
Qed.
Lemma lit_hull_keep : forall H m m' lo hi x n,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview segs H m' a = aview segs H m a) ->
SHADOW_OFF + 2 ^ 44 + 8 <= lo -> 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
shadow_hull_vis (aview segs H m) x n -> shadow_hull_vis (aview segs H m') x n.
Proof.
intros H m m' lo hi x n K Hlo Hx Hn Hxn R s Hs. unfold shadow_addr in Hs. unfold SHADOW_OFF in *.
rewrite K; [apply R; unfold shadow_addr, SHADOW_OFF; exact Hs | lia | lia].
Qed.
Lemma lit_garr8_keep : forall H m m' lo hi a l,
(forall b, 0 <= b < 2 ^ 64 -> ~ (lo <= b < hi) -> aview segs H m' b = aview segs H m b) ->
0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> (a + Z.of_nat (length l) <= lo \/ hi <= a) ->
garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H m') a l.
Proof.
intros H m m' lo hi a l K Ha Hal Hd G. apply (garr8_frame segs _ _ _ _ G).
intros b Hb. apply (mbyte_of_aview segs). apply K; lia.
Qed.
Lemma lit_rod_keep : forall (W : world segs) m m' lo hi rlo rhi B,
(forall b, 0 <= b < 2 ^ 64 -> ~ (lo <= b < hi) -> aview segs (w_H W) m' b = aview segs (w_H W) m b) ->
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) -> (forall a, rlo <= a < rhi -> in_img segs a) -> kLowMemEnd <= lo ->
PresetRodata.arodata_okP segs rlo rhi B (aview segs (w_H W) m) -> PresetRodata.arodata_okP segs rlo rhi B (aview segs (w_H W) m').
Proof.
intros W m m' lo hi rlo rhi B K Hlow Hrel Hlo R a Ha Hn He.
assert (Hi : in_img segs a).
{ destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (Hrel a Hr)]. }
pose proof (Hlow a Hi) as Hb. rewrite K; [exact (R a Ha Hn He) | unfold kLowMemEnd in *; lia | lia].
Qed.
Lemma lit_region_val : forall E m rs n lo hi wlo whi cs off (k : N) (e : sv) val,
mem_ok segs E m rs -> In (YP09.mkRegion (Some n) lo hi wlo whi cs) rs -> In (YP09.mkChunk off (CVal k e)) cs ->
sv_denot E e = Z_to_bv 64 val -> 0 <= val < 2 ^ (8 * Z.of_N k) -> Z.of_N k <= 8 ->
val_mem segs m (bv_unsigned (ew E n) + off) (N.to_nat k) val.
Proof.
intros E m rs n lo hi wlo whi cs off k e val HM Hin Hc He Hv Hk.
pose proof (mem_ok_region segs E m rs _ HM Hin) as HR. unfold region_ok in HR. cbv zeta in HR.
destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [base_val YP09.r_base] in Hck.
exact (val_of_chunk_ok segs E m _ off k e val Hck He Hv Hk).
Qed.
Lemma lit_aview_of_val : forall H m m' a n v,
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v ->
forall x, a <= x < a + Z.of_nat n -> aview segs H m' x = aview segs H m x.
Proof.
intros H m m' a n v V V' x Hx. unfold aview. cbv beta. replace x with (a + (x - a)) by lia.
rewrite (val_mem_agree segs _ _ a n v V V' (x - a)) by lia. reflexivity.
Qed.
Lemma lit_region_kept : forall H E (m m' : word -> option byte) r,
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> aview segs H m' a = aview segs H m a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> apresent H m' a) ->
region_kept segs E (mrestrict H m) (mrestrict H m') r.
Proof.
intros H E m m' r K P. split; intros a Ha; [apply (mbyte_of_aview segs); apply K; exact Ha | intros _; apply (apresent_writable segs); apply P; exact Ha].
Qed.
Lemma lit_garr8_vis : forall H m a l x, garr8 segs (mrestrict H m) a l -> a <= x < a + Z.of_nat (length l) -> aview segs H m x <> None.
Proof.
intros H m a l x G Hx. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (lit_garr8_aview H m a l _ G) by lia. discriminate.
Qed.
Lemma lit_first_byte : forall W m w (cw slack : list Z),
garr8 segs (mrestrict (w_H W) m) w (cw ++ 0 :: slack) -> ~ In 0 cw ->
first_byte segs W m w (Z.of_nat (length cw) + 1) 0 (Z.of_nat (length cw)).
Proof.
intros W m w cw slack G Hnz. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) cw 0). split.
+ replace (w + i) with (w + Z.of_nat (Z.to_nat i)) by lia. rewrite (lit_garr8_aview _ m w _ _ G) by (rewrite length_app; cbn; lia).
rewrite app_nth1 by lia. reflexivity.
+ intros E0. apply Hnz. rewrite <- E0. apply nth_In. lia.
- intros _. replace (w + Z.of_nat (length cw)) with (w + Z.of_nat (length cw + 0)) by lia.
rewrite (lit_garr8_aview _ m w _ _ G) by (rewrite length_app; cbn; lia).
rewrite app_nth2 by lia. replace (length cw + 0 - length cw)%nat with 0%nat by lia. reflexivity.
Qed.
Lemma lit_overread : forall H m w (cw slack : list Z),
garr8 segs (mrestrict H m) w (cw ++ 0 :: slack) -> (- (w + Z.of_nat (length cw) + 1)) mod 8 <= Z.of_nat (length slack) ->
forall a, w + Z.of_nat (length cw) < a < w + Z.of_nat (length cw) - (w + Z.of_nat (length cw)) mod 8 + 8 -> aview segs H m a <> None.
Proof.
intros H m w cw slack G Hsl a Ha. apply (lit_garr8_vis H m w _ a G). rewrite length_app. cbn [length].
pose proof (Z.mod_pos_bound (w + Z.of_nat (length cw)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (- (w + Z.of_nat (length cw) + 1)) 8 ltac:(lia)).
pose proof (Z.div_mod (w + Z.of_nat (length cw)) 8 ltac:(lia)).
pose proof (Z.div_mod (- (w + Z.of_nat (length cw) + 1)) 8 ltac:(lia)).
lia.
Qed.
Lemma lit_cmp_prefix : forall H m text (txt : list Z) w (cw slack : list Z) p,
garr8 segs (mrestrict H m) text txt -> garr8 segs (mrestrict H m) w (cw ++ 0 :: slack) ->
text <= p -> p + Z.of_nat (length cw) <= text + Z.of_nat (length txt) ->
((forall i, 0 <= i < Z.of_nat (length cw) -> aview segs H m (p + i) = aview segs H m (w + i)) <->
PjGrammar.prefixb cw (skipn (Z.to_nat (p - text)) txt) = true).
Proof.
intros H m text txt w cw slack p Gt Gw Hp Hl.
rewrite lit_prefixb_nth. rewrite length_skipn.
assert (AT : forall i, (i < length cw)%nat -> aview segs H m (p + Z.of_nat i) = Some (nth (Z.to_nat (p - text) + i) txt 0)).
{ intros i Hi. replace (p + Z.of_nat i) with (text + Z.of_nat (Z.to_nat (p - text) + i)) by lia.
apply lit_garr8_aview; [exact Gt | lia]. }
assert (AW : forall i, (i < length cw)%nat -> aview segs H m (w + Z.of_nat i) = Some (nth i cw 0)).
{ intros i Hi. rewrite (lit_garr8_aview H m w _ i Gw) by (rewrite length_app; cbn [length]; lia). rewrite app_nth1 by lia. reflexivity. }
split.
- intros Hc. split; [lia|]. intros i Hi. rewrite lit_nth_skipn.
specialize (Hc (Z.of_nat i) ltac:(lia)). rewrite AT, AW in Hc by lia. injection Hc as Hc. exact Hc.
- intros [_ Hc] i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite AT, AW by lia.
f_equal. rewrite <- lit_nth_skipn. apply Hc. lia.
Qed.
Lemma lit_in_img_rng : forall lo n,
existsb (fun sg => (Z.of_N (seg_base sg) <=? lo) && (lo + n <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs = true ->
forall x, lo <= x < lo + n -> in_img segs x.
Proof.
intros lo n Hb x Hx. apply existsb_exists in Hb as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.
End h.
Lemma lit_apart : forall (P : Z -> Prop) a n b m,
(forall x, a <= x < a + n -> ~ P x) -> (forall x, b <= x < b + m -> P x) -> 0 < n -> 0 < m ->
a + n <= b \/ b + m <= a.
Proof.
intros P a n b m Hn Hp Hn0 Hm0. destruct (Z_le_gt_dec (a + n) b) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (b + m) a) as [H'|H']; [right; exact H'|]. exfalso.
apply (Hn (Z.max a b)); [lia | apply Hp; lia].
Qed.
Lemma lit_U_sub : forall E (i j : nat) a b, ew E i = Z_to_bv 64 a -> ew E j = Z_to_bv 64 b -> 0 <= a <= b -> b < 2 ^ 64 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff i 0) (SLit (-1))) (SOff j 0)) = b - a.
Proof.
intros E i j a b Ha Hb Hab Hb64. rewrite U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw].
rewrite (U_atom E i a Ha), (U_atom E j b Hb) by lia. unfold zcanon, M64. Z.div_mod_to_equations. lia.
Qed.
Lemma lit_hull_sub : forall rd x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> 0 <= x' ->
shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 Hn Hx s Hs. apply H. unfold shadow_addr in *.
assert (M : forall u v, u <= v -> (SHADOW_OFF + u / 8) / 8 * 8 <= (SHADOW_OFF + v / 8) / 8 * 8).
{ intros u v Huv. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. pose proof (Z.div_le_mono u v 8 ltac:(lia) Huv). lia. }
pose proof (M x x' H1). pose proof (M (x' + n' - 1) (x + n - 1) ltac:(lia)). lia.
Qed.
Lemma lit_prefixb_short : forall (w x : list Z), (length x < length w)%nat -> PjGrammar.prefixb w x = false.
Proof.
intros w x Hl. destruct (PjGrammar.prefixb w x) eqn:E; [|reflexivity].
apply lit_prefixb_nth in E. lia.
Qed.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x.
Section fr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable psym : Type.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Variable listing : ptable psym.
Variable tpi0 : ptree psym.
Variable tw0 : ctable.
Hypothesis Hfetch : forall pc w, fetch pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Hypothesis Hcert : pi_check psym fetch val sigma listing = true.
Hypothesis HB : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Variable A_LIM : nat.
Hypothesis HLIM0 : (A_TEXT < A_LIM)%nat.
Hypothesis HLIM : forallb (pinstr_atoms_ltb A_LIM) listing = true.
Hypothesis HLEN : 4 * Z.of_nat (length listing) <= 2 ^ 40.
Hypothesis Htpi : ptree_of_list listing = tpi0.
Hypothesis Htw : tw_of 0 listing = tw0.
Lemma SRr_chain_pi_tok_AJx_fr : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env val A_LIM (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi segs val (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_pi_tok_AJx (SK := SK) psym segs B PST ARx val sigma A_LIM W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec_fr (SK := SK) segs B PST ARx LAWS segs_low) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
  + rewrite Hmm. exact Hfr.
  + rewrite Hmm. exact Hgr.
  + intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
  + rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_run_pi_tok_AJx_fr : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env val A_LIM E ->
st_ok_pi segs val E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_pi_tok_AJx (SK := SK) psym segs B PST ARx val sigma A_LIM W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJx_fr; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
End fr.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x pa_segs B ARx HL.
Definition paj_run_x_fr := SRr_run_pi_tok_AJx_fr (SK := SK) asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
End g.
