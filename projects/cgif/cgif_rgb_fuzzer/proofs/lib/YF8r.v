(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03 YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Lemma Hwx_tfa {imgk : img} : wx_segs_nowrap tfxsegs.
Proof. img_apply wx_segs_nowrap_of_b. img_case; vm_compute. all: img_refl. Qed.
Definition TFX_IMG_END {imgk : img} : Z := (0x5ff000 + D_1000).
Lemma seg_rom_none_high {imgk : img} : forall a, TFX_IMG_END <= a < 2 ^ 64 -> seg_rom tfxsegs (Z_to_bv 64 a) = None.
Proof. destruct imgk; [ pose (imgk_ := K_tra) | pose (imgk_ := K_trb) ]; img_expose.
{
intros a Ha. unfold TFX_IMG_END in Ha. unfold seg_rom, memory_read, YB0z.trasegs, Asan.M.loaded_segments.
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add].
rewrite !unsigned_lit_small by lia.
repeat match goal with
| |- context [ (?x <=? a) && (a + 1 <=? ?y) ] =>
replace ((x <=? a) && (a + 1 <=? y)) with false
by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec x a); [right; apply Z.leb_gt; lia | left; reflexivity])
end. reflexivity.
}
{
intros a Ha. unfold TFX_IMG_END in Ha. unfold seg_rom, memory_read, YB1u.trbsegs, AsanUbsan.M.loaded_segments.
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add].
rewrite !unsigned_lit_small by lia.
repeat match goal with
| |- context [ (?x <=? a) && (a + 1 <=? ?y) ] =>
replace ((x <=? a) && (a + 1 <=? y)) with false
by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec x a); [right; apply Z.leb_gt; lia | left; reflexivity])
end. reflexivity.
}
Qed.
Definition TFX_IMG_LO : Z := 0x10000.
Definition off_img {imgk : img} (a : Z) : Prop := (0 <= a < TFX_IMG_LO) \/ (TFX_IMG_END <= a < 2 ^ 64).
Lemma off_img_high {imgk : img} : forall a, TFX_IMG_END <= a < 2 ^ 64 -> off_img a.
Proof. intros a Ha. right. img_exact Ha. Qed.
Lemma seg_rom_none_off {imgk : img} : forall a, off_img a -> seg_rom tfxsegs (Z_to_bv 64 a) = None.
Proof. destruct imgk; [ pose (imgk_ := K_tra) | pose (imgk_ := K_trb) ]; img_expose.
{
intros a [Ha|Ha]; [|exact (seg_rom_none_high a Ha)].
unfold TFX_IMG_LO in Ha. unfold seg_rom, memory_read, YB0z.trasegs, Asan.M.loaded_segments.
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add].
rewrite !unsigned_lit_small by lia.
repeat match goal with
| |- context [ (?x <=? a) && (a + 1 <=? ?y) ] =>
replace ((x <=? a) && (a + 1 <=? y)) with false
by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec x a); [right; apply Z.leb_gt; lia | left; reflexivity])
end. reflexivity.
}
{
intros a [Ha|Ha]; [|exact (seg_rom_none_high a Ha)].
unfold TFX_IMG_LO in Ha. unfold seg_rom, memory_read, YB1u.trbsegs, AsanUbsan.M.loaded_segments.
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add].
rewrite !unsigned_lit_small by lia.
repeat match goal with
| |- context [ (?x <=? a) && (a + 1 <=? ?y) ] =>
replace ((x <=? a) && (a + 1 <=? y)) with false
by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec x a); [right; apply Z.leb_gt; lia | left; reflexivity])
end. reflexivity.
}
Qed.
Section g. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition img_cover {imgk : img} (ly : alayout) : Prop := fst (ly_img ly) <= TFX_IMG_LO /\ TFX_IMG_END <= fst (ly_img ly) + snd (ly_img ly).
Lemma img_cover_of_ledger {imgk : img} : forall ly S md, ALedger tfxsegs ly S md -> img_cover ly.
Proof. destruct imgk; [ pose (imgk_ := K_tra) | pose (imgk_ := K_trb) ]; img_expose.
{
intros ly S md L. split.
- destruct (al_img _ _ _ _ L Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _].
cbn in H. unfold TFX_IMG_LO. lia.
- destruct (al_img _ _ _ _ L Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
cbn in H. unfold TFX_IMG_END. lia.
}
{
intros ly S md L. split.
- destruct (al_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _].
cbn in H. unfold TFX_IMG_LO. lia.
- destruct (al_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
cbn in H. unfold TFX_IMG_END. lia.
}
Qed.
Definition zone3cases {imgk : img} (x sz : Z) : Prop :=
x + sz <= TFX_IMG_LO \/ (TFX_IMG_END <= x /\ x + sz <= kLowShadowBeg) \/ (kHighMemBeg <= x /\ x + sz <= ASAN_CEIL).
Definition zone3 {imgk : img} (x sz : Z) : Prop := 4096 <= x /\ x + sz <= ASAN_CEIL /\ zone3cases x sz.
Lemma zone3_intro {imgk : img} : forall ly x sz, img_cover ly -> 0 <= sz ->
in_app x sz -> zdisjoint (x, sz) (ly_img ly) -> zone3 x sz.
Proof.
intros ly x sz [C1 C2] Hsz [A1 A2] D. unfold zdisjoint in D. cbn [fst snd] in D.
pose proof ASAN_CEIL_range as [CR _].
unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in *. img_lia.
Qed.
Lemma zone3_off_img {imgk : img} : forall x sz a, zone3 x sz -> x <= a < x + sz -> off_img a.
Proof.
intros x sz a (Z0 & Z1 & Z2) Ha. pose proof ASAN_CEIL_range as [CR _].
unfold off_img, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in *. img_lia.
Qed.
Lemma zone3_apart_img {imgk : img} : forall x sz a, zone3 x sz -> TFX_IMG_LO <= a < TFX_IMG_END -> ~ (x <= a < x + sz).
Proof.
intros x sz a (Z0 & Z1 & Z2) Ha. pose proof ASAN_CEIL_range as [CR _].
unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in *. img_lia.
Qed.
Lemma zone3_apart_hsh {imgk : img} : forall x sz a, zone3 x sz -> kLowShadowBeg <= a < kHighMemBeg -> ~ (x <= a < x + sz).
Proof.
intros x sz a (Z0 & Z1 & Z2) Ha. pose proof ASAN_CEIL_range as [CR _].
unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in *. img_lia.
Qed.
Lemma le_byte_eq : forall z w k, YG0h.le_byte z w k = YP0g.le_byte z w k.
Proof. img_refl. Qed.
Lemma aview_some {imgk : img} : forall H mem a v,
aview tfxsegs H mem a = Some v <-> exists b, mbyte tfxsegs (mrestrict H mem) a = Some b /\ bv_unsigned b = v.
Proof.
intros H mem a v. unfold aview. destruct (mbyte tfxsegs (mrestrict H mem) a) as [b|]; cbn.
- split; [img_try (intros E; injection E as <-; exists b; auto) | img_try (intros (b' & E & <-); congruence)].
- split; [img_try (discriminate) | img_try (intros (b & E & _); discriminate)].
Qed.
Lemma aview_byte {imgk : img} : forall H mem a v,
aview tfxsegs H mem a = Some v -> mbyte tfxsegs (mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof.
intros H mem a v Hv. apply aview_some in Hv as (b & E & <-). rewrite Z_to_bv_bv_unsigned. img_exact E.
Qed.
Lemma aview_vis {imgk : img} : forall H mem a, aview tfxsegs H mem a <> None <-> mbyte tfxsegs (mrestrict H mem) a <> None.
Proof.
intros H mem a. unfold aview. destruct (mbyte tfxsegs (mrestrict H mem) a); cbn; split; congruence.
Qed.
Lemma cell_holds_val_mem {imgk : img} : forall B ly H mem e (w : nat) e',
cell_holds B ly (aview tfxsegs H mem) (ACell e w (AV e')) ->
val_mem tfxsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros B ly H mem e w e' Hc k Hk. cbn [cell_holds c_at c_val c_w] in Hc.
rewrite <- le_byte_eq. img_apply aview_byte. img_exact (Hc k Hk).
Qed.

Lemma Forall_nth_error {X} : forall (P : X -> Prop) l k x, Forall P l -> nth_error l k = Some x -> P x.
Proof.
intros P l k x H E. img_apply (proj1 (Forall_forall P l) H x). eapply nth_error_In. img_exact E.
Qed.
Lemma range_vis_mbyte {imgk : img} : forall B ly H mem e len i,
range_vis B ly (aview tfxsegs H mem) (e, len) -> 0 <= i < len ->
exists b, mbyte tfxsegs (mrestrict H mem) (aeval B ly e + i) = Some b.
Proof.
intros B ly H mem e len i Hv Hi. specialize (Hv i Hi). cbn [fst snd] in Hv.
destruct (mbyte tfxsegs (mrestrict H mem) (aeval B ly e + i)) as [b|] eqn:E; [img_try (exists b; img_refl)|].
exfalso. img_apply Hv. unfold aview. rewrite E. img_refl.
Qed.
Lemma mbyte_high_writable {imgk : img} : forall (m : word -> option byte) a b,
TFX_IMG_END <= a < 2 ^ 64 -> mbyte tfxsegs m a = Some b -> writable_at tfxsegs m a.
Proof.
intros m a b Ha Hb. unfold writable_at, wview. unfold mbyte in Hb.
destruct (m (Z_to_bv 64 a)) as [b'|] eqn:E; [img_try (discriminate)|].
rewrite (seg_rom_none_high a Ha) in Hb. discriminate.
Qed.
Lemma apresent_mbyte {imgk : img} : forall (H : word -> bool) mem a,
apresent H mem a -> exists b, mbyte tfxsegs (mrestrict H mem) a = Some b.
Proof.
intros H mem a [Hh [b Hb]]. exists b. unfold mbyte, mrestrict. rewrite Hh, Hb. img_refl.
Qed.
Lemma apresent_writable {imgk : img} : forall (H : word -> bool) mem a,
TFX_IMG_END <= a < 2 ^ 64 -> apresent H mem a -> writable_at tfxsegs (mrestrict H mem) a.
Proof.
intros H mem a Ha Hp. destruct (apresent_mbyte H mem a Hp) as [b Hb]. eapply mbyte_high_writable; eassumption.
Qed.
Lemma mbyte_high_apresent {imgk : img} : forall (H : word -> bool) mem a b,
TFX_IMG_END <= a < 2 ^ 64 -> mbyte tfxsegs (mrestrict H mem) a = Some b -> apresent H mem a.
Proof.
intros H mem a b Ha Hb. unfold mbyte, mrestrict in Hb.
destruct (H (Z_to_bv 64 a)) eqn:Hh.
- rewrite (seg_rom_none_high a Ha) in Hb. discriminate.
- destruct (mem (Z_to_bv 64 a)) as [b'|] eqn:E; [|img_try (rewrite (seg_rom_none_high a Ha) in Hb; discriminate)].
split; [img_try (img_exact Hh) | img_try (exists b'; img_exact E)].
Qed.
Section h. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.



End h.
End g.
Fixpoint aexp_eqb (a b : aexp) : bool :=
match a, b with
| ANum x, ANum y => x =? y
| ASp x, ASp y => x =? y | AQ x, AQ y => x =? y | AT x, AT y => x =? y | AC x, AC y => x =? y
| AF x, AF y => x =? y | ANB x, ANB y => x =? y | ASB x, ASB y => x =? y
| ASec r x, ASec s y => Nat.eqb r s && (x =? y)
| ATop x, ATop y => x =? y | ATsd x, ATsd y => x =? y | AStk x, AStk y => x =? y
| AInst x, AInst y => x =? y | ADepot x, ADepot y => x =? y | AStore x, AStore y => x =? y
| ATp x, ATp y => x =? y | AIal x, AIal y => x =? y | AD x, AD y => x =? y
| ASh a', ASh b' => aexp_eqb a' b'
| _, _ => false
end.
Fixpoint cell_lookup (l : list acell) (e : aexp) : option acell :=
match l with
| [] => None
| c :: t => if aexp_eqb (c_at c) e then Some c else cell_lookup t e
end.
Lemma cell_lookup_In : forall l e c, cell_lookup l e = Some c -> In c l.
Proof.
induction l as [|x t IH]; intros e c H; cbn in H; [img_try (discriminate)|].
destruct (aexp_eqb (c_at x) e); [img_try (injection H as ->; left; img_refl) | img_try (right; img_exact (IH e c H))].
Qed.
Section o. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma tfx_const_lookup {imgk : img} : forall B, TfxSyms B -> forall ly S H mem a (w : nat) v,
ARm B ly S (aview tfxsegs H mem) ->
cell_lookup (Tfx_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
val_mem tfxsegs (mrestrict H mem) a w v.
Proof.
intros B TB ly S H mem a w v M E.
img_apply (cell_holds_val_mem B ly H mem (ANum a) w (ANum v)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfxsegs H mem)) (as_const B ly)) (am_const B ly S _ M)).
rewrite (ts_const B TB ly). img_exact (cell_lookup_In _ _ _ E).
Qed.
Lemma tfx_const_lookup_sym {imgk : img} : forall B, TfxSyms B -> forall ly S H mem e (w : nat) e',
ARm B ly S (aview tfxsegs H mem) ->
cell_lookup (Tfx_const ly) e = Some (ACell e w (AV e')) ->
val_mem tfxsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros B TB ly S H mem e w e' M E.
img_apply (cell_holds_val_mem B ly H mem e w e').
apply (proj1 (Forall_forall (cell_holds B ly (aview tfxsegs H mem)) (as_const B ly)) (am_const B ly S _ M)).
rewrite (ts_const B TB ly). img_exact (cell_lookup_In _ _ _ E).
Qed.
End o.
Lemma mbyte_off_writable {imgk : img} : forall (m : word -> option byte) a b,
off_img a -> mbyte tfxsegs m a = Some b -> writable_at tfxsegs m a.
Proof.
intros m a b Ha Hb. unfold writable_at, wview. unfold mbyte in Hb.
destruct (m (Z_to_bv 64 a)) as [b'|] eqn:E; [img_try (discriminate)|].
rewrite (seg_rom_none_off a Ha) in Hb. discriminate.
Qed.
Lemma apresent_writable_off {imgk : img} : forall (H : word -> bool) mem a,
off_img a -> apresent H mem a -> writable_at tfxsegs (mrestrict H mem) a.
Proof.
intros H mem a Ha Hp. destruct (apresent_mbyte H mem a Hp) as [b Hb]. eapply mbyte_off_writable; eassumption.
Qed.
Lemma mbyte_off_apresent {imgk : img} : forall (H : word -> bool) mem a b,
off_img a -> mbyte tfxsegs (mrestrict H mem) a = Some b -> apresent H mem a.
Proof.
intros H mem a b Ha Hb. unfold mbyte, mrestrict in Hb.
destruct (H (Z_to_bv 64 a)) eqn:Hh.
- rewrite (seg_rom_none_off a Ha) in Hb. discriminate.
- destruct (mem (Z_to_bv 64 a)) as [b'|] eqn:E; [|img_try (rewrite (seg_rom_none_off a Ha) in Hb; discriminate)].
split; [img_try (img_exact Hh) | img_try (exists b'; img_exact E)].
Qed.
Section p. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma tfx_find_segment_none_low {imgk : img} : forall x, x < TFX_IMG_LO -> find_segment tfxsegs x 1 = None.
Proof. destruct imgk; [ pose (imgk_ := K_tra) | pose (imgk_ := K_trb) ]; img_expose.
{
intros x Hx. unfold TFX_IMG_LO in Hx. unfold YB0z.trasegs, Asan.M.loaded_segments. cbn -[Z.leb Z.add Z.of_N].
repeat match goal with
| |- context [ (?b <=? x) && ?c ] =>
replace ((b <=? x) && c) with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; cbn; lia)
end. reflexivity.
}
{
intros x Hx. unfold TFX_IMG_LO in Hx. unfold YB1u.trbsegs, AsanUbsan.M.loaded_segments. cbn -[Z.leb Z.add Z.of_N].
repeat match goal with
| |- context [ (?b <=? x) && ?c ] =>
replace ((b <=? x) && c) with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; cbn; lia)
end. reflexivity.
}
Qed.
Lemma tfx_find_segment_none_high {imgk : img} : forall x, TFX_IMG_END <= x -> find_segment tfxsegs x 1 = None.
Proof.
intros x Hx. img_apply (find_segment1_none_above tfxsegs TFX_IMG_END x); [img_try ((img_case; vm_compute); img_refl) | img_try (img_exact Hx)].
Qed.
Lemma writable_high_apresent {imgk : img} : forall (H : word -> bool) mem a,
TFX_IMG_END <= a < 2 ^ 64 -> writable_at tfxsegs (mrestrict H mem) a -> apresent H mem a.
Proof.
intros H mem a Ha Hw. unfold writable_at, wview, mrestrict in Hw. unfold apresent. unfold TFX_IMG_END in Ha.
rewrite (unsigned_lit_small a) in Hw by img_lia.
rewrite (tfx_find_segment_none_high a ltac:(img_try (unfold TFX_IMG_END; img_lia))) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:Hh; [img_try (exfalso; img_apply Hw; img_refl)|].
split; [img_refl|]. destruct (mem (Z_to_bv 64 a)) as [b|]; [img_try (exists b; img_refl) | img_try (exfalso; img_apply Hw; img_refl)].
Qed.
Lemma st_ok_window_writable {imgk : img} : forall (H : word -> bool) E ss ms i r a,
st_ok tfxsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
writable_at tfxsegs (mrestrict H (ms_mem ms)) a.
Proof.
intros H E ss ms i r a HS Hi Ha.
pose proof (st_ok_mem_ok tfxsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & Hw & _).
replace a with (base_val E (YQ0b.r_base r) + (a - base_val E (YQ0b.r_base r))) by img_lia. img_apply Hw. img_lia.
Qed.
Lemma st_ok_window_apresent {imgk : img} : forall (H : word -> bool) E ss ms i r a,
st_ok tfxsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
TFX_IMG_END <= a < 2 ^ 64 -> apresent H (ms_mem ms) a.
Proof.
intros H E ss ms i r a HS Hi Ha Hhi. img_apply writable_high_apresent; [img_try (img_exact Hhi)|].
eapply st_ok_window_writable; eassumption.
Qed.
Lemma writable_off_apresent {imgk : img} : forall (H : word -> bool) mem a,
off_img a -> writable_at tfxsegs (mrestrict H mem) a -> apresent H mem a.
Proof.
intros H mem a Ha Hw. destruct Ha as [Ha|Ha]; [|img_try (img_exact (writable_high_apresent H mem a Ha Hw))].
unfold writable_at, wview, mrestrict in Hw. unfold apresent. unfold TFX_IMG_LO in Ha.
rewrite (unsigned_lit_small a) in Hw by img_lia.
rewrite (tfx_find_segment_none_low a ltac:(img_try (unfold TFX_IMG_LO; img_lia))) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:Hh; [img_try (exfalso; img_apply Hw; img_refl)|].
split; [img_refl|]. destruct (mem (Z_to_bv 64 a)) as [b|]; [img_try (exists b; img_refl) | img_try (exfalso; img_apply Hw; img_refl)].
Qed.
Lemma st_ok_window_apresent_off {imgk : img} : forall (H : word -> bool) E ss ms i r a,
st_ok tfxsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
off_img a -> apresent H (ms_mem ms) a.
Proof.
intros H E ss ms i r a HS Hi Ha Hhi. img_apply writable_off_apresent; [img_try (img_exact Hhi)|].
eapply st_ok_window_writable; eassumption.
Qed.
Lemma st_ok_chunk_val {imgk : img} : forall (H : word -> bool) E ss ms i r j off (n : N) e v,
st_ok tfxsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YQ0b.r_chunks r) j = Some (YQ0b.mkChunk off (CVal n e)) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfxsegs (mrestrict H (ms_mem ms)) (base_val E (YQ0b.r_base r) + off) (N.to_nat n) v.
Proof.
intros H E ss ms i r j off n e v HS Hi Hj He Hv Hn.
pose proof (st_ok_mem_ok tfxsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
img_apply (val_of_chunk_ok tfxsegs E _ _ off n e v); [|img_try (img_exact He) | img_try (img_exact Hv) | img_try (img_exact Hn)].
img_exact (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)).
Qed.
Lemma st_ok_chunk_zero {imgk : img} : forall (H : word -> bool) E ss ms i r j off len a,
st_ok tfxsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YQ0b.r_chunks r) j = Some (YQ0b.mkChunk off (CZero len)) ->
base_val E (YQ0b.r_base r) + off <= a < base_val E (YQ0b.r_base r) + off + len ->
mbyte tfxsegs (mrestrict H (ms_mem ms)) a = Some (Z_to_bv 8 0).
Proof.
intros H E ss ms i r j off len a HS Hi Hj Ha.
pose proof (st_ok_mem_ok tfxsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)) as Hc.
destruct (Hc (a - (base_val E (YQ0b.r_base r) + off)) ltac:(img_try (cbn [YQ0b.c_len YQ0b.c_off YQ0b.c_val cv_len]; img_lia)))
as (b & Hb1 & Hb2).
cbn [cbyte YQ0b.c_off YQ0b.c_val] in Hb1. injection Hb1 as <-.
replace a with (base_val E (YQ0b.r_base r) + off + (a - (base_val E (YQ0b.r_base r) + off))) by img_lia. img_exact Hb2.
Qed.
Lemma st_ok_reg_denot {imgk : img} : forall (H : word -> bool) E ss ms (r : bv 5),
st_ok tfxsegs E ss (restrict H ms) -> getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros H E ss ms r HS. img_exact (st_ok_restrict_reg tfxsegs H E ss ms r HS). Qed.
Lemma frame_of_outside : forall E rs (m m' : word -> option byte) (x : word),
frame_of E rs m m' -> (forall r, In r rs -> YQ0b.r_whi r <= YQ0b.r_wlo r \/
~ (base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= bv_unsigned x < base_val E (YQ0b.r_base r) + YQ0b.r_whi r)) ->
m' x = m x.
Proof.
intros E rs m m' x HF Hout. img_apply HF. intros (r & Hin & Hr). destruct (Hout r Hin) as [He|Hn]; [img_lia | img_try (img_exact (Hn Hr))].
Qed.
End p.
Section q. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma st_ok_pin_reg {imgk : img} : forall E ss ms (r : bv 5) e,
st_ok tfxsegs E ss ms -> r <> 0%bv -> sv_denot E e = getr (ms_regs ms) r ->
st_ok tfxsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He.
img_apply (st_ok_regs tfxsegs E ss ms (sr_set (ss_regs ss) r e)); [img_try (img_exact HS)|].
intros x. destruct (base.decide (x = r)) as [->|Hne].
- rewrite sr_get_set_same; [| img_try (destruct (bv_eqb r 0) eqn:Hb; [apply bv_eqb_eq in Hb; congruence | img_refl])].
rewrite He. img_exact (st_ok_reg tfxsegs E ss ms r HS).
- rewrite sr_get_set_other by img_exact Hne. img_refl.
Qed.
Lemma st_ok_pin_regU {imgk : img} : forall E ss ms (r : bv 5) e,
st_ok tfxsegs E ss ms -> r <> 0%bv -> U E e = U E (sr_get (ss_regs ss) r) ->
st_ok tfxsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr HU. img_apply st_ok_pin_reg; [img_try (img_exact HS) | img_try (img_exact Hr)|].
rewrite (st_ok_reg tfxsegs E ss ms r HS). unfold U in HU. img_apply bv_eq. img_exact HU.
Qed.
Lemma st_ok_add_region {imgk : img} : forall E ss ms r,
st_ok tfxsegs E ss ms -> YQ0b.region_wf r = true -> region_ok tfxsegs E (ms_mem ms) r ->
all_disjoint E r (ss_mem ss) ->
st_ok tfxsegs E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (W & O & D) & H9) Hwf Hr Hd.
unfold st_ok; cbn. repeat (split; [img_try (assumption)|]). split; [|img_try (img_exact H9)].
split; [img_try (cbn; rewrite Hwf; img_exact W)|]. split; [img_try (constructor; assumption)|]. split; assumption.
Qed.
End q.
Fixpoint svpure (t : sv) : bool :=
match t with
| SLit _ | SOff _ _ => true
| SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => svpure a && svpure b
| SExt _ _ a => svpure a
| _ => false
end.
Fixpoint zev (rho : nat -> Z) (t : sv) : Z :=
match t with
| SLit z => zcanon z
| SOff a k => zcanon (rho a + k)
| SAlu op a b => zcanon (zalu_raw 63 64 op (zev rho a) (zev rho b))
| SAluw op a b => bv_wrap 64 (bv_swrap 32 (zalu_raw 31 32 op (zev rho a mod 2 ^ 32) (zev rho b mod 2 ^ 32)))
| SMd op a b => zcanon (zmd_raw 64 op (zev rho a) (zev rho b))
| SMdw op a b => bv_wrap 64 (bv_swrap 32 (zmd_raw 32 op (zev rho a mod 2 ^ 32) (zev rho b mod 2 ^ 32)))
| SExt sg w a => zcanon (if sg then bv_swrap w (zev rho a mod 2 ^ Z.of_N w) else zev rho a mod 2 ^ Z.of_N w)
| _ => 0
end.
Definition rho_of (E : env) : nat -> Z := fun a => bv_unsigned (ew E a).
Section u. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_zev : forall E t, svpure t = true -> U E t = zev (rho_of E) t.
Proof.
intros E t. induction t as [z | a k | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | sg w a IHa
| d i n0 | op a | op a b | op a b c]; cbn [svpure zev]; intros Hp; try discriminate.
- img_apply U_SLit.
- img_apply U_SOff.
- apply andb_prop in Hp as [Ha Hb]. rewrite U_SAlu, (IHa Ha), (IHb Hb). img_refl.
- apply andb_prop in Hp as [Ha Hb]. rewrite U_of_S, S_SAluw, (IHa Ha), (IHb Hb). img_refl.
- apply andb_prop in Hp as [Ha Hb]. rewrite U_SMd, (IHa Ha), (IHb Hb). img_refl.
- apply andb_prop in Hp as [Ha Hb]. rewrite U_of_S, S_SMdw, (IHa Ha), (IHb Hb). img_refl.
- rewrite U_SExt, (IHa Hp). img_refl.
Qed.
Lemma U_eq_by_zev : forall E a b,
svpure a = true -> svpure b = true -> zev (rho_of E) a = zev (rho_of E) b -> U E a = U E b.
Proof. intros E a b Ha Hb Hab. rewrite (U_zev E a Ha), (U_zev E b Hb). img_exact Hab. Qed.
End u.
Section a0. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma mbyte_mrestrict_same {imgk : img} : forall (H : word -> bool) (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> mbyte tfxsegs (mrestrict H mem') a = mbyte tfxsegs (mrestrict H mem) a.
Proof. intros H mem mem' a E. unfold mbyte, mrestrict. rewrite E. img_refl. Qed.
Lemma aview_same {imgk : img} : forall (H : word -> bool) (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview tfxsegs H mem' a = aview tfxsegs H mem a.
Proof. intros H mem mem' a E. unfold aview. rewrite (mbyte_mrestrict_same H mem mem' a E). img_refl. Qed.
Lemma val_mem_ext {imgk : img} : forall (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> mbyte tfxsegs m' (a + Z.of_nat k) = mbyte tfxsegs m (a + Z.of_nat k)) ->
val_mem tfxsegs m a n v -> val_mem tfxsegs m' a n v.
Proof. intros m m' a n v He Hv k Hk. rewrite (He k Hk). img_exact (Hv k Hk). Qed.
Lemma val_mem_frame {imgk : img} : forall (H : word -> bool) (mem mem' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> mem' (Z_to_bv 64 (a + Z.of_nat k)) = mem (Z_to_bv 64 (a + Z.of_nat k))) ->
val_mem tfxsegs (mrestrict H mem) a n v -> val_mem tfxsegs (mrestrict H mem') a n v.
Proof.
intros H mem mem' a n v He Hv. eapply val_mem_ext; [|img_try (img_exact Hv)]. intros k Hk. apply mbyte_mrestrict_same, He, Hk.
Qed.
Lemma apresent_same : forall (H : word -> bool) (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> apresent H mem a -> apresent H mem' a.
Proof. intros H mem mem' a E [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite E. img_exact Hb. Qed.
Lemma le_byte_split_lo : forall lo hi k, 0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 -> (k < 4)%nat ->
YG0h.le_byte (lo + 2 ^ 32 * hi) 8 k = YG0h.le_byte lo 4 k.
Proof.
intros lo hi k Hlo Hhi Hk. unfold YG0h.le_byte. rewrite !Z.shiftr_div_pow2 by img_lia.
rewrite (Z.mod_small (lo + 2 ^ 32 * hi)) by (img_try (img_change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 32 * 2 ^ 32); nia)).
rewrite (Z.mod_small lo) by (img_try (img_change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); img_lia)).
assert (Hk' : Z.of_nat k = 0 \/ Z.of_nat k = 1 \/ Z.of_nat k = 2 \/ Z.of_nat k = 3) by img_lia.
destruct Hk' as [E|[E|[E|E]]]; rewrite E.
- img_change (2 ^ (8 * 0)) with 1. rewrite !Z.div_1_r.
rewrite <- Zplus_mod_idemp_r. replace ((2 ^ 32 * hi) mod 256) with 0; [img_try (rewrite Z.add_0_r; img_refl)|].
symmetry. replace (2 ^ 32 * hi) with ((2 ^ 24 * hi) * 256) by img_lia. img_apply Z_mod_mult.
- img_change (2 ^ (8 * 1)) with 256.
replace (lo + 2 ^ 32 * hi) with (lo + (2 ^ 24 * hi) * 256) by img_lia. rewrite Z_div_plus by img_lia.
rewrite <- Zplus_mod_idemp_r. replace ((2 ^ 24 * hi) mod 256) with 0; [img_try (rewrite Z.add_0_r; img_refl)|].
symmetry. replace (2 ^ 24 * hi) with ((2 ^ 16 * hi) * 256) by img_lia. img_apply Z_mod_mult.
- img_change (2 ^ (8 * 2)) with 65536.
replace (lo + 2 ^ 32 * hi) with (lo + (2 ^ 16 * hi) * 65536) by img_lia. rewrite Z_div_plus by img_lia.
rewrite <- Zplus_mod_idemp_r. replace ((2 ^ 16 * hi) mod 256) with 0; [img_try (rewrite Z.add_0_r; img_refl)|].
symmetry. replace (2 ^ 16 * hi) with ((2 ^ 8 * hi) * 256) by img_lia. img_apply Z_mod_mult.
- img_change (2 ^ (8 * 3)) with 16777216.
replace (lo + 2 ^ 32 * hi) with (lo + (2 ^ 8 * hi) * 16777216) by img_lia. rewrite Z_div_plus by img_lia.
rewrite <- Zplus_mod_idemp_r. replace ((2 ^ 8 * hi) mod 256) with 0; [img_try (rewrite Z.add_0_r; img_refl)|].
symmetry. replace (2 ^ 8 * hi) with (hi * 256) by img_lia. img_apply Z_mod_mult.
Qed.
Lemma le_byte_split_hi : forall lo hi k, 0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 -> (k < 4)%nat ->
YG0h.le_byte (lo + 2 ^ 32 * hi) 8 (4 + k) = YG0h.le_byte hi 4 k.
Proof.
intros lo hi k Hlo Hhi Hk. unfold YG0h.le_byte. rewrite !Z.shiftr_div_pow2 by img_lia.
rewrite (Z.mod_small (lo + 2 ^ 32 * hi)) by (img_try (img_change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 32 * 2 ^ 32); nia)).
rewrite (Z.mod_small hi) by (img_try (img_change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); img_lia)).
replace (8 * Z.of_nat (4 + k)) with (32 + 8 * Z.of_nat k) by img_lia. rewrite Z.pow_add_r by img_lia.
rewrite <- Z.div_div by img_lia. replace ((lo + 2 ^ 32 * hi) / 2 ^ 32) with hi; [img_refl|].
symmetry. rewrite Z.mul_comm, Z_div_plus by img_lia. rewrite Z.div_small by img_lia. img_lia.
Qed.
Lemma val_mem_4_4 {imgk : img} : forall (m : word -> option byte) a lo hi,
0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 ->
val_mem tfxsegs m a 4 lo -> val_mem tfxsegs m (a + 4) 4 hi -> val_mem tfxsegs m a 8 (lo + 2 ^ 32 * hi).
Proof.
intros m a lo hi Hlo Hhi H1 H2 k Hk.
destruct (Nat.lt_ge_cases k 4) as [Hk4|Hk4].
- rewrite <- le_byte_eq, (le_byte_split_lo lo hi k Hlo Hhi Hk4), le_byte_eq. img_exact (H1 k Hk4).
- replace k with (4 + (k - 4))%nat by img_lia. rewrite <- le_byte_eq, (le_byte_split_hi lo hi (k - 4) Hlo Hhi ltac:(img_lia)), le_byte_eq.
replace (a + Z.of_nat (4 + (k - 4))) with (a + 4 + Z.of_nat (k - 4)) by img_lia. img_exact (H2 (k - 4)%nat ltac:(img_lia)).
Qed.
Lemma le_bytes8_sum : forall z, 0 <= z < 2 ^ 64 ->
let b := fun k => YG0h.le_byte z 8 k in
b 0%nat + 256 * (b 1%nat + 256 * (b 2%nat + 256 * (b 3%nat + 256 * (b 4%nat + 256 * (b 5%nat + 256 * (b 6%nat + 256 * b 7%nat)))))) = z.
Proof.
intros z Hz. cbn beta. unfold YG0h.le_byte. rewrite !Z.shiftr_div_pow2 by img_lia.
rewrite (Z.mod_small z) by (img_try (img_change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); img_lia)).
img_change (2 ^ (8 * Z.of_nat 0)) with 1. img_change (2 ^ (8 * Z.of_nat 1)) with 256. img_change (2 ^ (8 * Z.of_nat 2)) with (256 * 256).
img_change (2 ^ (8 * Z.of_nat 3)) with (256 * 256 * 256). img_change (2 ^ (8 * Z.of_nat 4)) with (256 * 256 * 256 * 256).
img_change (2 ^ (8 * Z.of_nat 5)) with (256 * 256 * 256 * 256 * 256). img_change (2 ^ (8 * Z.of_nat 6)) with (256 * 256 * 256 * 256 * 256 * 256).
img_change (2 ^ (8 * Z.of_nat 7)) with (256 * 256 * 256 * 256 * 256 * 256 * 256).
rewrite Z.div_1_r. rewrite <- !Z.div_div by img_lia.
assert (H7 : z / 256 / 256 / 256 / 256 / 256 / 256 / 256 < 256).
{ img_change (2 ^ 64) with (256 * 256 * 256 * 256 * 256 * 256 * 256 * 256) in Hz.
repeat (img_apply Z.div_lt_upper_bound; [img_lia|]). img_lia. }
rewrite (Z.mod_small (z / 256 / 256 / 256 / 256 / 256 / 256 / 256)) by (img_try (split; [img_try (repeat (img_apply Z.div_pos; [|img_lia]); img_lia) | img_try (img_exact H7)])).
pose proof (Z.div_mod z 256 ltac:(img_lia)) as E0.
pose proof (Z.div_mod (z / 256) 256 ltac:(img_lia)) as E1.
pose proof (Z.div_mod (z / 256 / 256) 256 ltac:(img_lia)) as E2.
pose proof (Z.div_mod (z / 256 / 256 / 256) 256 ltac:(img_lia)) as E3.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256) 256 ltac:(img_lia)) as E4.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256) 256 ltac:(img_lia)) as E5.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256 / 256) 256 ltac:(img_lia)) as E6.
img_lia.
Qed.
Lemma unsigned_lit_small8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. img_change (2 ^ Z.of_N 8) with 256. img_apply Z.mod_small. img_exact Hz. Qed.
Lemma val_mem_rdword {imgk : img} : forall (H : word -> bool) mem a v,
0 <= v < 2 ^ 64 -> val_mem tfxsegs (mrestrict H mem) a 8 v -> rdword (aview tfxsegs H mem) a = Some v.
Proof.
intros H mem a v Hv Hm. unfold rdword, aview.
assert (B : forall k, (k < 8)%nat -> mbyte tfxsegs (mrestrict H mem) (a + Z.of_nat k) = Some (Z_to_bv 8 (YG0h.le_byte v 8 k))).
{ intros k Hk. img_exact (Hm k Hk). }
assert (R : forall k, 0 <= YG0h.le_byte v 8 k < 256) by (img_try (intros k; unfold YG0h.le_byte; img_apply Z.mod_pos_bound; img_lia)).
replace a with (a + Z.of_nat 0) at 1 by img_lia.
replace (a + 1) with (a + Z.of_nat 1) by img_lia. replace (a + 2) with (a + Z.of_nat 2) by img_lia. replace (a + 3) with (a + Z.of_nat 3) by img_lia.
replace (a + 4) with (a + Z.of_nat 4) by img_lia. replace (a + 5) with (a + Z.of_nat 5) by img_lia. replace (a + 6) with (a + Z.of_nat 6) by img_lia.
replace (a + 7) with (a + Z.of_nat 7) by img_lia.
rewrite !B by img_lia. cbn [option_map]. rewrite !unsigned_lit_small8 by img_apply R.
f_equal. img_apply le_bytes8_sum. img_exact Hv.
Qed.
Lemma fpchain_ext : forall (load load' : Z -> option Z) top ch bp,
fpchain load bp top ch -> (forall a v, bp - 16 <= a -> load a = Some v -> load' a = Some v) -> fpchain load' bp top ch.
Proof.
intros load load' top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc Hx; cbn in *;
[img_try (destruct Hc as (r & Hr & Hr4); exists r; split; [img_apply Hx; [img_lia | img_exact Hr] | img_exact Hr4])|].
destruct Hc as (Hfp & Hal & Hra & Hnfp & H4096 & Hrest). (subst fp; cbv beta).
split; [img_refl|]. split; [img_try (img_exact Hal)|]. split; [img_try (img_apply Hx; [img_lia | img_exact Hra])|]. split; [img_try (img_apply Hx; [img_lia | img_exact Hnfp])|].
split; [img_try (img_exact H4096)|]. destruct (bad_next bp top nfp) eqn:Hb; [img_try (img_exact Hrest)|].
img_apply IH; [img_try (img_exact Hrest)|]. intros a v Ha Hv. img_apply Hx; [|img_try (img_exact Hv)].
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb _]. apply Z.leb_gt in Hb. img_lia.
Qed.
Lemma fpchain_ext2 : forall (load load' : Z -> option Z) top ch bp,
fpchain load bp top ch -> bp < top - 16 ->
(forall a v, bp - 16 <= a -> a + 8 <= top - 16 -> load a = Some v -> load' a = Some v) -> fpchain load' bp top ch.
Proof.
intros load load' top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc Hlt Hx; cbn in *;
[img_try (destruct Hc as (r & Hr & Hr4); exists r; split; [img_apply Hx; [img_lia | img_lia | img_exact Hr] | img_exact Hr4])|].
destruct Hc as (Hfp & Hal & Hra & Hnfp & H4096 & Hrest). (subst fp; cbv beta).
split; [img_refl|]. split; [img_try (img_exact Hal)|]. split; [img_try (img_apply Hx; [img_lia | img_lia | img_exact Hra])|]. split; [img_try (img_apply Hx; [img_lia | img_lia | img_exact Hnfp])|].
split; [img_try (img_exact H4096)|]. destruct (bad_next bp top nfp) eqn:Hb; [img_try (img_exact Hrest)|].
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
img_apply IH; [img_try (img_exact Hrest)| img_lia |]. intros a v Ha Ha' Hv. img_apply Hx; [img_lia | img_lia | img_try (img_exact Hv)].
Qed.
Lemma rdword_ext : forall (rd rd' : Z -> option Z) a v,
(forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
intros rd rd' a v He Hv. unfold rdword in *. replace a with (a + 0) in Hv |- * by img_lia. rewrite <- !Z.add_assoc in *. cbn [Z.add] in *.
rewrite !He by img_lia. img_exact Hv.
Qed.
End a0.
Fixpoint sv_only (a : nat) (t : sv) : bool :=
match t with
| SLit _ => true
| SOff b _ => Nat.eqb b a
| SAlu _ x y | SAluw _ x y | SMd _ x y | SMdw _ x y => sv_only a x && sv_only a y
| SExt _ _ x => sv_only a x
| _ => false
end.
Lemma zev_only : forall a rho t, sv_only a t = true -> zev rho t = zev (fun _ => rho a) t.
Proof.
intros a rho t. induction t; cbn [sv_only zev]; intros Hs; try img_refl; try discriminate;
try (apply andb_prop in Hs as [H1 H2]; rewrite (IHt1 H1), (IHt2 H2); img_refl).
- apply Nat.eqb_eq in Hs. (subst; cbv beta). img_refl.
- rewrite (IHt Hs). img_refl.
Qed.
Lemma forallb_seq_In : forall (f : nat -> bool) n i, forallb f (seq 0 n) = true -> (i < n)%nat -> f i = true.
Proof. intros f n i H Hi. img_apply (proj1 (forallb_forall _ _) H). img_apply in_seq. img_lia. Qed.
Section b0. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma st_ok_forget {imgk : img} : forall k E ss (H : word -> bool) ms (clob : list (bv 5)),
st_ok tfxsegs E ss (restrict H ms) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
regions_wf (ss_mem ss) = true -> no_cdata (ss_mem ss) = true -> mem_atoms_lt k (ss_mem ss) = true ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
st_ok tfxsegs (havoc E k (map (getr (ms_regs ms)) clob)) (ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss))
(restrict H (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom tfxsegs))).
Proof.
intros k E ss H ms clob HS Hrv Hat Hwf Hnc Hma Hnd Hnz. rewrite restrict_mkst_fx.
img_apply (st_ok_after_stretch tfxsegs k E ss (restrict H ms) (ms_regs ms) (mrestrict H (ms_mem ms)) (ss_mem ss) (ss_pc ss) clob
HS Hrv Hat Hwf Hnc Hma (submem_refl _) Hnd Hnz).
- intros r _. img_refl.
- img_apply Forall_forall. intros r _. split; intros a _; [img_refl | img_try (intros Hw; img_exact Hw)].
Qed.
End b0.
