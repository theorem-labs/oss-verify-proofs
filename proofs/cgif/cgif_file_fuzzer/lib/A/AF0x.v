(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Lemma Hwx_tfa : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Definition TFIB_IMG_END : Z := 0x5fb000.
Lemma seg_rom_none_high : forall a, TFIB_IMG_END <= a < 2 ^ 64 -> seg_rom tfibsegs (Z_to_bv 64 a) = None.
Proof.
intros a Ha. unfold TFIB_IMG_END in Ha. unfold seg_rom, memory_read, tfibsegs, Asan.M.loaded_segments.
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add].
rewrite !unsigned_lit_small by lia.
repeat match goal with
| |- context [ (?x <=? a) && (a + 1 <=? ?y) ] =>
replace ((x <=? a) && (a + 1 <=? y)) with false
by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec x a); [right; apply Z.leb_gt; lia | left; reflexivity])
end. reflexivity.
Qed.
Definition TFIB_IMG_LO : Z := 0x10000.
Definition off_img (a : Z) : Prop := (0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64).
Lemma off_img_high : forall a, TFIB_IMG_END <= a < 2 ^ 64 -> off_img a.
Proof. intros a Ha. right. exact Ha. Qed.
Lemma seg_rom_none_off : forall a, off_img a -> seg_rom tfibsegs (Z_to_bv 64 a) = None.
Proof.
intros a [Ha|Ha]; [|exact (seg_rom_none_high a Ha)].
unfold TFIB_IMG_LO in Ha. unfold seg_rom, memory_read, tfibsegs, Asan.M.loaded_segments.
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add].
rewrite !unsigned_lit_small by lia.
repeat match goal with
| |- context [ (?x <=? a) && (a + 1 <=? ?y) ] =>
replace ((x <=? a) && (a + 1 <=? y)) with false
by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec x a); [right; apply Z.leb_gt; lia | left; reflexivity])
end. reflexivity.
Qed.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition img_cover (ly : alayout) : Prop := fst (ly_img ly) <= TFIB_IMG_LO /\ TFIB_IMG_END <= fst (ly_img ly) + snd (ly_img ly).
Lemma img_cover_of_ledger : forall ly S md, ALedger tfibsegs ly S md -> img_cover ly.
Proof.
intros ly S md L. split.
- destruct (al_img _ _ _ _ L Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _].
cbn in H. unfold TFIB_IMG_LO. lia.
- destruct (al_img _ _ _ _ L Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
cbn in H. unfold TFIB_IMG_END. lia.
Qed.
Definition zone3cases (x sz : Z) : Prop :=
x + sz <= TFIB_IMG_LO \/ (TFIB_IMG_END <= x /\ x + sz <= kLowShadowBeg) \/ (kHighMemBeg <= x /\ x + sz <= ASAN_CEIL).
Definition zone3 (x sz : Z) : Prop := 4096 <= x /\ x + sz <= ASAN_CEIL /\ zone3cases x sz.
Lemma zone3_intro : forall ly x sz, img_cover ly -> 0 <= sz ->
in_app x sz -> zdisjoint (x, sz) (ly_img ly) -> zone3 x sz.
Proof.
intros ly x sz [C1 C2] Hsz [A1 A2] D. unfold zdisjoint in D. cbn [fst snd] in D.
pose proof ASAN_CEIL_range as [CR _].
unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma zone3_off_img : forall x sz a, zone3 x sz -> x <= a < x + sz -> off_img a.
Proof.
intros x sz a (Z0 & Z1 & Z2) Ha. pose proof ASAN_CEIL_range as [CR _].
unfold off_img, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma zone3_apart_img : forall x sz a, zone3 x sz -> TFIB_IMG_LO <= a < TFIB_IMG_END -> ~ (x <= a < x + sz).
Proof.
intros x sz a (Z0 & Z1 & Z2) Ha. pose proof ASAN_CEIL_range as [CR _].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma zone3_apart_hsh : forall x sz a, zone3 x sz -> kLowShadowBeg <= a < kHighMemBeg -> ~ (x <= a < x + sz).
Proof.
intros x sz a (Z0 & Z1 & Z2) Ha. pose proof ASAN_CEIL_range as [CR _].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma le_byte_eq : forall z w k, YG0f.le_byte z w k = YO0f.le_byte z w k.
Proof. reflexivity. Qed.
Lemma aview_some : forall H mem a v,
aview tfibsegs H mem a = Some v <-> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b /\ bv_unsigned b = v.
Proof.
intros H mem a v. unfold aview. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; cbn.
- split; [intros E; injection E as <-; exists b; auto | intros (b' & E & <-); congruence].
- split; [discriminate | intros (b & E & _); discriminate].
Qed.
Lemma aview_byte : forall H mem a v,
aview tfibsegs H mem a = Some v -> mbyte tfibsegs (mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof.
intros H mem a v Hv. apply aview_some in Hv as (b & E & <-). rewrite Z_to_bv_bv_unsigned. exact E.
Qed.
Lemma aview_vis : forall H mem a, aview tfibsegs H mem a <> None <-> mbyte tfibsegs (mrestrict H mem) a <> None.
Proof.
intros H mem a. unfold aview. destruct (mbyte tfibsegs (mrestrict H mem) a); cbn; split; congruence.
Qed.
Lemma cell_holds_val_mem : forall B ly H mem e (w : nat) e',
cell_holds B ly (aview tfibsegs H mem) (ACell e w (AV e')) ->
val_mem tfibsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros B ly H mem e w e' Hc k Hk. cbn [cell_holds c_at c_val c_w] in Hc.
rewrite <- le_byte_eq. apply aview_byte. exact (Hc k Hk).
Qed.
Lemma cell_holds_mask : forall B ly H mem e m v,
cell_holds B ly (aview tfibsegs H mem) (ACell e 1 (AVmask m v)) ->
exists b, mbyte tfibsegs (mrestrict H mem) (aeval B ly e) = Some b /\ Z.land (bv_unsigned b) m = v.
Proof.
intros B ly H mem e m v Hc. cbn [cell_holds c_at c_val c_w] in Hc. destruct Hc as (b & Hb & Hm).
apply aview_some in Hb as (b8 & E & <-). exists b8. auto.
Qed.
Lemma Forall_nth_error {X} : forall (P : X -> Prop) l k x, Forall P l -> nth_error l k = Some x -> P x.
Proof.
intros P l k x H E. apply (proj1 (Forall_forall P l) H x). eapply nth_error_In. exact E.
Qed.
Lemma range_vis_mbyte : forall B ly H mem e len i,
range_vis B ly (aview tfibsegs H mem) (e, len) -> 0 <= i < len ->
exists b, mbyte tfibsegs (mrestrict H mem) (aeval B ly e + i) = Some b.
Proof.
intros B ly H mem e len i Hv Hi. specialize (Hv i Hi). cbn [fst snd] in Hv.
destruct (mbyte tfibsegs (mrestrict H mem) (aeval B ly e + i)) as [b|] eqn:E; [exists b; reflexivity|].
exfalso. apply Hv. unfold aview. rewrite E. reflexivity.
Qed.
Lemma mbyte_high_writable : forall (m : word -> option byte) a b,
TFIB_IMG_END <= a < 2 ^ 64 -> mbyte tfibsegs m a = Some b -> writable_at tfibsegs m a.
Proof.
intros m a b Ha Hb. unfold writable_at, wview. unfold mbyte in Hb.
destruct (m (Z_to_bv 64 a)) as [b'|] eqn:E; [discriminate|].
rewrite (seg_rom_none_high a Ha) in Hb. discriminate.
Qed.
Lemma apresent_mbyte : forall (H : word -> bool) mem a,
apresent H mem a -> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b.
Proof.
intros H mem a [Hh [b Hb]]. exists b. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity.
Qed.
Lemma apresent_writable : forall (H : word -> bool) mem a,
TFIB_IMG_END <= a < 2 ^ 64 -> apresent H mem a -> writable_at tfibsegs (mrestrict H mem) a.
Proof.
intros H mem a Ha Hp. destruct (apresent_mbyte H mem a Hp) as [b Hb]. eapply mbyte_high_writable; eassumption.
Qed.
Lemma mbyte_high_apresent : forall (H : word -> bool) mem a b,
TFIB_IMG_END <= a < 2 ^ 64 -> mbyte tfibsegs (mrestrict H mem) a = Some b -> apresent H mem a.
Proof.
intros H mem a b Ha Hb. unfold mbyte, mrestrict in Hb.
destruct (H (Z_to_bv 64 a)) eqn:Hh.
- rewrite (seg_rom_none_high a Ha) in Hb. discriminate.
- destruct (mem (Z_to_bv 64 a)) as [b'|] eqn:E; [|rewrite (seg_rom_none_high a Ha) in Hb; discriminate].
split; [exact Hh | exists b'; exact E].
Qed.
Section h.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Lemma tfib_const_cell : forall ly S rd k c,
ARm B ly S rd -> nth_error (Tfib_const ly) k = Some c -> cell_holds B ly rd c.
Proof.
intros ly S rd k c M E. apply (Forall_nth_error (cell_holds B ly rd) (as_const B ly) k c).
- exact (am_const B ly S rd M).
- rewrite (ts_const B TB ly). exact E.
Qed.
Lemma tfib_const_val : forall ly S H mem k a (w : nat) v,
ARm B ly S (aview tfibsegs H mem) -> nth_error (Tfib_const ly) k = Some (ACell (ANum a) w (AV (ANum v))) ->
val_mem tfibsegs (mrestrict H mem) a w v.
Proof.
intros ly S H mem k a w v M E.
exact (cell_holds_val_mem B ly H mem (ANum a) w (ANum v) (tfib_const_cell ly S _ k _ M E)).
Qed.
Lemma tfib_const_val_sym : forall ly S H mem k e (w : nat) e',
ARm B ly S (aview tfibsegs H mem) -> nth_error (Tfib_const ly) k = Some (ACell e w (AV e')) ->
val_mem tfibsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros ly S H mem k e w e' M E.
exact (cell_holds_val_mem B ly H mem e w e' (tfib_const_cell ly S _ k _ M E)).
Qed.
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
induction l as [|x t IH]; intros e c H; cbn in H; [discriminate|].
destruct (aexp_eqb (c_at x) e); [injection H as ->; left; reflexivity | right; exact (IH e c H)].
Qed.
Section o. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tfib_const_lookup : forall B, TfibSyms B -> forall ly S H mem a (w : nat) v,
ARm B ly S (aview tfibsegs H mem) ->
cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
val_mem tfibsegs (mrestrict H mem) a w v.
Proof.
intros B TB ly S H mem a w v M E.
apply (cell_holds_val_mem B ly H mem (ANum a) w (ANum v)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly)) (am_const B ly S _ M)).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma tfib_const_lookup_sym : forall B, TfibSyms B -> forall ly S H mem e (w : nat) e',
ARm B ly S (aview tfibsegs H mem) ->
cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
val_mem tfibsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros B TB ly S H mem e w e' M E.
apply (cell_holds_val_mem B ly H mem e w e').
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly)) (am_const B ly S _ M)).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E).
Qed.
End o.
Lemma mbyte_off_writable : forall (m : word -> option byte) a b,
off_img a -> mbyte tfibsegs m a = Some b -> writable_at tfibsegs m a.
Proof.
intros m a b Ha Hb. unfold writable_at, wview. unfold mbyte in Hb.
destruct (m (Z_to_bv 64 a)) as [b'|] eqn:E; [discriminate|].
rewrite (seg_rom_none_off a Ha) in Hb. discriminate.
Qed.
Lemma apresent_writable_off : forall (H : word -> bool) mem a,
off_img a -> apresent H mem a -> writable_at tfibsegs (mrestrict H mem) a.
Proof.
intros H mem a Ha Hp. destruct (apresent_mbyte H mem a Hp) as [b Hb]. eapply mbyte_off_writable; eassumption.
Qed.
Lemma mbyte_off_apresent : forall (H : word -> bool) mem a b,
off_img a -> mbyte tfibsegs (mrestrict H mem) a = Some b -> apresent H mem a.
Proof.
intros H mem a b Ha Hb. unfold mbyte, mrestrict in Hb.
destruct (H (Z_to_bv 64 a)) eqn:Hh.
- rewrite (seg_rom_none_off a Ha) in Hb. discriminate.
- destruct (mem (Z_to_bv 64 a)) as [b'|] eqn:E; [|rewrite (seg_rom_none_off a Ha) in Hb; discriminate].
split; [exact Hh | exists b'; exact E].
Qed.
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tfib_find_segment_none_low : forall x, x < TFIB_IMG_LO -> find_segment tfibsegs x 1 = None.
Proof.
intros x Hx. unfold TFIB_IMG_LO in Hx. unfold tfibsegs, Asan.M.loaded_segments. cbn -[Z.leb Z.add Z.of_N].
repeat match goal with
| |- context [ (?b <=? x) && ?c ] =>
replace ((b <=? x) && c) with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; cbn; lia)
end. reflexivity.
Qed.
Lemma tfib_find_segment_none_high : forall x, TFIB_IMG_END <= x -> find_segment tfibsegs x 1 = None.
Proof.
intros x Hx. apply (find_segment1_none_above tfibsegs TFIB_IMG_END x); [vm_compute; reflexivity | exact Hx].
Qed.
Lemma writable_high_apresent : forall (H : word -> bool) mem a,
TFIB_IMG_END <= a < 2 ^ 64 -> writable_at tfibsegs (mrestrict H mem) a -> apresent H mem a.
Proof.
intros H mem a Ha Hw. unfold writable_at, wview, mrestrict in Hw. unfold apresent. unfold TFIB_IMG_END in Ha.
rewrite (unsigned_lit_small a) in Hw by lia.
rewrite (tfib_find_segment_none_high a ltac:(unfold TFIB_IMG_END; lia)) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:Hh; [exfalso; apply Hw; reflexivity|].
split; [reflexivity|]. destruct (mem (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply Hw; reflexivity].
Qed.
Lemma st_ok_window_writable : forall (H : word -> bool) E ss ms i r a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
writable_at tfibsegs (mrestrict H (ms_mem ms)) a.
Proof.
intros H E ss ms i r a HS Hi Ha.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & Hw & _).
replace a with (base_val E (YP09.r_base r) + (a - base_val E (YP09.r_base r))) by lia. apply Hw. lia.
Qed.
Lemma st_ok_window_apresent : forall (H : word -> bool) E ss ms i r a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
TFIB_IMG_END <= a < 2 ^ 64 -> apresent H (ms_mem ms) a.
Proof.
intros H E ss ms i r a HS Hi Ha Hhi. apply writable_high_apresent; [exact Hhi|].
eapply st_ok_window_writable; eassumption.
Qed.
Lemma writable_off_apresent : forall (H : word -> bool) mem a,
off_img a -> writable_at tfibsegs (mrestrict H mem) a -> apresent H mem a.
Proof.
intros H mem a Ha Hw. destruct Ha as [Ha|Ha]; [|exact (writable_high_apresent H mem a Ha Hw)].
unfold writable_at, wview, mrestrict in Hw. unfold apresent. unfold TFIB_IMG_LO in Ha.
rewrite (unsigned_lit_small a) in Hw by lia.
rewrite (tfib_find_segment_none_low a ltac:(unfold TFIB_IMG_LO; lia)) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:Hh; [exfalso; apply Hw; reflexivity|].
split; [reflexivity|]. destruct (mem (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply Hw; reflexivity].
Qed.
Lemma st_ok_window_apresent_off : forall (H : word -> bool) E ss ms i r a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
off_img a -> apresent H (ms_mem ms) a.
Proof.
intros H E ss ms i r a HS Hi Ha Hhi. apply writable_off_apresent; [exact Hhi|].
eapply st_ok_window_writable; eassumption.
Qed.
Lemma st_ok_chunk_val : forall (H : word -> bool) E ss ms i r j off (n : N) e v,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros H E ss ms i r j off n e v HS Hi Hj He Hv Hn.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
apply (val_of_chunk_ok tfibsegs E _ _ off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)).
Qed.
Lemma st_ok_chunk_zero : forall (H : word -> bool) E ss ms i r j off len a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CZero len)) ->
base_val E (YP09.r_base r) + off <= a < base_val E (YP09.r_base r) + off + len ->
mbyte tfibsegs (mrestrict H (ms_mem ms)) a = Some (Z_to_bv 8 0).
Proof.
intros H E ss ms i r j off len a HS Hi Hj Ha.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)) as Hc.
destruct (Hc (a - (base_val E (YP09.r_base r) + off)) ltac:(cbn [YP09.c_len YP09.c_off YP09.c_val cv_len]; lia))
as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_off YP09.c_val] in Hb1. injection Hb1 as <-.
replace a with (base_val E (YP09.r_base r) + off + (a - (base_val E (YP09.r_base r) + off))) by lia. exact Hb2.
Qed.
Lemma st_ok_reg_denot : forall (H : word -> bool) E ss ms (r : bv 5),
st_ok tfibsegs E ss (restrict H ms) -> getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros H E ss ms r HS. exact (st_ok_restrict_reg tfibsegs H E ss ms r HS). Qed.
Lemma frame_of_outside : forall E rs (m m' : word -> option byte) (x : word),
frame_of E rs m m' -> (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r \/
~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= bv_unsigned x < base_val E (YP09.r_base r) + YP09.r_whi r)) ->
m' x = m x.
Proof.
intros E rs m m' x HF Hout. apply HF. intros (r & Hin & Hr). destruct (Hout r Hin) as [He|Hn]; [lia | exact (Hn Hr)].
Qed.
End p.
Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_ok_pin_reg : forall E ss ms (r : bv 5) e,
st_ok tfibsegs E ss ms -> r <> 0%bv -> sv_denot E e = getr (ms_regs ms) r ->
st_ok tfibsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He.
apply (st_ok_regs tfibsegs E ss ms (sr_set (ss_regs ss) r e)); [exact HS|].
intros x. destruct (base.decide (x = r)) as [->|Hne].
- rewrite sr_get_set_same; [| destruct (bv_eqb r 0) eqn:Hb; [apply bv_eqb_eq in Hb; congruence | reflexivity]].
rewrite He. exact (st_ok_reg tfibsegs E ss ms r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Lemma st_ok_pin_regU : forall E ss ms (r : bv 5) e,
st_ok tfibsegs E ss ms -> r <> 0%bv -> U E e = U E (sr_get (ss_regs ss) r) ->
st_ok tfibsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr HU. apply st_ok_pin_reg; [exact HS | exact Hr|].
rewrite (st_ok_reg tfibsegs E ss ms r HS). unfold U in HU. apply bv_eq. exact HU.
Qed.
Lemma st_ok_add_region : forall E ss ms r,
st_ok tfibsegs E ss ms -> YP09.region_wf r = true -> region_ok tfibsegs E (ms_mem ms) r ->
all_disjoint E r (ss_mem ss) ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (W & O & D) & H9) Hwf Hr Hd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [cbn; rewrite Hwf; exact W|]. split; [constructor; assumption|]. split; assumption.
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
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma U_zev : forall E t, svpure t = true -> U E t = zev (rho_of E) t.
Proof.
intros E t. induction t as [z | a k | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | sg w a IHa
| d i n0 | op a | op a b | op a b c]; cbn [svpure zev]; intros Hp; try discriminate.
- apply U_SLit.
- apply U_SOff.
- apply andb_prop in Hp as [Ha Hb]. rewrite U_SAlu, (IHa Ha), (IHb Hb). reflexivity.
- apply andb_prop in Hp as [Ha Hb]. rewrite U_of_S, S_SAluw, (IHa Ha), (IHb Hb). reflexivity.
- apply andb_prop in Hp as [Ha Hb]. rewrite U_SMd, (IHa Ha), (IHb Hb). reflexivity.
- apply andb_prop in Hp as [Ha Hb]. rewrite U_of_S, S_SMdw, (IHa Ha), (IHb Hb). reflexivity.
- rewrite U_SExt, (IHa Hp). reflexivity.
Qed.
Lemma U_eq_by_zev : forall E a b,
svpure a = true -> svpure b = true -> zev (rho_of E) a = zev (rho_of E) b -> U E a = U E b.
Proof. intros E a b Ha Hb Hab. rewrite (U_zev E a Ha), (U_zev E b Hb). exact Hab. Qed.
End u.
Section a0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mbyte_mrestrict_same : forall (H : word -> bool) (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> mbyte tfibsegs (mrestrict H mem') a = mbyte tfibsegs (mrestrict H mem) a.
Proof. intros H mem mem' a E. unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma aview_same : forall (H : word -> bool) (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview tfibsegs H mem' a = aview tfibsegs H mem a.
Proof. intros H mem mem' a E. unfold aview. rewrite (mbyte_mrestrict_same H mem mem' a E). reflexivity. Qed.
Lemma val_mem_ext : forall (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> mbyte tfibsegs m' (a + Z.of_nat k) = mbyte tfibsegs m (a + Z.of_nat k)) ->
val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v He Hv k Hk. rewrite (He k Hk). exact (Hv k Hk). Qed.
Lemma val_mem_frame : forall (H : word -> bool) (mem mem' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> mem' (Z_to_bv 64 (a + Z.of_nat k)) = mem (Z_to_bv 64 (a + Z.of_nat k))) ->
val_mem tfibsegs (mrestrict H mem) a n v -> val_mem tfibsegs (mrestrict H mem') a n v.
Proof.
intros H mem mem' a n v He Hv. eapply val_mem_ext; [|exact Hv]. intros k Hk. apply mbyte_mrestrict_same, He, Hk.
Qed.
Lemma apresent_same : forall (H : word -> bool) (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> apresent H mem a -> apresent H mem' a.
Proof. intros H mem mem' a E [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite E. exact Hb. Qed.
Lemma le_byte_split_lo : forall lo hi k, 0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 -> (k < 4)%nat ->
YG0f.le_byte (lo + 2 ^ 32 * hi) 8 k = YG0f.le_byte lo 4 k.
Proof.
intros lo hi k Hlo Hhi Hk. unfold YG0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small (lo + 2 ^ 32 * hi)) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 32 * 2 ^ 32); nia).
rewrite (Z.mod_small lo) by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia).
assert (Hk' : Z.of_nat k = 0 \/ Z.of_nat k = 1 \/ Z.of_nat k = 2 \/ Z.of_nat k = 3) by lia.
destruct Hk' as [E|[E|[E|E]]]; rewrite E.
- change (2 ^ (8 * 0)) with 1. rewrite !Z.div_1_r.
rewrite <- Zplus_mod_idemp_r. replace ((2 ^ 32 * hi) mod 256) with 0; [rewrite Z.add_0_r; reflexivity|].
symmetry. replace (2 ^ 32 * hi) with ((2 ^ 24 * hi) * 256) by lia. apply Z_mod_mult.
- change (2 ^ (8 * 1)) with 256.
replace (lo + 2 ^ 32 * hi) with (lo + (2 ^ 24 * hi) * 256) by lia. rewrite Z_div_plus by lia.
rewrite <- Zplus_mod_idemp_r. replace ((2 ^ 24 * hi) mod 256) with 0; [rewrite Z.add_0_r; reflexivity|].
symmetry. replace (2 ^ 24 * hi) with ((2 ^ 16 * hi) * 256) by lia. apply Z_mod_mult.
- change (2 ^ (8 * 2)) with 65536.
replace (lo + 2 ^ 32 * hi) with (lo + (2 ^ 16 * hi) * 65536) by lia. rewrite Z_div_plus by lia.
rewrite <- Zplus_mod_idemp_r. replace ((2 ^ 16 * hi) mod 256) with 0; [rewrite Z.add_0_r; reflexivity|].
symmetry. replace (2 ^ 16 * hi) with ((2 ^ 8 * hi) * 256) by lia. apply Z_mod_mult.
- change (2 ^ (8 * 3)) with 16777216.
replace (lo + 2 ^ 32 * hi) with (lo + (2 ^ 8 * hi) * 16777216) by lia. rewrite Z_div_plus by lia.
rewrite <- Zplus_mod_idemp_r. replace ((2 ^ 8 * hi) mod 256) with 0; [rewrite Z.add_0_r; reflexivity|].
symmetry. replace (2 ^ 8 * hi) with (hi * 256) by lia. apply Z_mod_mult.
Qed.
Lemma le_byte_split_hi : forall lo hi k, 0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 -> (k < 4)%nat ->
YG0f.le_byte (lo + 2 ^ 32 * hi) 8 (4 + k) = YG0f.le_byte hi 4 k.
Proof.
intros lo hi k Hlo Hhi Hk. unfold YG0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small (lo + 2 ^ 32 * hi)) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 32 * 2 ^ 32); nia).
rewrite (Z.mod_small hi) by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia).
replace (8 * Z.of_nat (4 + k)) with (32 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia.
rewrite <- Z.div_div by lia. replace ((lo + 2 ^ 32 * hi) / 2 ^ 32) with hi; [reflexivity|].
symmetry. rewrite Z.mul_comm, Z_div_plus by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma val_mem_4_4 : forall (m : word -> option byte) a lo hi,
0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 ->
val_mem tfibsegs m a 4 lo -> val_mem tfibsegs m (a + 4) 4 hi -> val_mem tfibsegs m a 8 (lo + 2 ^ 32 * hi).
Proof.
intros m a lo hi Hlo Hhi H1 H2 k Hk.
destruct (Nat.lt_ge_cases k 4) as [Hk4|Hk4].
- rewrite <- le_byte_eq, (le_byte_split_lo lo hi k Hlo Hhi Hk4), le_byte_eq. exact (H1 k Hk4).
- replace k with (4 + (k - 4))%nat by lia. rewrite <- le_byte_eq, (le_byte_split_hi lo hi (k - 4) Hlo Hhi ltac:(lia)), le_byte_eq.
replace (a + Z.of_nat (4 + (k - 4))) with (a + 4 + Z.of_nat (k - 4)) by lia. exact (H2 (k - 4)%nat ltac:(lia)).
Qed.
Lemma le_bytes8_sum : forall z, 0 <= z < 2 ^ 64 ->
let b := fun k => YG0f.le_byte z 8 k in
b 0%nat + 256 * (b 1%nat + 256 * (b 2%nat + 256 * (b 3%nat + 256 * (b 4%nat + 256 * (b 5%nat + 256 * (b 6%nat + 256 * b 7%nat)))))) = z.
Proof.
intros z Hz. cbn beta. unfold YG0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with (256 * 256).
change (2 ^ (8 * Z.of_nat 3)) with (256 * 256 * 256). change (2 ^ (8 * Z.of_nat 4)) with (256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 5)) with (256 * 256 * 256 * 256 * 256). change (2 ^ (8 * Z.of_nat 6)) with (256 * 256 * 256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 7)) with (256 * 256 * 256 * 256 * 256 * 256 * 256).
rewrite Z.div_1_r. rewrite <- !Z.div_div by lia.
assert (H7 : z / 256 / 256 / 256 / 256 / 256 / 256 / 256 < 256).
{ change (2 ^ 64) with (256 * 256 * 256 * 256 * 256 * 256 * 256 * 256) in Hz.
repeat (apply Z.div_lt_upper_bound; [lia|]). lia. }
rewrite (Z.mod_small (z / 256 / 256 / 256 / 256 / 256 / 256 / 256)) by (split; [repeat (apply Z.div_pos; [|lia]); lia | exact H7]).
pose proof (Z.div_mod z 256 ltac:(lia)) as E0.
pose proof (Z.div_mod (z / 256) 256 ltac:(lia)) as E1.
pose proof (Z.div_mod (z / 256 / 256) 256 ltac:(lia)) as E2.
pose proof (Z.div_mod (z / 256 / 256 / 256) 256 ltac:(lia)) as E3.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E4.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E5.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E6.
lia.
Qed.
Lemma unsigned_lit_small8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hz. Qed.
Lemma val_mem_rdword : forall (H : word -> bool) mem a v,
0 <= v < 2 ^ 64 -> val_mem tfibsegs (mrestrict H mem) a 8 v -> rdword (aview tfibsegs H mem) a = Some v.
Proof.
intros H mem a v Hv Hm. unfold rdword, aview.
assert (B : forall k, (k < 8)%nat -> mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat k) = Some (Z_to_bv 8 (YG0f.le_byte v 8 k))).
{ intros k Hk. exact (Hm k Hk). }
assert (R : forall k, 0 <= YG0f.le_byte v 8 k < 256) by (intros k; unfold YG0f.le_byte; apply Z.mod_pos_bound; lia).
replace a with (a + Z.of_nat 0) at 1 by lia.
replace (a + 1) with (a + Z.of_nat 1) by lia. replace (a + 2) with (a + Z.of_nat 2) by lia. replace (a + 3) with (a + Z.of_nat 3) by lia.
replace (a + 4) with (a + Z.of_nat 4) by lia. replace (a + 5) with (a + Z.of_nat 5) by lia. replace (a + 6) with (a + Z.of_nat 6) by lia.
replace (a + 7) with (a + Z.of_nat 7) by lia.
rewrite !B by lia. cbn [option_map]. rewrite !unsigned_lit_small8 by apply R.
f_equal. apply le_bytes8_sum. exact Hv.
Qed.
Lemma fpchain_ext : forall (load load' : Z -> option Z) top ch bp,
fpchain load bp top ch -> (forall a v, bp - 16 <= a -> load a = Some v -> load' a = Some v) -> fpchain load' bp top ch.
Proof.
intros load load' top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc Hx; cbn in *;
[destruct Hc as (r & Hr & Hr4); exists r; split; [apply Hx; [lia | exact Hr] | exact Hr4]|].
destruct Hc as (Hfp & Hal & Hra & Hnfp & H4096 & Hrest). subst fp.
split; [reflexivity|]. split; [exact Hal|]. split; [apply Hx; [lia | exact Hra]|]. split; [apply Hx; [lia | exact Hnfp]|].
split; [exact H4096|]. destruct (bad_next bp top nfp) eqn:Hb; [exact Hrest|].
apply IH; [exact Hrest|]. intros a v Ha Hv. apply Hx; [|exact Hv].
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb _]. apply Z.leb_gt in Hb. lia.
Qed.
Lemma fpchain_ext2 : forall (load load' : Z -> option Z) top ch bp,
fpchain load bp top ch -> bp < top - 16 ->
(forall a v, bp - 16 <= a -> a + 8 <= top - 16 -> load a = Some v -> load' a = Some v) -> fpchain load' bp top ch.
Proof.
intros load load' top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc Hlt Hx; cbn in *;
[destruct Hc as (r & Hr & Hr4); exists r; split; [apply Hx; [lia | lia | exact Hr] | exact Hr4]|].
destruct Hc as (Hfp & Hal & Hra & Hnfp & H4096 & Hrest). subst fp.
split; [reflexivity|]. split; [exact Hal|]. split; [apply Hx; [lia | lia | exact Hra]|]. split; [apply Hx; [lia | lia | exact Hnfp]|].
split; [exact H4096|]. destruct (bad_next bp top nfp) eqn:Hb; [exact Hrest|].
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
apply IH; [exact Hrest| lia |]. intros a v Ha Ha' Hv. apply Hx; [lia | lia | exact Hv].
Qed.
Lemma rdword_ext : forall (rd rd' : Z -> option Z) a v,
(forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
intros rd rd' a v He Hv. unfold rdword in *. replace a with (a + 0) in Hv |- * by lia. rewrite <- !Z.add_assoc in *. cbn [Z.add] in *.
rewrite !He by lia. exact Hv.
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
intros a rho t. induction t; cbn [sv_only zev]; intros Hs; try reflexivity; try discriminate;
try (apply andb_prop in Hs as [H1 H2]; rewrite (IHt1 H1), (IHt2 H2); reflexivity).
- apply Nat.eqb_eq in Hs. subst. reflexivity.
- rewrite (IHt Hs). reflexivity.
Qed.
Lemma forallb_seq_In : forall (f : nat -> bool) n i, forallb f (seq 0 n) = true -> (i < n)%nat -> f i = true.
Proof. intros f n i H Hi. apply (proj1 (forallb_forall _ _) H). apply in_seq. lia. Qed.
Section b0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_ok_forget : forall k E ss (H : word -> bool) ms (clob : list (bv 5)),
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
regions_wf (ss_mem ss) = true -> no_cdata (ss_mem ss) = true -> mem_atoms_lt k (ss_mem ss) = true ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms)) clob)) (ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss))
(restrict H (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom tfibsegs))).
Proof.
intros k E ss H ms clob HS Hrv Hat Hwf Hnc Hma Hnd Hnz. rewrite restrict_mkst_fx.
apply (st_ok_after_stretch tfibsegs k E ss (restrict H ms) (ms_regs ms) (mrestrict H (ms_mem ms)) (ss_mem ss) (ss_pc ss) clob
HS Hrv Hat Hwf Hnc Hma (submem_refl _) Hnd Hnz).
- intros r _. reflexivity.
- apply Forall_forall. intros r _. split; intros a _; [reflexivity | intros Hw; exact Hw].
Qed.
End b0.
