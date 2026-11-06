
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym DiscoSyms DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Export DiscoRoList.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Definition in_zs (a n : Z) : Prop :=
exists q m, In (q, m) (as_zero_shadow B) /\ q <= a /\ a + n <= q + m.
Definition img_shadow_vis : Prop :=
forall ly S (W : world segs) mem md a,
AR segs B ly S W mem md -> IMG_LO <= a < IMG_TOP -> aview segs (w_H W) mem (shadow_addr a) <> None.
Lemma zs_range : forall q m, In (q, m) (as_zero_shadow B) ->
forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
0 <= q /\ 0 <= m /\ q mod 8 = 0 /\ m mod 8 = 0 /\ q + m <= kLowMemEnd.
Proof.
intros q m Hin ly S W mem md HAR.
pose proof (am_syms _ _ _ _ (proj1 HAR)) as HS.
pose proof (proj1 (Forall_forall _ _) (aso_zshadow B HS) (q, m) Hin) as H.
cbn [fst snd] in H. exact H.
Qed.
Lemma zs_zero : forall q m, In (q, m) (as_zero_shadow B) ->
forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
zero_shadow (aview segs (w_H W) mem) SHADOW_OFF q m.
Proof.
intros q m Hin ly S W mem md HAR.
exact (al_zshadow _ _ LAWS ly S W mem md (q, m) HAR (or_intror Hin)).
Qed.
Lemma ro_usable : forall ly S (W : world segs) mem md a n,
AR segs B ly S W mem md -> in_zs a n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR (q & m & Hin & H1 & H2).
destruct (zs_range q m Hin ly S W mem md HAR) as (Hq0 & Hm0 & Hq8 & Hm8 & Hhi).
pose proof (zs_zero q m Hin ly S W mem md HAR) as Hz.
apply (range_addressable_sub (aview segs (w_H W) mem) SHADOW_OFF q m a n); [| exact H1 | exact H2].
exact (zero_shadow_range (aview segs (w_H W) mem) SHADOW_OFF q m Hq8 Hm8 Hz).
Qed.
Lemma ro_hull : forall ly S (W : world segs) mem md a n,
img_shadow_vis -> AR segs B ly S W mem md -> 0 < n ->
IMG_LO + 64 <= a -> a + n + 64 <= IMG_TOP ->
shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
intros ly S W mem md a n HV HAR Hn Hlo Hhi s Hs.
unfold shadow_addr in Hs.
set (x := 8 * (s - SHADOW_OFF)).
assert (Hx : shadow_addr x = s).
{ unfold shadow_addr, x. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
assert (Hxlo : IMG_LO <= x) by (unfold x; lia).
assert (Hxhi : x < IMG_TOP) by (unfold x; lia).
rewrite <- Hx. exact (HV ly S W mem md x HAR (conj Hxlo Hxhi)).
Qed.
Lemma ro_read_ok : forall ly S (W : world segs) mem md a n,
img_shadow_vis -> AR segs B ly S W mem md -> 0 < n ->
IMG_LO + 64 <= a -> a + n + 64 <= IMG_TOP -> in_zs a n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\
shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
intros ly S W mem md a n HV HAR Hn Hlo Hhi Hz. split.
- exact (ro_usable ly S W mem md a n HAR Hz).
- exact (ro_hull ly S W mem md a n HV HAR Hn Hlo Hhi).
Qed.
Definition globs_marked (G : list (Z * Z)) : Prop :=
forall ly S (W : world segs) mem md q sz,
In (q, sz) G -> AR segs B ly S W mem md ->
block_shadow (aview segs (w_H W) mem) SHADOW_OFF q sz.
Lemma ro_usable_glob : forall G ly S (W : world segs) mem md q sz a n,
globs_marked G -> In (q, sz) G -> AR segs B ly S W mem md -> q <= a -> a + n <= q + sz ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros G ly S W mem md q sz a n HG Hin HAR H1 H2.
exact (block_shadow_range (aview segs (w_H W) mem) SHADOW_OFF q sz a n (HG ly S W mem md q sz Hin HAR) H1 H2).
Qed.
Lemma ro_read_ok_glob : forall G ly S (W : world segs) mem md q sz a n,
globs_marked G -> In (q, sz) G -> img_shadow_vis -> AR segs B ly S W mem md ->
q <= a -> a + n <= q + sz -> 0 < n -> IMG_LO + 64 <= a -> a + n + 64 <= IMG_TOP ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\
shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
intros G ly S W mem md q sz a n HG Hin HV HAR H1 H2 Hn Hlo Hhi. split.
- exact (ro_usable_glob G ly S W mem md q sz a n HG Hin HAR H1 H2).
- exact (ro_hull ly S W mem md a n HV HAR Hn Hlo Hhi).
Qed.
End c.
End b.
Definition ro_unowned (B : asyms) (lo n : Z) : Prop :=
forall a, lo <= a < lo + n -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Definition disco_ro_unowned (B : asyms) : Prop := Forall (fun r => ro_unowned B (fst r) (snd r)) disco_ro_ranges.
Lemma disco_ro_unowned_at : forall B lo n, disco_ro_unowned B -> In (lo, n) disco_ro_ranges -> ro_unowned B lo n.
Proof. intros B lo n H Hin. exact (proj1 (Forall_forall _ _) H (lo, n) Hin). Qed.
Lemma ro_bytes : forall segs rlo rhi B (rd : reader) lo n a,
arodata_okP segs rlo rhi B rd -> in_roP segs rlo rhi a -> ro_unowned B lo n -> lo <= a < lo + n ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Proof. intros segs rlo rhi B rd lo n a HA Hro HU Ha. destruct (HU a Ha) as [H1 H2]. exact (HA a Hro H1 H2). Qed.
Section dro. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {L : ptable dsym} {PI : PAImg L}.
Lemma disco_ro_in_ro : forall q sz x, In (q, sz) disco_ro_all -> q <= x < q + sz -> in_roP pa_segs pa_relro_lo pa_relro_hi x.
Proof. intros q sz x Hin Hx. unfold in_roP. exact (pa_ro_ok q sz x Hin Hx). Qed.
Lemma disco_ro_readable : forall (B : asyms) (rd : reader) q sz x, arodata_okP pa_segs pa_relro_lo pa_relro_hi B rd ->
disco_ro_unowned B -> In (q, sz) disco_ro_ranges -> q <= x < q + sz -> rd x <> None.
Proof.
intros B rd q sz x HA DRO Hin Hx.
assert (Hin' : In (q, sz) disco_ro_all) by (unfold disco_ro_all; apply in_or_app; left; exact Hin).
rewrite (ro_bytes pa_segs pa_relro_lo pa_relro_hi B rd q sz x HA (disco_ro_in_ro q sz x Hin' Hx) (disco_ro_unowned_at B q sz DRO Hin) Hx).
pose proof (pa_ro_present q sz x Hin' Hx) as H. destruct (seg_rom pa_segs (Z_to_bv 64 x)); [discriminate|contradiction].
Qed.
Lemma disco_ro_view : forall (H : word -> bool) (mem : word -> option byte) q sz x,
In (q, sz) disco_ro_all -> q <= x < q + sz -> aview pa_segs H mem x <> None.
Proof.
intros H mem q sz x Hin Hx. pose proof (pa_ro_present q sz x Hin Hx) as P.
unfold aview, YP09.mbyte, YK04.mrestrict. destruct (H (Z_to_bv 64 x)).
- destruct (seg_rom pa_segs (Z_to_bv 64 x)); [discriminate|contradiction].
- destruct (mem (Z_to_bv 64 x)); [discriminate|].
  destruct (seg_rom pa_segs (Z_to_bv 64 x)); [discriminate|contradiction].
Qed.
End dro.
