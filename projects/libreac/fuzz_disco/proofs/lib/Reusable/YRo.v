(* Modified by Theorem Labs, 2026-10: copied from fuzz_grant's lib/A/Prog/GrantRo.v (a working branch) for libreac/fuzz_disco's asan-ubsan walks, with its module paths changed and its read range cited from YImgTop (was fuzz_grant's 0x10000 / 0x5fa000); the byte facts at the end (tfib_globs: fuzz_disco.asan-ubsan's 49 registered globals from its asan_globals descriptors; tfib_ro_extra; ro_unowned; ro_bytes) follow the asan side's DiscoRo.v. *)
(* The image's read-only data is marked usable, in every state.

   The memory-checking runtime registers the program's globals at start-up and
   marks the bytes of each one usable, with unusable guard bytes around it; the
   ranges it leaves usable are `as_zero_shadow B`, whose shadow bytes `AR` keeps
   zero in every state (lib/Reusable/YG0n.v:188-191, the law at YG0d.v:435-438).
   Every walk that reads a table of the image needs the same two facts:
     - `ro_usable`: the shadow says those bytes are accessible, which is what an
       instrumented load and the wrappers check;
     - `ro_hull`: the shadow bytes of the 8-byte window around the range are
       readable, which is what `__asan_memcpy` asks for before it copies. Those
       window bytes reach a global's guard bytes, which are marked unusable, not
       zero, so this one comes from the whole image's shadow being mapped
       (`img_shadow_vis`, a fact of the runtime's symbols that a Theorem Labs lane gives).
   A walk takes `in_zs B q n` for the table it reads and `img_shadow_vis`; never
   their consequences. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
(* [a, a + n) lies in one range the runtime leaves marked usable. *)
Definition in_zs (a n : Z) : Prop :=
exists q m, In (q, m) (as_zero_shadow B) /\ q <= a /\ a + n <= q + m.
(* every shadow byte of the image's read range is mapped *)
Definition img_shadow_vis : Prop :=
forall ly S (W : world segs) mem md a,
AR segs B ly S W mem md -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP -> aview segs (w_H W) mem (shadow_addr a) <> None.
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
(* The bytes of a registered global are marked usable. *)
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
(* The shadow bytes the wrappers' window reaches are readable. *)
Lemma ro_hull : forall ly S (W : world segs) mem md a n,
img_shadow_vis -> AR segs B ly S W mem md -> 0 < n ->
YImgTop.IMG_LO + 64 <= a -> a + n + 64 <= YImgTop.IMG_TOP ->
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
assert (Hxlo : YImgTop.IMG_LO <= x) by (unfold x; lia).
assert (Hxhi : x < YImgTop.IMG_TOP) by (unfold x; lia).
rewrite <- Hx. exact (HV ly S W mem md x HAR (conj Hxlo Hxhi)).
Qed.
(* Both facts at once, in the shape the walks consume. *)
Lemma ro_read_ok : forall ly S (W : world segs) mem md a n,
img_shadow_vis -> AR segs B ly S W mem md -> 0 < n ->
YImgTop.IMG_LO + 64 <= a -> a + n + 64 <= YImgTop.IMG_TOP -> in_zs a n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\
shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
intros ly S W mem md a n HV HAR Hn Hlo Hhi Hz. split.
- exact (ro_usable ly S W mem md a n HAR Hz).
- exact (ro_hull ly S W mem md a n HV HAR Hn Hlo Hhi).
Qed.
(* ---- a registered global whose last granule is partial -------------------
   `as_zero_shadow B` holds whole granules, so it cannot cover the last bytes
   of a global whose size is not a multiple of 8: the memory-checking runtime
   writes that granule's shadow byte as `sz mod 8`, which marks the global's
   own bytes usable and the rest of the granule unusable. In fuzz_disco.asan-ubsan
   40 of the 49 registered globals (tfib_globs) are of that shape. `globs_marked G` is the start-up certificate for the list
   G of registered globals, which the composition discharges; a walk names the
   table it reads with `In (q, sz) G`. *)
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
q <= a -> a + n <= q + sz -> 0 < n -> YImgTop.IMG_LO + 64 <= a -> a + n + 64 <= YImgTop.IMG_TOP ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\
shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
intros G ly S W mem md q sz a n HG Hin HV HAR H1 H2 Hn Hlo Hhi. split.
- exact (ro_usable_glob G ly S W mem md q sz a n HG Hin HAR H1 H2).
- exact (ro_hull ly S W mem md a n HV HAR Hn Hlo Hhi).
Qed.
End c.
End b.
Definition tfib_globs : list (Z * Z) := [(0x20f80, 30); (0x20fc0, 8); (0x20fe0, 6); (0x21000, 5); (0x21020, 6); (0x21040, 5); (0x21060, 4); (0x21080, 5); (0x210a0, 6); (0x210c0, 6); (0x210e0, 6); (0x21100, 7); (0x21120, 10); (0x21140, 5); (0x21160, 4); (0x21180, 7); (0x211c0, 7); (0x211e0, 7); (0x21200, 8); (0x21220, 5); (0x21240, 3); (0x21260, 7); (0x21280, 6); (0x212e0, 4); (0x21300, 7); (0x21320, 8); (0x21340, 2); (0x21360, 41); (0x213c0, 2); (0x213e0, 1); (0x21400, 13); (0x21420, 14); (0x21440, 17); (0x21480, 19); (0x214c0, 15); (0x214e0, 12); (0x21500, 5); (0x21520, 6); (0x21540, 16); (0x21560, 2); (0x215a0, 7); (0x215e0, 7); (0x21600, 6); (0x21620, 8); (0x21640, 8); (0x21680, 12); (0xa0660, 24); (0xa06a0, 24); (0xa06e0, 24)].
Definition tfib_ro_extra : list (Z * Z) := [(0x212b8, 36); (0x10340, 8); (0x10370, 8); (0x10310, 8); (0x103d8, 8); (0x10318, 8); (0x103c8, 8); (0x10368, 32)].
Definition tfib_ro_ranges : list (Z * Z) := tfib_globs ++ tfib_ro_extra.
Definition ro_unowned (B : asyms) (lo n : Z) : Prop :=
forall a, lo <= a < lo + n -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Definition tfib_ro_unowned (B : asyms) : Prop := Forall (fun r => ro_unowned B (fst r) (snd r)) tfib_ro_ranges.
Lemma tfib_ro_unowned_at : forall B lo n, tfib_ro_unowned B -> In (lo, n) tfib_ro_ranges -> ro_unowned B lo n.
Proof. intros B lo n H Hin. exact (proj1 (Forall_forall _ _) H (lo, n) Hin). Qed.
Lemma ro_bytes : forall segs rlo rhi B (rd : reader) lo n a,
arodata_okP segs rlo rhi B rd -> in_roP segs rlo rhi a -> ro_unowned B lo n -> lo <= a < lo + n ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Proof. intros segs rlo rhi B rd lo n a HA Hro HU Ha. destruct (HU a Ha) as [H1 H2]. exact (HA a Hro H1 H2). Qed.
