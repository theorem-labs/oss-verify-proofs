(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/Prog/GrantRo.v (a working branch 85e206d1c4c) for libreac/fuzz_boxreg, as fuzz_identity's lib/A/Prog/IdentRo.v (ea5560a967b) carries it: module paths changed; IMG_LO / IMG_HI come from Reusable/YImgTop.v and the registered globals named below are fuzz_boxreg.asan's (5, not identity's 50); YI0f (cgif's frame-flush model, which this file does not use and fuzz_boxreg's lib does not have) is not required. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* fuzz_boxreg.asan's read range: Reusable/YImgTop.v (IMG_LO is its notation; IMG_HI names IMG_TOP here). *)
Definition IMG_HI : Z := IMG_TOP.
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
AR segs B ly S W mem md -> IMG_LO <= a < IMG_HI -> aview segs (w_H W) mem (shadow_addr a) <> None.
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
IMG_LO + 64 <= a -> a + n + 64 <= IMG_HI ->
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
assert (Hxhi : x < IMG_HI) by (unfold x; lia).
rewrite <- Hx. exact (HV ly S W mem md x HAR (conj Hxlo Hxhi)).
Qed.
(* Both facts at once, in the shape the walks consume. *)
Lemma ro_read_ok : forall ly S (W : world segs) mem md a n,
img_shadow_vis -> AR segs B ly S W mem md -> 0 < n ->
IMG_LO + 64 <= a -> a + n + 64 <= IMG_HI -> in_zs a n ->
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
   own bytes usable and the rest of the granule unusable. fuzz_boxreg.asan
   registers 5 globals (its asan_globals section, 0x9d770 to 0x9d8b0, five
   64-byte records): ZERO at 0x20cc0 (6 bytes), the string literals at 0x20ce0
   (1 byte), 0x20d40 (3 bytes) and 0x20d60 (1 byte), and read_mac.base at
   0x20d00 (5 bytes). No size is a multiple of 8, so all 5 are of that shape
   and `as_zero_shadow B` covers none of them. `globs_marked G` is the
   start-up certificate for the list G of registered globals, which the
   composition discharges; a walk names the table it reads with
   `In (q, sz) G`. *)
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
q <= a -> a + n <= q + sz -> 0 < n -> IMG_LO + 64 <= a -> a + n + 64 <= IMG_HI ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\
shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
intros G ly S W mem md q sz a n HG Hin HV HAR H1 H2 Hn Hlo Hhi. split.
- exact (ro_usable_glob G ly S W mem md q sz a n HG Hin HAR H1 H2).
- exact (ro_hull ly S W mem md a n HV HAR Hn Hlo Hhi).
Qed.
End c.
End b.
