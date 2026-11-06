(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the part of proofs/cgif/cgif_file_fuzzer/lib/YC20.v that carries no cgif name, as fuzz_grant's lib/A/Prog/GrantBase.v (origin/cold/pg-prog 4a980cd5011) and fuzz_identity's lib/A/Prog/IdentBase.v (origin/cold/port-libreac-identity ea5560a967b) carry it, with only the unit's module prefix changed, for libreac/fuzz_boxreg: the read-only range, the frame object and the shape of a call's post-condition. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxBase.v at origin/ossv/recipes ee71d1fd3fc
   for reac-pw/fuzz_role (image A and image B): module paths changed; its lines 17-45 (in_roP, arodata_okP,
   ro_below_ofl, ro_spares, arodata_ok_journalP) are taken as they stand; its lines 46-107 (afobj, apost_base,
   apost_baseF, fxr, apost_baseF_continue) are left out and replaced by the role definitions below (rl_fxk in place of
   fxr, for role's float registers; rl_wcell in place of afobj, for a cell that lies on the stack or in a side-stack
   frame); the role constants, the string predicate rl_cstr and the read-only cell predicate rl_ro_cells are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgBase.v at 0de5d668c87e for reac-pw/fuzz_rate
   (image A and image B): module paths changed; in_roP .. arodata_ok_journalP taken as they stand; the prefix rl_
   becomes rt_ (rl_fxk, rl_cstr, rl_ro_cells, rl_wcell, rl_fresh_awr(_n), rl_x, rl_xv, rl_loc, rl_at, rl_cut, rl_fsh,
   rl_inw); the role constants are replaced by rate's (rt_len, rt_bl and the texts the checks compare, from the shared
   Pod model); role's quantity record rl_env becomes rt_renv with rate's three blocks and seven header values, and
   rl_x gains their constructors; rt_i32tab (a table of 4-byte values read by instrumented loads) and rt_rom_kept
   (the read-only image as every call keeps it: the released fuzz_boxreg lib/A/Rt/SnprintfDef.v asn_rom_kept) with
   its two sources are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Prog/DiscoRo.v and
   proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxRo.v at origin/ossv/recipes 09c6822d886 (img_shadow_vis, globs_marked,
   ro_unowned, ro_usable_glob, ro_hull, ro_read_ok_glob) become rt_img_shadow_vis, rt_globs_marked, rt_ro_unowned,
   rt_glob_usable, rt_img_hull and rt_glob_read_ok, with the image's range as parameters in place of IMG_LO / IMG_TOP;
   rt_img_unowned, rt_aview_mbyte, rt_cstr_at, rt_i32tab_at, rt_u64tab_at, rt_img_bytes, rt_img_val, rt_ro_mbyte,
   rt_val_of_ro, rt_bytes_of_ro, rt_rom_pinned, rt_rom_view_of and rt_glob_of_b are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgBase.v, with its module paths and module names changed; 68 of its 106 lines of code are new or changed and 299 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/Prog/GrantRo.v (85e206d1c4c) for libreac/fuzz_identity: module paths changed; IMG_LO / IMG_HI and the registered globals named below are fuzz_identity.asan's; YI0f (cgif's frame-flush model, which this file does not use and fuzz_identity's lib does not have) is not required. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_identity/lib/A/Prog/IdentRo.v (origin/ossv/recipes 4b6f0df50aa7) for libdiginet/fuzz_codec's ASan + UBSan build (image B, fuzz_codec.asan-ubsan sha256 73109e32e77b...): module paths changed; IMG_LO / IMG_HI are fuzz_codec.asan-ubsan's (lib/AU/YImgTopU.v), the registered globals named below are its 40; every definition and proof is the donor's text. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YImgTopU.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* fuzz_codec.asan-ubsan's read range: AU/YImgTopU.v (IMG_LO is its notation; IMG_HI names IMG_TOP here). *)
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
   own bytes usable and the rest of the granule unusable. DESK (12 bytes),
   switch.table.diginet_seg7 (364 bytes) and 31 string literals (1 to 10
   bytes), 33 of the 40 globals fuzz_codec.asan-ubsan registers (its asan_globals
   section), are all of that shape. `globs_marked G` is the start-up
   certificate for the list G of registered globals, which the composition
   discharges; a walk names the table it reads with `In (q, sz) G`. *)
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
