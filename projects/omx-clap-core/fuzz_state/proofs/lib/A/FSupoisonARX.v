(* The image premises of lib/A/FSupoisonARXm.v discharged for fuzz_state's image A (POISON-U lane, a Theorem Labs lane).

   lib/A/FSupoisonARXm.v (image-free) proves the AR -> ARU transfer of a Theorem Labs lane's frozen allocator interface records
   under two named image premises; this file discharges them for A (fs.asan, sha256 64b53ff86172...):
   - [inst_low]: [fs_inst_low] at [fs_inst_ok inst := inst = TFIB_INST] (0xa48d8, AF0m.v:15; lib/A/FSRealloc_inst.v
     instantiates ARX with [inst = TFIB_INST]); [inst_low_window] for any window of cgif AGif0cgif.inst_ok's shape
     below the shadow.
   - [zones_free]: [zones_free_shape] for every DZONE / CZONE of AGis.v:230's / AGif0cgif.CZONE's shape, from
     layout_ok (the NB, SB, thread, context and D extents are owned extents) and one ledger fact, a lower bound on the
     image's end; [fs_img_end] proves that bound for A from ALedger.al_img (AF0x.img_cover_of_ledger: TFIB_IMG_END =
     0x5fd000), so [fs_zones_free] needs only six linear inequalities on the zone's literal bounds.
   Sections 0-2 of the former file (the helpers, [ush_lo] and the memory transfer, the old AGif0 field copies and
   AIface_U) are gone: 0-1 moved to lib/A/FSupoisonARXm.v under the same names; 2 and AIface_U_fs were the transfer of
   the OLD AGif0 field set, which the frozen interface replaces (deleted, a Theorem Labs lane 12:3xZ).  lib/B/FSupoisonARX.v is
   this file's image-B twin.

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0q YG0s YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
(* the image-free premises ([inst_low], [zones_free]) and [ush_free] *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonARXm.
(* fs's image A: its segments, its symbols' addresses, its image cover. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AB1v AF0m AF0x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The image premises of FSupoisonARXm, discharged for fs's image A.                                             *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section prem. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- inst_low ---- *)

(* AGif0.v:49's shape (cgif: lo = 0xa00a0, hi = 0xa3aa0): any 8-aligned window of the image below the shadow. *)
Definition inst_ok_window (lo hi : Z) (inst : Z) : Prop := lo <= inst /\ inst + 0xe60 <= hi /\ inst mod 8 = 0.

Lemma inst_low_window : forall lo hi, 0 <= lo -> hi <= SHADOW_OFF -> inst_low (inst_ok_window lo hi).
Proof. intros lo hi H0 H1 inst (I1 & I2 & _). lia. Qed.

(* fs's instance (image A): TFIB_INST = 0xa48d8 (AF0m.v:15), the [this] of asan_realloc's Reallocate call
   (`auipc a0, 0x72` 0x32904 + `addi a0, a0, -0x2c` 0x32908; lib/A/FSRealloc_inst.v @ 6352f71b619, header).
   fs's lib has no inst_ok text (no port of AGif0); FSRealloc_inst.v's ARX is [inst = TFIB_INST /\ ARU ..]. *)
Definition fs_inst_ok (inst : Z) : Prop := inst = AF0m.TFIB_INST.

Lemma fs_inst_low : inst_low fs_inst_ok.
Proof. intros inst ->. unfold AF0m.TFIB_INST, SHADOW_OFF. lia. Qed.

(* ---- zones_free ---- *)

(* AGis.v:230's DZONE and AGif0.v:54's CZONE, with their literal bounds as parameters (cgif: DZONE_shape 0x178148
   0x5c88d0; CZONE_shape 0x10000 0x5fb000 0x7fff8000 0x80050000 TFIB_TSD).  fs's relocated AGis text (AFis.v:228)
   is DZONE_shape 0x179e08 0x5ca590. *)
Definition DZONE_shape (dlo dhi : Z) (ly : alayout) (a : Z) : Prop :=
(dlo <= a < dhi) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Definition CZONE_shape (ilo ihi slo shi tsd0 : Z) (ly : alayout) (a : Z) : Prop :=
(ilo <= a < ihi) \/ (slo <= a < shi) \/ (ly_T ly <= a < ly_T ly + 80) \/ (ly_C ly <= a < ly_C ly + 160) \/
(tsd0 <= a < tsd0 + 8) \/ (ly_D ly <= a < ly_D ly + 4096).

(* An address of an owned extent is off every shadow byte of a live block. *)
Lemma owned_ext_free : forall ly lo len a, layout_ok ly -> In (lo, len) (owned_extents ly) -> lo <= a < lo + len ->
0 <= a < 2 ^ 64 /\ ush_free ly a.
Proof.
intros ly lo len a LO Hin Ha.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LO) (lo, len) Hin) as [P1 P2]. cbn [fst snd] in P1, P2.
pose proof (lo_img ly LO) as (I0 & I1 & I2 & I3).
pose proof ASAN_CEIL_range as [CR _].
assert (DIV0 : 0 <= (fst (ly_img ly) + snd (ly_img ly)) / 8) by (apply Z.div_pos; unfold kImgLo in *; lia).
unfold ush_free, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
destruct P2 as [P2|[P2 P3]].
- split; [lia | left; lia].
- split; [lia | right; lia].
Qed.

(* zones_free for every zone of the two shapes: the literal ranges lie below the shadow, the shadow band below
   the shadow of [E], and [E] is a lower bound of the image's end that AR guarantees (the ledger fact). *)
Lemma zones_free_shape : forall segs B (E dlo dhi ilo ihi slo shi tsd0 : Z),
(forall ly S W mem md, AR segs B ly S W mem md -> E <= fst (ly_img ly) + snd (ly_img ly)) ->
0 <= dlo -> dhi <= SHADOW_OFF -> 0 <= ilo -> ihi <= SHADOW_OFF -> 0 <= tsd0 -> tsd0 + 8 <= SHADOW_OFF ->
0 <= slo -> shi <= shadow_addr E ->
zones_free segs B (DZONE_shape dlo dhi) (CZONE_shape ilo ihi slo shi tsd0).
Proof.
intros segs B E dlo dhi ilo ihi slo shi tsd0 IMG Hd0 Hd1 Hi0 Hi1 Ht0 Ht1 Hs0 Hs1 ly S W mem md a HAR Hz.
pose proof (am_layout B ly S _ (proj1 HAR)) as LO.
pose proof (IMG ly S W mem md HAR) as IE.
pose proof (lo_img ly LO) as (I0 & I1 & I2 & I3).
assert (DIV0 : 0 <= (fst (ly_img ly) + snd (ly_img ly)) / 8) by (apply Z.div_pos; unfold kImgLo in *; lia).
assert (DD : (fst (ly_img ly) + snd (ly_img ly)) / 8 <= kImgEnd / 8)
  by (apply Z.div_le_mono; unfold kImgLo, kImgEnd in *; lia).
assert (EE : kImgEnd / 8 = 847360) by reflexivity.
assert (LOWF : forall x, 0 <= x < SHADOW_OFF -> 0 <= x < 2 ^ 64 /\ ush_free ly x).
{ intros x Hx. unfold ush_free, shadow_addr, SHADOW_OFF in *. split; [lia | left; lia]. }
destruct Hz as [[HD|[HD|HD]] | [HC|[HC|[HC|[HC|[HC|HC]]]]]].
- apply LOWF. lia.
- exact (owned_ext_free ly (ly_NB ly) kNodesBlockSize a LO ltac:(unfold owned_extents; cbn [In]; tauto) HD).
- exact (owned_ext_free ly (ly_SB ly) kStoreBlockSize a LO ltac:(unfold owned_extents; cbn [In]; tauto) HD).
- apply LOWF. lia.
- pose proof (shadow_addr_mono E _ IE) as SM.
  unfold ush_free. unfold shadow_addr, SHADOW_OFF in *. split; [lia | left; lia].
- apply (owned_ext_free ly (ly_T ly) kThreadObjSize a LO ltac:(unfold owned_extents; cbn [In]; tauto)).
  unfold kThreadObjSize. lia.
- apply (owned_ext_free ly (ly_C ly) 256 a LO ltac:(unfold owned_extents; cbn [In]; tauto)). lia.
- apply LOWF. lia.
- exact (owned_ext_free ly (ly_D ly) 4096 a LO ltac:(unfold owned_extents; cbn [In]; tauto) HC).
Qed.

(* The ledger fact for fs's image A: every segment of A lies in [ly_img] (ALedger.al_img), so the image ends at
   or above TFIB_IMG_END = 0x5fd000 (AF0x.img_cover_of_ledger). *)
Lemma fs_img_end : forall B ly S W mem md, AR AB1v.tfibsegs B ly S W mem md ->
AF0x.TFIB_IMG_END <= fst (ly_img ly) + snd (ly_img ly).
Proof. intros B ly S W mem md HAR. exact (proj2 (AF0x.img_cover_of_ledger ly S md (proj1 (proj2 HAR)))). Qed.

(* zones_free for A, for every DZONE / CZONE of the two shapes whose literal bounds satisfy six inequalities
   (shadow_addr TFIB_IMG_END = 0x800b7a00). *)
Lemma fs_zones_free : forall B dlo dhi ilo ihi slo shi,
0 <= dlo -> dhi <= SHADOW_OFF -> 0 <= ilo -> ihi <= SHADOW_OFF -> 0 <= slo -> shi <= shadow_addr AF0x.TFIB_IMG_END ->
zones_free AB1v.tfibsegs B (DZONE_shape dlo dhi) (CZONE_shape ilo ihi slo shi AF0m.TFIB_TSD).
Proof.
intros B dlo dhi ilo ihi slo shi Hd0 Hd1 Hi0 Hi1 Hs0 Hs1.
apply (zones_free_shape AB1v.tfibsegs B AF0x.TFIB_IMG_END dlo dhi ilo ihi slo shi AF0m.TFIB_TSD (fs_img_end B)
  Hd0 Hd1 Hi0 Hi1); [unfold AF0m.TFIB_TSD; lia | unfold AF0m.TFIB_TSD, SHADOW_OFF; lia | exact Hs0 | exact Hs1].
Qed.

(* The concrete check: fs's DZONE (AFis.v:228) and AGif0.v:54's CZONE read over A's image range and A's TSD,
   with cgif's shadow band [0x7fff8000, 0x80050000) (A's band comes with the port of AGif0; any band ending at or
   below 0x800b7a00 is covered by [fs_zones_free]). *)
Lemma fs_zones_free_ex : forall B,
zones_free AB1v.tfibsegs B (DZONE_shape 0x179e08 0x5ca590)
  (CZONE_shape AF0x.TFIB_IMG_LO AF0x.TFIB_IMG_END 0x7fff8000 0x80050000 AF0m.TFIB_TSD).
Proof.
intros B. apply fs_zones_free; unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, SHADOW_OFF; try lia.
unfold shadow_addr, SHADOW_OFF. assert (E : 6279168 / 8 = 784896) by reflexivity. rewrite E. lia.
Qed.

End prem.
