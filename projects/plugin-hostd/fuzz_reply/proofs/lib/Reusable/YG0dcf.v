(* CARRIED from commit f02099425ace9f613657229b085bb00b2e89f977,
   proofs/cgif/cgif_file_fuzzer/lib/YG0dcf.v, sha256 ad2dabf4baa20e6cc40881b9ab2c5feb623cd74df4815e0f25f0910a61f2b194 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the text is otherwise unchanged. *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: acall_pre_cf's stack-bottom conjunct is A7d's `ly_bot ly + ACALL_PREFIX < spZ regs` (a3e599d9f79e Reusable/YG0dcf.v:52), with the Notation ACALL_PREFIX taken from a3e599d9f79e Reusable/YG0d.v:21; nothing else of that set is taken. *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the CALL FORMS and the
   STATEMENTS of the AR laws, over ARcf. cgif's YG0d.v is NOT edited.
   Restated from YG0d.v: acall_pre (:226-234) without `aregime S` and with qmeter_cf, acall_post (:235-243),
   ecall_pre (:278-284), and the fourteen AR laws (:423-511). Reused AS THEY STAND, because they name neither
   AR nor Wf: ascratch (:215-216), chain_pre (:218-223), call_trace (:224-225), cfg_at (:213-214), ablocks
   (:421-422), shadow_hull_vis (:310-311), dest_ok / src_ok's ingredients.
   Every form takes the ghost set Hp right after the state; every allocator call leaves it unchanged.
   The proofs of the laws are in YG0qcf.v / YG0scf.v / YG0tcf.v, by source file, as in cgif. No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf.
(* YAkMemnorm (c-omx-alloc's engine file, override-free; its closure adds YAkMemnorm.v and YP00.v only: YM03's lia /
   nia / tauto override is already loaded here through YK11) states memnorm, the overlay normal form. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* Taken from a working branch A7d a3e599d9f79e proofs/omx-clap-core/fuzz_preset/lib/Reusable/YG0d.v:21, provisional:
   the stack an allocator interceptor uses above the ASan stack bottom ly_bot before it enters Allocate / Deallocate /
   Reallocate.  A numeral notation, so that lia sees its value; it stands before Section G because a notation
   declared inside a section disappears when the section closes. *)
Notation ACALL_PREFIX := 4096%Z (only parsing).


Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* The two names AR_head_frame_law_cf needs, VERBATIM from h-rw-man-5's YGcfHp.v:46-51
   (cold/h-rw-man-5-cfhp 29c8b46b1cef). They live here, not in YGcfHp.v, because the law is
   a field of AR_laws_cf below and YGcfHp.v imports this file (a cycle otherwise).
   amc_hp_live's body (YG0ncf.v), named: p is the user base of a live block of at least
   cf_head bytes. *)
Definition hp_live_cf (B : asyms) (ly : alayout) (S : astate) (p : Z) : Prop :=
exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\ p = sptr_addr B ly (ck_user k) /\ cf_head <= ck_n k.

(* The shadow bytes of the hidden-head granules of L. *)
Definition hd_shadow (L : list Z) (a : Z) : Prop :=
exists g, g mod 8 = 0 /\ in_head L g = true /\ a = shadow_addr g.

(* ---------------------------------------------------------------------------- *)
(* Read-only image bytes (field round 3, Main 2026-10-30). mbyte (YP09.v:17) falls *)
(* back to seg_rom when the overlay has no byte.                                   *)
Section RO.
Variable segs : list Segment.

(* memnorm (YAkMemnorm.v:42) keeps the overlay off every read-only address, so a read-only byte reads as the image's
   (a Theorem Labs lane's rif_vsn; the shape of the kit's mem_inv_ro_read, kit 7bb12afd3646 A/Bk/Lib/Mem.v:363).  Field round
   3 part 3c: no call carries memnorm any more; the report's read-only reads go through aro_read_cf below.  This lemma
   stays as a standalone fact. *)
Lemma ro_byte_read_cf : forall (H : word -> bool) mem a, YAkMemnorm.memnorm segs mem ->
  YAkMemnorm.ro_addr segs (Z_to_bv 64 a) = true -> mbyte segs (mrestrict H mem) a = seg_rom segs (Z_to_bv 64 a).
Proof.
intros H mem a [MN _] RO. unfold mbyte, mrestrict. destruct (H (Z_to_bv 64 a)); [reflexivity|].
destruct (mem (Z_to_bv 64 a)) as [b|] eqn:E; [|reflexivity].
rewrite (MN _ b E) in RO. discriminate RO.
Qed.

(* The addresses arodata_ok_cf covers (part 3c): the relocation-read-only range [cf_relro_lo, cf_relro_hi) and the
   class-full report's read-only reads cf_ro_reads (CfImg). *)
Definition aro_addr_cf (a : Z) : Prop := (cf_relro_lo <= a < cf_relro_hi) \/ Exists (in_zr a) cf_ro_reads.

(* The relocation-read-only range [cf_relro_lo, cf_relro_hi) (PT_GNU_RELRO, CfImg) in VALUE form (Main 2026-10-30, after
   a Theorem Labs lane's measurement: a form over aview travels through preset's journal / K0 texts, a 'no overlay byte' form does
   not): an overlay byte at a non-owned RELRO address equals the image's byte (the owned GOT rows there stay pinned by
   amc_const). NOT an ARcf conjunct: the walks carry it at the call. WHY it holds: all five images (cgif, reply A /
   B, preset A / AU) are ET_EXEC (e_type 2), so no runtime relocation writes RELRO, start-up writes no RELRO byte
   outside the owned rows other than the image's own (cgif's start-up band YB01.v / YB03.v has no KWord in
   [0x9dc70, 0x9f000)), and no walk writes there (the raw frames). Every C_SILENT cell (ReportFile::Write's GOT word)
   lies in a non-owned gap of its unit's Tfib_owned_static: cgif 0x9edd0 in [0x9ed78, 0x9ee60), reply A 0x9e598 in
   [0x9e540, 0x9e628), reply B 0x9eb18 in [0x9eac0, 0x9eba8), preset A 0xa2bd8 in [0xa2b80, 0xa2c68), preset AU 0xa3418
   in [0xa33c0, 0xa34a8).
   PART 3c (a Theorem Labs lane 2026-10-30 21:23Z): the same value form also covers cf_ro_reads, the five read-only objects the
   refill's class-full report reads (VSNPrintf's formats, the tool name, its 's' / 'u' jump-table words), which lie in
   a non-writable segment, outside every owned extent: no store reaches them (store_ok fails there) and a ROM copy has
   the ROM's value.  This replaces the overlay normal form (memnorm) at every call: memnorm's one consumer was the
   report's read of those bytes (RepArmTcf.rep_img_of_seam). *)
Definition arodata_ok_cf (B : asyms) (mem : word -> option byte) : Prop :=
forall a b, mem (Z_to_bv 64 a) = Some b -> aro_addr_cf a -> ~ Exists (in_zr a) (as_owned_static B) ->
seg_rom segs (Z_to_bv 64 a) = Some b.

(* The consumer: a non-owned covered byte reads as the image's: mbyte reads the overlay byte, which equals seg_rom, or
   else falls back to seg_rom (the same mbyte fallback as ro_byte_read_cf). *)
Lemma arodata_byte_cf : forall B (H : word -> bool) mem a, arodata_ok_cf B mem -> aro_addr_cf a ->
  ~ Exists (in_zr a) (as_owned_static B) -> mbyte segs (mrestrict H mem) a = seg_rom segs (Z_to_bv 64 a).
Proof.
intros B H mem a AR Ha NO. unfold mbyte, mrestrict. destruct (H (Z_to_bv 64 a)); [reflexivity|].
destruct (mem (Z_to_bv 64 a)) as [b|] eqn:E; [|reflexivity].
symmetry. exact (AR a b E Ha NO).
Qed.

(* Part 3c: the report's read-only reads, through arodata (the twin of ro_byte_read_cf). *)
Lemma aro_read_cf : forall B (H : word -> bool) mem a, arodata_ok_cf B mem -> Exists (in_zr a) cf_ro_reads ->
  ~ Exists (in_zr a) (as_owned_static B) -> mbyte segs (mrestrict H mem) a = seg_rom segs (Z_to_bv 64 a).
Proof. intros B H mem a AR Ha NO. exact (arodata_byte_cf B H mem a AR (or_intror Ha) NO). Qed.

(* The keep from a raw frame: a memory that equals mem outside X keeps arodata_ok_cf when X misses every non-owned
   covered byte. *)
Lemma arodata_frame_cf : forall B (X : Z -> Prop) (mem mem' : word -> option byte),
  (forall x : word, ~ X (bv_unsigned x) -> mem' x = mem x) ->
  (forall a, aro_addr_cf a -> ~ Exists (in_zr a) (as_owned_static B) -> 0 <= a < 2 ^ 64 /\ ~ X a) ->
  arodata_ok_cf B mem -> arodata_ok_cf B mem'.
Proof.
intros B X mem mem' F HX AR a b E Ha NO.
destruct (HX a Ha NO) as [Hb NX]. apply (AR a b); [|exact Ha | exact NO].
rewrite <- (F (Z_to_bv 64 a)); [exact E|].
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). exact NX.
Qed.

(* Field round 3 part 3 (MPWrite, 2026-10-30): the geometry behind arodata_frame_cf's second premise, moved here
   VERBATIM from YGcfRodata.v:34-116 (which Requires YGcfMallocCompose, so the free / realloc compositions cannot use
   it where it was).  YGcfRodata keeps relro_not_block_cf (it needs YG0scf) and the seven leaf keeps. *)

(* Every shadow range of aowned starts at a non-negative address, so its shadow is at or above SHADOW_OFF. *)
Lemma relro_shadow_fst_cf : forall B ly S Hp rd r, ARmcf B ly S Hp rd ->
  In r (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]) ->
  0 <= fst r.
Proof.
intros B ly S Hp rd r M Hr. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_syms _ _ _ _ _ M) as SY.
rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|[Hr|[Hr|Hr]]]].
- unfold static_extents in Hr. apply in_app_iff in Hr as [Hr|Hr].
  + pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) r Hr) as A. cbv beta in A. unfold in_app in A.
    destruct A as [A _]. lia.
  + pose proof (lo_top _ LO) as (_ & _ & _ & _ & _ & _ & T7). pose proof (lo_img _ LO) as (J0 & _).
    destruct Hr as [<-|[<-|[]]]; cbn [fst]; unfold kHighMemBeg, kImgLo in *; lia.
- pose proof (amc_placed _ _ _ _ _ M) as [PL _].
  pose proof (proj1 (Forall_forall _ _) PL r Hr) as (_ & A & _). unfold in_app in A. destruct A as [A _]. lia.
- unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
  + pose proof (lo_top _ LO) as (_ & _ & _ & _ & _ & _ & T7). cbn [fst]. unfold kHighMemBeg in T7. lia.
  + pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ SY) r Hr) as A. cbv beta in A. destruct A as [A _]. lia.
- pose proof (proj1 (Forall_forall _ _) (aso_static _ SY) r Hr) as A. cbv beta in A. destruct A as [A _]. lia.
- destruct Hr as [<-|[<-|[]]]; cbn [fst hm_zone lm_zone]; unfold kHighMemBeg; lia.
Qed.

(* A non-owned covered byte (RELRO or a report read, part 3c) is in the image window, outside aowned and outside the
   errbuf extent, at any state the relation holds. *)
Lemma relro_apart_cf : forall B ly S Hp W mem md a, ARcf segs B ly S Hp W mem md -> relro_seg_t segs ->
  aro_addr_cf a -> ~ Exists (in_zr a) (as_owned_static B) ->
  kImgLo <= a < kImgEnd /\ in_zr a (ly_img ly) /\ ~ aowned B ly S a /\ ~ Exists (in_zr a) (xs_cf ly S).
Proof.
intros B ly S Hp W mem md a (M & L & _) [RSR RSD] Ha NO.
pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_img _ LO) as (J0 & J1 & J2 & J3).
(* the segment that holds a: RELRO's, or the read range's *)
assert (SG : exists sg, In sg segs /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)).
{ destruct Ha as [Ha|Ha].
  - destruct RSR as (sg & Hsg & L1 & L2). exists sg. split; [exact Hsg | lia].
  - apply Exists_exists in Ha as (r & Hr & Hin). destruct (proj1 (Forall_forall _ _) RSD r Hr) as (sg & Hsg & L1 & L2).
    exists sg. unfold in_zr in Hin. split; [exact Hsg | lia]. }
destruct SG as (sg & Hsg & L1 & L2).
pose proof (alc_img _ _ _ _ L sg Hsg) as [I1 I2].
assert (IMG : in_zr a (ly_img ly)) by (unfold in_zr; lia).
assert (RNG : kImgLo <= a < kImgEnd) by (unfold in_zr in IMG; lia).
assert (HI : In (ly_img ly) (static_extents ly)).
{ unfold static_extents. apply in_or_app. right. right. left. reflexivity. }
assert (DO : forall e, In e (owned_extents ly) -> ~ in_zr a e).
{ intros e He Hin. pose proof (lo_disj _ LO) as PD.
  pose proof (cfb_pairwise_app zdisjoint (owned_extents ly) [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly]
    e (ly_img ly) PD He ltac:(right; left; reflexivity)) as D.
  unfold zdisjoint, in_zr in *. lia. }
pose proof (amc_placed _ _ _ _ _ M) as [PL PS].
assert (DS : forall e, In e (sec_extents ly S) -> ~ in_zr a e).
{ intros e He Hin. pose proof (cfb_pairwise_app zdisjoint (sec_extents ly S) (static_extents ly) e (ly_img ly) PS He HI) as D.
  unfold zdisjoint, in_zr in *. lia. }
split; [exact RNG|]. split; [exact IMG|]. split.
- intros [[O|[O|[O|[O|O]]]] _].
  + exact (NO O).
  + apply Exists_exists in O as (e & He & Hin). exact (DO e He Hin).
  + apply (DO (ly_C ly, 256)); [unfold owned_extents; cbn; tauto | exact O].
  + apply Exists_exists in O as (e & He & Hin). exact (DS e He Hin).
  + apply Exists_exists in O as (r & Hr & Hin). cbv beta in Hin. pose proof (relro_shadow_fst_cf B ly S Hp _ r M Hr) as F0.
    pose proof (Z.div_pos (fst r) 8 F0 ltac:(lia)). unfold in_zr, shadow_addr, SHADOW_OFF in Hin. cbn [fst snd] in Hin.
    unfold kImgEnd in RNG. lia.
- intros X. apply Exists_exists in X as (e & He & Hin).
  pose proof (proj1 (Forall_forall _ _) (amc_xs_placed _ _ _ _ _ M) e He) as (_ & _ & _ & FD).
  pose proof (proj1 (Forall_forall _ _) FD (ly_img ly) ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HI)) as D.
  unfold zdisjoint, in_zr in *. lia.
Qed.

(* The keep from a raw frame whose exception set X misses every non-owned covered byte, given the relation at the two
   ends. *)
Lemma arodata_keep_cf : forall B ly S Hp W mem md ly' S' Hp' W' mem' md' (X : Z -> Prop),
  ARcf segs B ly S Hp W mem md -> ARcf segs B ly' S' Hp' W' mem' md' -> relro_seg_t segs ->
  (forall a, aro_addr_cf a -> ~ Exists (in_zr a) (as_owned_static B) -> kImgLo <= a < kImgEnd ->
     in_zr a (ly_img ly) -> in_zr a (ly_img ly') -> ~ aowned B ly S a -> ~ aowned B ly' S' a ->
     ~ Exists (in_zr a) (xs_cf ly S) -> ~ Exists (in_zr a) (xs_cf ly' S') -> ~ X a) ->
  (forall x : word, ~ X (bv_unsigned x) -> mem' x = mem x) ->
  arodata_ok_cf B mem -> arodata_ok_cf B mem'.
Proof.
intros B ly S Hp W mem md ly' S' Hp' W' mem' md' X A A' RS HX F.
apply (arodata_frame_cf B X mem mem' F). intros a Ha NO.
destruct (relro_apart_cf B ly S Hp W mem md a A RS Ha NO) as (R & I & NA & NX).
destruct (relro_apart_cf B ly' S' Hp' W' mem' md' a A' RS Ha NO) as (_ & I' & NA' & NX').
split; [unfold kImgLo, kImgEnd in R; lia | exact (HX a Ha NO R I I' NA NA' NX NX')].
Qed.

(* The stack windows sit above kHighMemBeg, errno is apart from every covered range (errno_relro_t). *)
Lemma relro_not_scratch_cf : forall B ly (stk : Z) (regs : bvmap 5 word) a, layout_ok ly -> ly_stk_lo ly + stk <= spZ regs ->
  errno_relro_t B -> aro_addr_cf a -> kImgLo <= a < kImgEnd -> ~ ascratch B stk regs a.
Proof.
intros B ly stk regs a LO STK [ERR ERD] Ha R [Hs|He].
- pose proof (lo_top _ LO) as (_ & _ & _ & _ & _ & _ & T7). unfold kHighMemBeg, kImgEnd in *. lia.
- destruct Ha as [Ha|Ha].
  + lia.
  + apply Exists_exists in Ha as (r & Hr & Hin). pose proof (proj1 (Forall_forall _ _) ERD r Hr) as E.
    unfold in_zr in Hin. cbv beta in E. lia.
Qed.
End RO.

Section J.
Variable segs : list Segment.
Variable B : asyms.
Let code := as_code B.

(* ---------------------------------------------------------------------------- *)
(* The call forms.                                                                *)
Definition acall_pre_cf (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
ARcf segs B ly S Hp W mem md /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + ASTACK <= spZ regs /\ ly_bot ly + ACALL_PREFIX < spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
chain_pre ly (aview segs (w_H W) mem) regs ch /\
qmeter_cf S /\
(* The live-secondary premise. A secondary malloc appends one entry to st_sec_arr, and
   nothing in the allocator bounds the count: it comes from the program, through the
   input. So the call carries it, strictly, and wfc_sec_live survives the +1. *)
Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max /\
(* The errbuf premise, for the same reason: the number of class-full reports comes
   from the program, and each may grow the buffer (ERRB_ROOM, YG00cf.v). *)
ERRB_ROOM S /\
(* The free path's headroom: a free may grow free arrays, which raises abudget_cf
   through prim_committed and its shadow prim_committed / 8, by at most FA_GROW_MAX +
   FA_GROW_MAX / 8 (YG0ncf.v's abudget_cf_fa_grow), so the call carries room for it and
   every such map stays funded (free_fa_grow_funded_cf, whose premise this is): the
   refused branch, a spin, has no LPS step. *)
abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8 <= CF_MAX /\
(* Class kBatchClass keeps cgif's vacuous class-full arm on malloc and free (YG00cf.v),
   so the walks carry its room (batch_room_cf, YG00cf.v). *)
batch_room_cf S /\
(* the driver's hull admission at the call (Main 2026-10-30) *)
cf_hull_ok S /\
(* the read-only bytes (RELRO and the report reads, arodata_ok_cf) at the call (field round 3, Main 2026-10-30: the call
   boundary carries them; each walk keeps them from its entry, YGcfRodata.v; part 3c: memnorm is no longer carried) *)
arodata_ok_cf segs B mem.

Definition acall_post_cf (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
ARcf segs B ly' S' Hp W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).

Definition ecall_pre_cf (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ARcf segs B ly S Hp W mem md /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + ESTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).

(* ---------------------------------------------------------------------------- *)
(* The allocator call forms, FIRST BATCH (fuzz_reply's critical path): malloc,    *)
(* free, strnlen and strndup. cgif's YG0d.v:256-289 and :414-432 with AR -> ARcf, *)
(* Hp threaded unchanged, malloc -> malloc_cf, MALLOC_MAX -> cf_malloc_max.        *)
Definition malloc_leaf_cf (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_cf ASTACK ly S Hp W regs mem md
(* E: the new block, and the error-message buffer before and after (xs_cf, YG0ncf.v). The
   buffer is outside sec_extents, hence not aowned, yet a class-full report writes into it
   and a remap unmaps the old one and maps a new one, so both extents are frame exceptions. *)
(fun a => (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
\/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r) /\
(* the WRAPPER's own NULL-path writes, at its return: Allocate sets the out-of-memory byte
   (val_mem oomb 1 on PNull, c-asan), then SetErrnoOnNull stores ENOMEM; both cells are per
   image (as_errno B, as_oom_byte B). *)
(fst r = PNull -> rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1) /\
(* the errbuf slot stays placed (xs_placed_cf, YG0ncf.v): on a class-full remap the Allocate walk
   proves it once, from the granted KMmapSec answer (grant_ok_na_pin / the LPS placement facts);
   otherwise the slot is unchanged. *)
xs_placed_cf ly' (snd r) /\
(* errno's four bytes are kept on the SUCCESS arm (the raw form of c-asan's alloc_post_e, Allocate's grant leaf);
   the refusal arm stores ENOMEM, above. *)
(fst r <> PNull -> forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(* the frame on the RAW memory (c-asan AllocG.alloc_post's raw clause, AllocG.v:99-101, at this leaf's exception
   set): aview falls back to seg_rom on a segment byte, so only the raw frame keeps presence on image bytes
   (YGcfPres.acall_post_cf_presence_raw). *)
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= bv_unsigned x < sptr_addr B ly' (fst r) + req_size n)
    \/ Exists (in_zr (bv_unsigned x)) (xs_cf ly S ++ xs_cf ly' (snd r))) ->
 mem' x = mem x).

(* The REFUSED arm of malloc, for preset's allocator walks (S1, K0) and c-asan's realloc.
   Same argument list as malloc_leaf_cf. On a realized path every kernel ask is granted
   (amreal, YG0d.v:73-92, forces bit = 1 off the spin branch), so a PNull result is the
   class-full arm and nothing else: map_more_user_cf refused class (chunk_class n), set its
   exhausted byte, and added no chunk. The wrapper then stores errno = ENOMEM (12) and the
   allocator's out-of-memory byte := 1; both cells are per image (as_errno B,
   as_oom_byte B), never literals. This is the fact malloc_cf_success_of_room refutes. *)
Definition malloc_cf_null_post (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
fst r = PNull /\
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_cf ASTACK ly S Hp W regs mem md (fun a => Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 0 /\
qtight (snd r) /\
blocks (snd r) = blocks S /\ st_chunks (snd r) = st_chunks S /\
rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\
aview segs (w_H W') mem' (as_oom_byte B) = Some 1 /\
from_primary n = true /\ exh_mem_cf (snd r) (chunk_class n) = true /\
(* the raw frame, at the refusal's exception set (malloc_leaf_cf's at PNull) *)
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly S ++ xs_cf ly' (snd r)) ->
 mem' x = mem x).

Definition amalloc_realizes_cf : Prop :=
forall ly S Hp W regs mem md n ch,
acall_pre_cf ly S Hp W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly (pc_malloc_ra0 code) regs ch) S ->
amreal segs (malloc_cf n (call_trace ly (pc_malloc_ra0 code) regs ch) S) W
(cfg_at segs (pc_wrap_malloc code) regs mem md)
(malloc_leaf_cf ly S Hp W regs mem md n).

(* ---------------------------------------------------------------------------- *)
(* The malloc interceptor's BODY, the contract the allocating string entries use   *)
(* (a Theorem Labs lane's agreed text of 2026-10-30 09:02Z;                                   *)
(* copied from fuzz_command's RtDDefs.v, a working branch 8aaeb29ab7b2, with _cf      *)
(* names and this file's cf forms; its universe premise is P'''s `admits`, as       *)
(* amalloc_realizes_cf's).                                                          *)

(* The allocating string entries call the malloc path below the trampoline that
   amalloc_realizes_cf is stated at: strndup (reply A 0x427b4) calls the malloc
   interceptor's body (pc_malloc code, A 0x53fc4), which builds the stack trace itself
   (pc0 = pc_malloc_ra0 code). Window: astrndup_realizes_cf gives ASTACK below the entry's
   sp; the entry's own frame is 2,160 bytes (STRNDUP_FRAME_CF), so at the inner call
   ASTACK - 2,160 = 14,224 bytes are known present. The body contract is therefore stated
   at MALLOC_IN_STK_CF = 14,208 (16-aligned), not at ASTACK; fuzz_command measured the depth
   of the malloc path below the body's entry at 5,584 bytes on the same bytes (bytecmp:
   ___interceptor_malloc EQUAL-mod-pcrel). *)
Definition MALLOC_IN_STK_CF : Z := 14208.
(* The sp drop from the malloc body's entry to ALLOCATE's entry, the max over the units,
   16-aligned: 2,144 at every unit measured. It is the body's own frame (2,128) PLUS the
   frame of the function that calls Allocate: at cgif the body 0x52b34 drops 2,032 + 96
   and jumps to 0x52c58, whose `jal 0x314f4` at 0x52c64 enters the function that calls
   Allocate, and that function drops 16 more before its `jal 0x31550` at 0x3151c
   (2,128 + 16 = 2,144; measured on cgif_file_fuzzer.asan-ubsan, the CfImg_cgif image);
   reply A / B are 2,128 + asan_malloc's 16 before its `jal Allocate` at 0x31ba4 / 0x31bfc,
   and preset A' is 2,144 measured. *)
Definition MALLOC_BODY_FRAME_CF : Z := 2144.

(* acall_pre_cf with the window [stk] for ASTACK and the stack-bottom premise strengthened by
   MALLOC_BODY_FRAME_CF, so that the body's own callee (Allocate) still has ly_bot ly < its sp:
   the caller of the body has the plain premise for its OWN stack pointer, which is 2,160 bytes
   higher for strndup. *)
Definition acall_pre_cf_w (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
ARcf segs B ly S Hp W mem md /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + stk <= spZ regs /\ ly_bot ly + MALLOC_BODY_FRAME_CF < spZ regs /\
spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
chain_pre ly (aview segs (w_H W) mem) regs ch /\
qmeter_cf S /\
Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max /\
ERRB_ROOM S /\
abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8 <= CF_MAX /\
batch_room_cf S /\
cf_hull_ok S /\
arodata_ok_cf segs B mem.

(* No inner trace: with ly_bot ly + MALLOC_BODY_FRAME_CF < spZ regs in the pre, the unwinder's
   bottom case is unreachable at the body, so the trace is call_trace at the body's regs. *)
(* malloc_leaf_cf with the window [stk] for ASTACK (both places: acall_post_cf and the raw
   frame's ascratch). *)
Definition malloc_leaf_cf_w (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_cf stk ly S Hp W regs mem md
(fun a => (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
\/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r) /\
(fst r = PNull -> rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1) /\
xs_placed_cf ly' (snd r) /\
(fst r <> PNull -> forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B stk regs (bv_unsigned x) ->
 ~ ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= bv_unsigned x < sptr_addr B ly' (fst r) + req_size n)
    \/ Exists (in_zr (bv_unsigned x)) (xs_cf ly S ++ xs_cf ly' (snd r))) ->
 mem' x = mem x).

(* The malloc interceptor's body, entered by a call (reply A strndup 0x427b4): amalloc_realizes_cf
   at (pc_malloc code) with the unwinder pc [pc_ra0] and the window MALLOC_IN_STK_CF. strndup passes
   pc_ra0 := pc_malloc_ra0 code. *)
Definition amalloc_body_realizes_cf (pc_ra0 : Z) : Prop :=
forall ly S Hp W regs mem md n ch,
acall_pre_cf_w MALLOC_IN_STK_CF ly S Hp W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly pc_ra0 regs ch) S ->
amreal segs (malloc_cf n (call_trace ly pc_ra0 regs ch) S) W
(cfg_at segs (pc_malloc code) regs mem md)
(malloc_leaf_cf_w MALLOC_IN_STK_CF ly S Hp W regs mem md n).

(* free is cgif's free unchanged (free_cf, YGcfNames.v). The leaf's post keeps Hp: the
   harness unpoisons a hidden head BEFORE it frees (its disown step), so a freed base
   is never in Hp at the call; am_hp_live then forces it out of Hp after. *)
Definition free_leaf_cf (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_cf ASTACK ly S Hp W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
qtight (snd r) /\
(* errno's four bytes are kept (the raw form of c-asan's dealloc_post_raw_e: every Deallocate leaf) *)
(forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(* the frame on the RAW memory (c-asan DeallocG.dealloc_post_raw's clause, at free's exception set) *)
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) ->
 mem' x = mem x).

Definition afree_realizes_cf : Prop :=
forall ly S Hp W regs mem md p n ch,
acall_pre_cf ly S Hp W regs mem md ch ->
(p = PNull \/ In (p, n) (blocks S)) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
admits (as_universe B) (call_trace ly (pc_free_ra0 code) regs ch) S ->
amreal segs (free_cf p (call_trace ly (pc_free_ra0 code) regs ch) S) W
(cfg_at segs (pc_wrap_free code) regs mem md)
(free_leaf_cf ly S Hp W regs mem md p n).

(* strnlen: cgif's YG0d.v:414-432 with AR -> ARcf via ecall_pre_cf. *)
Definition astrnlen_realizes_cf (pc : Z) : Prop :=
forall ly S Hp W regs mem md x n k,
ecall_pre_cf ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x n 0 k ->
src_ok segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
rom_view segs W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARcf segs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* strndup: fuzz_reply's drain calls it with 15 <= n <= 5,999, blocks of 16 .. 6,000 B,
   class 1 to class 24, never secondary. Its shape is strnlen, then malloc of k + 1, then
   a copy and a terminating NUL, so it is stated as the malloc_cf tree on k + 1 landing
   in malloc_leaf_cf, strengthened by the copy on success. *)
Definition strndup_leaf_cf (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (x k : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_cf ASTACK ly S Hp W regs mem md
(fun a => (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size (k + 1))
\/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r) /\
(fst r <> PNull ->
(forall i, 0 <= i < k -> aview segs (w_H W') mem' (sptr_addr B ly' (fst r) + i) = aview segs (w_H W) mem (x + i)) /\
aview segs (w_H W') mem' (sptr_addr B ly' (fst r) + k) = Some 0) /\
(fst r = PNull -> rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1) /\
(* strndup's internal malloc can take the class-full arm in any unit that fills a class *)
xs_placed_cf ly' (snd r) /\
(* malloc_leaf_cf's last two conjuncts at request k + 1: errno kept on success (raw; strnlen, a granted
   Allocate and the copy write no errno), the raw frame at this leaf's exception set *)
(fst r <> PNull -> forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall w : word, ~ aowned B ly S (bv_unsigned w) -> ~ aowned B ly' (snd r) (bv_unsigned w) ->
 ~ ascratch B ASTACK regs (bv_unsigned w) ->
 ~ ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= bv_unsigned w < sptr_addr B ly' (fst r) + req_size (k + 1))
    \/ Exists (in_zr (bv_unsigned w)) (xs_cf ly S ++ xs_cf ly' (snd r))) ->
 mem' w = mem w).

(* The granules of a hidden head: hd_skip Hp p is cf_head when p is hidden, 0 otherwise.
   It stands here because the strndup form below names it (its other users are the AR laws). *)
Definition hd_skip (Hp : list Z) (p : Z) : Z := if existsb (Z.eqb p) Hp then cf_head else 0.

(* The trace malloc records when the strndup interceptor calls the malloc body itself (A 0x427b4
   `jal 53fc4`, not the trampoline): the malloc frame's first bp (UnwindFast) is the entry sp less
   the interceptor's frame, 2,160 B (`addi sp,sp,-2032; addi sp,sp,-128`, the same in every image
   measured: fuzz_reply A / B, fuzz_command A / B), and its first return address is mid, the
   interceptor's return from that call (reply A 0x427b8, reply B 0x42810). The unwinder records only
   [pc0] when that bp is at or below the stack bottom, at or above the stack top less 16, or the
   first return address is below a page; else mid, then the caller's chain under call_trace's stop
   rules. This is fuzz_command's adup_trace (a working branch 8aaeb29ab7b2, lib/A/Rt/RtAlloc.v)
   verbatim with STRNDUP_FRAME renamed; its RtDStrndupA.v snd_trace_eq proves the body records
   exactly it. *)
Definition STRNDUP_FRAME_CF : Z := 2160.
Definition adup_trace_cf (ly : alayout) (pc0 mid : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list Z :=
if (spZ regs - STRNDUP_FRAME_CF <=? ly_bot ly) || (ly_top ly - 16 <=? spZ regs - STRNDUP_FRAME_CF) || (mid <? 4096)
then [pc0]
else if frame0_ok ly regs
then unwind_of_chain pc0 ((0, mid, 0) :: (spZ regs, raZ regs, s0Z regs) :: ch)
else unwind_of_chain pc0 [(0, mid, 0)].

(* mid: the image's strndup-malloc return, passed by the consumer (reply A 0x427b8, reply B 0x42810). *)
Definition astrndup_realizes_cf (pc mid : Z) : Prop :=
forall ly S Hp W regs mem md x n k ch,
acall_pre_cf ly S Hp W regs mem md ch ->
(* room for the interceptor's own frame and the malloc body's, so the body's pre holds at the inner call *)
ly_bot ly + STRNDUP_FRAME_CF + MALLOC_BODY_FRAME_CF < spZ regs ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k <= n -> k + 1 < cf_malloc_max -> blocks_bytes S + (k + 1) <= LIVE_MAX ->
first_byte segs W mem x n 0 k ->
src_ok segs W regs mem x (Z.min n (k + 1)) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (Z.min n (k + 1)) ->
(* the source lies in a live block, whose shadow the post-malloc check reads (AR_shadow_law_cf at the post state) *)
(exists p m, In (p, m) (ablocks B ly S) /\ p + hd_skip Hp p <= x /\ x + Z.min n (k + 1) <= p + req_size m) ->
admits (as_universe B) (adup_trace_cf ly (pc_malloc_ra0 code) mid regs ch) S ->
amreal segs (malloc_cf (k + 1) (adup_trace_cf ly (pc_malloc_ra0 code) mid regs ch) S) W
(cfg_at segs pc regs mem md)
(strndup_leaf_cf ly S Hp W regs mem md x k).

(* ---------------------------------------------------------------------------- *)
(* The frame-area (fake stack) forms, ADOPTED verbatim from h-asan-init-2's ArT   *)
(* (origin/cold/h-asan-init-2-art 47e01d3478d5, YG0tcf.v:33-83), so there is ONE   *)
(* definition; checked there by eq_refl against PresetFrameClasses' frozen        *)
(* FCiface.v at ARx := ARcf segs B. They live here, not in YGcfNames.v, because    *)
(* they mention ARcf and ecall_pre_cf, which import YGcfNames (a cycle otherwise). *)
(* The class set is NOT in them: it is cf_fs_classes in the API record.            *)
Definition astack_malloc_realizes_cf (cid : Z) : Prop :=
forall ly S Hp W regs mem md pos S',
ecall_pre_cf ly S Hp W regs mem md ->
count_cid cid (frames S) < fs_frames cid ->
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
SRr segs W (cfg_at segs (pc_stack_malloc (as_code B) cid) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARcf segs B ly S' Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (frame_addr ly cid pos) /\
zero_shadow (aview segs (w_H W) mem') SHADOW_OFF (frame_addr ly cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem') (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* YG0d.v:313-321, AR -> ARcf, Hp after S, Hp unchanged. *)
Definition astack_free_law_cf : Prop :=
forall ly S Hp W mem md mem' md' cid pos,
ARcf segs B ly S Hp W mem md -> In (cid, pos) (frames S) ->
aview segs (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARcf segs B ly (stack_free_state cid pos S) Hp W mem' md'.

(* YG0t.v:577-589 (= FCiface.v astack_malloc_law_x), AR -> ARcf, Hp after S, Hp unchanged. *)
Definition astack_malloc_law_cf : Prop := forall ly S Hp W mem md mem' md' cid pos hint',
ARcf segs B ly S Hp W mem md -> 0 <= cid <= 10 ->
fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S))) = Some (pos, hint') ->
let S' := set_fs (mkFS (zupd cid hint' (fs_hint (st_fs S))) ((cid, pos) :: fs_live (st_fs S))) S in
(forall k, (k < 8)%nat -> aview segs (w_H W) mem' (ly_F ly + 8 * cid + Z.of_nat k) = Some (le_byte hint' 8 k)) ->
aview segs (w_H W) mem' (flag_addr ly cid pos) = Some 1 ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> ~ (ly_F ly + 8 * cid <= a < ly_F ly + 8 * cid + 8) -> a <> flag_addr ly cid pos ->
~ in_zr a (frame_addr ly cid pos, fs_frame_bytes cid) -> ~ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARcf segs B ly S' Hp W mem' md'.

(* ---------------------------------------------------------------------------- *)
(* The fourteen AR laws (YG0d.v:435-523) over ARcf. Thirteen are cgif's statement *)
(* with AR -> ARcf and an Hp binder. AR_shadow_law_cf is the one that CHANGES: a    *)
(* hidden head [p, p + cf_head) is poisoned 0xf7, so block_shadow holds only past   *)
(* it, exactly when p is in Hp. With Hp = [] the head term is 0 and the statement   *)
(* is cgif's, word for word.                                                         *)
(* hd_skip stands above, with the strndup forms that use it. *)

Definition AR_blocks_law_cf : Prop :=
forall ly S Hp W mem md p n,
ARcf segs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\
0 <= n < cf_malloc_max.
Definition AR_shadow_law_cf : Prop :=
forall ly S Hp W mem md p n,
ARcf segs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
block_shadow (aview segs (w_H W) mem) SHADOW_OFF (p + hd_skip Hp p) (req_size n - hd_skip Hp p) /\
shadow_hull_vis (aview segs (w_H W) mem) p (req_size n).
Definition AR_zshadow_law_cf : Prop :=
forall ly S Hp W mem md r,
ARcf segs B ly S Hp W mem md -> In r (zero_shadow_ranges B ly) ->
zero_shadow (aview segs (w_H W) mem) SHADOW_OFF (fst r) (snd r).
Definition AR_frame_law_cf : Prop :=
forall ly S Hp W mem md mem' md',
ARcf segs B ly S Hp W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARcf segs B ly S Hp W mem' md'.
Definition AR_frames_law_cf : Prop :=
forall ly S Hp W mem md cid pos,
ARcf segs B ly S Hp W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos mod 32 = 0 /\ in_app (frame_addr ly cid pos) (fs_frame_bytes cid) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
(forall i, 0 <= i < fs_frame_bytes cid / 8 ->
apresent (w_H W) mem (shadow_addr (frame_addr ly cid pos) + i) /\
~ aowned B ly S (shadow_addr (frame_addr ly cid pos) + i)).
Definition AR_flag_law_cf : Prop :=
forall ly S Hp (W : world segs) mem md cid pos,
ARcf segs B ly S Hp W mem md -> In (cid, pos) (frames S) ->
apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned B ly S (flag_addr ly cid pos) /\
in_app (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < alloc_ceiling.
Definition AR_const_law_cf : Prop :=
forall ly S Hp W mem md,
ARcf segs B ly S Hp W mem md ->
rdword (aview segs (w_H W) mem) (as_shadow_cell B) = Some SHADOW_OFF /\
rd32 (aview segs (w_H W) mem) (as_uar_cell B) 1 /\
rdword (aview segs (w_H W) mem) (as_got_shadow B) = Some (as_shadow_cell B) /\
rdword (aview segs (w_H W) mem) (as_got_uar B) = Some (as_uar_cell B).
Definition AR_stack_law_cf : Prop :=
forall ly S Hp W mem md a,
ARcf segs B ly S Hp W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly S a.
Definition AR_owned_low_law_cf : Prop :=
forall ly S Hp W mem md a, ARcf segs B ly S Hp W mem md -> aowned B ly S a -> 0 <= a < alloc_ceiling.
Definition AR_owned_image_law_cf : Prop :=
forall ly S Hp W mem md a, ARcf segs B ly S Hp W mem md -> in_img segs a ->
(aowned B ly S a <-> Exists (in_zr a) (as_owned_static B)).
Definition AR_sep_law_cf : Prop :=
forall ly S Hp W mem md, ARcf segs B ly S Hp W mem md ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)
++ map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) (frames S)) /\
Forall (fun f => 4096 <= frame_addr ly (fst f) (snd f) /\ frame_addr ly (fst f) (snd f) + fs_frame_bytes (fst f) <= alloc_ceiling) (frames S).
Definition AR_layout_law_cf : Prop :=
forall ly S Hp W mem md ly',
ARcf segs B ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly' ->
ablocks B ly' S = ablocks B ly S /\ (forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) /\
(forall a, aowned B ly' S a <-> aowned B ly S a).
Definition AR_wle_law_cf : Prop :=
forall ly S Hp W W' mem md,
ARcf segs B ly S Hp W mem md -> wle W W' -> (forall i, In i (w_A W) -> In i (w_A W')) ->
A_bytes (w_A W') <= abudget_cf S -> ARcf segs B ly S Hp W' mem md.
Definition AR_client_img_law_cf : Prop :=
forall ly S Hp W mem md a, ARcf segs B ly S Hp W mem md ->
((exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) \/
(exists cid pos, In (cid, pos) (frames S) /\ a = flag_addr ly cid pos)) ->
~ in_zr a (ly_img ly) /\ ~ in_img segs a.

(* The law AR_laws_cf lacked, VERBATIM from h-rw-man-5's YGcfHp.v:63-76 (29c8b46b1cef):
   cgif's AR_frame_law (YG0d.v:445) with two changes: the owned bytes that may change are
   the hidden-head shadow bytes of Hp and Hp', and each such byte that shadow_ok_cf governs
   takes the value shadow_ok_cf at Hp' demands; the result is ARcf at Hp', given that every
   base in Hp' is live. *)
Definition AR_head_frame_law_cf : Prop :=
forall ly S Hp Hp' W mem md mem' md',
ARcf segs B ly S Hp W mem md ->
Forall (hp_live_cf B ly S) Hp' ->
(forall g v, g mod 8 = 0 -> ashadow B ly S g = Some v -> in_head Hp g = true \/ in_head Hp' g = true ->
aview segs (w_H W) mem' (shadow_addr g) = Some (if in_head Hp' g then shUserPoison else v)) ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> ~ hd_shadow (Hp ++ Hp') a ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARcf segs B ly S Hp' W mem' md'.

Record AR_laws_cf : Prop := {
alc_blocks : AR_blocks_law_cf;
alc_shadow : AR_shadow_law_cf;
alc_zshadow : AR_zshadow_law_cf;
alc_frame : AR_frame_law_cf;
alc_frames : AR_frames_law_cf;
alc_flag : AR_flag_law_cf;
alc_const : AR_const_law_cf;
alc_stack : AR_stack_law_cf;
alc_wle : AR_wle_law_cf;
alc_layout : AR_layout_law_cf;
alc_owned_low : AR_owned_low_law_cf;
alc_owned_image : AR_owned_image_law_cf;
alc_sep : AR_sep_law_cf;
alc_client_img : AR_client_img_law_cf;
(* the 15th law: the frame law with Hp moving, h-rw-man-5's statement (YGcfHp.v:63 at
   29c8b46b1cef), defined above in this file; proved in h-asan-init-2's YG0tcf.v. *)
alc_head_frame : AR_head_frame_law_cf
}.

(* With Hp = [] the head term vanishes, so the cf shadow law IS cgif's. *)
Lemma hd_skip_nil : forall p, hd_skip [] p = 0.
Proof. reflexivity. Qed.

End J.
End G.
