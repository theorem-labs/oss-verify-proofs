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
(* The image-independent definitions that the ASan-level contracts of reac-pw/fuzz_rate's program functions
   (lib/A/RtPgCSpec.v) are stated over. No image module is Required: every address is an argument.

   Why the float state appears here: rate's program changes float registers. LLVMFuzzerTestOneInput loads fa0
   (flw, before the pod_nearest call); reac_rate_prop_parse writes fa3, fa4 and fa5 (fld, fcvt.d.s, fadd.d) and
   accrues fflags; pod_nearest writes fa5 (fmv.w.x) and accrues fflags; reac_rate_drivable_csv's snprintf wrapper
   (the musl printf core under it) may write fa0. A configuration of this semantics carries the float state in mkst,
   so a function that changes it returns at some other float state fx'. rt_fxk names what such a function keeps:
   every float register outside a given list, and a zero rounding mode (each of these functions runs with a zero
   rounding mode and writes no rounding mode). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor Model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition in_roP (segs : list Segment) (rlo rhi : Z) (a : Z) : Prop :=
(exists s, In s segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
\/ (rlo <= a < rhi).
Definition arodata_okP (segs : list Segment) (rlo rhi : Z) (B : asyms) (rd : reader) : Prop :=
forall a, in_roP segs rlo rhi a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Class ro_below_ofl (segs : list Segment) (rlo rhi : Z) {SK : YI16.sink_head} : Prop :=
ro_below_ofl_at : forall a, in_roP segs rlo rhi a -> a < YI16.sk_ofl_head.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variables rlo rhi : Z.
Hypothesis relro_img : forall a, rlo <= a < rhi -> in_img segs a.
Context {RO : ro_below_ofl segs rlo rhi}.
Lemma ro_spares : forall FP a, in_roP segs rlo rhi a -> fp_spares FP a.
Proof. intros FP a Hro. apply fp_spares_below. exact (@ro_below_ofl_at segs rlo rhi SK RO a Hro). Qed.
Lemma arodata_ok_journalP : forall B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> arodata_okP segs rlo rhi B (aview segs (w_H W') mem').
Proof.
intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (ro_spares FP a Hro)].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
exact (relro_img a Hgot).
Qed.
End e.
End d.

(* ======================================== rate's shared quantities ======================================== *)
(* pp->len after pod_build of the bytes after the 7-byte header: the plain contract's rate_len
   (lib/Prog/LLVMFuzzerTestOneInput_c.v), the length of the pod that LLVMFuzzerTestOneInput allocates. *)
Definition rt_len (rest : list byte) : Z := Z.of_nat (length (Model.buf (fst (Model.pod_build rest)))).
(* buf's malloc request and block length, buflen ? buflen : 1: the plain contract's rate_bl. *)
Definition rt_bl (buflen : Z) : Z := buflen + (if buflen =? 0 then 1 else 0).

(* The text reac_rate_drivable_csv passes to snprintf as its format ("%s%d", reac_rate_cfg.c:60) and its two
   separators ("," and ""), as byte values without the NUL. *)
Definition STR_FMT_SD : list Z := [37; 115; 37; 100].
Definition STR_COMMA : list Z := [44].
Definition STR_EMPTY : list Z := [].

(* The float state a function returns at: every float register outside ks as at entry (Sem.reg_get, so f0 is
   covered too), and a zero rounding mode. *)
Definition rt_fxk (ks : list Z) (fx fx' : YK11.FPState) : Prop :=
(forall k : bv 5, ~ In (bv_unsigned k) ks -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
YK0o.frm_zero (@fp_csr fx').

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* A NUL-terminated string s at a, as the strcmp wrapper's contract reads it: its bytes and the NUL, each nonzero
   before the NUL; it lies in the image, low enough for the shadow map, with its len + 1 bytes marked usable and
   their shadow bytes readable. *)
Definition rt_cstr (H : word -> bool) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
(forall i, 0 <= i < Z.of_nat (length s) -> aview segs H mem (a + i) = Some (nth (Z.to_nat i) s 0)) /\
aview segs H mem (a + Z.of_nat (length s)) = Some 0 /\
Forall (fun b => 0 < b < 256) s /\
0 < a /\ a + Z.of_nat (length s) + 1 <= 2 ^ 63 /\
(forall i, 0 <= i <= Z.of_nat (length s) -> in_img segs (a + i)) /\
amem_range a (Z.of_nat (length s) + 1) /\
range_addressable (aview segs H mem) SHADOW_OFF a (Z.of_nat (length s) + 1) /\
shadow_hull_vis (aview segs H mem) a (Z.of_nat (length s) + 1).
(* 8-byte cells with their values that the code loads with ld: the parse's doubles (no shadow check) and the
   harness's pointer tables (after a shadow check, whose bytes hi_globs marks usable). *)
Definition rt_ro_cells (H : word -> bool) (mem : word -> option byte) (cs : list (Z * Z)) : Prop :=
Forall (fun c => val_mem segs (mrestrict H mem) (fst c) 8 (snd c)) cs.
(* A table of 4-byte values vs at t, read by instrumented 4-byte loads (closed_list in check_list and check_csv,
   ordered in reac_rate_drivable_csv): in the image, 4-aligned, each value's bytes, every byte marked usable. *)
Definition rt_i32tab (H : word -> bool) (mem : word -> option byte) (t : Z) (vs : list Z) : Prop :=
(forall i, 0 <= i < 4 * Z.of_nat (length vs) -> in_img segs (t + i)) /\
t mod 4 = 0 /\
(forall i, 0 <= i < Z.of_nat (length vs) -> val_mem segs (mrestrict H mem) (t + 4 * i) 4 (nth (Z.to_nat i) vs 0)) /\
range_addressable (aview segs H mem) SHADOW_OFF t (4 * Z.of_nat (length vs)).
(* A table of n 8-byte values vs at t, read by instrumented 8-byte loads (reac_rate_refuse_code's codes, check_code's
   switch table): in the image, 8-aligned, each value's bytes, every byte marked usable. *)
Definition rt_u64tab (H : word -> bool) (mem : word -> option byte) (t : Z) (vs : list Z) : Prop :=
(forall i, 0 <= i < 8 * Z.of_nat (length vs) -> in_img segs (t + i)) /\
t mod 8 = 0 /\ Forall (fun v => 0 <= v < 2 ^ 64) vs /\
(forall i, 0 <= i < Z.of_nat (length vs) -> val_mem segs (mrestrict H mem) (t + 8 * i) 8 (nth (Z.to_nat i) vs 0)) /\
range_addressable (aview segs H mem) SHADOW_OFF t (8 * Z.of_nat (length vs)).
End s.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
(* The read-only image as every call keeps it (the released fuzz_boxreg lib/A/Rt/SnprintfDef.v asn_rom_kept): a byte
   of a read-only segment that is neither an owned static nor an errno byte reads as the image's byte. An ajournal
   keeps exactly these bytes (YCbq.v ajournal), so the fact survives a call whose post lets runtime-owned bytes
   change; the musl printf core under the snprintf wrapper reads its constants through it. *)
Definition rt_rom_kept (W : world segs) (mem : word -> option byte) : Prop :=
forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Lemma rt_rom_kept_of_rom_view : forall W mem, rom_view segs W mem -> rt_rom_kept W mem.
Proof. intros W mem H a Ha _ _. exact (H a Ha). Qed.
Lemma rt_rom_kept_of_aro : forall (W : world segs) mem rlo rhi,
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> rt_rom_kept W mem.
Proof.
intros W mem rlo rhi H a Ha Ho He. apply (H a); [| exact Ho | exact He].
left. destruct Ha as (sg & Hs & Hw & Hr). exists sg. auto.
Qed.
End k.

(* Bounds that a block or a side-stack frame live in an AR state has (YG0d.v AR_blocks_law, AR_sep_law): image B's
   undefined-behaviour checks ask them of the harness's blocks and of a callee's frame (no wrap of p + n, of
   F + size). *)
Section ar. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Lemma rt_block_bounds : forall ly S W mem md p n, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
0 < p /\ p mod 16 = 0 /\ p + n <= 2 ^ 63.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (H16 & H4096 & Hc & _).
pose proof (@YM05.alloc_ceiling_lt rc) as Hc0. unfold req_size in Hc.
destruct (Z.eqb_spec n 0); lia.
Qed.
Lemma rt_frame_bounds : forall ly S W mem md cid pos, AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
0 < frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= 2 ^ 63.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [_ Hf].
rewrite Forall_forall in Hf. specialize (Hf (cid, pos) Hin). cbn [fst snd] in Hf.
pose proof (@YM05.alloc_ceiling_lt rc) as Hc0. lia.
Qed.
End ar.

(* =============== the image's registered globals after a call that lets runtime-owned bytes change ===============
   A malloc, a free, a side-stack frame's allocation (YG0d.v astack_malloc_realizes keeps only the bytes owned at
   neither state) and the two contracts that end in rt_cpost_o may change any byte the runtime owns, and every shadow
   byte of the image is runtime-owned (the lm_zone disjunct of aowned, YG0n.v aowned). So a walk cannot carry the
   shadow conjuncts of rt_cstr / rt_i32tab / rt_u64tab across such a call. The released units take three facts of the
   runtime's symbol record B for it (fuzz_disco lib/A/DiscoAsanT.v H_RO_stmt over lib/A/Prog/DiscoRo.v img_shadow_vis,
   globs_marked and ro_unowned; fuzz_boxreg lib/A/Prog/BoxRo.v img_shadow_vis and globs_marked), stated here with the
   image's range and its registered globals as parameters:
   - rt_img_shadow_vis lo hi: in every AR state every shadow byte of [lo, hi) is readable (the shadow-hull conjuncts);
   - rt_globs_marked G: in every AR state each registered global (q, sz) of G has the runtime's shadow (YG0v.v
     block_shadow: 0 for each full granule, sz mod 8 for a last partial one), so its bytes are marked usable;
   - rt_ro_unowned lo n: no byte of [lo, lo + n) is an owned static or an errno byte of B (no state).
   The bytes of a global are NOT an invariant of AR: AR states nothing of the memory at a read-only address that is no
   owned static, so a walk keeps them from the state before the call. Such a byte is owned in no AR state
   (YG0d.v AR_owned_image_law; rt_img_unowned below), so every call above keeps it (the frame law's clause for bytes
   owned at neither state; rt_cpost_o's E is the owned set at the call). rt_cstr_at, rt_i32tab_at and rt_u64tab_at
   rebuild the three predicates at the state after the call from the ones before it and the kept bytes; at a state
   with arodata_okP the bytes come from the image instead (rt_bytes_of_ro, rt_val_of_ro).
   An image discharges the three facts at its own symbol record by computation: rt_img_shadow_vis and
   rt_globs_marked from AR's constant shadow cells (am_const) and zero-shadow ranges (am_zshadow), rt_ro_unowned from
   B's owned-static list and errno cell: fuzz_disco lib/A/Prog/DiscoRoClose.v disco_img_shadow_vis,
   disco_globs_marked, disco_ro_unowned_tfib; fuzz_boxreg lib/A/Prog/BoxGShadow.v img_shadow_vis_box,
   globs_marked_box. *)
(* A pair (a, sz) with len <= sz found by a boolean search is in the list. *)
Lemma rt_glob_of_b : forall (a len : Z) (l : list (Z * Z)),
  existsb (fun g => (fst g =? a) && (len <=? snd g)) l = true -> exists sz, In (a, sz) l /\ len <= sz.
Proof.
intros a len l E. apply existsb_exists in E. destruct E as ((q, sz) & Hg & Hq). cbn [fst snd] in Hq.
apply andb_true_iff in Hq. destruct Hq as [Hq Hsz]. apply Z.eqb_eq in Hq. subst q. apply Z.leb_le in Hsz.
exists sz. split; [exact Hg | exact Hsz].
Qed.
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Definition rt_img_shadow_vis (lo hi : Z) : Prop :=
forall ly S (W : world segs) mem md a,
AR segs B ly S W mem md -> lo <= a < hi -> aview segs (w_H W) mem (shadow_addr a) <> None.
Definition rt_globs_marked (G : list (Z * Z)) : Prop :=
forall ly S (W : world segs) mem md q sz,
In (q, sz) G -> AR segs B ly S W mem md -> block_shadow (aview segs (w_H W) mem) SHADOW_OFF q sz.
Definition rt_ro_unowned (lo n : Z) : Prop :=
forall a, lo <= a < lo + n -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis LAWS : AR_laws segs B.
(* An image byte that is no owned static is owned in no AR state. *)
Lemma rt_img_unowned : forall ly S (W : world segs) mem md a, AR segs B ly S W mem md ->
in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof.
intros ly S W mem md a HAR Hi Ho Hw. apply Ho.
exact (proj1 (al_owned_image _ _ LAWS ly S W mem md a HAR Hi) Hw).
Qed.
(* The bytes of a registered global are marked usable (BoxRo.v ro_usable_glob). *)
Lemma rt_glob_usable : forall G ly S (W : world segs) mem md q sz a n,
rt_globs_marked G -> In (q, sz) G -> AR segs B ly S W mem md -> q <= a -> a + n <= q + sz ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros G ly S W mem md q sz a n HG Hin HAR H1 H2.
exact (block_shadow_range (aview segs (w_H W) mem) SHADOW_OFF q sz a n (HG ly S W mem md q sz Hin HAR) H1 H2).
Qed.
(* The shadow hull of a range 64 bytes inside the image's range is readable (BoxRo.v ro_hull). *)
Lemma rt_img_hull : forall lo hi ly S (W : world segs) mem md a n,
rt_img_shadow_vis lo hi -> AR segs B ly S W mem md -> 0 < n -> lo + 64 <= a -> a + n + 64 <= hi ->
shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
intros lo hi ly S W mem md a n HV HAR Hn Hlo Hhi s Hs.
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
assert (Hxlo : lo <= x) by (unfold x; lia).
assert (Hxhi : x < hi) by (unfold x; lia).
rewrite <- Hx. exact (HV ly S W mem md x HAR (conj Hxlo Hxhi)).
Qed.
(* Both, in the shape the walks consume (BoxRo.v / DiscoRo.v ro_read_ok_glob). *)
Lemma rt_glob_read_ok : forall G lo hi ly S (W : world segs) mem md q sz a n,
rt_globs_marked G -> In (q, sz) G -> rt_img_shadow_vis lo hi -> AR segs B ly S W mem md ->
q <= a -> a + n <= q + sz -> 0 < n -> lo + 64 <= a -> a + n + 64 <= hi ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
intros G lo hi ly S W mem md q sz a n HG Hin HV HAR H1 H2 Hn Hlo Hhi. split.
- exact (rt_glob_usable G ly S W mem md q sz a n HG Hin HAR H1 H2).
- exact (rt_img_hull lo hi ly S W mem md a n HV HAR Hn Hlo Hhi).
Qed.
(* Two reads that agree as values agree as bytes. *)
Lemma rt_aview_mbyte : forall (H H' : word -> bool) (m m' : word -> option byte) a,
aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte segs (mrestrict H' m') a) as [b'|]; destruct (mbyte segs (mrestrict H m) a) as [b|];
cbn [option_map] in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
(* A string that is a registered global 64 bytes inside the image's range, at an AR state whose bytes there are the
   ones of a state where it held: it holds again. *)
Lemma rt_cstr_at : forall G lo hi ly S (W : world segs) mem md (H0 : word -> bool) mem0 a s sz,
rt_globs_marked G -> rt_img_shadow_vis lo hi -> AR segs B ly S W mem md ->
In (a, sz) G -> Z.of_nat (length s) + 1 <= sz -> lo + 64 <= a -> a + Z.of_nat (length s) + 1 + 64 <= hi ->
rt_cstr segs H0 mem0 a s ->
(forall i, 0 <= i <= Z.of_nat (length s) -> aview segs (w_H W) mem (a + i) = aview segs H0 mem0 (a + i)) ->
rt_cstr segs (w_H W) mem a s.
Proof.
intros G lo hi ly S W mem md H0 mem0 a s sz HG HV HAR Hin Hsz Hlo Hhi (C1 & C2 & C3 & C4 & C5 & C6 & C7 & _ & _) Heq.
destruct (rt_glob_read_ok G lo hi ly S W mem md a sz a (Z.of_nat (length s) + 1) HG Hin HV HAR
  ltac:(lia) ltac:(lia) ltac:(lia) Hlo ltac:(lia)) as [RA HU].
unfold rt_cstr. split.
{ intros i Hi. rewrite Heq by lia. exact (C1 i Hi). }
split; [rewrite Heq by lia; exact C2|].
split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|]. split; [exact C7|].
split; [exact RA | exact HU].
Qed.
(* The same for a table of 4-byte values and a table of 8-byte values that are registered globals. *)
Lemma rt_i32tab_at : forall G ly S (W : world segs) mem md (H0 : word -> bool) mem0 t vs sz,
rt_globs_marked G -> AR segs B ly S W mem md -> In (t, sz) G -> 4 * Z.of_nat (length vs) <= sz ->
rt_i32tab segs H0 mem0 t vs ->
(forall i, 0 <= i < 4 * Z.of_nat (length vs) -> aview segs (w_H W) mem (t + i) = aview segs H0 mem0 (t + i)) ->
rt_i32tab segs (w_H W) mem t vs.
Proof.
intros G ly S W mem md H0 mem0 t vs sz HG HAR Hin Hsz (C1 & C2 & C3 & _) Heq.
split; [exact C1|]. split; [exact C2|]. split.
- intros i Hi. unfold val_mem. intros k Hk.
  assert (E : mbyte segs (mrestrict (w_H W) mem) (t + 4 * i + Z.of_nat k) =
              mbyte segs (mrestrict H0 mem0) (t + 4 * i + Z.of_nat k)).
  { apply rt_aview_mbyte. replace (t + 4 * i + Z.of_nat k) with (t + (4 * i + Z.of_nat k)) by lia.
    apply Heq. lia. }
  rewrite E. exact (C3 i Hi k Hk).
- exact (rt_glob_usable G ly S W mem md t sz t (4 * Z.of_nat (length vs)) HG Hin HAR ltac:(lia) ltac:(lia)).
Qed.
Lemma rt_u64tab_at : forall G ly S (W : world segs) mem md (H0 : word -> bool) mem0 t vs sz,
rt_globs_marked G -> AR segs B ly S W mem md -> In (t, sz) G -> 8 * Z.of_nat (length vs) <= sz ->
rt_u64tab segs H0 mem0 t vs ->
(forall i, 0 <= i < 8 * Z.of_nat (length vs) -> aview segs (w_H W) mem (t + i) = aview segs H0 mem0 (t + i)) ->
rt_u64tab segs (w_H W) mem t vs.
Proof.
intros G ly S W mem md H0 mem0 t vs sz HG HAR Hin Hsz (C1 & C2 & C3 & C4 & _) Heq.
split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split.
- intros i Hi. unfold val_mem. intros k Hk.
  assert (E : mbyte segs (mrestrict (w_H W) mem) (t + 8 * i + Z.of_nat k) =
              mbyte segs (mrestrict H0 mem0) (t + 8 * i + Z.of_nat k)).
  { apply rt_aview_mbyte. replace (t + 8 * i + Z.of_nat k) with (t + (8 * i + Z.of_nat k)) by lia.
    apply Heq. lia. }
  rewrite E. exact (C4 i Hi k Hk).
- exact (rt_glob_usable G ly S W mem md t sz t (8 * Z.of_nat (length vs)) HG Hin HAR ltac:(lia) ltac:(lia)).
Qed.
(* ---- the bytes from the read-only data as in the image (arodata_okP, which every journal keeps) ----
   At a state that has arodata_okP, a read byte that is no owned static and no errno byte reads as the image's byte,
   so a string, cell or table whose image bytes are known holds there with no earlier state (what the main walk
   needs at its cuts, where the harness pre gives arodata_okP and the journal keeps it). *)
(* The image holds the bytes l at a, each in the read-only range (no state). *)
Definition rt_img_bytes (rlo rhi a : Z) (l : list Z) : Prop :=
forall i, 0 <= i < Z.of_nat (length l) -> in_roP segs rlo rhi (a + i) /\
option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 (a + i))) = Some (nth (Z.to_nat i) l 0).
(* The image holds the n-byte little-endian value v at a, each byte in the read-only range (no state). *)
Definition rt_img_val (rlo rhi a : Z) (n : nat) (v : Z) : Prop :=
forall k, (k < n)%nat -> in_roP segs rlo rhi (a + Z.of_nat k) /\
seg_rom segs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte v n k)).
Lemma rt_ro_mbyte : forall rlo rhi (W : world segs) mem x,
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> in_roP segs rlo rhi x ->
~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
mbyte segs (mrestrict (w_H W) mem) x = seg_rom segs (Z_to_bv 64 x).
Proof.
intros rlo rhi W mem x HA Hro Ho He. pose proof (HA x Hro Ho He) as E. unfold aview in E.
destruct (mbyte segs (mrestrict (w_H W) mem) x) as [b'|]; destruct (seg_rom segs (Z_to_bv 64 x)) as [b|];
cbn [option_map] in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma rt_val_of_ro : forall rlo rhi (W : world segs) mem a n v,
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> rt_ro_unowned a (Z.of_nat n) -> rt_img_val rlo rhi a n v ->
val_mem segs (mrestrict (w_H W) mem) a n v.
Proof.
intros rlo rhi W mem a n v HA HU HI. unfold val_mem. intros k Hk. destruct (HI k Hk) as [Hro Hb].
destruct (HU (a + Z.of_nat k) ltac:(lia)) as [Ho He].
rewrite (rt_ro_mbyte rlo rhi W mem _ HA Hro Ho He). exact Hb.
Qed.
Lemma rt_bytes_of_ro : forall rlo rhi (W : world segs) mem a l,
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> rt_ro_unowned a (Z.of_nat (length l)) ->
rt_img_bytes rlo rhi a l ->
forall i, 0 <= i < Z.of_nat (length l) -> aview segs (w_H W) mem (a + i) = Some (nth (Z.to_nat i) l 0).
Proof.
intros rlo rhi W mem a l HA HU HI i Hi. destruct (HI i Hi) as [Hro Hb]. destruct (HU (a + i) ltac:(lia)) as [Ho He].
rewrite (HA (a + i) Hro Ho He). exact Hb.
Qed.
(* Every read-only byte that is an owned static (or an errno byte) reads as the image's byte in every AR state: the
   start-up pins such bytes as AR constant cells (am_const; the globals' guard bytes in .rodata, the runtime's
   read-only constants). A fact of B, proved at the image's symbol record by computation. With arodata_okP for the
   other bytes it gives rom_view (one of rt_seg_pre's read-only conjuncts) at every AR state. *)
Definition rt_rom_pinned : Prop :=
forall ly S (W : world segs) mem md a, AR segs B ly S W mem md -> in_rom segs a ->
Exists (in_zr a) (as_owned_static B) \/ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Lemma rt_rom_view_of : forall rlo rhi ly S (W : world segs) mem md,
rt_rom_pinned -> AR segs B ly S W mem md -> arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
rom_view segs W mem.
Proof.
intros rlo rhi ly S W mem md HP HAR HA a Ha.
assert (D : forall r, {in_zr a r} + {~ in_zr a r}).
{ intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r));
  [left; lia | right; lia | right; lia | right; lia]. }
destruct (Exists_dec (in_zr a) (as_owned_static B) D) as [Ho|Ho]; [exact (HP ly S W mem md a HAR Ha (or_introl Ho))|].
destruct (Z_le_dec (as_errno B) a) as [E1|E1]; [destruct (Z_lt_dec a (as_errno B + 4)) as [E2|E2]|].
- exact (HP ly S W mem md a HAR Ha (or_intror (conj E1 E2))).
- apply (HA a); [left; destruct Ha as (sg & Hs & Hw & Hr); exists sg; auto | exact Ho | lia].
- apply (HA a); [left; destruct Ha as (sg & Hs & Hw & Hr); exists sg; auto | exact Ho | lia].
Qed.
End img.

(* A cell [q, q + n) that a callee with stack use T at sp may write for its caller: in the caller's stack window
   [sp0 - STK, sp0), or in one of the side-stack frames own the caller holds; and outside the callee's own stack
   [sp - T, sp). Both places are writable under the caller's journal (YCbq.v awr_byte). *)
Definition rt_wcell (STK sp0 : Z) (ly : alayout) (own : list (Z * Z)) (sp T q n : Z) : Prop :=
((sp0 - STK <= q /\ q + n <= sp0) \/
 (exists cid pos, In (cid, pos) own /\ 0 <= cid /\
  frame_addr ly cid pos <= q /\ q + n <= frame_addr ly cid pos + fs_frame_bytes cid)) /\
(sp <= q \/ q + n <= sp - T).

(* The bridge from a block made since the journal's start (in the current blocks blc, not in the start blocks bl0)
   to the journal's write right on each of its bytes (YCbq.v awr_byte, its in_tmp_block case): what the segment
   walks use for their writes to pp, pod and buf, from rt_seg_pre's `~ In (q_pp e, Layout.PP_SIZE) (ablocks B ly S)`
   conjunct and the pod / buf premises of
   rate_check_contract / rate_csv_contract. *)
Lemma rt_fresh_awr : forall STK sp0 FP bl0 blc ly own p n i,
In (p, n) blc -> ~ In (p, n) bl0 -> 0 <= i < req_size n -> awr_byte STK sp0 FP bl0 blc ly own (p + i).
Proof.
intros STK sp0 FP bl0 blc ly own p n i Hin Hout Hi. right. right. left.
exists p, n. split; [exact Hin|]. split; [exact Hout|]. lia.
Qed.
Lemma rt_fresh_awr_n : forall STK sp0 FP bl0 blc ly own p n,
In (p, n) blc -> ~ In (p, n) bl0 -> 0 < n ->
forall i, 0 <= i < n -> awr_byte STK sp0 FP bl0 blc ly own (p + i).
Proof.
intros STK sp0 FP bl0 blc ly own p n Hin Hout Hn i Hi. apply (rt_fresh_awr STK sp0 FP bl0 blc ly own p n i Hin Hout).
unfold req_size. destruct (Z.eqb_spec n 0); lia.
Qed.

(* ================ the cut states of LLVMFuzzerTestOneInput, as data each image fills ================
   The two ASan images keep the harness's values in different registers and real-frame cells, so a cut state is a
   list of (location, value) facts over the run's quantities rt_renv. A location is a register or an 8-byte cell at a
   base plus an offset; a value is one of the quantities, an address made from pp, a header value shifted left, or a
   constant. The image's lists are measured from its code. *)
(* The run's quantities: S the entry sp; R the 32-aligned base of the real frame (R + its size <= S); F the frame
   for locals (a side-stack frame); pp, pod and buf the three blocks; len = pp->len after the build (rt_len of the
   input after the 7-byte header); fl, mask, buflen (byte 2 mod 24) and b3 .. b6 the header values (fuzz_rate.c:236-239,
   each 0 when the input is shorter); src and left the input cursor and the bytes left after the header. *)
Record rt_renv := RtEnv {
q_S : Z; q_R : Z; q_F : Z; q_pp : Z; q_pod : Z; q_buf : Z; q_len : Z;
q_fl : Z; q_mask : Z; q_buflen : Z; q_b3 : Z; q_b4 : Z; q_b5 : Z; q_b6 : Z;
q_src : Z; q_left : Z }.
(* Header byte i (3 .. 6) of the u32 `other` (fuzz_rate.c:239), 0 for any other i. *)
Definition rt_hb (e : rt_renv) (i : Z) : Z :=
if i =? 3 then q_b3 e else if i =? 4 then q_b4 e else if i =? 5 then q_b5 e else if i =? 6 then q_b6 e else 0.
(* XShF is the shadow address of F, (F >> 3) + K with K the runtime's shadow offset (SHADOW_OFF); XPpShr c is
   (pp + c) >> 3, a shadow index before K is added; XLenNZ is the malloc request len + (len == 0); XBl is buf's
   request buflen + (buflen == 0) (rt_bl); XHb i sh is header byte i shifted left by sh bits (the code keeps b4 and b6
   as b << 8). *)
Inductive rt_x :=
| XS | XR | XF | XShF | XPp (c : Z) | XPpShr (c : Z) | XPod | XBuf | XLen | XLenNZ | XBl
| XFl | XMask | XBuflen | XHb (i sh : Z) | XSrc | XLeft | XC (c : Z).
Definition rt_xv (e : rt_renv) (x : rt_x) : Z :=
match x with
| XS => q_S e | XR => q_R e | XF => q_F e | XShF => shadow_addr (q_F e)
| XPp c => q_pp e + c | XPpShr c => Z.shiftr (q_pp e + c) 3 | XPod => q_pod e | XBuf => q_buf e
| XLen => q_len e | XLenNZ => q_len e + (if q_len e =? 0 then 1 else 0) | XBl => rt_bl (q_buflen e)
| XFl => q_fl e | XMask => q_mask e | XBuflen => q_buflen e | XHb i sh => Z.shiftl (rt_hb e i) sh
| XSrc => q_src e | XLeft => q_left e | XC c => c
end.
Inductive rt_loc := LReg (r : Z) | LCell (b : rt_x) (off : Z).
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* A register holds the 64-bit word of v; a cell holds its 8 little-endian bytes. *)
Definition rt_at (H : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : rt_renv)
(l : rt_loc) (v : Z) : Prop :=
match l with
| LReg r => getr regs (Z_to_bv 5 r) = w64 v
| LCell b o => val_mem segs (mrestrict H mem) (rt_xv e b + o) 8 (v mod 2 ^ 64)
end.
Definition rt_cut (H : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : rt_renv)
(L : list (rt_loc * rt_x)) : Prop :=
Forall (fun f => rt_at H mem regs e (fst f) (rt_xv e (snd f))) L.
(* The shadow bytes of the frame for locals, from shadow_addr F on (one byte per 8-byte granule of F). *)
Definition rt_fsh (H : word -> bool) (mem : word -> option byte) (F : Z) (pat : list Z) : Prop :=
forall i, 0 <= i < Z.of_nat (length pat) -> aview segs H mem (shadow_addr F + i) = Some (nth (Z.to_nat i) pat 0).
End u.
(* a lies in one of the ranges ws: (base, offset, length) -> [base + offset, base + offset + length). *)
Definition rt_inw (e : rt_renv) (ws : list (rt_x * Z * Z)) (a : Z) : Prop :=
Exists (fun w => rt_xv e (fst (fst w)) + snd (fst w) <= a < rt_xv e (fst (fst w)) + snd (fst w) + snd w) ws.
