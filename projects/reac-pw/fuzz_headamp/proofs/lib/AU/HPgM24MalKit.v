(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v at 6ebe35ba632; its rt_chain is ported here as rl_c23_chain (statement kept, proof by the kernel's achain_push); the rest of this file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM24Mal.v at be048d930b4 (image A's
   malloc(first) step); its step-independent part (the entry state of a one-`jal` run, the seg_rom coverage of the
   image and the errno cell's readability, an 8-byte cell as a word, the register-name lemmas, the caller chain
   and the call's caller-chain list) moved here for image B's three allocator steps: image B's segments
   (lib/AU/Img0U.v rsegs), image B's record of the harness entry (lib/AU/HPgSegM.v hqu_hcx, fields hu_ly .. hu_pl), the run's
   pc a parameter; prefix hk_ -> hkb_. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): the step-independent lemmas of image B's
   three allocator steps (lib/AU/HPgSegM.v hqu_S_C23_stmt / hqu_S_C45_stmt / hqu_S_C67_stmt; the steps are proved
   in lib/AU/HPgM24C23.v, HPgM24C45.v, HPgM24C67.v). Proves no function (kind: segment lemma).
   - hkb_entry: the entry state of a run over one `jal` word at any pc, every register an atom, no region.
   - hkb_segs_ok / hkb_seg_rom_img / hkb_errno_rd: every byte of image B's segments has an image byte (each
     segment is one hex chunk of its size; checked by vm_compute over the image's bytes), so the view reads every
     in-image address at every memory (YP09.v mbyte falls back to seg_rom), and the errno cell, which lies in the
     image (YCbq.v api_env), is readable after any call: the allocator's contract (YG0d.v acall_post, ascratch)
     does not keep its value.
   - hkb_cell / hkb_rdword_of_val_mem: an HPgBase cell fact as a word of the view.
   - hkb_chain / hkb_ch: the caller chain the allocator's trace reads at a call from the harness's frame (the
     entry's achain pushed with the record the prologue stored at S - 8 / S - 16). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YK07.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0f YG0s YG0q YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the entry state of a run over one word at pc: the registers as atoms, no region, no fact (at any float state) *)
Definition hkb_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma hkb_entry : forall (pc : Z) (fx' : YK11.FPState) (W : world rsegs) regs memc,
@st_ok rsegs fx' (Ereg regs rt_extra) (hkb_ss pc)
  (restrict (w_H W) (@mkst fx' regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc fx' W regs memc. rewrite restrict_mkst_fx. unfold hkb_ss. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.

(* ---- every byte of image B's segments has an image byte (each segment is one hex chunk of its size) ---- *)
Definition hkb_seg_ok (sg : Segment) : bool :=
  seg_readable sg &&
  match seg_bytes sg with
  | [s] => N.leb (seg_size sg) (Z.to_N (Uint63.to_Z (PrimString.length s) / 2)) && scanN s 64 0 (seg_size sg)
  | _ => false
  end.
Lemma hkb_segs_ok : forallb hkb_seg_ok rsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hkb_find_some : forall (l : list Segment) a,
(exists sg, In sg l /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) ->
exists sg, find_segment l a 1 = Some sg.
Proof.
induction l as [|s0 l IH]; intros a (sg & Hin & Hr); [destruct Hin|].
cbn [find_segment]. cbv zeta.
match goal with |- context [if ?c then _ else _] => destruct c eqn:Eb end.
- exists s0. reflexivity.
- destruct Hin as [<-|Hin].
  + exfalso. apply andb_false_iff in Eb as [Eb|Eb]; apply Z.leb_gt in Eb; lia.
  + exact (IH a (ex_intro _ sg (conj Hin Hr))).
Qed.
Lemma hkb_seg_rom_img : forall a, 0 <= a < 2 ^ 64 -> in_img rsegs a -> seg_rom rsegs (Z_to_bv 64 a) <> None.
Proof.
intros a Ha Himg. destruct (hkb_find_some rsegs a Himg) as (sg & Hf).
pose proof Hf as Hf'. apply find_segment_some_spec in Hf' as (Hin & H1 & H2).
pose proof (proj1 (forallb_forall _ _) hkb_segs_ok sg Hin) as Hok. unfold hkb_seg_ok in Hok.
apply andb_prop in Hok as [Hr Hb].
unfold seg_rom, memory_read. rewrite unsigned_lit_small by exact Ha.
change (Z.of_N 1) with 1. rewrite Hf, Hr. cbv beta iota zeta.
destruct (seg_bytes sg) as [|s [|s' rest]] eqn:Eb; try discriminate Hb.
apply andb_prop in Hb as [Hle Hscan]. apply N.leb_le in Hle.
change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
destruct (segment_byte_at [s] (Z.to_N (a - Z.of_N (seg_base sg)))) as [b|] eqn:Es.
- cbn. discriminate.
- exfalso. apply (segment_byte_at_some1 s (seg_size sg) (Z.to_N (a - Z.of_N (seg_base sg))) Hscan Hle); [|exact Es].
  rewrite Z2N.id by lia. lia.
Qed.
Lemma hkb_aview_some : forall H (mem : word -> option byte) a, 0 <= a < 2 ^ 64 -> in_img rsegs a ->
exists v, aview rsegs H mem a = Some v /\ 0 <= v < 256.
Proof.
intros H mem a Ha Himg. unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|] eqn:E.
- exists (bv_unsigned b). split; [reflexivity|]. pose proof (bv_unsigned_in_range 8 b) as Hb.
  change (bv_modulus 8) with 256 in Hb. exact Hb.
- destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b|] eqn:E2.
  + exists (bv_unsigned b). split; [reflexivity|]. pose proof (bv_unsigned_in_range 8 b) as Hb.
    change (bv_modulus 8) with 256 in Hb. exact Hb.
  + exfalso. exact (hkb_seg_rom_img a Ha Himg E2).
Qed.
(* four bytes as one little-endian 4-byte value *)
Lemma hkb_le4 : forall v0 v1 v2 v3, 0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 ->
YG0f.le_byte (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) 4 0 = v0 /\
YG0f.le_byte (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) 4 1 = v1 /\
YG0f.le_byte (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) 4 2 = v2 /\
YG0f.le_byte (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) 4 3 = v3.
Proof.
intros v0 v1 v2 v3 H0 H1 H2 H3. unfold YG0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 0)) with 1.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with 65536.
change (2 ^ (8 * Z.of_nat 3)) with 16777216.
split; [|split; [|split]]; Z.to_euclidean_division_equations; lia.
Qed.
(* the errno cell is readable at every memory: its four bytes lie in the image (api_env) *)
Lemma hkb_errno_rd : forall (B : asyms) H (mem : word -> option byte), api_env rsegs B ->
exists ev, rd32 (aview rsegs H mem) (as_errno B) ev.
Proof.
intros B H mem (He & Hi & _).
assert (G : forall k, 0 <= k < 4 -> exists v, aview rsegs H mem (as_errno B + k) = Some v /\ 0 <= v < 256).
{ intros k Hk. apply hkb_aview_some; [unfold kLowMemEnd in He; lia | apply Hi; lia]. }
destruct (G 0 ltac:(lia)) as (v0 & A0 & B0). destruct (G 1 ltac:(lia)) as (v1 & A1 & B1).
destruct (G 2 ltac:(lia)) as (v2 & A2 & B2). destruct (G 3 ltac:(lia)) as (v3 & A3 & B3).
destruct (hkb_le4 v0 v1 v2 v3 B0 B1 B2 B3) as (L0 & L1 & L2 & L3).
exists (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3).
unfold rd32. intros k Hk.
destruct k as [|[|[|[|k]]]]; [| | | | lia].
- change (Z.of_nat 0) with 0. rewrite A0, L0. reflexivity.
- change (Z.of_nat 1) with 1. rewrite A1, L1. reflexivity.
- change (Z.of_nat 2) with 2. rewrite A2, L2. reflexivity.
- change (Z.of_nat 3) with 3. rewrite A3, L3. reflexivity.
Qed.

(* ---- an 8-byte cell as a word of the view (the converse of YCbq.val_mem_of_rdword) ---- *)
Section h. Context {rc : YM05.RunCeil}.
(* the frame's shadow bytes lie apart from every application range (a heap block) *)
Lemma hkb_shadow_apart : forall F p n i, in_app F 1024 -> in_app p n -> alloc_ceiling <= 0x7fffff800000 ->
0 <= i < 128 -> ~ (p <= shadow_addr F + i < p + n).
Proof.
intros F p n i HF Hp Hc Hi. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HF, Hp.
unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
lia.
Qed.
Lemma hkb_rdword_of_val_mem : forall H mem a v, 0 <= v < 2 ^ 64 ->
val_mem rsegs (mrestrict H mem) a 8 v -> rdword (aview rsegs H mem) a = Some v.
Proof.
intros H mem a v Hv Hm. unfold val_mem in Hm.
pose proof (Hm 0%nat ltac:(lia)) as H0. pose proof (Hm 1%nat ltac:(lia)) as H1. pose proof (Hm 2%nat ltac:(lia)) as H2.
pose proof (Hm 3%nat ltac:(lia)) as H3. pose proof (Hm 4%nat ltac:(lia)) as H4. pose proof (Hm 5%nat ltac:(lia)) as H5.
pose proof (Hm 6%nat ltac:(lia)) as H6. pose proof (Hm 7%nat ltac:(lia)) as H7.
cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3, H4, H5, H6, H7. rewrite Z.add_0_r in H0.
unfold rdword, aview. cbv beta.
rewrite H0, H1, H2, H3, H4, H5, H6, H7. cbn [option_map].
assert (Hb : forall k, bv_unsigned (Z_to_bv 8 (YO0f.le_byte v 8 k)) = YG0f.le_byte v 8 k).
{ intros k. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change (YO0f.le_byte v 8 k) with (YG0f.le_byte v 8 k). rewrite YG0s.le_byte_8. apply Z.mod_mod. lia. }
rewrite !Hb. f_equal. apply YG0s.le_bytes8. exact Hv.
Qed.
(* a cell fact of HPgBase as a word of the view *)
Lemma hkb_cell : forall H mem regs e b o v, 0 <= v < 2 ^ 64 ->
hd_at rsegs H mem regs e (LCell b o) v -> rdword (aview rsegs H mem) (hd_xv e b + o) = Some v.
Proof.
intros H mem regs e b o v Hv Hc. cbn [hd_at] in Hc. rewrite Z.mod_small in Hc by exact Hv.
apply hkb_rdword_of_val_mem; assumption.
Qed.

(* ---- register names: a literal and Z_to_bv 5 of its number name the same register ---- *)
Lemma hkb_getr_eq : forall regs (b b' : bv 5), bv_unsigned b = bv_unsigned b' -> getr regs b = getr regs b'.
Proof. intros regs b b' E. apply bv_eq in E. subst b'. reflexivity. Qed.

(* ---- the caller chain at a call from the harness frame [knock APgRt.v rt_chain] ---- *)
Lemma hkb_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) sp',
achain ly rd (spZ regs) (s0Z regs) [] -> ly_top ly <= 2 ^ 64 ->
(forall a, spZ regs <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (spZ regs - 8) = Some (raZ regs) -> rdword rd' (spZ regs - 16) = Some (s0Z regs) -> 4096 <= raZ regs ->
alloc_ceiling <= spZ regs -> spZ regs mod 8 = 0 -> sp' + 16 <= spZ regs ->
achain ly rd' sp' (spZ regs) (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []).
Proof.
intros ly rd rd' regs sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal Hsp'.
destruct (Z.ltb_spec (spZ regs + 16) (ly_top ly)) as [Hlt | Hge].
- exact (achain_push ly rd rd' (spZ regs) (s0Z regs) (raZ regs) [] sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal ltac:(lia) Hsp').
- left. split; [right; left; lia | reflexivity].
Qed.
End h.

(* the side goals of a register the run did not touch (clob = [ra]) *)
Ltac hkb_rk :=
first
[ solve [vm_compute; let Hx := fresh "Hx" in intros Hx; discriminate Hx]
| solve [let Hx := fresh "Hx" in intros Hx; cbn [In] in Hx;
         repeat (destruct Hx as [Hx|Hx]; [apply (f_equal (@bv_unsigned 5)) in Hx; vm_compute in Hx; discriminate Hx|]);
         exact Hx] ].

Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the caller chain the malloc call sees: the harness entry's own record (sp, ra, s0) when its frame is below the
   stack top (scene P_LLVMFuzzerTestOneInput_ctx.v rt_ch) *)
Definition hkb_ch (hx : hqu_hcx rsegs) : list (Z * Z * Z) :=
if spZ (hu_regs rsegs hx) + 16 <? ly_top (hu_ly rsegs hx)
then [(spZ (hu_regs rsegs hx), raZ (hu_regs rsegs hx), s0Z (hu_regs rsegs hx))] else [].
End b.

Print Assumptions hkb_entry.
Print Assumptions hkb_seg_rom_img.
Print Assumptions hkb_errno_rd.
Print Assumptions hkb_cell.
Print Assumptions hkb_chain.
