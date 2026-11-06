(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b for
   reac-pw/fuzz_headamp image A: its start-fact record hd_c3 / hd_c3_of, its bounds lemma hd_bounds and its walk hd_A
   (a nonzero test of a block, a register move, a zero test of the length, the __asan_memcpy, its return) restated for
   headamp's segment M04a (C7 0x83744 -> C8 0x83764) as h4a_c7 / h4a_c7_of / h4a_bounds / h4a_copy over HPgSeg.hs_scx,
   with headamp's registers and real-frame cells; its helpers hd_getr_z, hd_reg_atom, hd_aview_some and hd_frame_ro
   taken renamed (h4a_); role's own memcpy step replaced by the shared lib/A/HPgIntrin.v hd_memcpy_at; the arm with
   no copy (h4a_zero), the extra-atom register lemma h4a_reg_at and the post construction h4a_close are new; role's
   parse step, .rodata zone and string lemmas are not taken (M04a calls no parse). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module paths and module names changed; 344 of its 383 lines of code are new or changed and 430 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW3b.v at 4d659c905bca (its shape-7 part:
   w3b_b7_core, w3b_img_b7, w3b_b7_img and rs_piece_W3b_b7), for the same unit's image B: image B's pcs and code; the
   values the header reads come from real-frame cells (pp at R+0x168, &pp->len at R+0x158, the shadow address of
   &pp->len at R+0x170, ~pp at R+0x108) and pp is the register a6; the two UBSan tests of pod_put32 (pod.h:179) and
   the shape-7 flag store R+0x110 are new; the statement is lib/AU/RtPgSegB.v's rsb_piece_W3b_b7_stmt. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgW3aB7.v, with its addresses and numbers changed; 270 of its 424 lines of code are new or changed and 229 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW3b.v at 470a2fe18f00, ported to
   reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan): image B's pcs; pp, &pp->len, the shadow address of &pp->len and
   ~pp are cells of the real frame and not registers, so the engine's state is one region on R and two on pp, and the
   shadow base is s4 (x20); the second pod_put32 is out of line at 0x827e0, so the code table is two blocks; the six
   UBSan trap branches of the piece are decided by the atom ranges of len and of ~pp; the piece also writes the
   shape-7 flag cell R+0x110; the shape is register a3's own atom; the image facts come from lib/AU/RtPgStepsB.v and
   the memory lemmas from lib/AU/RtPgMemB.v. The shape-7 header B7 -> PH is image B's W3a lane, not this file. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the Object header of the
   build (M01) of LLVMFuzzerTestOneInput 0x8076c. Proves no function (kind: segment lemma). The preheader that
   follows it (PH 0x80ea0 -> N / P) is RtPgW3bPreB.v.

   THE PIECE. BO 0x80d1c -> PH 0x80ea0 (pod.h:392-395, shape <> 7): three pod_put32 calls (POD_OBJECT = 15;
   POD_OBJECT_PROPINFO 0x40001 when shape = 6 else POD_OBJECT_PROPS 0x40002; POD_PARAM_PROPS 2) at pp + 4, pp + 8 and
   pp + 12, then is_props := (shape <> 6) at pp + 0x4008 and the shape-7 flag cell R+0x110 := 0 (0x80e90). The second
   call is out of line: `j 0x827e0` 0x80dc0 and `j 0x80ddc` 0x82868. Each call has its two store checks (the first
   and the last byte of the four), the check of &pp->len through the shadow address the cell R+0x170 holds, and two
   UBSan trap branches, `bltu len, 0x4001` (bounds) and `bgeu ~pp, len` (pointer overflow): six in all. len is 4 at
   BO and 8 and 12 at the later calls, so every capacity test (`bltu len - 0x3ffd, -0x4001`, with -0x3ffd reloaded
   from R+0x120) is decided on literals and falls through.

   HOW. The piece rebuilds a symbolic state from its start cut (the registers as their own atoms, the R-relative
   cells and the two pp windows as regions) and runs the kit's token engine (lib/Reusable/YCbn.v through
   YCbq.aj_run_to_tok). The shadow base is s4 = x20 itself (its atom has the exact range [SHADOW_OFF, SHADOW_OFF]),
   and one shadow entry (pp's 19744 bytes on x16) covers every check of the piece, the one through the cell R+0x170
   included, whose chunk is the expression ((pp + 0x4000) >> 3) + s4 that E01 put there: the engine reads each shadow
   byte as the literal 0, so no check leaves an obligation and no slow block is run. The six trap branches are
   decided by the atom ranges, which are closed numerals: len is a literal on each arm and ~pp lies in
   [2^63, 2^64 - 1]. The stores into pp are allowed by the journal through RtPgBase.rt_fresh_awr (pp is not live at
   the harness entry: RtPgCSpec.rt_seg_pre's pp conjunct) and the store into R+0x110 by the segment's stack window.
   The values the header writes depend on the shape; the run leaves them as expressions in a3's atom, and the end
   splits the shape into its seven values. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YI00 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ===================================== the engine's context ===================================== *)
Definition W3BB_BO : Z := 0x80d1c.
Definition W3BB_PH : Z := 0x80ea0.
(* the 97 instruction words 0x80d1c .. 0x80e9c and the 35 of the out-of-line second put32 0x827e0 .. 0x82868 *)
Definition w3bb_tbl : ctable := build_table rsegs W3BB_BO 97 (build_table rsegs 0x827e0 35 TEmpty).
Lemma w3bb_tbl_ok : table_ok rsegs w3bb_tbl.
Proof. apply build_table_ok; [unfold W3BB_BO; lia|]. apply build_table_ok0. lia. Qed.
(* the shadow base is x20 (s4) *)
Definition w3bb_Bx : sv := SOff 20 0.
Definition w3bb_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the shadow address of &pp->len, as the cell R+0x170 holds it: ((pp + 0x4000) >> 3) + s4 *)
Definition w3bb_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 16 16384) (SLit 3)) (SOff 20 0).
(* pp on x16 (a6), 19744 bytes: one entry covers the header words and &pp->len alike *)
Definition w3bb_SH : list shent := [mkSHE 16 0 19744].
Definition W3BB_PPHI : Z := 0x7fffff800000 - 19744.
Definition W3BB_RLO : Z := 0x7fff7f800000.
Definition W3BB_RHI : Z := 2 ^ 47.
Definition W3BB_M3FFD : Z := 0xffffffffffffc003.   (* -0x3ffd mod 2^64 *)
Definition W3BB_A2BO : Z := 0xffffffffffffc007.    (* 4 - 0x3ffd mod 2^64 *)
(* every bound is a closed numeral: the engine decides the six trap branches by computing over sv_range *)
Definition w3bb_atoms : list (nat * afact) :=
[(9%nat, mkAF W3BB_RLO W3BB_RHI 0); (16%nat, mkAF 4096 W3BB_PPHI 0);
 (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (13%nat, mkAF 0 6 0);
 (32%nat, mkAF 9223372036854775808 18446744073709551615 0)].

(* ---- BO: a0 = len = 4 and a2 = len - 0x3ffd are pinned; a6 = pp, a3 = the shape, s1 = R and s4 = SHADOW_OFF are
   their own atoms, and ~pp is the extra atom 32. The cells the header reads are one region on R
   ([R+0x108, R+0x178), with the shape-7 flag cell [R+0x110, R+0x118) its write window) and the two windows of pp it
   writes are two regions on a6. ---- *)
Definition w3bb_regs_bo : list sv :=
sr_set (sr_set sr_atoms (Z_to_bv 5 10) (SLit 4)) (Z_to_bv 5 12) (SLit W3BB_A2BO).
Definition w3bb_rR : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x108 0x178 0x110 0x118
[YP09.mkChunk 0x108 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x120 (CVal 8 (SLit W3BB_M3FFD));
 YP09.mkChunk 0x158 (CVal 8 (SOff 16 16384)); YP09.mkChunk 0x168 (CVal 8 (SOff 16 0));
 YP09.mkChunk 0x170 (CVal 8 w3bb_shx)].
Definition w3bb_rH : YP09.region := YP09.mkRegion (Some 16%nat) 4 16 4 16 [].
Definition w3bb_rL : YP09.region :=
YP09.mkRegion (Some 16%nat) 0x4000 0x400c 0x4000 0x400c [YP09.mkChunk 0x4000 (CVal 8 (SLit 4))].
Definition w3bb_ss_bo : sstate :=
mkSS W3BB_BO w3bb_regs_bo [w3bb_rR; w3bb_rH; w3bb_rL] None (mkFacts w3bb_atoms [] []).

(* the registers the piece leaves alone: all but a0, a2, a3, a4, a5 *)
Definition W3BB_KEPT : list Z :=
[1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

(* the block's image at PH: the top size word, the twelve header bytes at 4, len = 16 and is_props at 0x4008 *)
Lemma w3bb_img_ph : forall sh, 0 <= sh <= 6 ->
pc_image (PbCut sh [] None) =
overwrite (rtmb_slice rsb_img_hdr 0 16384) 4 (hdr_bytes sh) ++ le64 16 ++ le32 (Z.b2z (negb (sh =? 6))) ++
rtmb_slice rsb_img_hdr 16396 3348.
Proof.
intros sh Hsh. assert (H : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6) by lia.
destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]]; vm_compute; reflexivity.
Qed.
Lemma w3bb_len_hdr : forall sh, sh <> 7 -> length (hdr_bytes sh) = 12%nat.
Proof. intros sh Hsh. unfold hdr_bytes. rewrite (proj2 (Z.eqb_neq sh 7) Hsh). reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* ===================================== small facts ===================================== *)
(* a register the final symbolic state still holds as its own atom keeps its value *)
Lemma w3bb_reg_kept : forall E ss ms regs0 extra (H : word -> bool) (r : bv 5),
st_ok rsegs E ss (restrict H ms) -> (forall n, (n < 32)%nat -> ew E n = ew (Ereg regs0 extra) n) ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra H r HS HA Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
pose proof (u5_range r) as Hr. rewrite HA by lia. apply ew_Ereg_reg.
Qed.

(* one byte a run stored, as the walk reads it back: a CVal 1 chunk of a final region at base + off *)
Lemma w3bb_chunk1 : forall E (H : word -> bool) ms base off e (b : byte),
YP09.chunk_ok rsegs E (ms_mem (restrict H ms)) base (YP09.mkChunk off (CVal 1 e)) ->
byte_of_word (sv_denot E e) 0 = b -> forall a, a = base + off -> aview rsegs H (ms_mem ms) a = Some (bv_unsigned b).
Proof.
intros E H ms base off e b C Hb a ->. destruct (C 0 ltac:(cbn; lia)) as (b' & H1 & H2).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in H1, H2. injection H1 as <-. rewrite Z.add_0_r in H2.
unfold aview. change (mrestrict H (ms_mem ms)) with (ms_mem (restrict H ms)). rewrite H2, Hb. reflexivity.
Qed.

(* the value of an atom's offset expression *)
Lemma w3bb_off : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H. apply bv_eq. rewrite denot_SOff, H, !Z_to_bv_unsigned.
unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* the complement of an address, as the cell R+0x108 holds it *)
Lemma w3bb_lnot_small : forall p, 0 <= p < 2 ^ 64 -> Z.lnot p mod 2 ^ 64 = 2 ^ 64 - 1 - p.
Proof.
intros p Hp. replace (Z.lnot p) with ((2 ^ 64 - 1 - p) + (-1) * 2 ^ 64) by (unfold Z.lnot; lia).
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* the cell R+0x170 holds ((pp + 0x4000) >> 3) + s4 *)
Lemma w3bb_shx_val : forall E pp, ew E 16 = Z_to_bv 64 pp -> ew E 20 = Z_to_bv 64 SHADOW_OFF ->
4096 <= pp -> pp + 19744 <= 0x7fffff800000 ->
sv_denot E w3bb_shx = Z_to_bv 64 (shadow_addr (pp + 0x4000) mod 2 ^ 64).
Proof.
intros E pp E16 E20 Hp0 Hp1.
unfold w3bb_shx. rewrite denot_lit_U. apply Z_to_bv64_eq_mod.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E 16 pp 16384 E16 ltac:(lia) ltac:(lia)).
rewrite (U_atom E 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold shadow_addr, zcanon, M64.
assert (0 <= (pp + 0x4000) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite (Z.mod_small ((pp + 0x4000) / 8)) by lia.
rewrite (Z.mod_small ((pp + 0x4000) / 8 + SHADOW_OFF)) by (unfold SHADOW_OFF; lia).
rewrite ?Zmod_mod. first [reflexivity | f_equal; lia | lia].
Qed.

Section d.
Variable B : asyms.

Lemma w3bb_ph_img : forall H mem H' mem' pp sh, 0 <= sh <= 6 ->
rtmb_bytes rsegs H mem pp rsb_img_hdr ->
rtmb_bytes rsegs H' mem' (pp + 4) (hdr_bytes sh) ->
rtmb_bytes rsegs H' mem' (pp + 16384) (le64 16) ->
rtmb_bytes rsegs H' mem' (pp + 16392) (le32 (Z.b2z (negb (sh =? 6)))) ->
(forall y, pp <= y < pp + 19744 -> ~ (pp + 4 <= y < pp + 16) -> ~ (pp + 16384 <= y < pp + 16396) ->
 aview rsegs H' mem' y = aview rsegs H mem y) ->
rtmb_bytes rsegs H' mem' pp (pc_image (PbCut sh [] None)).
Proof.
intros H mem H' mem' pp sh Hsh B0 Bh Bl Bi K.
rewrite (w3bb_img_ph sh Hsh).
assert (L0 : length rsb_img_hdr = 19744%nat) by (vm_compute; reflexivity).
assert (L1 : length (rtmb_slice rsb_img_hdr 0 16384) = 16384%nat) by (vm_compute; reflexivity).
assert (L2 : length (rtmb_slice rsb_img_hdr 16396 3348) = 3348%nat) by (vm_compute; reflexivity).
pose proof (w3bb_len_hdr sh ltac:(lia)) as Lh.
assert (Lo : length (overwrite (rtmb_slice rsb_img_hdr 0 16384) 4 (hdr_bytes sh)) = 16384%nat)
  by (rewrite length_overwrite; [exact L1 | rewrite Lh, L1; apply Nat.leb_le; vm_compute; reflexivity]).
apply rtmb_bytes_app. split.
- pose proof (rtmb_bytes_slice rsegs H mem pp rsb_img_hdr 0 16384 B0
    ltac:(rewrite L0; apply Nat.leb_le; vm_compute; reflexivity)) as Bb.
  change (Z.of_nat 0) with 0 in Bb. rewrite Z.add_0_r in Bb.
  apply (rtmb_bytes_patch rsegs H mem H' mem' pp _ 4 _ Bb);
    [exact Bh | rewrite Lh, L1; apply Nat.leb_le; vm_compute; reflexivity |].
  rewrite Lh, L1. intros y Hy Hn. change (Z.of_nat 16384) with 16384 in Hy.
  change (Z.of_nat 4) with 4 in Hn. change (Z.of_nat (4 + 12)) with 16 in Hn. apply K; lia.
- rewrite Lo. change (Z.of_nat 16384) with 16384. apply rtmb_bytes_app. split; [exact Bl|].
  change (length (le64 16)) with 8%nat. change (Z.of_nat 8) with 8. apply rtmb_bytes_app. split.
  + replace (pp + 16384 + 8) with (pp + 16392) by lia. exact Bi.
  + change (length (le32 (Z.b2z (negb (sh =? 6))))) with 4%nat. change (Z.of_nat 4) with 4.
    pose proof (rtmb_bytes_slice rsegs H mem pp rsb_img_hdr 16396 3348 B0
      ltac:(rewrite L0; apply Nat.leb_le; vm_compute; reflexivity)) as Bt.
    change (Z.of_nat 16396) with 16396 in Bt. replace (pp + 16384 + 8 + 4) with (pp + 16396) by lia.
    apply (rtmb_bytes_kept rsegs H mem H' mem' _ _ Bt). rewrite L2. change (Z.of_nat 3348) with 3348.
    intros y Hy. apply K; lia.
Qed.

(* ===================================== BO -> PH: the Object header =====================================
   Entry facts: a0 = len = 4, a2 = len - 0x3ffd, a6 = pp, a3 = the shape, s1 = R, s4 = SHADOW_OFF, and the cells
   R+0x108 (~pp), R+0x120 (-0x3ffd), R+0x158 (&pp->len), R+0x168 (pp), R+0x170 (the shadow address of &pp->len) and
   pp->len = 4. At 0x80ea0: a0 .. a5 changed, the header bytes at pp + 4, len = 16, is_props, R+0x110 = 0, every
   other byte as before. *)
Lemma w3bb_hdr_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world rsegs) memc mdc k
(regs : bvmap 5 word) (R pp sh : Z) (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (pp, PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, PP_SIZE) (ablocks B ly S) ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a) ->
W3BB_RLO <= R -> R + 0x220 <= sp0 -> sp0 - STK <= R - 16384 -> R + 0x220 <= W3BB_RHI ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 4 ->
getr regs (Z_to_bv 5 12) = w64 (4 - 0x3ffd) ->
getr regs (Z_to_bv 5 16) = w64 pp -> getr regs (Z_to_bv 5 20) = w64 SHADOW_OFF ->
getr regs (Z_to_bv 5 13) = w64 sh -> 0 <= sh <= 6 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (Z.lnot pp mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x120) 8 (-0x3ffd mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 ((pp + 0x4000) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x168) 8 (pp mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x170) 8 (shadow_addr (pp + 0x4000) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 4 ->
(forall (regs2 : bvmap 5 word) mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
 same_io mdc md2 ->
 (forall r, In r W3BB_KEPT -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 4 <= a < pp + 16) -> ~ (pp + 0x4000 <= a < pp + 0x400c) ->
  ~ (R + 0x110 <= a < R + 0x118) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) ->
 rtmb_bytes rsegs (w_H W) mem2 (pp + 4) (hdr_bytes sh) ->
 rtmb_bytes rsegs (w_H W) mem2 (pp + 16384) (le64 16) ->
 rtmb_bytes rsegs (w_H W) mem2 (pp + 16392) (le32 (Z.b2z (negb (sh =? 6)))) ->
 val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x110) 8 0 ->
 SRr rsegs W (cfg_at rsegs W3BB_PH regs2 mem2 md2) Q) ->
SRr rsegs W (cfg_at rsegs W3BB_BO regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp sh Q HJ Hin Hout Hpres
  HR0 HR1 HR2 HR3 R9 R10 R12 R16 R20 R13 Hsh V108 V120 V158 V168 V170 Vlen KONT.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof RtPgStepsB.rtsb_wx as Hwx. pose proof RtPgStepsB.rtsb_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (Erq : req_size PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp PP_SIZE HAR Hin) as (_ & Hpp0 & Hppc & Happ & Hppr & _).
rewrite Erq in Hppc, Happ, Hppr.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
assert (Hpphi : pp + 19744 <= 0x7fffff800000) by (unfold W3BB_RLO, W3BB_RHI in *; lia).
pose proof (w3bb_lnot_small pp ltac:(lia)) as Hnpp.
remember (Ereg regs [Z_to_bv 64 (Z.lnot pp mod 2 ^ 64)]) as E eqn:HE.
assert (HAE : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 (Z.lnot pp mod 2 ^ 64)]) n)
  by (intros; subst E; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; exact (ew_Ereg_nat regs _ n r Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 (Z.lnot pp mod 2 ^ 64)) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E9 : ew E 9 = Z_to_bv 64 R) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); exact R9).
assert (E16 : ew E 16 = Z_to_bv 64 pp) by (rewrite (EE 16%nat (Z_to_bv 5 16) eq_refl); exact R16).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (E13 : ew E 13 = Z_to_bv 64 sh) by (rewrite (EE 13%nat (Z_to_bv 5 13) eq_refl); exact R13).
assert (U9 : bv_unsigned (ew E 9) = R)
  by (rewrite E9; apply unsigned_lit_small; unfold W3BB_RLO, W3BB_RHI in *; lia).
assert (U16 : bv_unsigned (ew E 16) = pp) by (rewrite E16; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U13 : bv_unsigned (ew E 13) = sh) by (rewrite E13; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = Z.lnot pp mod 2 ^ 64)
  by (rewrite E32; apply unsigned_lit_small; rewrite Hnpp; lia).
(* the symbolic state at BO *)
assert (HS : st_ok rsegs E w3bb_ss_bo (restrict (w_H W) (mkst regs (Z_to_bv 64 W3BB_BO) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. unfold w3bb_ss_bo. apply (entry_st_ok_full rsegs).
  - unfold w3bb_regs_bo.
    apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |] | reflexivity |].
    + rewrite R10. reflexivity.
    + rewrite R12. unfold w64. cbn [sv_denot]. apply Z_to_bv64_eq_mod. reflexivity.
  - vm_compute. reflexivity.
  - rewrite <- HE. repeat apply Forall_cons; try apply Forall_nil.
    + unfold region_ok, w3bb_rR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [unfold W3BB_RLO in *; lia|]. split; [unfold W3BB_RHI in *; lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs E _ R 0x108 8 (SOff 32 0) (Z.lnot pp mod 2 ^ 64));
        [ rewrite (w3bb_off E 32%nat _ 0 E32), Z.add_0_r; apply Z_to_bv64_eq_mod; rewrite Zmod_mod; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite Hnpp; lia | cbn; lia | exact V108].
      * apply (chunk_ok_val rsegs E _ R 0x120 8 (SLit W3BB_M3FFD) (-0x3ffd mod 2 ^ 64));
        [reflexivity | split; [vm_compute; discriminate | vm_compute; reflexivity] | cbn; lia | exact V120].
      * apply (chunk_ok_val rsegs E _ R 0x158 8 (SOff 16 16384) ((pp + 0x4000) mod 2 ^ 64));
        [ rewrite (w3bb_off E 16%nat pp 16384 E16); apply Z_to_bv64_eq_mod; rewrite Zmod_mod; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | cbn; lia | exact V158].
      * apply (chunk_ok_val rsegs E _ R 0x168 8 (SOff 16 0) (pp mod 2 ^ 64));
        [ rewrite (w3bb_off E 16%nat pp 0 E16), Z.add_0_r; apply Z_to_bv64_eq_mod; rewrite Zmod_mod; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | cbn; lia | exact V168].
      * apply (chunk_ok_val rsegs E _ R 0x170 8 w3bb_shx (shadow_addr (pp + 0x4000) mod 2 ^ 64));
        [ apply (w3bb_shx_val E pp E16 E20); lia
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | cbn; lia | exact V170].
    + unfold region_ok, w3bb_rH. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U16. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). apply (proj1 (Hppr (pp + o) ltac:(lia))).
    + unfold region_ok, w3bb_rL. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U16. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply (proj1 (Hppr (pp + o) ltac:(lia)))|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SLit 4) 4);
        [reflexivity | split; [vm_compute; discriminate | vm_compute; reflexivity] | cbn; lia | exact Vlen].
  - rewrite <- HE. apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val w3bb_rR w3bb_rH w3bb_rL]. rewrite U9, U16.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; unfold W3BB_RLO in *; lia.
  - rewrite <- HE. split; [|split; exact I]. cbn [f_atoms w3bb_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U9, U16, U20, U13, U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    rewrite Hnpp. unfold W3BB_PPHI, W3BB_RLO, W3BB_RHI, SHADOW_OFF. repeat split; try exact I; lia. }
assert (SHOK : sh_ok rsegs w3bb_Bx w3bb_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, w3bb_SH. repeat apply Forall_cons; try apply Forall_nil.
  unfold shent_ok, app_apart, w3bb_Bx. cbn [she_m she_lo she_hi].
  rewrite (U_atom E 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom E 16 pp E16) by lia.
  split.
  - change (rd_of rsegs (mrestrict (w_H W) memc)) with (aview rsegs (w_H W) memc).
    apply (range_addressable_of_block rsegs B LAWS lyc Sc W memc mdc pp PP_SIZE);
      [exact HAR | exact Hin | lia | rewrite Erq; lia].
  - intros a Ha. unfold SHADOW_OFF. lia. }
clear HE.
unfold cfg_at. change (w64 W3BB_BO) with (Z_to_bv 64 W3BB_BO).
aj_run_to_tok w3bb_tbl_ok HS HJ SHOK w3bb_Bspan W3BB_PH.
{ (* the run writes the shape-7 flag cell of the real frame and pp's two windows *)
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
    [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_gen; [reflexivity | exact U16 | | ].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (pp + (a - pp)) by lia.
    apply (rt_fresh_awr _ _ _ _ _ _ _ pp PP_SIZE); [exact Hin | exact Hout | rewrite Erq; lia]. }
  eapply awr_ok_cons_gen; [reflexivity | exact U16 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (pp + (a - pp)) by lia.
  apply (rt_fresh_awr _ _ _ _ _ _ _ pp PP_SIZE); [exact Hin | exact Hout | rewrite Erq; lia]. }
(* ---- the state at 0x80ea0 ---- *)
pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _). cbn [ss_mem] in HOK.
pose proof (Forall_inv HOK) as (_ & _ & _ & Cr).
pose proof (Forall_inv (Forall_inv_tail HOK)) as (_ & _ & _ & Ch).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HOK))) as (_ & _ & _ & Cl).
cbn [YP09.r_base YP09.r_chunks base_val] in Cr, Ch, Cl. rewrite U9 in Cr. rewrite U16 in Ch, Cl. clear HOK.
repeat rewrite Forall_cons_iff in Cr. repeat rewrite Forall_cons_iff in Ch.
repeat rewrite Forall_cons_iff in Cl.
destruct Cr as (C110 & _).
destruct Cl as (Cisp & Clen & _).
destruct Ch as (C15 & C14 & C13 & C12 & C11 & C10 & C9 & C8 & C7 & C6 & C5 & C4 & _).
assert (Hs7 : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6) by lia.
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1.
apply (KONT (ms_regs ms) (ms_mem ms)).
- exact HJ.
- apply RtPgStepsB.same_io_wvb.
- intros r Hr. cbv [W3BB_KEPT] in Hr.
  repeat (destruct Hr as [<-|Hr];
    [eapply (w3bb_reg_kept E _ ms regs [Z_to_bv 64 (Z.lnot pp mod 2 ^ 64)] (w_H W));
       [exact HS | exact HAE | vm_compute; reflexivity] |]).
  destruct Hr.
- intros a Ha Ha1 Ha2 Ha3. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (rg & Hr & Hb).
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U9, ?U16 in Hb; lia | ]).
  destruct Hr.
- (* the twelve header bytes, one CVal 1 chunk each, at each of the seven shapes *)
  apply (proj2 (rtmb_bytes_aview rsegs (w_H W) (ms_mem ms) (pp + 4) (hdr_bytes sh))). intros i Hi.
  destruct Hs7 as [Hs|[Hs|[Hs|[Hs|[Hs|[Hs|Hs]]]]]]; rewrite Hs in E13, Hi |- *; cbn in Hi;
  (do 12 (destruct i as [|i];
    [ match goal with C : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 _)) |- _ =>
        eapply (w3bb_chunk1 E (w_H W) ms pp o _ _ C);
        [ | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia];
        cbn [sv_denot]; rewrite ?E13; vm_compute; reflexivity end | ])); lia.
- (* len = 16 *)
  apply rtmb_bytes_of_val.
  exact (val_of_chunk_ok rsegs E _ pp 16384 8 (SLit 16) 16 Clen eq_refl
    ltac:(split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(cbn; lia)).
- (* is_props = (shape <> 6) *)
  apply rtmb_bytes_of_val.
  apply (val_of_chunk_ok rsegs E _ pp 16392 4 _ _ Cisp); [ | | cbn; lia].
  + destruct Hs7 as [Hs|[Hs|[Hs|[Hs|[Hs|[Hs|Hs]]]]]]; rewrite Hs in E13 |- *;
    cbn [sv_denot]; rewrite E13; vm_compute; reflexivity.
  + destruct (negb (sh =? 6)); cbn; lia.
- (* the shape-7 flag cell is 0 *)
  exact (val_of_chunk_ok rsegs E _ R 272 8 (SLit 0) 0 C110 eq_refl
    ltac:(split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(cbn; lia)).
Qed.

(* ===================================== the piece statement ===================================== *)
Section e.
Variable MT : ameter_ops.

Ltac w3bb_in_kept := cbv [W3BB_KEPT]; cbn [In]; lia.
(* a cell fact of BO's list that the run keeps: none of its 8 bytes is in a write window *)
Ltac w3bb_cell C :=
  lazymatch goal with
  | HM : forall a, _ -> _ -> _ -> _ -> aview _ _ ?m3 a = aview _ _ ?m2 a |- _ =>
      eapply (rtmb_at_kept rsegs _ m2 _ m3 _ _ _ _ _ C);
      cbn [rtmb_keeps rt_xv]; let i := fresh "i" in let Hi := fresh "Hi" in
      intros i Hi; apply HM; lia
  end.

(* BO -> PH *)
Lemma rsb_piece_W3b_hdr : rsb_piece_W3b_hdr_stmt rsegs B MT.
Proof.
intros cx POST rest HST HPH ly2 S2 W2 regs2 mem2 md2 r sh np (HC & HA13 & Hsh7).
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct HST as (HPRE & _ & _ & _ & _).
pose proof HPRE as (HJc & _ & _ & _ & _ & HSe & _ & HRsz & HRstk & Hown & HFe & _ & Hppc & _ & _ & _ & _ & _ & _ & _
  & Hfresh & _ & _).
cbn [hi_rsz hi_cid rate_himg_B] in HRsz, Hown, HFe.
destruct HC as (HCORE & HAT & HFSH & HPP & HIN & HSUF & Esh & Enp & Er).
pose proof HCORE as (HJ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
(* the bounds of R and pp *)
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HT : T_SEG_STK = 16384) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppc) as (_ & Hpp0 & Hppcl & Happ & _ & _).
change (req_size PP_SIZE) with 19744 in Hppcl, Happ.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
assert (Hsh : 0 <= sh <= 6)
  by (assert (0 <= sh < 8) by (rewrite Esh; unfold rsb_sh; apply Z.mod_pos_bound; lia); lia).
assert (Hin2 : In (q_pp (x_e rsegs cx), PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppc]).
(* pp lies well below the segment's stack window *)
assert (HppR : q_pp (x_e rsegs cx) + 19744 <= q_R (x_e rsegs cx) - 16384) by lia.
(* the facts of BO's location list *)
unfold rsb_at_cx, rsb_at, rsb_L_hdr, rsb_Hch, rsb_cur2 in HAT. cbn [app] in HAT.
repeat rewrite Forall_cons_iff in HAT.
destruct HAT as (A10 & A12 & A16 & A17 & A22 & A8 & A9 & A19 & A20 & C158 & A24 & A25 & C168 & C50 & C118 & C170
  & C120 & A11 & C108 & C48 & C30 & C38 & C40 & A26 & C148 & A18 & A29 & _).
unfold rsb_at_cx, rsb_at in HA13. pose proof (Forall_inv HA13) as A13.
pose proof C108 as V108. pose proof C120 as V120. pose proof C158 as V158.
pose proof C168 as V168. pose proof C170 as V170.
cbn [fst snd rt_at rt_xv] in A10, A12, A16, A17, A22, A8, A9, A19, A20, A24, A25, A11, A26, A18, A29, A13,
  V108, V120, V158, V168, V170.
pose proof (rtmb_pp_len rsegs (le32 0) false false false [] false
  ltac:(unfold POD_BUF_MAX; rewrite length_le32; lia) ltac:(cbn; lia) ltac:(constructor)
  (w_H W2) mem2 (q_pp (x_e rsegs cx)) HPP) as Vlen.
unfold OFF_LEN in Vlen. rewrite length_le32 in Vlen. cbn [Z.of_nat Pos.of_succ_nat] in Vlen.
eapply (w3bb_hdr_core _ _ _ _ _ _ _ _ _ ly2 S2 W2 mem2 md2 _ regs2 (q_R (x_e rsegs cx)) (q_pp (x_e rsegs cx)) sh
  POST HJ Hin2 Hfresh Hstkp);
  try (unfold W3BB_RLO, W3BB_RHI; lia); try eassumption.
intros regs3 mem3 md3 HJ3 Hio3 HK3 HM3 Bh Bl Bi V110.
apply (HPH ly2 S2 W2 regs3 mem3 md3 r sh np).
unfold rsb_cut_PH. split; [|split; [|split; [|split]]].
- (* the journal and the kept bytes *)
  unfold rsb_core, rsb_mid. split; [exact HJ3|].
  split; [intros rr Hrr; rewrite <- (H234 rr Hrr); destruct Hrr as [->|[->| ->]]; apply HK3; w3bb_in_kept|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
  split; [exact Hmo|].
  intros a Ha HnS HnE. rewrite <- (Hkeep a Ha HnS HnE).
  apply HM3; [exact Ha | | |].
  + intros X. apply HnE. right. unfold PP_SIZE. lia.
  + intros X. apply HnE. right. unfold PP_SIZE. lia.
  + intros X. apply HnE. left. unfold rt_inw. cbn [hi_w1 rate_himg_B].
    apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd rt_xv]. lia.
- (* PH's location list: BO's facts, kept, with the shape-7 flag cell the run wrote *)
  unfold rsb_at_cx, rsb_at, rsb_L_PH, rsb_Hch, rsb_cur2. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  first
    [ (* a register the run leaves alone *)
      cbn [rt_at];
      lazymatch goal with |- getr _ (Z_to_bv 5 ?n) = _ => rewrite (HK3 n ltac:(w3bb_in_kept)) end;
      assumption
    | (* the shape-7 flag cell, the only one of the list the run wrote *)
      cbn [rt_at rt_xv]; rewrite (proj2 (Z.eqb_neq sh 7) Hsh7); cbn [Z.b2z];
      change (0 mod 2 ^ 64) with 0; exact V110
    | (* a cell of BO's list: none of its eight bytes is in a write window *)
      cbn [rt_at rt_xv]; let k := fresh "k" in let Hk := fresh "Hk" in
      intros k Hk;
      rewrite (mbyte_of_aview rsegs (w_H W2) (w_H W2) mem2 mem3) by (apply HM3; lia);
      revert k Hk; assumption ].
- (* the frame's shadow: no byte of it is written *)
  apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 _ rsb_P0 HFSH).
  intros i Hi. change (length rsb_P0) with 88%nat in Hi.
  assert (HFd : 0 <= q_F (x_e rsegs cx) / 8 <= 17592184995840).
  { assert (HFin : In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx)))
      by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
    destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HARc HFin) as (HF0 & HFc & _).
    rewrite <- HFe in HF0, HFc. change (fs_frame_bytes 4) with 1024 in HFc.
    split; [apply Z.div_pos; lia | apply (Z.div_le_mono _ 0x7fffff800000 8); lia]. }
  apply HM3; unfold shadow_addr, SHADOW_OFF; lia.
- (* the block holds the empty record of this shape *)
  apply (w3bb_ph_img (w_H W2) mem2 (w_H W2) mem3 _ sh Hsh HPP Bh Bl Bi).
  intros y Hy Hn1 Hn2. apply HM3; lia.
- split; [exact HIN|]. split; [exact HSUF|]. split; [exact Esh|]. split; [exact Enp | exact Er].
Qed.
End e.
End d.
End b.

Print Assumptions rsb_piece_W3b_hdr.
