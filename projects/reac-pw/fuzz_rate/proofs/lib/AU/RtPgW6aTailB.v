(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at (lines 2155-2206) restated for image A's code with the callee's same_but_materialized kept as same_io in the post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Call.v at 888d1ffb4c3 for reac-pw/fuzz_headamp image A: module paths changed, w_intrin_at renamed hd_intrin_at, role's RPgCfgChanges.cfg_segs_low replaced by HPgSteps.img_segs_low over headamp's segments; the two instances hd_memset_at / hd_memcpy_at are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgIntrin.v at 021dba8dbbd; hd_intrin_at renamed cb_intrin_at and stated over image B's segments (lib/AU/Img0U.v rsegs, lib/AU/HPgSteps.v img_segs_low, AR_laws from YG0q.AR_laws_ok), hd_memset_at / hd_memcpy_at renamed cb_memset_at / cb_memcpy_at with the entry pc made a parameter (image B's entries CB_ASAN_MEMSET 0x52228 and CB_ASAN_MEMCPY 0x51d8c stated as constants). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6cKit.v at 80bf14ccf11 (PART 1, a segment's start facts at a cut); rs_ -> cb_, restated over lib/AU/HPgSeg.v (hsu_pre, hsu_core, hsu_E1, hsu_in, hsu_fsh_at) at image B's record headamp_himg_B: the frame for locals of class 4 (1024 bytes, 128 shadow bytes), the 116-byte prologue pattern in place of role's 52, R + 0x220 in place of 0x1a0, image B's three write ranges of hi_w1, the image fact segs_low taken from lib/AU/HPgSteps.v img_segs_low instead of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v at 80bf14ccf11 (w6_ctx, w6_caller_saved and Section seq only; w6_in as cb_in); w6_ -> cb_, the frame (4, pos) and R + 0x220 of image B, R's cells [R, R + 0x198), and the block post w6_post replaced by the shared layer's hdu_blk_postE (lib/AU/HPgSteps.v), rl_blk_post by hdu_blk_post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6a.v at 80bf14ccf11 (its generic helpers only: the list tactics, the register and location-list lemmas, the geometry of a cut, the image's first write range, the suffix and cursor lemmas, pp's image length, the cut's geometry and context, the core step, the input kept, the block step and the side tactics); w6_ -> cb_, over lib/AU/HPgSeg.v at image B: w6_geo with image B's frame (1024 / 128 bytes, R + 0x220) and the conjuncts F mod 32 = 0 and in_app pp, its head- and tail-specific cell lemmas replaced by write-set-free disjointness lemmas, w6_in_kept and the side tactics generalised over the write set, cb_blkE_step added for a block that writes. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at 80bf14ccf11 (w6h_div, w6h_sh_e, w6h_e_mod8, w6h_bounds, w6h_callee, w6h_val_kept, w6h_chunk0, w6h_region_nth, w6h_chunks); w6h_ -> cb_, the shadow and alignment lemmas generalised over the offset, the bounds at class 4 (1024 bytes, 128 shadow bytes) and e62's 104 bytes at F + 0x210. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at f3898085bda (w7_post,
   w7_post_of_run), RPgW7bKit.v at f3898085bda (w7_kept, w7_hull, w7_ra_kept, w7_hull_kept, w7_strok, w7_strz and
   their lemmas), RPgCfgChanges.v at f3898085bda (kept_run), RPgW6aTail.v at f3898085bda (tl_byte, tl_val_of_chunk,
   tl_val_at), RPgW6aC2h.v at f3898085bda (c2_all256, c2_envz, c2_nz, c2_notin, c2_kio) and RPgW7bIter.v at
   f3898085bda (w7_cs_bv, w7_cs_out, w7_reg_eq), by way of lib/AU/HPgW6bC1k.v's and
   HPgW6bC1.v's hb1_* copies for reac-pw/fuzz_headamp's image B: moved here and renamed cb_* by the dedup, one copy
   kept for the equal helpers of 17 lib/AU files (HPgE0Base, HPgW7bBase, HPgW7bIter, HPgW6aTail, HPgW6aC2 and
   others); cb_val_at_rng is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgCaseB.v, with its module paths and module names changed; 158 of its 211 lines of code are new or changed and 1036 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aTail.v at e261793226b4; ported to reac-pw/fuzz_rate's image A: module paths changed (images.Asan for lib/A/Img0, RtPgBase / RtPgCSpec / RtPgSteps / RtPgW6aBase for the RPg files, RtPgSteps' rts_wx / rts_segs_low / same_io_wvb / regs_kept_of_st_ok / rts_post for RPgCfgChanges' and RPgSteps' facts and w6_post); rate's pcs and the cell [R+0x138] for [R+0xf0]; rate's tail stores in.n to s8 (`mv s8,a1`) instead of the cell [R+0xf8], so the s1-based region is read-only, the post has three stored values and s8 in place of s9; the frame facts use the kit's AR_laws_ok instead of a LAWS hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aTail.v at 88912827c774; ported to image B (fuzz_rate.asan-ubsan): images.AsanUbsan, lib/AU/RtPgStepsB.v and lib/AU/RtPgW6aBaseB.v; B's four entries 0x82038 / 0x8203c / 0x820bc / 0x820c0 (a4 = 4 pinned at the second entry of each case), e62 based at s6 (x22) in the class-4 frame (1024 bytes) instead of a pointer loaded from [R+0x138], the read-only cell [R+0x158] reloaded into s2, the post t1 / s10 / s2 and the three stored values; AR_laws is a Section hypothesis. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the block lemma w6b_tail_all
   of lib/AU/RtPgW6aBaseB.v, the common tail of ent_build's cases 2 and 3 (pod.h:301, pod.h:321-322) to the join
   J 0x820dc. Proves no function (kind: segment lemma).
     0x82038  li a4,4                                    (case 2 from the u32 block)
     0x8203c  sw a4,0(s6) (e62.type = 4); j 0x820c8       (case 2 from its head, a4 = 4)
     0x820bc  li a4,4                                    (case 3 from the u32 block)
     0x820c0  li a0,6; sw a0,0(s6) (e62.type = 6)         (case 3 from its head, a4 = 4)
     0x820c8  sw a4,4(s6); sw a1,8(s6); mv t1,a2; mv s10,s2; 0x820d8 ld s2,0x158(s1)   -> J 0x820dc
   No instrumented check and no branch: one engine run from the entry's pc to J.
   THE ENTRY STATE, over Ereg regs [pv] (env slot 32 = the value of the cell [R+0x158, R+0x160)):
     tl_rR  based at s1 = R (x9): the cell [R+0x158, R+0x160), the 8-byte chunk holding slot 32's atom, so
            `ld s2,0x158(s1)` leaves s2 = that atom. No write window (awr_ok_cons_ro).
     tl_rE  based at s6 = F + 0x210 (x22): the write window [0, 12) = e62.type, e62.size, e62.body[0..4), inside the
            frame (4, pos) the harness owns (fs_frame_bytes 4 = 1024): awr_ok_cons_gen + in_frames.
     a4     at the second entry of each case (a = false) pinned to the literal 4 (the premise getr regs 14 = w64 4).
     facts: R in [2^46, 2^47] and F + 0x210 in [4096, 2^47], both 16-aligned. The block reads no shadow (no shadow
     entry, no obligation), so the shadow span the write windows are checked against is empty: (0, 0).
   THE POST: the three stored values from the final state's chunks (tl_val_at), the registers outside
   w6b_tail_clob from their atoms (regs_kept_of_st_ok), t1 = a2's atom, s10 = s2's atom, s2 = slot 32's atom, every
   byte outside w6b_tail_wr from the run's frame. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgStepsB RtPgW6aBaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term (as
   RtPgStepsB.v) *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the entry state ======================================== *)
Definition tl_rR : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x158 0x160 0 0 [YP09.mkChunk 0x158 (CVal 8 (SOff 32 0))].
Definition tl_rE : YP09.region := YP09.mkRegion (Some 22%nat) 0 12 0 12 [].
Definition tl_regions : smem := [tl_rR; tl_rE].
Definition tl_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (22%nat, mkAF 4096 (2 ^ 47) 4)] [] [].
(* the registers at entry: their own atoms; at the second entry of each case (a = false) a4 = 4 *)
Definition tl_sr (a : bool) : list sv := if a then sr_atoms else sr_set sr_atoms (14%bv : bv 5) (SLit 4).
Definition ss_tl (pc : Z) (a : bool) : sstate := mkSS pc (tl_sr a) tl_regions None tl_facts.
Definition tl_extra (pv : Z) : list word := [Z_to_bv 64 pv].
Definition tl_Bx : sv := SLit SHADOW_OFF.
Definition tl_Bspan : Z * Z := (0, 0).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ======================================== helpers ======================================== *)
(* byte k of a stored word is byte k of its low w bytes *)
Lemma tl_byte : forall v (w k : nat), (k < w)%nat -> (w <= 8)%nat ->
Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) (8 * Z.of_nat k)) = Z_to_bv 8 (YO0f.le_byte v w k).
Proof.
intros v w k Hk Hw. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64). change 256 with (2 ^ 8).
rewrite Z.mod_mod by lia.
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hi8|Hi8].
- rewrite !(Z.mod_pow2_bits_low _ 8 i) by lia. rewrite !Z.shiftr_spec by lia.
  rewrite (Z.mod_pow2_bits_low v 64) by lia. rewrite (Z.mod_pow2_bits_low v (8 * Z.of_nat w)) by lia. reflexivity.
- rewrite !(Z.mod_pow2_bits_high _ 8 i) by lia. reflexivity.
Qed.
(* a chunk CVal n e of a region holds the low n bytes of e's value *)
Lemma tl_val_of_chunk : forall E mem base off (n : N) e v,
YP09.chunk_ok rsegs E mem base (YP09.mkChunk off (CVal n e)) -> sv_denot E e = Z_to_bv 64 v -> (N.to_nat n <= 8)%nat ->
val_mem rsegs mem (base + off) (N.to_nat n) v.
Proof.
intros E mem base off n e v H He Hn k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
unfold YP09.byte_of_word in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal. apply tl_byte; lia.
Qed.
(* the stored value as the statement gives it (mod 2 ^ (8 n)) *)
Lemma tl_val_mod : forall mem a (n : nat) v M, 2 ^ (8 * Z.of_nat n) = M ->
val_mem rsegs mem a n v -> val_mem rsegs mem a n (v mod M).
Proof.
intros mem a n v M HM H k Hk. rewrite (H k Hk). subst M. unfold YO0f.le_byte.
rewrite Z.mod_mod; [reflexivity|]. apply Z.pow_nonzero; lia.
Qed.
(* a chunk of region i of a final state, at absolute address a *)
Lemma tl_val_at : forall E ss H ms i r off (n : N) e v b a,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) -> base_val E (YP09.r_base r) = b ->
sv_denot E e = Z_to_bv 64 v -> (N.to_nat n <= 8)%nat -> a = b + off ->
val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof.
intros E ss H ms i r off n e v b a HS Hi Hc Hb He Hn ->.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hok & _).
rewrite Forall_forall in Hok. specialize (Hok r (nth_error_In _ _ Hi)).
pose proof (YP09.region_ok_chunk rsegs E _ r _ Hok Hc) as Hck. rewrite Hb in Hck.
exact (tl_val_of_chunk E _ b off n e v Hck He Hn).
Qed.
(* a register of a final state *)
Lemma tl_reg : forall E ss H ms (r : bv 5) e w,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = w -> getr (ms_regs ms) r = w.
Proof. intros E ss H ms r e w HS He Hw. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), He. exact Hw. Qed.
Lemma tl_atom : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
sv_denot (Ereg regs extra) (SOff n 0) = getr regs r.
Proof.
intros regs extra n r Hn. apply bv_eq. rewrite denot_SOff, (ew_Ereg_nat regs extra n r Hn), Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
unfold M64. lia.
Qed.

(* the entry state with every register its own atom is sound for the machine at any pc *)
Lemma tl_entry : forall pc (W : world rsegs) regs memc R F pv,
getr regs 9 = w64 R -> 2 ^ 46 <= R -> R + 0x160 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 22 = w64 (F + 0x210) -> 4096 <= F -> F + 1024 <= R -> F mod 32 = 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 pv -> 0 <= pv < 2 ^ 64 ->
(forall a, F + 0x210 <= a < F + 0x21c -> apresent (w_H W) memc a) ->
st_ok rsegs (Ereg regs (tl_extra pv)) (ss_tl pc true)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc W regs memc R F pv H9 HR0 HR1 HR16 H22 HF0 HFR HF32 Hval Hpv HpE.
rewrite restrict_mkst_fx.
assert (B9 : bv_unsigned (ew (Ereg regs (tl_extra pv)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (B22 : bv_unsigned (ew (Ereg regs (tl_extra pv)) 22) = F + 0x210)
  by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl), H22; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs (tl_extra pv)) 32 = Z_to_bv 64 pv) by exact (ew_Ereg_extra regs (tl_extra pv) 0).
assert (HE16 : (F + 0x210) mod 16 = 0).
{ apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). apply (proj1 (Z.mod_divide F 32 ltac:(lia))) in HF32.
  destruct HF32 as [q Hq]. exists (2 * q + 33). lia. }
unfold ss_tl, tl_sr. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold tl_regions, tl_rR, tl_rE. constructor; [|constructor; [|constructor]].
  + unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9.
    split; [lia|]. split; [lia|]. split.
    * intros o Ho. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ R 0x158 8 (SOff 32 0) pv).
      -- apply rtsb_den_atom; [exact E32 | exact Hpv].
      -- change (8 * Z.of_N 8) with 64. lia.
      -- cbn. lia.
      -- exact Hval.
  + unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B22.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply HpE. lia.
- unfold tl_regions, tl_rR, tl_rE. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B9, B22.
  split; [split; [right; lia | exact I] | split; exact I].
- split; [|split; [exact I | exact I]]. cbn [tl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite B9, B22. change (2 ^ 4) with 16. repeat split; lia.
Qed.

Ltac tl_reg_tac HS r :=
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e := eval vm_compute in (sr_get (ss_regs ssf) r) in
  eapply (tl_reg _ ssf _ _ r e); [exact HS | vm_compute; reflexivity |] end.
Ltac tl_in := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* the four entries at once: c3 picks the case, a the entry (from the u32 block, or from the head with a4 = 4) *)
Lemma w6b_tail_all : forall c3 a, w6b_tail_stmt B MT c3 a.
Proof using MTL LAWS.
intros c3 a. unfold w6b_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos n' v cn pv
  (HJ & HR16 & HRhi & HRlo & Hown & HF & Hrom) H9 H22 H11 H12 H18 H14 Hcell Hpv.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Has : T_SEG_STK = 16384) by reflexivity.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF32 & _ & HFpres & _).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _).
rewrite <- HF in HF32, HFpres, HF4096, HFceil.
change (fs_frame_bytes 4) with 1024 in HFpres, HFceil.
assert (BR : 2 ^ 46 <= R /\ R + 0x160 <= 2 ^ 47 /\ F + 1024 <= R) by lia.
destruct BR as (BR0 & BR1 & BR2).
assert (B9 : bv_unsigned (ew (Ereg regs (tl_extra pv)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (B22 : bv_unsigned (ew (Ereg regs (tl_extra pv)) 22) = F + 0x210)
  by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl), H22; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs (tl_extra pv)) 32 = Z_to_bv 64 pv) by exact (ew_Ereg_extra regs (tl_extra pv) 0).
assert (HS0 : forall pc, st_ok rsegs (Ereg regs (tl_extra pv)) (ss_tl pc true)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs)))).
{ intros pc. apply (tl_entry pc W regs memc R F pv H9 BR0 BR1 HR16 H22 HF4096 BR2 HF32 Hcell Hpv).
  intros x Hx. apply (proj1 (HFpres x ltac:(lia))). }
assert (HS : st_ok rsegs (Ereg regs (tl_extra pv)) (ss_tl (w6b_tail_pc c3 a) a)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (w6b_tail_pc c3 a)) memc (seg_rom rsegs)))).
{ destruct a; [exact (HS0 _)|].
  exact (st_ok_pin_lit rsegs _ (ss_tl (w6b_tail_pc c3 false) true) _ 14%bv 4 (HS0 _) eq_refl H14). }
clear HS0.
assert (SHOK : sh_ok rsegs tl_Bx [] (Ereg regs (tl_extra pv)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (tl_extra pv)) (Ereg regs (tl_extra pv))) by apply env_agree_refl.
destruct c3, a; cbv beta iota in H14; cbn [w6b_tail_pc] in HS |- *;
unfold cfg_at;
(aj_run_to_tok w6b_tbl_ok HS HJ SHOK tl_Bspan W6B_J;
[ (* the write windows: the s1 cell is read-only, e62's 12 bytes lie in the frame (4, pos) *)
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 22%nat (F + 0x210));
  [ reflexivity | exact B22
  | cbn [YP09.r_wlo YP09.r_whi]; intros x Hx;
    right; right; right; exists 4, pos; split; [exact Hown|]; left;
    unfold in_zr; cbn [fst snd]; rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia
  | apply awr_ok_nil ]
| (* the leaf at J *)
  lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ =>
    apply SRr_ret; unfold rtsb_post; exists lyc, Sc, (ms_regs ms), (ms_mem ms), md end;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs (tl_extra pv) (w_H W) _ HS HAE); vm_compute; reflexivity|];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
  split; [apply mo_le_refl; assumption|];
  split;
  [ intros x Hx Hn; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 x)); [reflexivity|];
    intros (r & Hin & Hr); apply Hn; unfold w6b_tail_wr; rewrite unsigned_lit_small in Hr by lia;
    cbn [ss_mem ss_tl tl_regions In] in Hin;
    destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val tl_rR tl_rE] in Hr;
    rewrite ?B9, ?B22 in Hr; lia
  | cbv beta ];
  split; [tl_reg_tac HS (6%bv : bv 5); rewrite (tl_atom regs _ 12 12%bv eq_refl); exact H12|];
  split; [tl_reg_tac HS (26%bv : bv 5); rewrite (tl_atom regs _ 18 18%bv eq_refl); exact H18|];
  split; [tl_reg_tac HS (18%bv : bv 5); unfold w64; apply rtsb_den_atom; [exact E32 | exact Hpv]|];
  split; [eapply (tl_val_at _ _ (w_H W) ms 1%nat _ 0 4%N _ _ (F + 0x210) _);
          [exact HS | reflexivity | tl_in | cbn [YP09.r_base base_val]; exact B22 | reflexivity | cbn; lia | lia]|];
  split; [eapply (tl_val_at _ _ (w_H W) ms 1%nat _ 4 4%N _ _ (F + 0x210) _);
          [exact HS | reflexivity | tl_in | cbn [YP09.r_base base_val]; exact B22 | reflexivity | cbn; lia | lia]|];
  apply (tl_val_mod _ _ 4 v (2 ^ 32)); [reflexivity|];
  eapply (tl_val_at _ _ (w_H W) ms 1%nat _ 8 4%N _ v (F + 0x210) _);
  [exact HS | reflexivity | tl_in | cbn [YP09.r_base base_val]; exact B22
  | rewrite (tl_atom regs _ 11 11%bv eq_refl); exact H11 | cbn; lia | lia] ]).
Qed.
End d.
End b.

Print Assumptions w6b_tail_all.
