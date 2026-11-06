(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 174 of its 211 lines of code are new or changed and 253 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aTail.v at e261793226b4; ported to reac-pw/fuzz_rate's image A: module paths changed (images.Asan for lib/A/Img0, RtPgBase / RtPgCSpec / RtPgSteps / RtPgW6aBase for the RPg files, RtPgSteps' rts_wx / rts_segs_low / same_io_wvb / regs_kept_of_st_ok / rts_post for RPgCfgChanges' and RPgSteps' facts and w6_post); rate's pcs and the cell [R+0x138] for [R+0xf0]; rate's tail stores in.n to s8 (`mv s8,a1`) instead of the cell [R+0xf8], so the s1-based region is read-only, the post has three stored values and s8 in place of s9; the frame facts use the kit's AR_laws_ok instead of a LAWS hypothesis. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aTail.v, with its module paths, module names, addresses and numbers changed; 139 of its 207 lines of code are new or changed and 143 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aTail.v at e261793226b4; restated for
   reac-pw/fuzz_headamp image B: module paths fuzz_role -> fuzz_headamp, lib/A/Img0 -> lib/AU/Img0U, the tl_ prefix
   -> w6t_; role's two entries (which reload &e from [R+0xf0]) replaced by image B's four entries (&e62 already in
   s4; two of them after a fuzz_u32 block, which first set a4 := 4); image B's read of the cell [R+0x138] into s2 in
   place of role's store to [R+0xf8]; the frame class 3 -> 4; the post hdu_blk_postE of lib/AU/HPgSteps.v and the
   context cb_ctx of lib/AU/HPgCaseB.v in place of role's w6_post / w6_ctx. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the block lemmas w6b_tail2u / w6b_tail2 / w6b_tail3u / w6b_tail3 of lib/AU/HPgW6aBase.v, the common tail
   of ent_build's cases 2 and 3 (pod.h:298-324) in LLVMFuzzerTestOneInput (0x80c40), to the join J 0x82618.
   Proves no function (kind: segment lemma).
     0x82574  addi a4,zero,4                                    (case 2's fuzz_u32 exit only)
     0x82578  sw a4,0(s4); 0x8257c j 0x82604                     e62.type := 4 (case 2)
     0x825f8  addi a4,zero,4                                    (case 3's fuzz_u32 exit and its literal arms)
     0x825fc  addi a0,zero,6; 0x82600 sw a0,0(s4)               e62.type := 6 (case 3)
     0x82604  sw a4,4(s4)                                       e62.size := 4
     0x82608  sw a1,8(s4)                                       e62.body[0..4) := the low four bytes of a1
     0x8260c  mv t1,a2; 0x82610 mv a3,s2; 0x82614 ld s2,0x138(s1)                                -> J 0x82618
   No instrumented check and no conditional branch: one engine run per entry over w6b_tbl.
   THE REGISTERS AND CELLS. s1 = x9 = R (the real frame's base), s4 = x20 = F + 0x210 (&e62), a1 = x11 = the value,
   a2 = x12 = what is left, s2 = x18 = the cursor, a4 = x14 = 4 (set by the block on the two fuzz_u32 entries, a
   premise on the two others), a0 = x10 = 6 (case 3); the block writes t1 = x6, a0, a3 = x13, a4 and s2. The one
   real-frame cell it reads is [R+0x138] = pp + Layout.OFF_LEN.
   THE ENTRY STATE, over Ereg regs [pp + Layout.OFF_LEN] (env slot 32 = the value of the cell [R+0x138]):
     w6t_rR  based at s1 = R: the cell [R+0x138, R+0x140), read only, a chunk holding slot 32's atom (the premise
             val_mem (R+0x138) 8 (pp + Layout.OFF_LEN), taken mod 2 ^ 64), so `ld s2,0x138(s1)` leaves s2 = that
             atom.
     w6t_rE  based at s4 = F + 0x210: the write window [0, 12) = e62.type, e62.size, e62.body[0..4), inside the
             frame (4, pos) the harness owns (fs_frame_bytes 4 = 1024): awr_ok_cons_gen + in_frames.
     facts: R in [2^46, 2^47] and F + 0x210 in [4096, 2^47], both 16-aligned. The block reads no shadow byte.
   THE POST: the three stored words from the final state's chunks (cb_val_at), t1 / a3 / s2 from the final state's
   registers (w6t_reg), the registers outside [t1; a0; a3; a4; s2] from their atoms (regs_kept_of_st_ok), every byte
   outside w6b_tail_wr from the run's frame. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg HPgCaseB.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgW6aBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the entry state ======================================== *)
Definition w6t_rR : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x138 0x140 0 0 [YP09.mkChunk 0x138 (CVal 8 (SOff 32 0))].
Definition w6t_rE : YP09.region := YP09.mkRegion (Some 20%nat) 0 12 0 12 [].
Definition w6t_regions : smem := [w6t_rR; w6t_rE].
Definition w6t_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF 4096 (2 ^ 47) 4)] [] [].
Definition ss_w6t (pc : Z) : sstate := mkSS pc sr_atoms w6t_regions None w6t_facts.
Definition w6t_extra (pp : Z) : list word := [Z_to_bv 64 (pp + Layout.OFF_LEN)].
(* the four entries: c3 picks the case, u the entry after the case's fuzz_u32 block *)
Definition w6t_pc (c3 u : bool) : Z :=
if c3 then (if u then W6B_U3E else W6B_T3) else (if u then W6B_U2E else W6B_T2).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ======================================== helpers ======================================== *)
(* a stored value as the statement gives it (mod 2 ^ (8 n)) *)
Lemma w6t_val_mod : forall mem a (n : nat) v M, 2 ^ (8 * Z.of_nat n) = M ->
val_mem rsegs mem a n v -> val_mem rsegs mem a n (v mod M).
Proof.
intros mem a n v M HM H k Hk. rewrite (H k Hk). subst M. unfold YO0f.le_byte.
rewrite Z.mod_mod; [reflexivity|]. apply Z.pow_nonzero; lia.
Qed.
(* a register of a final state *)
Lemma w6t_reg : forall E ss H ms (r : bv 5) e w,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = w -> getr (ms_regs ms) r = w.
Proof. intros E ss H ms r e w HS He Hw. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), He. exact Hw. Qed.
(* an atom read as a value *)
Lemma w6t_soff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. apply bv_eq. rewrite denot_SOff, Z.add_0_r. apply zcanon_id.
pose proof (bv_unsigned_in_range _ (ew E n)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
Qed.

(* the entry state is sound for the machine at any of the four entries *)
Lemma w6t_entry : forall pc (W : world rsegs) regs memc R F pp,
getr regs 9 = w64 R -> getr regs 20 = w64 (F + 0x210) ->
2 ^ 46 <= R -> R + 0x140 <= 2 ^ 47 -> R mod 16 = 0 ->
4096 <= F -> F + 0x21c <= R + 0x138 -> F mod 32 = 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + Layout.OFF_LEN) ->
(forall a, F + 0x210 <= a < F + 0x21c -> apresent (w_H W) memc a) ->
st_ok rsegs (Ereg regs (w6t_extra pp)) (ss_w6t pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc W regs memc R F pp H9 H20 HR0 HR1 HR16 HF0 HFR HF32 Hval HpE.
rewrite restrict_mkst_fx.
assert (B9 : bv_unsigned (ew (Ereg regs (w6t_extra pp)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (B20 : bv_unsigned (ew (Ereg regs (w6t_extra pp)) 20) = F + 0x210)
  by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs (w6t_extra pp)) 32 = Z_to_bv 64 (pp + Layout.OFF_LEN))
  by exact (ew_Ereg_extra regs (w6t_extra pp) 0).
assert (HE16 : (F + 0x210) mod 16 = 0).
{ apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). apply (proj1 (Z.mod_divide F 32 ltac:(lia))) in HF32.
  destruct HF32 as [q Hq]. exists (2 * q + 33). lia. }
unfold ss_w6t. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold w6t_regions, w6t_rR, w6t_rE. constructor; [|constructor; [|constructor]].
  + unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ R 0x138 8 (SOff 32 0) ((pp + Layout.OFF_LEN) mod 2 ^ 64)).
    * rewrite w6t_soff0, E32. symmetry. apply Z_to_bv_mod64.
    * change (8 * Z.of_N 8) with 64. apply Z.mod_pos_bound. lia.
    * cbn. lia.
    * apply (w6t_val_mod _ _ 8 _ (2 ^ 64)); [reflexivity | exact Hval].
  + unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B20.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply HpE. lia.
- unfold w6t_regions, w6t_rR, w6t_rE. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B9, B20.
  split; [split; [right; lia | exact I] | split; exact I].
- split; [|split; [exact I | exact I]]. cbn [w6t_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite B9, B20. change (2 ^ 4) with 16. repeat split; lia.
Qed.

Ltac w6t_reg_tac HS r :=
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e := eval vm_compute in (sr_get (ss_regs ssf) r) in
  eapply (w6t_reg _ ssf _ _ r e); [exact HS | vm_compute; reflexivity |] end.
Ltac w6t_in := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).
(* the value 4 of a4: a literal on the fuzz_u32 entries, the entry atom (premise H14) on the two others *)
Ltac w6t_sv4 regs H14 :=
first [ reflexivity | rewrite w6t_soff0, (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14 ].

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the geometry the block needs, from the block context: R above the frame (4, pos), both in [2^46, 2^47) *)
Lemma w6t_geo : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos,
cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\ In (4, pos) own /\ F = frame_addr lyc 4 pos /\
R mod 16 = 0 /\ 2 ^ 46 <= R /\ R + 0x140 <= 2 ^ 47 /\ F + 0x21c <= R + 0x138.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos (HJ & HR32 & HRsp & HRstk & Hown & HFa & _).
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & HFceil & _).
rewrite <- HFa in HFceil. change (fs_frame_bytes 4) with 1024 in HFceil.
split; [exact HJ|]. split; [exact Hown|]. split; [exact HFa|].
split.
{ apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). apply (proj1 (Z.mod_divide R 32 ltac:(lia))) in HR32.
  destruct HR32 as [q Hq]. exists (2 * q). lia. }
clear HR32. unfold T_SEG_STK, ASTACK in HRstk. repeat split; lia.
Qed.

(* the four entries at once: c3 picks the case and the type word, u the entry pc *)
Lemma w6b_tail_all : forall c3 u, w6b_tail_stmt B MT c3 (w6t_pc c3 u).
Proof using MTL.
intros c3 u. unfold w6b_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos pp n' v c'
  Hctx _ H9 H20 H11 H12 H18 H14 Hcell.
destruct (w6t_geo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx) as (HJ & Hown & HFa & HR16 & HR0 & HR1 & HFR).
clear Hctx.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF32 & _ & HFpres & _).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & _ & _).
rewrite <- HFa in HF32, HFpres, HF4096.
change (fs_frame_bytes 4) with 1024 in HFpres.
assert (HS : st_ok rsegs (Ereg regs (w6t_extra pp)) (ss_w6t (w6t_pc c3 u))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (w6t_pc c3 u)) memc (seg_rom rsegs)))).
{ apply (w6t_entry _ W regs memc R F pp H9 H20 HR0 HR1 HR16 HF4096 HFR HF32 Hcell).
  intros a Ha. apply (proj1 (HFpres a ltac:(lia))). }
assert (B9 : bv_unsigned (ew (Ereg regs (w6t_extra pp)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (B20 : bv_unsigned (ew (Ereg regs (w6t_extra pp)) 20) = F + 0x210)
  by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs (w6t_extra pp)) 32 = Z_to_bv 64 (pp + Layout.OFF_LEN))
  by exact (ew_Ereg_extra regs (w6t_extra pp) 0).
clear HR16 HF32 HFpres Hcell.
unfold cfg_at. change (w64 (w6t_pc c3 u)) with (Z_to_bv 64 (w6t_pc c3 u)).
destruct c3, u; cbn [w6t_pc] in HS, H14 |- *;
try specialize (H14 (or_introl eq_refl)); try specialize (H14 (or_intror eq_refl));
(aj_run_to w6b_tbl_ok HS HJ W6B_J;
[ (* the write windows: none in [R+0x138, R+0x140), e62's first 12 bytes in the frame (4, pos) *)
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 20%nat (F + 0x210));
  [ reflexivity | exact B20
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
    right; right; right; exists 4, pos; split; [exact Hown|]; left;
    unfold in_zr; cbn [fst snd]; rewrite <- HFa; change (fs_frame_bytes 4) with 1024; lia
  | apply awr_ok_nil ]
| (* the leaf at J *)
  apply SRr_ret; red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs (w6t_extra pp) (w_H W) [6; 10; 13; 14; 18]%bv);
          [exact HS | apply env_agree_refl | vm_compute; reflexivity]|];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
  split; [apply mo_le_refl; exact MTL|];
  split;
  [ intros a Ha Hn; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
    intros (rg & Hin & Hr); apply Hn; unfold w6b_tail_wr; rewrite unsigned_lit_small in Hr by lia;
    cbn [ss_mem ss_w6t w6t_regions In] in Hin;
    destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val w6t_rR w6t_rE] in Hr;
    rewrite ?B9, ?B20 in Hr; lia
  | cbv beta ];
  split; [w6t_reg_tac HS (6%bv : bv 5); rewrite w6t_soff0, (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12|];
  split; [w6t_reg_tac HS (13%bv : bv 5); rewrite w6t_soff0, (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18|];
  split; [w6t_reg_tac HS (18%bv : bv 5); rewrite w6t_soff0, E32; reflexivity|];
  split; [eapply (cb_val_at _ _ (w_H W) ms 1%nat _ 0 4%N _ _ (F + 0x210) _);
          [exact HS | reflexivity | w6t_in | cbn [YP09.r_base base_val]; exact B20 | w6t_sv4 regs H14
          | cbn; lia | lia]|];
  split; [eapply (cb_val_at _ _ (w_H W) ms 1%nat _ 4 4%N _ _ (F + 0x210) _);
          [exact HS | reflexivity | w6t_in | cbn [YP09.r_base base_val]; exact B20 | w6t_sv4 regs H14
          | cbn; lia | lia]|];
  apply (w6t_val_mod _ _ 4 v (2 ^ 32)); [reflexivity|];
  eapply (cb_val_at _ _ (w_H W) ms 1%nat _ 8 4%N _ v (F + 0x210) _);
  [ exact HS | reflexivity | w6t_in | cbn [YP09.r_base base_val]; exact B20
  | rewrite w6t_soff0, (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11 | cbn; lia | lia ] ]).
Qed.

Theorem w6b_tail2u : w6b_tail2u_stmt B MT.
Proof using MTL. exact (w6b_tail_all false true). Qed.
Theorem w6b_tail2 : w6b_tail2_stmt B MT.
Proof using MTL. exact (w6b_tail_all false false). Qed.
Theorem w6b_tail3u : w6b_tail3u_stmt B MT.
Proof using MTL. exact (w6b_tail_all true true). Qed.
Theorem w6b_tail3 : w6b_tail3_stmt B MT.
Proof using MTL. exact (w6b_tail_all true false). Qed.
End d.
End b.

Print Assumptions w6b_tail2u.
Print Assumptions w6b_tail2.
Print Assumptions w6b_tail3u.
Print Assumptions w6b_tail3.
