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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module paths and module names changed; 250 of its 289 lines of code are new or changed and 430 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM3bPair.v at 42ff422eb80 (image A's
   twin of this piece, same unit): the prefix hp_ -> hpu_, image A's code 0x8307c .. 0x8309c replaced by image B's
   0x8314c .. 0x8318c (B's pair head reads pp->n_ent through an instrumented check and tests it, makes the entry
   offset by `mulhu` of a real-frame multiplier and leaves to RC when no entry is left, where A's head only moves
   five entry-table registers and falls through), the cut rebuilt over lib/AU/HPgSegM.v's hqu_cut_PAIR /
   hqu_cut_SCAN / hqu_cut_RC and lib/AU/HPgBM3bBase.v. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, the same loaded bytes except .note.gnu.build-id): the piece "the pair
   loop's head" of the walk of LLVMFuzzerTestOneInput, lib/AU/HPgSegM.v hqu_piece_M3b_pair_stmt. Proves no
   function (kind: segment lemma).

   THE CODE (PAIR 0x8314c .. 0x8318c, pod_next_pair's set-up, pod.h:134-135, inlined into the `for` of
   fuzz_headamp.c:119)
     0x8314c  ld a0,0x130(s1)      a0 := the shadow address of &pp->n_ent (R+0x130)
     0x83150  lb a0,0(a0)          a0 := that shadow byte
     0x83154  bnez a0,0x83790      the slow block; not taken, the shadow byte is 0
     0x83158  ld a0,0x120(s1)      a0 := &pp->n_ent (R+0x120)
     0x8315c  lw a3,0(a0)          a3 := pp->n_ent
     0x83160  bge a2,a3,0x83850    at >= n_ent: the loop is done, RC
     0x83164  slli a0,a2,0x20      a0 := at << 32
     0x83168  srli s2,a0,0x20      s2 := at
     0x8316c  addi a1,zero,0x21    a1 := 33
     0x83170  mv a4,s2             a4 := at
     0x83174  bltu a1,s2,0x8317c   33 < at: not taken (at <= 32)
     0x83178  addi a4,zero,0x21    a4 := 33, the scan's index bound
     0x8317c  addi s7,zero,0       s7 := 0, the rotated scan head's "no answer yet"
     0x83180  ld a1,0x118(s1)      a1 := the multiplier 0xd * 2 ^ 35 (R+0x118)
     0x83184  mulhu s8,a0,a1       s8 := 104 at
     0x83188  ld a0,0x128(s1)      a0 := the one's complement of &ent[0].body (R+0x128)
     0x8318c  sub a5,a0,s8         a5 := the one's complement of &ent[at].body
   and falls through to the scan's head SCAN 0x83190 with at0 = m = at. No store, no call: the piece writes no
   byte and changes no float register.

   REGISTERS AND R-CELLS. It reads s1 = R, a2 = at and the real-frame cells R+0x118 (the multiplier), R+0x120
   (&pp->n_ent), R+0x128 (the one's complement of &ent[0].body) and R+0x130 (the shadow address of &pp->n_ent);
   it writes a0, a1, a3, a4, a5, s2, s7, s8.

   HOW. hpu_blk is the piece as a block lemma over the machine state at PAIR (lib/Reusable: the token engine
   YCbn.v, the journal YCbq.v), stated for any float state: the entry state has the registers as atoms, the four
   real-frame cells as one read-only region over four extra atoms, the shadow byte as a one-byte read-only region
   whose value is the literal 0 and pp->n_ent as a four-byte read-only region over a fifth atom, with the atom
   ranges 0 <= at <= 32 and 1 <= n_ent <= 32 that decide the `bltu`. The engine splits the `bge` it cannot decide
   and runs each arm to its end pc. hbu_pair_B reads the PAIR cut, pays the shadow byte from the pp block's
   shadow (HPgBM3bBase.hbu_blk_sh0) and n_ent from the block's image (HPgMem.hm_pp_n_ent), runs hpu_blk at the
   run's own float state and rebuilds either the SCAN cut at at0 = m = at (the scan's operand registers: the
   index bound 33, the entry offset 104 at by hqu_mul104_ok, and the one's complement of &ent[at].body) or the
   RC cut (no entry is left, so the fold is the identity: HPgBM3bBase.hbu_fold_end, hbu_exp_rc). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgBM3bBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* ================================ the code table and the entry state ================================ *)
(* the seventeen words 0x8314c .. 0x8318c and the three of the slow block 0x83790; the end pcs SCAN 0x83190 and
   RC 0x83850 lie outside both *)
Definition hpu_tbl : ctable := build_table rsegs 0x83790 3 (build_table rsegs HQU_PAIR 17 TEmpty).
Lemma hpu_tbl_ok : table_ok rsegs hpu_tbl.
Proof. apply build_table_ok; [lia | apply build_table_ok0; unfold HQU_PAIR; lia]. Qed.

(* the registers the piece does not write: all but a0, a1, a3, a4, a5, s2, s7, s8 *)
Definition hpu_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 16; 17; 19; 20; 21; 22; 25; 26; 27; 28; 29; 30; 31].

(* atom 32 is the token base of the kit's no-check runs (HPgSteps.rt_extra); atoms 33 .. 37 are the one's
   complement of &ent[0].body, &pp->n_ent, that address's shadow byte, pp->n_ent and the multiplier *)
Definition hpu_R : YP09.region := YP09.mkRegion (Some 9%nat) 0x118 0x138 0 0
  [YP09.mkChunk 0x118 (CVal 8 (SOff 37 0)); YP09.mkChunk 0x120 (CVal 8 (SOff 34 0));
   YP09.mkChunk 0x128 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x130 (CVal 8 (SOff 35 0))].
Definition hpu_NE : YP09.region := YP09.mkRegion (Some 34%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 36 0))].
Definition hpu_SH : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition hpu_facts : facts := mkFacts [(12%nat, mkAF 0 32 0); (36%nat, mkAF 1 32 0)] [] [].
Definition hpu_ss0 : sstate := mkSS HQU_PAIR sr_atoms [hpu_R; hpu_NE; hpu_SH] None hpu_facts.
Definition hpu_extra (NB NE SHA nent : Z) : list word :=
  [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 NB; Z_to_bv 64 NE; Z_to_bv 64 SHA; Z_to_bv 64 nent;
   Z_to_bv 64 HQU_MUL104].

(* what the scan's arm computes *)
Definition hpu_RR (i nent NB : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 12) = w64 i /\ getr regs2 (Z_to_bv 5 18) = w64 i /\
getr regs2 (Z_to_bv 5 13) = w64 nent /\ getr regs2 (Z_to_bv 5 14) = w64 33 /\
getr regs2 (Z_to_bv 5 23) = w64 0 /\ getr regs2 (Z_to_bv 5 24) = w64 (104 * i) /\
getr regs2 (Z_to_bv 5 15) = w64 (NB - 104 * i).

(* the `bge` of 0x83160, as the engine leaves it *)
Lemma hpu_bge : forall i n, 0 <= i < 2 ^ 63 -> 0 <= n < 2 ^ 63 ->
branch_taken BC_GE (Z_to_bv 64 i) (Z_to_bv 64 n) = negb (i <? n).
Proof.
intros i n Hi Hn. rewrite YO0c.branch_ge, !unsigned_lit_small by lia.
rewrite !YO0b.s64_small by lia. reflexivity.
Qed.

Ltac hpu_lit := hbu_sv; cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity.
Ltac hpu_atom :=
hbu_sv; rewrite hbu_denot0;
lazymatch goal with |- ew _ ?n = _ => lazymatch goal with En : ew _ n = Z_to_bv 64 _ |- _ => rewrite En; reflexivity end end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

Lemma hpu_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R i nent NB NE SHA : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 12) = w64 i ->
0 <= R -> R + 0x138 <= 2 ^ 64 -> 0 <= i <= 32 -> 1 <= nent <= 32 ->
0 <= NE -> NE + 4 <= 2 ^ 64 -> 0 <= SHA -> SHA + 1 <= 2 ^ 64 ->
NE + 4 <= R + 0x118 -> SHA + 1 <= R + 0x118 -> (SHA + 1 <= NE \/ NE + 4 <= SHA) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (HQU_MUL104 mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x120) 8 (NE mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x128) 8 (NB mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (SHA mod 2 ^ 64) ->
aview rsegs (w_H W) memc SHA = Some 0 ->
val_mem rsegs (mrestrict (w_H W) memc) NE 4 nent ->
SRr rsegs W (cfg_at rsegs HQU_PAIR regs memc mdc)
(fun W2 c2 =>
 (nent <= i /\ hbu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RC hpu_kept
                 (fun _ => True) W2 c2) \/
 (i < nent /\ hbu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_SCAN hpu_kept
                 (hpu_RR i nent NB) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i nent NB NE SHA
  HJ H9 H12 HR0 HR1 Hi Hn HNE0 HNE1 HSH0 HSH1 Hd1 Hd2 Hd3 V118 V120 V128 V130 Vsh Vne.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hpu_extra NB NE SHA nent) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E12 : ew (Ereg regs ex) 12 = Z_to_bv 64 i) by (rewrite (EA 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 NB) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 NE) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew (Ereg regs ex) 35 = Z_to_bv 64 SHA) by (subst ex; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew (Ereg regs ex) 36 = Z_to_bv 64 nent) by (subst ex; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew (Ereg regs ex) 37 = Z_to_bv 64 HQU_MUL104) by (subst ex; exact (ew_Ereg_extra regs _ 5)).
assert (HM : 0 <= HQU_MUL104 < 2 ^ 64) by (unfold HQU_MUL104; lia).
assert (HS : st_ok rsegs (Ereg regs ex) hpu_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HQU_PAIR) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hpu_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
      repeat apply Forall_cons; try apply Forall_nil.
      * exact (hbu_slot_chunk _ _ _ R 0x118 HQU_MUL104 37 E37 V118).
      * exact (hbu_slot_chunk _ _ _ R 0x120 NE 34 E34 V120).
      * exact (hbu_slot_chunk _ _ _ R 0x128 NB 33 E33 V128).
      * exact (hbu_slot_chunk _ _ _ R 0x130 SHA 35 E35 V130).
    + apply (hm_ro_region rsegs _ (w_H W) memc 34 NE); [rewrite E34; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ NE 0 4 (SOff 36 0) nent); [rewrite hbu_denot0; exact E36 | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vne.
    + apply (hm_ro_region rsegs _ (w_H W) memc 35 SHA); [rewrite E35; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ SHA 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (proj1 (hm_aview_val1 rsegs (w_H W) memc SHA 0 Vsh)).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val hpu_R hpu_NE hpu_SH].
    rewrite E9, E34, E35, !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite !(Z.mod_small _ (2 ^ 64)) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct Hd3 as [Hd3|Hd3]; repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [hpu_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E12, E36, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    rewrite !(Z.mod_small _ (2 ^ 64)) by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HQU_PAIR) with (Z_to_bv 64 HQU_PAIR).
(* 0x8314c .. 0x8315c: the shadow check and the n_ent load; stop at the `bge` *)
aj_run_tok hpu_tbl_ok HS HJ SHOK HPgSteps.RTBspan; [awr_ok_tac | ]. hbu_mem.
srr_branch_tok hpu_tbl_ok HS SHOK HPgSteps.RTBspan;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end;
rewrite !hbu_denot0, E12, E36, hpu_bge in Hc by lia.
- (* taken: at >= n_ent, the loop is done *)
  aj_run_to_tok hpu_tbl_ok HS HJ SHOK HPgSteps.RTBspan HQU_RC; [awr_ok_tac | ]. hbu_mem.
  apply SRr_ret; left. split; [apply negb_true_iff, Z.ltb_ge in Hc; exact Hc|].
  hbu_post_intro B hpu_kept. exact I.
- (* not taken: at < n_ent, the scan's head *)
  aj_run_to_tok hpu_tbl_ok HS HJ SHOK HPgSteps.RTBspan HQU_SCAN; [awr_ok_tac | ]. hbu_mem.
  apply SRr_ret; right. split; [apply negb_false_iff, Z.ltb_lt in Hc; exact Hc|].
  hbu_post_intro B hpu_kept.
  unfold hpu_RR. lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  split; [hpu_atom|]. split; [hpu_atom|].
  split; [hpu_atom|]. split; [hpu_lit|]. split; [hpu_lit|].
  split.
  { hbu_sv. rewrite denot_lit_U. unfold w64. apply Z_to_bv64_eq_mod.
    repeat first [rewrite U_SAlu | rewrite U_SMd | rewrite U_SLit]. cbn [zmd_raw zalu_raw].
    change (Z.land (zcanon 32) 63) with 32.
    rewrite (U_atom E 12 i E12), (U_atom E 37 HQU_MUL104 E37) by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    unfold zcanon, M64. change (Z.of_N 64) with 64.
    rewrite (Z.mod_small (i * 2 ^ 32)) by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite hqu_mul104_ok by lia. rewrite Z.mod_mod by lia. reflexivity. }
  { assert (U33 : U E (SOff 33 0) = NB mod 2 ^ 64).
    { unfold U. rewrite hbu_denot0, E33, Z_to_bv_unsigned.
      unfold bv_wrap, bv_modulus. cbn [Z.of_N]. reflexivity. }
    hbu_sv. rewrite denot_lit_U. unfold w64. apply Z_to_bv64_eq_mod.
    repeat first [rewrite U_SAlu | rewrite U_SMd | rewrite U_SLit]. cbn [zmd_raw zalu_raw].
    change (Z.land (zcanon 32) 63) with 32. rewrite U33.
    rewrite (U_atom E 12 i E12), (U_atom E 37 HQU_MUL104 E37) by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    unfold zcanon, M64. change (Z.of_N 64) with 64.
    rewrite (Z.mod_small (i * 2 ^ 32)) by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite hqu_mul104_ok by lia.
    rewrite (Z.mod_small (104 * i)) by lia.
    rewrite Z.mod_mod by lia. rewrite Zminus_mod_idemp_l. reflexivity. }
Qed.
End d.
End b.

(* ================================ the cuts ================================ *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem hbu_pair_B : hqu_piece_M3b_pair_stmt rsegs B MT.
Proof.
unfold hqu_piece_M3b_pair_stmt. intros cx POST r ev i HS HSC HRC.
unfold hqu_from_PAIR. intros fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf Hcut.
pose proof Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hf3 & Hlive & Hn0 & Hil & Hx & Hfold).
pose proof Hb3 as (Hcore & _ & _ & _ & Hpp & _).
pose proof Hcore as (HJ & _ & _ & Hperm & _).
pose proof (hbu_start_wf B cx r ev HS) as Hwf.
pose proof (hbu_start_R B cx r ev HS) as (HR0 & HR1 & _ & HRc).
pose proof (hbu_start_pp B cx r ev HS) as (Hppin & Hal16 & Hp4k & Hpc & Hceil).
pose proof (Permutation_in _ (Permutation_sym Hperm) Hppin) as Hin2.
pose proof HJ as (HAR & _).
pose proof (al_blocks rsegs B (AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ HAR Hin2) as (_ & _ & _ & Happ & _).
assert (Hrq : req_size PP_SIZE = PP_SIZE) by reflexivity. rewrite Hrq in Happ.
pose proof (@alloc_ceiling_val rc) as [[Hc0 Hc1] _].
pose proof (proj1 (ents_wf r Hwf)) as Hn32.
pose proof (proj2 (ents_wf r Hwf)) as Hews.
(* the shadow byte of &pp->n_ent and the count itself *)
assert (Hp8 : e_pp (x_e cx) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 16); [exists 2; reflexivity|].
  apply Z.mod_divide; [lia | exact Hal16]. }
assert (Vsh : aview rsegs (w_H W2) mem2 (shadow_addr (e_pp (x_e cx) + Layout.OFF_N_ENT)) = Some 0)
  by (apply (hbu_blk_sh0 B ly2 S2 W2 mem2 md2);
      [exact HAR | exact Hin2 | exact Hp8 | unfold PP_SIZE, Layout.OFF_N_ENT; lia]).
assert (Hb : Z.of_nat (length (buf r)) <= POD_BUF_MAX)
  by (pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & HL); unfold POD_BUF_MAX; lia).
assert (Hs : Forall (fun e => (length (e_body e) <= 96)%nat) (ents r)).
{ eapply Forall_impl; [|exact Hews]. intros e (_ & He & Hz). lia. }
pose proof (hm_pp_n_ent rsegs (buf r) (is_props r) (has_params r) (params_struct r) (ents r) (corrupt r)
  Hb Hn32 Hs (w_H W2) mem2 (e_pp (x_e cx)) Hpp) as Vne.
(* the registers and cells at PAIR *)
unfold hsu_at_cx in Hat.
pose proof (hbu_at_get _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(hbu_in)) as R9.
pose proof (hbu_at_get _ _ _ _ _ 12 (Z.of_nat i) Hat ltac:(hbu_in)) as R12.
pose proof (hbu_at_cell _ _ _ _ _ XR 0x118 HQU_MUL104 Hat ltac:(hbu_in)) as C118.
pose proof (hbu_at_cell _ _ _ _ _ XR 0x120 (e_pp (x_e cx) + Layout.OFF_N_ENT) Hat ltac:(hbu_in)) as C120.
pose proof (hbu_at_cell _ _ _ _ _ XR 0x128 (hqu_not (e_pp (x_e cx) + Layout.OFF_ENT + 8)) Hat ltac:(hbu_in)) as C128.
pose proof (hbu_at_cell _ _ _ _ _ XR 0x130 (shadow_addr (e_pp (x_e cx) + Layout.OFF_N_ENT)) Hat ltac:(hbu_in)) as C130.
cbn [hd_xv] in C118, C120, C128, C130.
(* the shadow cell lies in the shadow band, below the stack and apart from the block *)
assert (Hpl2 : e_pp (x_e cx) + 19744 <= alloc_ceiling) by (unfold PP_SIZE in Hpc; exact Hpc).
assert (Hpk : 0 <= e_pp (x_e cx) + Layout.OFF_N_ENT < kHighMemEnd)
  by (unfold Layout.OFF_N_ENT, kHighMemEnd; lia).
assert (Hsb : kLowMemEnd <= shadow_addr (e_pp (x_e cx) + Layout.OFF_N_ENT) < kHighMemBeg).
{ pose proof (hm_shadow_band _ Hpk) as H. unfold shadow_addr. unfold shadow_of_addr in H. exact H. }
assert (Hna : ~ (e_pp (x_e cx) <= shadow_addr (e_pp (x_e cx) + Layout.OFF_N_ENT)
                 < e_pp (x_e cx) + PP_SIZE)).
{ pose proof (@hm_shadow_not_app rc _ _ PP_SIZE Hpk Happ) as H.
  unfold shadow_addr. unfold shadow_of_addr in H. exact H. }
assert (Hnent : 1 <= Z.of_nat (length (ents r)) <= 32) by (unfold hqu_nent in Hn0; lia).
unfold Layout.OFF_N_ENT in *. unfold PP_SIZE in *.
unfold kLowMemEnd, kHighMemBeg in Hsb. unfold T_SEG_STK, ASTACK in HRc.
eapply SRr_bind.
{ apply (hpu_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (Z.of_nat i)
    (Z.of_nat (length (ents r))) (hqu_not (e_pp (x_e cx) + Layout.OFF_ENT + 8))
    (e_pp (x_e cx) + 0x4d14) (shadow_addr (e_pp (x_e cx) + 0x4d14)) HJ R9 R12); try lia.
  - exact C118.
  - exact C120.
  - exact C128.
  - exact C130.
  - exact Vsh.
  - exact Vne. }
intros W3 c3 _ [(Hge & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)
              | (Hlt & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HRR)].
- (* RC: no entry is left, so x holds expect_of's answer *)
  pose proof (hbu_at_keep _ _ _ _ _ Hat regs3 hpu_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  destruct (hbu_fold_end rsegs cx r i cs keys rf Hfold ltac:(lia)) as (-> & -> & ->).
  apply (HRC fx2 ly2 S2 W2 regs3 mem2 md3).
  split.
  { apply (hbu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
    intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hpu_kept; hbu_kin. }
  split; [unfold hsu_at_cx; hbu_sub Hat3|].
  split; [exact (proj1 (proj2 Hlive))|].
  split; [exact (hbu_exp_rc rsegs cx r Hlive) | exact Hx].
- (* SCAN at at0 = m = i *)
  destruct HRR as (Q12 & Q18 & Q13 & Q14 & Q23 & Q24 & Q15).
  pose proof (hbu_at_keep _ _ _ _ _ Hat regs3 hpu_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  apply (HSC fx2 ly2 S2 W2 regs3 mem2 md3 cs keys rf).
  split.
  { apply (hbu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
    intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hpu_kept; hbu_kin. }
  split.
  { unfold hsu_at_cx. apply hbu_at_app; split; [hbu_sub Hat3|].
    apply hbu_at_app; split; [hbu_sub Hat3|].
    apply hbu_at_app; split; [hbu_sub Hat3|].
    apply hbu_at_app; split; [hbu_sub Hat3|].
    unfold hsu_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - rewrite Hk3 by (unfold hpu_kept; hbu_kin). exact (hbu_at_get _ _ _ _ _ 21 8 Hat ltac:(hbu_in)).
    - exact Q23.
    - exact Q12.
    - exact Q18.
    - rewrite Q24; unfold w64, Layout.ENT_SIZE; f_equal; lia.
    - rewrite Q13. unfold w64, hqu_nent. reflexivity.
    - rewrite Q14; unfold w64; f_equal; lia.
    - rewrite Q15; unfold w64, hqu_not, Layout.ENT_SIZE; f_equal; lia. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|].
  split; [exact Hlive|].
  split; [lia|].
  split; [intros q Hq; lia|].
  split; [exact Hx | exact Hfold].
Qed.
End c.

Print Assumptions hbu_pair_B.
