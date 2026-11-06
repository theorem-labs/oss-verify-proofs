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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module paths and module names changed; 198 of its 236 lines of code are new or changed and 431 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM3bLatch.v at 42ff422eb80 (image A's
   twin of this piece, same unit): the prefix hl_ -> hlu_, image A's code 0x83474 .. 0x8348c replaced by image B's
   0x836b4 .. 0x836e0 (B's latch reads pp->params_struct through an instrumented check and reloads five entry-table
   registers, where A's reads n_ent - 1 from a real-frame cell and splits a `blt`), the cut rebuilt over
   lib/AU/HPgSegM.v's hqu_cut_LATCH / hqu_cut_PAIR and lib/AU/HPgBM3bBase.v. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, the same loaded bytes except .note.gnu.build-id): the piece "the pair
   loop's latch" of the walk of LLVMFuzzerTestOneInput, lib/AU/HPgSegM.v hqu_piece_M3b_latch_stmt. Proves no
   function (kind: segment lemma).

   THE CODE (LATCH 0x836b4 .. 0x836e0, the `for` of fuzz_headamp.c:119 and the params-Struct test)
     0x836b4  lb a0,0(t6)          a0 := the shadow byte of &pp->params_struct (t6 holds its address)
     0x836b8  bnez a0,0x8379c      the slow block; not taken, the shadow byte is 0
     0x836bc  lw a0,0(t5)          a0 := pp->params_struct (t5 = &pp->params_struct)
     0x836c0  ld a2,0xd8(s1)       a2 := j, the next pair index (R+0xd8, written by the key piece)
     0x836c4  addi s5,zero,8       s5 := the String type
     0x836c8  ld t1,0x100(s1)      t1 := &ent[0].size
     0x836cc  ld t0,0xf8(s1)       t0 := &ent[0]
     0x836d0  ld t4,0xe8(s1)       t4 := &ent[0].body
     0x836d4  ld t2,0xf0(s1)       t2 := the one's complement of &ent[0]
     0x836d8  ld t3,0xe0(s1)       t3 := &ent[0].body
     0x836dc  bnez a0,0x8314c      params_struct <> 0: the pair loop's head PAIR
     0x836e0  j 0x83850            else RC
   The record the loop runs on has params_struct = true (HPgSegM.hqu_live, a conjunct of every cut of the loop),
   so pp->params_struct is 1 and the `j 0x83850` is not reached: this piece does not use its RC continuation.
   The piece makes no store and no call: it writes no byte and changes no float register.

   REGISTERS AND R-CELLS. It reads s1 = R, t5 = &pp->params_struct, t6 = that address's shadow byte, and the
   real-frame cells R+0xd8, R+0xe0, R+0xe8, R+0xf0, R+0xf8, R+0x100; it writes a0, a2, s5, t0, t1, t2, t3, t4.

   HOW. hlu_blk is the piece as a block lemma over the machine state at LATCH (lib/Reusable: the token engine
   YCbn.v, the journal YCbq.v), stated for any float state: the entry state has the registers as atoms, the six
   real-frame cells as one read-only region over five extra atoms, the shadow byte as a one-byte read-only region
   on t6 whose value is the literal 0, and pp->params_struct as a four-byte read-only region on t5 whose value is
   the literal 1, so the engine decides both branches and runs straight to PAIR. hbu_latch_B reads the LATCH cut,
   pays the shadow byte from the pp block's shadow (HPgBM3bBase.hbu_blk_sh0: the block's size is a multiple of 8)
   and the params-struct word from the block's image (HPgMem.hm_pp_params_struct), runs hlu_blk at the run's own
   float state and rebuilds the PAIR cut at the same index. *)
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
(* the twelve words 0x836b4 .. 0x836e0 and the four of the slow block 0x8379c; the end pc PAIR 0x8314c lies
   outside both *)
Definition hlu_tbl : ctable := build_table rsegs 0x8379c 4 (build_table rsegs HQU_LATCH 12 TEmpty).
Lemma hlu_tbl_ok : table_ok rsegs hlu_tbl.
Proof. apply build_table_ok; [lia | apply build_table_ok0; unfold HQU_LATCH; lia]. Qed.

(* the registers the piece does not write: all but a0, a2, s5, t0, t1, t2, t3, t4 *)
Definition hlu_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 8; 9; 11; 13; 14; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 30; 31].

(* atom 32 is the token base of the kit's no-check runs (HPgSteps.rt_extra); atoms 33 .. 37 are the five
   values of the six real-frame cells (R+0xe0 and R+0xe8 hold the same address) *)
Definition hlu_R : YP09.region := YP09.mkRegion (Some 9%nat) 0xd8 0x108 0 0
  [YP09.mkChunk 0xd8 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xe0 (CVal 8 (SOff 34 0));
   YP09.mkChunk 0xe8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0xf0 (CVal 8 (SOff 35 0));
   YP09.mkChunk 0xf8 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x100 (CVal 8 (SOff 37 0))].
Definition hlu_T6 : YP09.region := YP09.mkRegion (Some 31%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition hlu_T5 : YP09.region := YP09.mkRegion (Some 30%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition hlu_ss0 : sstate := mkSS HQU_LATCH sr_atoms [hlu_R; hlu_T6; hlu_T5] None (mkFacts [] [] []).
Definition hlu_extra (j A0 : Z) : list word :=
  [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 j; Z_to_bv 64 (A0 + 8); Z_to_bv 64 (hqu_not A0);
   Z_to_bv 64 A0; Z_to_bv 64 (A0 + 4)].

(* what the piece leaves: the loop's index, the String type and the five entry-table registers *)
Definition hlu_RR (j A0 : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 12) = w64 j /\ getr regs2 (Z_to_bv 5 21) = w64 8 /\
getr regs2 (Z_to_bv 5 5) = w64 A0 /\ getr regs2 (Z_to_bv 5 6) = w64 (A0 + 4) /\
getr regs2 (Z_to_bv 5 7) = w64 (hqu_not A0) /\
getr regs2 (Z_to_bv 5 28) = w64 (A0 + 8) /\ getr regs2 (Z_to_bv 5 29) = w64 (A0 + 8).

Ltac hlu_lit := hbu_sv; cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity.
Ltac hlu_atom :=
hbu_sv; rewrite hbu_denot0;
lazymatch goal with |- ew _ ?n = _ => lazymatch goal with En : ew _ n = Z_to_bv 64 _ |- _ => rewrite En; reflexivity end end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

Lemma hlu_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R j A0 P5 P6 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R ->
getr regs (Z_to_bv 5 30) = w64 P5 -> getr regs (Z_to_bv 5 31) = w64 P6 ->
0 <= R -> R + 0x108 <= 2 ^ 64 ->
0 <= P5 -> P5 + 4 <= 2 ^ 64 -> 0 <= P6 -> P6 + 1 <= 2 ^ 64 ->
P5 + 4 <= R + 0xd8 -> P6 + 1 <= R + 0xd8 -> (P6 + 1 <= P5 \/ P5 + 4 <= P6) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 (j mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 ((A0 + 8) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 ((A0 + 8) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 (hqu_not A0 mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (A0 mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 ((A0 + 4) mod 2 ^ 64) ->
aview rsegs (w_H W) memc P6 = Some 0 ->
val_mem rsegs (mrestrict (w_H W) memc) P5 4 1 ->
SRr rsegs W (cfg_at rsegs HQU_LATCH regs memc mdc)
(hbu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_PAIR hlu_kept (hlu_RR j A0)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R j A0 P5 P6
  HJ H9 H30 H31 HR0 HR1 HP50 HP51 HP60 HP61 Hd1 Hd2 Hd3 Vd8 Ve0 Ve8 Vf0 Vf8 V100 Vsh Vps.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hlu_extra j A0) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E30 : ew (Ereg regs ex) 30 = Z_to_bv 64 P5) by (rewrite (EA 30%nat (Z_to_bv 5 30) eq_refl); exact H30).
assert (E31 : ew (Ereg regs ex) 31 = Z_to_bv 64 P6) by (rewrite (EA 31%nat (Z_to_bv 5 31) eq_refl); exact H31).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 j) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 (A0 + 8)) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew (Ereg regs ex) 35 = Z_to_bv 64 (hqu_not A0)) by (subst ex; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew (Ereg regs ex) 36 = Z_to_bv 64 A0) by (subst ex; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew (Ereg regs ex) 37 = Z_to_bv 64 (A0 + 4)) by (subst ex; exact (ew_Ereg_extra regs _ 5)).
assert (HS : st_ok rsegs (Ereg regs ex) hlu_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HQU_LATCH) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hlu_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
      repeat apply Forall_cons; try apply Forall_nil.
      * exact (hbu_slot_chunk _ _ _ R 0xd8 j 33 E33 Vd8).
      * exact (hbu_slot_chunk _ _ _ R 0xe0 (A0 + 8) 34 E34 Ve0).
      * exact (hbu_slot_chunk _ _ _ R 0xe8 (A0 + 8) 34 E34 Ve8).
      * exact (hbu_slot_chunk _ _ _ R 0xf0 (hqu_not A0) 35 E35 Vf0).
      * exact (hbu_slot_chunk _ _ _ R 0xf8 A0 36 E36 Vf8).
      * exact (hbu_slot_chunk _ _ _ R 0x100 (A0 + 4) 37 E37 V100).
    + apply (hm_ro_region rsegs _ (w_H W) memc 31 P6); [rewrite E31; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ P6 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (proj1 (hm_aview_val1 rsegs (w_H W) memc P6 0 Vsh)).
    + apply (hm_ro_region rsegs _ (w_H W) memc 30 P5); [rewrite E30; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ P5 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vps.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val hlu_R hlu_T6 hlu_T5].
    rewrite E9, E30, E31, !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite !(Z.mod_small _ (2 ^ 64)) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct Hd3 as [Hd3|Hd3]; repeat split; lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HQU_LATCH) with (Z_to_bv 64 HQU_LATCH).
aj_run_to_tok hlu_tbl_ok HS HJ SHOK HPgSteps.RTBspan HQU_PAIR; [awr_ok_tac | ]. hbu_mem.
apply SRr_ret. hbu_post_intro B hlu_kept.
unfold hlu_RR. lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
split; [hlu_atom|]. split; [hlu_lit|]. split; [hlu_atom|]. split; [hlu_atom|].
split; [hlu_atom|]. split; [hlu_atom|]. hlu_atom.
Qed.
End d.
End b.

(* ================================ the cut ================================ *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem hbu_latch_B : hqu_piece_M3b_latch_stmt rsegs B MT.
Proof.
unfold hqu_piece_M3b_latch_stmt. intros cx POST r ev j HS HP HRC.
unfold hqu_from_LATCH. intros fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf Hcut.
pose proof Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hf3 & Hlive & Hn0 & Hjn & Hx & Hfold).
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
(* the shadow byte of &pp->params_struct and the word itself *)
assert (Hp8 : e_pp (x_e cx) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 16); [exists 2; reflexivity|].
  apply Z.mod_divide; [lia | exact Hal16]. }
assert (Vsh : aview rsegs (w_H W2) mem2 (shadow_addr (e_pp (x_e cx) + Layout.OFF_PARAMS_STRUCT)) = Some 0)
  by (apply (hbu_blk_sh0 B ly2 S2 W2 mem2 md2); [exact HAR | exact Hin2 | exact Hp8 | unfold PP_SIZE, Layout.OFF_PARAMS_STRUCT; lia]).
pose proof (proj1 (ents_wf r Hwf)) as Hn32.
pose proof (proj2 (ents_wf r Hwf)) as Hews.
assert (Hb : Z.of_nat (length (buf r)) <= POD_BUF_MAX)
  by (pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & HL); unfold POD_BUF_MAX; lia).
assert (Hs : Forall (fun e => (length (e_body e) <= 96)%nat) (ents r)).
{ eapply Forall_impl; [|exact Hews]. intros e (_ & He & Hz). lia. }
pose proof (hm_pp_params_struct rsegs (buf r) (is_props r) (has_params r) (params_struct r) (ents r) (corrupt r)
  Hb Hn32 Hs (w_H W2) mem2 (e_pp (x_e cx)) Hpp) as Vps.
destruct Hlive as (Hnull & Hcorr & Hisp & Hpst).
rewrite Hpst in Vps. cbn [Z.b2z] in Vps.
(* the registers and cells at LATCH *)
unfold hsu_at_cx in Hat.
pose proof (hbu_at_get _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(hbu_in)) as R9.
pose proof (hbu_at_get _ _ _ _ _ 30 (e_pp (x_e cx) + Layout.OFF_PARAMS_STRUCT) Hat ltac:(hbu_in)) as R30.
pose proof (hbu_at_get _ _ _ _ _ 31 (shadow_addr (e_pp (x_e cx) + Layout.OFF_PARAMS_STRUCT)) Hat ltac:(hbu_in)) as R31.
pose proof (hbu_at_cell _ _ _ _ _ XR 0xd8 (Z.of_nat j) Hat ltac:(hbu_in)) as Cd8.
pose proof (hbu_at_cell _ _ _ _ _ XR 0xe0 (e_pp (x_e cx) + Layout.OFF_ENT + 8) Hat ltac:(hbu_in)) as Ce0.
pose proof (hbu_at_cell _ _ _ _ _ XR 0xe8 (e_pp (x_e cx) + Layout.OFF_ENT + 8) Hat ltac:(hbu_in)) as Ce8.
pose proof (hbu_at_cell _ _ _ _ _ XR 0xf0 (hqu_not (e_pp (x_e cx) + Layout.OFF_ENT)) Hat ltac:(hbu_in)) as Cf0.
pose proof (hbu_at_cell _ _ _ _ _ XR 0xf8 (e_pp (x_e cx) + Layout.OFF_ENT) Hat ltac:(hbu_in)) as Cf8.
pose proof (hbu_at_cell _ _ _ _ _ XR 0x100 (e_pp (x_e cx) + Layout.OFF_ENT + 4) Hat ltac:(hbu_in)) as C100.
cbn [hd_xv] in Cd8, Ce0, Ce8, Cf0, Cf8, C100.
(* the shadow cell lies in the shadow band, below the stack and apart from the block *)
assert (Hpl1 : 4096 <= e_pp (x_e cx)) by exact Hp4k.
assert (Hpl2 : e_pp (x_e cx) + 19744 <= alloc_ceiling) by (unfold PP_SIZE in Hpc; exact Hpc).
assert (Hpk : 0 <= e_pp (x_e cx) + Layout.OFF_PARAMS_STRUCT < kHighMemEnd)
  by (unfold Layout.OFF_PARAMS_STRUCT, kHighMemEnd; lia).
assert (Hsb : kLowMemEnd <= shadow_addr (e_pp (x_e cx) + Layout.OFF_PARAMS_STRUCT) < kHighMemBeg).
{ pose proof (hm_shadow_band _ Hpk) as H. unfold shadow_addr. unfold shadow_of_addr in H. exact H. }
assert (Hna : ~ (e_pp (x_e cx) <= shadow_addr (e_pp (x_e cx) + Layout.OFF_PARAMS_STRUCT)
                 < e_pp (x_e cx) + PP_SIZE)).
{ pose proof (@hm_shadow_not_app rc _ _ PP_SIZE Hpk Happ) as H.
  unfold shadow_addr. unfold shadow_of_addr in H. exact H. }
unfold Layout.OFF_PARAMS_STRUCT in *. unfold PP_SIZE in *.
unfold kLowMemEnd, kHighMemBeg in Hsb. unfold T_SEG_STK, ASTACK in HRc.
eapply SRr_bind.
{ apply (hlu_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (Z.of_nat j)
    (e_pp (x_e cx) + Layout.OFF_ENT) (e_pp (x_e cx) + 0x4010)
    (shadow_addr (e_pp (x_e cx) + 0x4010)) HJ R9 R30 R31); try lia.
  - exact Cd8.
  - exact Ce0.
  - exact Ce8.
  - exact Cf0.
  - exact Cf8.
  - exact C100.
  - exact Vsh.
  - exact Vps. }
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HRR).
destruct HRR as (Q12 & Q21 & Q5 & Q6 & Q7 & Q28 & Q29).
pose proof (hbu_at_keep _ _ _ _ _ Hat regs3 hlu_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
apply (HP fx2 ly2 S2 W2 regs3 mem2 md3 cs keys rf).
split.
{ apply (hbu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
  intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hlu_kept; hbu_kin. }
split.
{ unfold hsu_at_cx. apply hbu_at_app; split; [hbu_sub Hat3|].
  apply hbu_at_app; split; [hbu_sub Hat3|].
  apply hbu_at_app; split.
  - unfold hqu_L_loopr, hsu_at. cbv zeta. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    + exact Q5.
    + exact Q6.
    + exact Q7.
    + exact Q28.
    + exact Q29.
  - apply hbu_at_app; split; [hbu_sub Hat3|].
    unfold hsu_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    + exact Q12.
    + exact Q21. }
split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|].
split; [repeat split; assumption|]. split; [exact Hn0|].
split; [exact Hjn|]. split; [exact Hx | exact Hfold].
Qed.
End c.

Print Assumptions hbu_latch_B.
