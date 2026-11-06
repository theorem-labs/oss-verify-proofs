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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module paths and module names changed; 180 of its 219 lines of code are new or changed and 430 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanOuter.v at a5a28fb15bdf for
   reac-pw/fuzz_rate's image A: role's pcs (O 0x821bc, I 0x821e0, ABS 0x82380) become rate's (0x829c0, 0x829e4,
   0x82b7c), the registers are renamed as rate's code has them (n_ent t2 -> t3, at0 s5 -> s6, at + 1 s9 -> s7, the
   five operands t3 t6 t5 t4 s11 -> t2 t6 t5 t4 s10), the cut file is lib/A/RtPgSeg.v (rl_ -> rt_, e_ -> q_), the
   entry state and the list lemmas come from lib/A/RtPgScanKit.v and the image facts from lib/A/RtPgSteps.v. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgScanOuter.v at fa28558fbb17 for image B
   (fuzz_rate.asan-ubsan); the pcs are image B's (O 0x82b48, I 0x82b74, ABS 0x82d1c) and so is the code (eleven
   words: at in a2, n_ent in s10, at zero-extended into s6, the trap-test bound a3 = max(at, 33), the offset
   s8 = 104 at by `mulhu`, the bound a4 = ~(&ent[0] + 8) - 104 at, and the loop head's `bnez a0` not taken); the
   entry state gives at's atom the range [0, 32] so that the engine decides the `bltu`; the cut file is
   lib/AU/RtPgSegB.v, the model facts lib/AU/RtPgScanFB.v, the image facts lib/AU/RtPgStepsB.v, and the post, its
   intro and the atom read-back are the kit's skb_post / skb_post_intro / skb_denot0 (lib/AU/RtPgScanKitB.v). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgScanOuterB.v at e4ef964f482f for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments are
   lib/AU/Img0.v rsegs, the cut file is lib/AU/RPgSeg.v (rsb_ -> rs_, RSB_ -> RS_, rt_ -> rl_, q_ -> e_), the kit
   lib/AU/RPgScanKit.v (skb_ -> sk_), the model facts lib/AU/RPgScanF.v (rkb_ -> rk_), the image facts
   lib/AU/RPgSteps.v; the pcs are role B's (O 0x82278, I 0x822a4, ABS 0x8245c) and so are the registers (n_ent s10 ->
   s9, at zero-extended s6 -> s5, the offset s8 -> s7); the header cells of rate's lists are gone. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the piece "outer scan head"
   of the walk of LLVMFuzzerTestOneInput, lib/AU/RPgSeg.v rs_piece_W11a_outer_stmt. Proves no function (kind:
   segment lemma).

   THE CODE (O 0x82278, the `while` of fuzz_role.c:47 and pod_next_pair's set-up, pod.h:134-135)
     0x82278  bge a2,s9,0x8245c      at >= n_ent: no pair is left, to the absent check ABS
     0x8227c  slli a1,a2,32          a1 := at << 32
     0x82280  srli s5,a1,32          s5 := at (at is in [0, 32])
     0x82284  li a0,33
     0x82288  mv a3,s5
     0x8228c  bltu a0,s5,0x82294     33 < at: never, as at <= 32
     0x82290  li a3,33               a3 := 33 = max(at, 33)
     0x82294  li a0,0                a0 := 0, the loop head's "no key yet"
     0x82298  mulhu s7,a1,t1         s7 := (at << 32) * (104 << 32) >> 64 = 104 at
     0x8229c  sub a4,t0,s7           a4 := ~(&ent[0] + 8) - 104 at
     0x822a0  bnez a0,0x82370        a0 = 0: not taken
   and falls through to the inner scan I 0x822a4 with at0 = m = at. No load, no store, no instrumented check, no
   call, no trap branch: the piece writes no byte and changes no float register.

   HOW. ro_blk is the piece as a block lemma over the machine state at O (the registers as atoms, at's atom in
   [0, 32], no region): the engine (lib/Reusable/YCbn.v, YCbq.v) splits the `bge` (srr_branch_tok), runs each arm to
   its end pc, and decides the `bltu` from at's range and the `bnez` from the literal; the post sk_post keeps the
   journal, the memory (the region list is empty, so the run's frame is the whole memory) and the 25 registers the
   piece does not write, and gives the values the fall-through computes. rk_outer_B reads O's cut (rs_cut_O), runs
   ro_blk at the run's own float state, and rebuilds ABS's cut (taken: at >= n_ent, the answer is (None, 0) by
   RPgScanF.rk_inv_end) or I's cut at at0 = m = at (fall-through), then hands the state to the continuation. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YO0b YO0c YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSeg RPgScanF RPgScanKit.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgSteps.
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

(* ================================ the code table ================================ *)
(* the eleven words 0x82278 .. 0x822a0; both end pcs (I 0x822a4, ABS 0x8245c) lie outside it *)
Definition ro_tbl : ctable := build_table rsegs RS_O 11 TEmpty.
Lemma ro_tbl_ok : table_ok rsegs ro_tbl.
Proof. apply build_table_ok0. unfold RS_O. lia. Qed.

(* the registers the piece does not write (it writes a0, a1, a3, a4, s5, s7): ra, sp, gp, tp, t0 .. t2, s0, s1,
   a2, a5 .. a7, s2 .. s4, s6, s8 .. s11, t3 .. t6 *)
Definition ro_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 15; 16; 17; 18; 19; 20; 22; 24; 25; 26; 27; 28; 29; 30; 31].

(* the entry state: the registers as atoms, no region, and at's atom (a2) in [0, 32] (at <= n_ent <= 32), from
   which the engine decides the `bltu` 0x8228c *)
Definition ro_facts : facts := mkFacts [(12%nat, mkAF 0 32 0)] [] [].
Definition ro_ss : sstate := mkSS RS_O sr_atoms [] None ro_facts.

(* ================================ arithmetic ================================ *)
Lemma ro_bge : forall j n, 0 <= j < 2 ^ 63 -> 0 <= n < 2 ^ 63 ->
branch_taken BC_GE (Z_to_bv 64 j) (Z_to_bv 64 n) = negb (j <? n).
Proof.
intros j n Hj Hn. rewrite YO0c.branch_ge, !unsigned_lit_small by lia.
rewrite !YO0b.s64_small by lia. reflexivity.
Qed.

(* the `mulhu` 0x82298: (at << 32) * (104 << 32) >> 64 = 104 at *)
Lemma ro_U_s7 : forall E j, ew E 12 = Z_to_bv 64 j -> ew E 6 = Z_to_bv 64 (104 * 2 ^ 32) -> 0 <= j <= 32 ->
U E (SMd M_MULHU (SAlu ALU_SLL (SOff 12 0) (SLit 32)) (SOff 6 0)) = 104 * j.
Proof.
intros E j H12 H6 Hj. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 12 j H12) by lia. rewrite (U_atom E 6 (104 * 2 ^ 32) H6) by lia. rewrite U_SLit.
change (zcanon 32) with 32. change (Z.land 32 63) with 32.
rewrite (zcanon_id (Z.shiftl j 32)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (Z.of_N 64) with 64.
replace (j * 2 ^ 32 * (104 * 2 ^ 32)) with (104 * j * 2 ^ 64) by ring.
rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* a difference, as the 64-bit word of the difference of the values *)
Lemma ro_sub : forall E a b va vb, sv_denot E a = Z_to_bv 64 va -> U E b = vb ->
sv_denot E (SAlu ALU_SUB a b) = Z_to_bv 64 (va - vb).
Proof.
intros E a b va vb Ha Hb. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite Hb.
unfold U. rewrite Ha, unsigned_lit, Z_to_bv64_canon.
apply Z_to_bv64_eq_mod. unfold zcanon, M64. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

(* membership in a concrete list of facts *)
Ltac ro_in := unfold rs_L_scan, rs_L_chk; cbn [In app]; repeat (first [left; reflexivity | right]).
Ltac ro_kin := unfold ro_kept; apply in_map; cbn [In]; lia.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma ro_entry : forall (W : world rsegs) regs memc j, getr regs (Z_to_bv 5 12) = w64 j -> 0 <= j <= 32 ->
st_ok rsegs (Ereg regs sk_extra) ro_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 RS_O) memc (seg_rom rsegs))).
Proof.
intros W regs memc j H12 Hj.
rewrite restrict_mkst_fx.
unfold ro_ss. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; [exact I | exact I]]. cbn [ro_facts f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Ereg_nat regs _ 12 (Z_to_bv 5 12) eq_refl), H12. unfold w64.
  rewrite unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
Qed.

Section d.
Variable B : asyms.

(* ================================ the block ================================ *)
(* what the fall-through computes: s5 = at, s7 = 104 at, a3 = max(at, 33), a4 = t0 - 104 at *)
Definition ro_I_R (j t0 : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 21) = w64 j /\ getr regs2 (Z_to_bv 5 23) = w64 (104 * j) /\
getr regs2 (Z_to_bv 5 13) = w64 (Z.max j 33) /\ getr regs2 (Z_to_bv 5 14) = w64 (t0 - 104 * j).

Ltac ro_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply RPgSteps.same_io_wvb]; kio] in kio.
(* the symbolic value of register r in the engine's last state, as a closed term *)
Ltac ro_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.

Lemma ro_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (j n t0 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 12) = w64 j -> getr regs (Z_to_bv 5 25) = w64 n ->
getr regs (Z_to_bv 5 6) = w64 (104 * 2 ^ 32) -> getr regs (Z_to_bv 5 5) = w64 t0 ->
0 <= j <= n -> n <= 32 ->
SRr rsegs W (cfg_at rsegs RS_O regs memc mdc)
(fun W2 c2 =>
 (n <= j /\ sk_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_ABS ro_kept (fun _ => True) W2 c2) \/
 (j < n /\ sk_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_I ro_kept (ro_I_R j t0) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs j n t0 HJ H12 H25 H6 H5 Hj Hn.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof RPgSteps.rl_wx as Hwx. pose proof RPgSteps.rl_segs_low as Hsegs.
pose proof (ro_entry W regs memc j H12 ltac:(lia)) as HS.
remember (Ereg regs sk_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs sk_extra) E) by (subst E; apply env_agree_refl).
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm; subst E; exact (ew_Ereg_nat regs _ m r Hm)).
clear HE.
assert (E12 : ew E 12 = Z_to_bv 64 j) by (rewrite (EA 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (E25 : ew E 25 = Z_to_bv 64 n) by (rewrite (EA 25%nat (Z_to_bv 5 25) eq_refl); exact H25).
assert (E6 : ew E 6 = Z_to_bv 64 (104 * 2 ^ 32)) by (rewrite (EA 6%nat (Z_to_bv 5 6) eq_refl); exact H6).
assert (E5 : ew E 5 = Z_to_bv 64 t0) by (rewrite (EA 5%nat (Z_to_bv 5 5) eq_refl); exact H5).
assert (SHOK : sh_ok rsegs SKBx [] E (mrestrict (w_H W) memc)) by constructor.
unfold cfg_at. change (w64 RS_O) with (Z_to_bv 64 RS_O).
srr_branch_tok ro_tbl_ok HS SHOK SKspan.
- (* taken: at >= n_ent, 0x82278 to ABS 0x8245c *)
  aj_run_to_tok ro_tbl_ok HS HJ SHOK SKspan RS_ABS; [awr_ok_tac | ].
  lazymatch goal with
  | HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HF : frame_of ?E0 ?rs0 _ (ms_mem ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    Hc : branch_taken _ _ _ = _ |- _ =>
    pose proof (frame_of_read_only E0 rs0 _ _ eq_refl HF) as Hmem; rewrite Hmem in HJ;
    rewrite !sk_denot0, E12, E25, ro_bge in Hc by lia;
    apply SRr_ret; left; split; [apply negb_true_iff, Z.ltb_ge in Hc; lia|];
    apply (sk_post_intro B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ro_kept _ E' ss' ms _ HS eq_refl eq_refl Hmem HJ);
    [ ro_io
    | intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E' ss' (restrict (w_H W) ms) regs sk_extra ro_kept HS HAE
        ltac:(vm_compute; reflexivity) r Hr)
    | exact I ]
  end.
- (* fall-through: at < n_ent, 0x8227c .. 0x822a0, to I 0x822a4 *)
  aj_run_to_tok ro_tbl_ok HS HJ SHOK SKspan RS_I; [awr_ok_tac | ].
  lazymatch goal with
  | HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HF : frame_of ?E0 ?rs0 _ (ms_mem ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    Hc : branch_taken _ _ _ = _ |- _ =>
    pose proof (frame_of_read_only E0 rs0 _ _ eq_refl HF) as Hmem; rewrite Hmem in HJ;
    rewrite !sk_denot0, E12, E25, ro_bge in Hc by lia;
    apply SRr_ret; right; split; [apply negb_false_iff, Z.ltb_lt in Hc; lia|];
    apply (sk_post_intro B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ro_kept _ E' ss' ms _ HS eq_refl eq_refl Hmem HJ);
    [ ro_io
    | intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E' ss' (restrict (w_H W) ms) regs sk_extra ro_kept HS HAE
        ltac:(vm_compute; reflexivity) r Hr)
    | ];
    unfold ro_I_R; rewrite !(st_ok_restrict_reg rsegs (w_H W) E' ss' ms _ HS)
  end.
  (* the engine leaves s5 as at's own atom (the `srli` of the `slli` folds by at's range), a3 as the literal 33 (the
     `bltu` decided by that range), s7 as the `mulhu` and a4 as t0 minus it *)
  split.
  { ro_sv. rewrite sk_denot0, E12. reflexivity. }
  split.
  { ro_sv. rewrite denot_lit_U, (ro_U_s7 E j E12 E6) by lia. reflexivity. }
  split.
  { ro_sv. rewrite denot_lit_U, U_SLit. unfold w64. rewrite Z_to_bv64_canon. f_equal. lia. }
  { ro_sv. unfold w64. apply (ro_sub E (SOff 5 0) _ t0 (104 * j)).
    - rewrite sk_denot0. exact E5.
    - apply (ro_U_s7 E j E12 E6). lia. }
Qed.

End d.
End b.

(* ================================ the cuts ================================ *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem rk_outer_B : rs_piece_W11a_outer_stmt rsegs B MT.
Proof.
unfold rs_piece_W11a_outer_stmt. intros cx POST inp j _ HI HA.
unfold rs_from_O. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HO.
pose proof HO as (Hbase & Hat & Hrole & Hinv & Hrec).
pose proof Hbase as (Hcore & _ & _ & _ & _ & Hwf & _).
pose proof Hcore as (HJ & _ & _ & _ & Hio & _).
pose proof (rk_nent_le rec Hwf) as Hn32.
pose proof Hinv as (Hjn & _).
unfold rs_at_cx in Hat.
pose proof (sk_at_get _ _ _ _ _ 12 (Z.of_nat j) Hat ltac:(ro_in)) as R12.
pose proof (sk_at_get _ _ _ _ _ 25 (Z.of_nat (length (ents rec))) Hat ltac:(ro_in)) as R25.
pose proof (sk_at_get _ _ _ _ _ 6 (104 * 2 ^ 32) Hat ltac:(ro_in)) as R6.
pose proof (sk_at_get _ _ _ _ _ 5 (Z.lnot (e_pp (x_e cx) + 0x401c)) Hat ltac:(ro_in)) as R5.
unfold rs_at in Hat. apply Forall_app in Hat as [Hscan _].
fold (rs_at rsegs (w_H W2) mem2 regs2 (x_e cx) (rs_L_scan rsegs cx rec)) in Hscan.
eapply SRr_bind.
{ apply (ro_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (Z.of_nat j) (Z.of_nat (length (ents rec)))
    (Z.lnot (e_pp (x_e cx) + 0x401c)) HJ R12 R25 R6 R5); lia. }
intros W3 c3 _ [(Hge & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk & _) | (Hlt & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk & HR)].
- (* ABS: no pair is left, the answer is (None, 0) *)
  assert (HE0 : rs_E0 rec = (None, 0)) by (apply (rk_inv_end rec j Hinv); lia).
  pose proof Hrec as (_ & _ & _ & Hsnd & Hfst).
  rewrite HE0 in Hsnd, Hfst. cbn [fst snd] in Hsnd, Hfst.
  pose proof (sk_at_keep _ _ regs2 regs3 _ (rs_L_scan rsegs cx rec) ro_kept Hk ltac:(vm_compute; reflexivity) Hscan)
    as Hscan3.
  apply (HA fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  split; [exact (sk_chk_base B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hbase HJ3 Hio3
    ltac:(intros r Hr; apply Hk; destruct Hr as [->|[->| ->]]; ro_kin))|].
  split.
  { unfold rs_at_cx. unfold rs_L_scan in Hscan3. rewrite Hsnd in Hscan3.
    apply (sk_at_sub _ _ _ _ _ _ Hscan3). intros x Hx. unfold rs_L_chk in Hx |- *. cbn [In app] in Hx |- *.
    repeat (destruct Hx as [<-|Hx]; [repeat (first [left; reflexivity | right]) |]); destruct Hx. }
  split; [exact Hrole|]. split; assumption.
- (* I: at0 = m = at *)
  destruct HR as (Q21 & Q23 & Q13 & Q14).
  pose proof (sk_at_keep _ _ regs2 regs3 _ (rs_L_scan rsegs cx rec) ro_kept Hk ltac:(vm_compute; reflexivity) Hscan)
    as Hscan3.
  apply (HI fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  split; [exact (sk_chk_base B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hbase HJ3 Hio3
    ltac:(intros r Hr; apply Hk; destruct Hr as [->|[->| ->]]; ro_kin))|].
  split.
  { unfold rs_at_cx, rs_at. apply Forall_app. split; [exact Hscan3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rl_at fst snd].
    - rewrite (Hk (Z_to_bv 5 12) ltac:(ro_kin)). exact R12.
    - exact Q21.
    - exact Q23.
    - exact Q13.
    - exact Q14. }
  split; [exact Hrole|]. split; [exact Hinv|]. split; [exact Hrec|].
  split; [lia|]. intros q Hq. lia.
Qed.
End e.
End c.
