(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths and module names changed; 177 of its 213 lines of code are new or changed and 978 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanOuter.v at a5a28fb15bdf for
   reac-pw/fuzz_rate's image A: role's pcs (O 0x821bc, I 0x821e0, ABS 0x82380) become rate's (0x829c0, 0x829e4,
   0x82b7c), the registers are renamed as rate's code has them (n_ent t2 -> t3, at0 s5 -> s6, at + 1 s9 -> s7, the
   five operands t3 t6 t5 t4 s11 -> t2 t6 t5 t4 s10), the cut file is lib/A/RtPgSeg.v (rl_ -> rt_, e_ -> q_), the
   entry state and the list lemmas come from lib/A/RtPgScanKit.v and the image facts from lib/A/RtPgSteps.v. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the piece "outer scan head"
   of the walk of LLVMFuzzerTestOneInput, lib/A/RtPgSeg.v rs_piece_W11a_outer_stmt. Proves no function (kind:
   segment lemma).

   THE CODE (O 0x829c0, the `while` of fuzz_rate.c:70 and pod_next_pair's set-up, pod.h:134-135)
     0x829c0  bge a1,t3,0x82b7c      at >= n_ent: no pair is left, to the absent check ABS
     0x829c4  addi s7,a1,1           s7 := at + 1
     0x829c8  mul a4,a1,a4           a4 := at * 104 (a4 = 104 at O)
     0x829cc  mv a5,t2               a5 := &ent[0]
     0x829d0  mv a2,t6               a2 := &ent[0] + 4
     0x829d4  mv a3,t5               a3 := &ent[0] + 8
     0x829d8  mv a7,t4               a7 := &ent[0] + 8
     0x829dc  mv a6,s10              a6 := &ent[0]
     0x829e0  mv s6,a1               s6 := at
   and falls through to the inner head I 0x829e4 with at0 = m = at. No load, no store, no instrumented check, no
   call: the piece writes no byte and changes no float register.

   HOW. ro_blk is the piece as a block lemma over the machine state at O (the registers as atoms, no region): the
   engine (lib/Reusable/YCbn.v, YCbq.v) splits the `bge` (srr_branch_tok) and runs each arm to its end pc; the post
   ro_post keeps the journal, the memory (the region list is empty, so the run's frame is the whole memory) and 19
   registers, and gives the values the arm computes. rk_outer_A reads O's cut (rs_cut_O), runs ro_blk at the run's
   own float state, and rebuilds ABS's cut (taken: at >= n_ent, the answer is (None, 0) by RtPgScanF.rk_inv_end) or
   I's cut at at0 = m = at (fall-through), then hands the state to the continuation. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YO0b YO0c YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg RtPgScanF RtPgScanKit.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgSteps.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* ================================ the code table ================================ *)
(* the nine words 0x829c0 .. 0x829e0; both end pcs (I 0x829e4, ABS 0x82b7c) lie outside it *)
Definition ro_tbl : ctable := build_table rsegs RS_O 9 TEmpty.
Lemma ro_tbl_ok : table_ok rsegs ro_tbl.
Proof. apply build_table_ok0. unfold RS_O. lia. Qed.

(* the registers the piece does not write and the cuts it reaches name: ra, sp, gp, tp, t2, s0, s1, s2 .. s5,
   s8 .. s11, t3 .. t6 *)
Definition ro_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 7; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27; 28; 29; 30; 31].

(* ================================ arithmetic ================================ *)
Lemma ro_bge : forall j n, 0 <= j < 2 ^ 63 -> 0 <= n < 2 ^ 63 ->
branch_taken BC_GE (Z_to_bv 64 j) (Z_to_bv 64 n) = negb (j <? n).
Proof.
intros j n Hj Hn. rewrite YO0c.branch_ge, !unsigned_lit_small by lia.
rewrite !YO0b.s64_small by lia. reflexivity.
Qed.
Lemma ro_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* membership in a concrete list of facts *)
Ltac ro_in := unfold rs_L_scan, rs_L_chk, rs_Hc; cbn [In app]; repeat (first [left; reflexivity | right]).
Ltac ro_kin := unfold ro_kept; apply in_map; cbn [In]; lia.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* ================================ the block ================================ *)
(* the state at the block's end pc: the world, the journal and the memory as at O, the I/O state, the kept
   registers, and R *)
Definition ro_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (pc : Z) (R : bvmap 5 word -> Prop)
: world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) memc (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md2 k /\ same_io mdc md2 /\
(forall r, In r ro_kept -> getr regs2 r = getr regs r) /\ R regs2.

(* what the fall-through computes *)
Definition ro_I_R (regs : bvmap 5 word) (j : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 14) = w64 (104 * j) /\ getr regs2 (Z_to_bv 5 22) = w64 j /\
getr regs2 (Z_to_bv 5 23) = w64 (j + 1) /\
getr regs2 (Z_to_bv 5 16) = getr regs (Z_to_bv 5 26) /\ getr regs2 (Z_to_bv 5 15) = getr regs (Z_to_bv 5 7) /\
getr regs2 (Z_to_bv 5 12) = getr regs (Z_to_bv 5 31) /\ getr regs2 (Z_to_bv 5 13) = getr regs (Z_to_bv 5 30) /\
getr regs2 (Z_to_bv 5 17) = getr regs (Z_to_bv 5 29).

Lemma ro_post_intro : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc (R : bvmap 5 word -> Prop)
E' ss' ms md',
st_ok rsegs E' ss' (restrict (w_H W) ms) -> ss_resv ss' = None -> ss_pc ss' = pc -> ms_mem ms = memc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md' k -> same_io mdc md' ->
(forall r, In r ro_kept -> getr (ms_regs ms) r = getr regs r) -> R (ms_regs ms) ->
ro_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc R W (mkCfg ms md').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc R E' ss' ms md' HS Hrv Hpc Hm HJ Hio Hk HR.
split; [reflexivity|]. exists (ms_regs ms), md'.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E' ss' ms HS Hrv) at 1; rewrite Hpc, Hm; reflexivity|].
split; [exact HJ|]. split; [exact Hio|]. split; [exact Hk | exact HR].
Qed.

Ltac ro_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply RtPgSteps.same_io_wvb]; kio] in kio.
(* the symbolic value of register r in the engine's last state, as a closed term *)
Ltac ro_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.

Lemma ro_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (j n : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 11) = w64 j -> getr regs (Z_to_bv 5 28) = w64 n -> getr regs (Z_to_bv 5 14) = w64 104 ->
0 <= j <= n -> n <= 32 ->
SRr rsegs W (cfg_at rsegs RS_O regs memc mdc)
(fun W2 c2 =>
 (n <= j /\ ro_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_ABS (fun _ => True) W2 c2) \/
 (j < n /\ ro_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_I (ro_I_R regs j) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs j n HJ H11 H28 H14 Hj Hn.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof RtPgSteps.rts_wx as Hwx. pose proof RtPgSteps.rts_segs_low as Hsegs.
pose proof (sk_entry RS_O W regs memc ltac:(unfold RS_O; lia)) as HS.
remember (Ereg regs sk_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs sk_extra) E) by (subst E; apply env_agree_refl).
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm; subst E; exact (ew_Ereg_nat regs _ m r Hm)).
clear HE.
assert (E11 : ew E 11 = Z_to_bv 64 j) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E28 : ew E 28 = Z_to_bv 64 n) by (rewrite (EA 28%nat (Z_to_bv 5 28) eq_refl); exact H28).
assert (E14 : ew E 14 = Z_to_bv 64 104) by (rewrite (EA 14%nat (Z_to_bv 5 14) eq_refl); exact H14).
assert (SHOK : sh_ok rsegs SKBx [] E (mrestrict (w_H W) memc)) by constructor.
unfold cfg_at. change (w64 RS_O) with (Z_to_bv 64 RS_O).
srr_branch_tok ro_tbl_ok HS SHOK SKspan.
- (* taken: at >= n_ent, 0x829c0 to ABS 0x82b7c *)
  aj_run_to_tok ro_tbl_ok HS HJ SHOK SKspan RS_ABS; [awr_ok_tac | ].
  lazymatch goal with
  | HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HF : frame_of ?E0 ?rs0 _ (ms_mem ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    Hc : branch_taken _ _ _ = _ |- _ =>
    pose proof (frame_of_read_only E0 rs0 _ _ eq_refl HF) as Hmem; rewrite Hmem in HJ;
    rewrite !ro_denot0, E11, E28, ro_bge in Hc by lia;
    apply SRr_ret; left; split; [apply negb_true_iff, Z.ltb_ge in Hc; lia|];
    apply (ro_post_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' ss' ms _ HS eq_refl eq_refl Hmem HJ);
    [ ro_io
    | intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E' ss' (restrict (w_H W) ms) regs sk_extra ro_kept HS HAE
        ltac:(vm_compute; reflexivity) r Hr)
    | exact I ]
  end.
- (* fall-through: at < n_ent, 0x829c4 .. 0x829e0, to I 0x829e4 *)
  aj_run_to_tok ro_tbl_ok HS HJ SHOK SKspan RS_I; [awr_ok_tac | ].
  lazymatch goal with
  | HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HF : frame_of ?E0 ?rs0 _ (ms_mem ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    Hc : branch_taken _ _ _ = _ |- _ =>
    pose proof (frame_of_read_only E0 rs0 _ _ eq_refl HF) as Hmem; rewrite Hmem in HJ;
    rewrite !ro_denot0, E11, E28, ro_bge in Hc by lia;
    apply SRr_ret; right; split; [apply negb_false_iff, Z.ltb_lt in Hc; lia|];
    apply (ro_post_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' ss' ms _ HS eq_refl eq_refl Hmem HJ);
    [ ro_io
    | intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E' ss' (restrict (w_H W) ms) regs sk_extra ro_kept HS HAE
        ltac:(vm_compute; reflexivity) r Hr)
    | ];
    unfold ro_I_R; rewrite !(st_ok_restrict_reg rsegs (w_H W) E' ss' ms _ HS)
  end.
  split.
  { ro_sv. rewrite denot_lit_U. unfold w64. f_equal. rewrite U_SMd. cbn [zmd_raw].
    rewrite (U_atom E 11 j E11), (U_atom E 14 104 E14) by lia. unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
  split.
  { ro_sv. rewrite ro_denot0, E11. reflexivity. }
  split.
  { ro_sv. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 11 j 1 E11) by lia. reflexivity. }
  repeat split; ro_sv; rewrite ro_denot0; apply EA; reflexivity.
Qed.

End d.
End b.

(* ================================ the cuts ================================ *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem rk_outer_A : rs_piece_W11a_outer_stmt rsegs B MT.
Proof.
unfold rs_piece_W11a_outer_stmt. intros cx POST inp j _ HI HA.
unfold rs_from_O. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HO.
pose proof HO as (Hbase & Hat & Hhz & Hinv & Hrec).
pose proof Hbase as (Hcore & _ & _ & _ & _ & Hwf & _).
pose proof Hcore as (HJ & _ & _ & _ & Hio & _).
pose proof (rk_nent_le rec Hwf) as Hn32.
pose proof Hinv as (Hjn & _).
unfold rs_at_cx in Hat.
pose proof (sk_at_get _ _ _ _ _ 11 (Z.of_nat j) Hat ltac:(ro_in)) as R11.
pose proof (sk_at_get _ _ _ _ _ 28 (Z.of_nat (length (ents rec))) Hat ltac:(ro_in)) as R28.
pose proof (sk_at_get _ _ _ _ _ 14 104 Hat ltac:(ro_in)) as R14.
pose proof (sk_at_get _ _ _ _ _ 26 (q_pp (x_e cx) + 0x4014) Hat ltac:(ro_in)) as R26.
pose proof (sk_at_get _ _ _ _ _ 7 (q_pp (x_e cx) + 0x4014) Hat ltac:(ro_in)) as R7.
pose proof (sk_at_get _ _ _ _ _ 31 (q_pp (x_e cx) + 0x4018) Hat ltac:(ro_in)) as R31.
pose proof (sk_at_get _ _ _ _ _ 29 (q_pp (x_e cx) + 0x401c) Hat ltac:(ro_in)) as R29.
pose proof (sk_at_get _ _ _ _ _ 30 (q_pp (x_e cx) + 0x401c) Hat ltac:(ro_in)) as R30.
unfold rs_at in Hat. apply Forall_app in Hat as [Hscan _].
fold (rs_at rsegs (w_H W2) mem2 regs2 (x_e cx) (rs_L_scan rsegs cx rec)) in Hscan.
eapply SRr_bind.
{ apply (ro_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (Z.of_nat j) (Z.of_nat (length (ents rec))) HJ R11 R28 R14);
  lia. }
intros W3 c3 _ [(Hge & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk & _) | (Hlt & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk & HR)].
- (* ABS: no pair is left, the answer is (None, 0) *)
  assert (HE0 : rs_E0 rec = (None, 0)) by (apply (rk_inv_end rec j Hinv); lia).
  pose proof Hrec as (_ & _ & _ & Hsnd & Hfst).
  rewrite HE0 in Hsnd, Hfst. cbn [fst snd] in Hsnd, Hfst.
  pose proof (sk_at_keep _ _ regs2 regs3 _ (rs_L_scan rsegs cx rec) ro_kept Hk ltac:(vm_compute; reflexivity) Hscan) as Hscan3.
  apply (HA fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  split; [exact (sk_chk_base B MT cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hbase HJ3 Hio3
    ltac:(intros r Hr; apply Hk; destruct Hr as [->|[->| ->]]; ro_kin))|].
  split.
  { unfold rs_at_cx. unfold rs_L_scan in Hscan3. rewrite Hsnd in Hscan3.
    apply (sk_at_sub _ _ _ _ _ _ Hscan3). intros x Hx. unfold rs_L_chk, rs_Hc in Hx |- *. cbn [In app] in Hx |- *.
    repeat (destruct Hx as [<-|Hx]; [repeat (first [left; reflexivity | right]) |]); destruct Hx. }
  split; [exact Hhz|]. split; assumption.
- (* I: at0 = m = at *)
  destruct HR as (Q14 & Q22 & Q23 & Q16 & Q15 & Q12 & Q13 & Q17).
  pose proof (sk_at_keep _ _ regs2 regs3 _ (rs_L_scan rsegs cx rec) ro_kept Hk ltac:(vm_compute; reflexivity) Hscan) as Hscan3.
  apply (HI fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  split; [exact (sk_chk_base B MT cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hbase HJ3 Hio3
    ltac:(intros r Hr; apply Hk; destruct Hr as [->|[->| ->]]; ro_kin))|].
  split.
  { unfold rs_at_cx, rs_at. apply Forall_app. split; [exact Hscan3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rt_at fst snd].
    - exact Q14.
    - exact Q22.
    - exact Q23.
    - rewrite Q16, R26. unfold w64. f_equal. lia.
    - rewrite Q15, R7. unfold w64. f_equal. lia.
    - rewrite Q12, R31. unfold w64. f_equal. lia.
    - rewrite Q13, R30. unfold w64. f_equal. lia.
    - rewrite Q17, R29. unfold w64. f_equal. lia. }
  split; [exact Hhz|]. split; [exact Hinv|]. split; [exact Hrec|].
  split; [lia|]. intros q Hq. lia.
Qed.
End e.
End c.

Print Assumptions rk_outer_A.
