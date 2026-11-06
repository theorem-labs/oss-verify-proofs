(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95be for
   reac-pw/fuzz_rate's image A: role's pcs (C3 0x820c4, the memcpy return 0x820e4, the parse return 0x8210c, E
   0x8212c, MAL 0x823fc, T 0x82408) become rate's (0x828b8, 0x828dc, 0x8290c, E 0x82930, MAL 0x82c9c, A 0x82ca8);
   the registers are renamed as rate's code has them (pod s2 -> s6, &cell s6 -> s5 = &hz, flags & 1 s4 -> s3, the
   frame's shadow base s3 -> s4, the shadow offset s7 -> s2, len s8 -> s10, pp + 0x4d18 s10 -> s9); F is read from
   the cell R+0x78 (blocks A and C: a read-only region at R), the hz cell takes the 4-byte 0x5a5a5a5a, block B also
   stores pod into R+0x138 (a writable window of the region at R) and reloads the flags byte into s10; the memcpy call
   is lib/A/RtPgSteps.v rts_intrin_at (role's hd_memcpy dropped), the .rodata zone is [0x10000, 0x22000), the cut file
   is lib/A/RtPgSeg.v (rl_ -> rt_, e_ -> q_, the role cell -> rs_hz_at, the frame pattern at the exits rs_PZ), the
   entry-state and list lemmas come from lib/A/RtPgScanKit.v and the memory facts from lib/A/RtPgMem.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgScanHead.v, with its module paths changed; 139 of its 173 lines of code are new or changed and 997 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id): the piece "the pair
   loop's latch" of the walk of LLVMFuzzerTestOneInput, lib/A/HPgSegM.v hq_piece_M3b_latch_stmt. Proves no function
   (kind: segment lemma).

   THE CODE (LATCH 0x83474 .. 0x8348c, the `for` of fuzz_headamp.c:119 and pod_next_pair's test, pod.h:134)
     0x83474  ld t3,0xd0(s1)       t3 := n_ent - 1 (R+0xd0, stored by the key piece at 0x83174)
     0x83478  addi a7,zero,0x68    a7 := 104
     0x8347c  addi t4,zero,8       t4 := the String type
     0x83480  addi t5,zero,-1      t5 := -1
     0x83484  ld ra,0xc8(s1)       ra := &ent[0] (R+0xc8, stored at 0x83170)
     0x83488  blt s5,t2,0x8307c    at < n_ent: the pair loop's head PAIR
     0x8348c  j 0x83694            else the loop is done: RC
   No store, no call, no instrumented check: the piece writes no byte and changes no float register.

   HOW. hl_blk is the piece as a block lemma over the machine state at LATCH (lib/Reusable: the token engine YCbn.v,
   the journal YCbq.v), stated for any float state: the entry state has the registers as atoms and the two
   real-frame cells R+0xc8 and R+0xd0 as one read-only region over two extra atoms; the engine runs to the `blt`,
   splits it, and runs each arm to its end pc. hb_latch_A reads the LATCH cut, runs hl_blk at the run's own float
   state, and rebuilds the PAIR cut at the same index (taken: j < n_ent) or the RC cut (j >= n_ent: no pair is
   left, so x holds expect_of's answer, HPgM3bBase.hb_fold_end). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgM3bBase.
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
(* the seven words 0x83474 .. 0x8348c; both end pcs (PAIR 0x8307c, RC 0x83694) lie outside it *)
Definition hl_tbl : ctable := build_table rsegs HQ_LATCH 7 TEmpty.
Lemma hl_tbl_ok : table_ok rsegs hl_tbl.
Proof. apply build_table_ok0. unfold HQ_LATCH. lia. Qed.

(* the registers the piece does not write: all but ra, a7, t3, t4, t5 *)
Definition hl_kept : list (bv 5) :=
map (Z_to_bv 5) [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31].

(* atom 32 is the token base of the kit's no-check runs (HPgSteps.rt_extra); atoms 33 and 34 are the two cells *)
Definition hl_R : YP09.region := YP09.mkRegion (Some 9%nat) 0xc8 0xd8 0 0
  [YP09.mkChunk 0xc8 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xd0 (CVal 8 (SOff 34 0))].
Definition hl_ss0 : sstate := mkSS HQ_LATCH sr_atoms [hl_R] None (mkFacts [] [] []).
Definition hl_extra (vra vt3 : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 vra; Z_to_bv 64 vt3].

(* what both arms compute *)
Definition hl_RR (vra vt3 : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 28) = w64 vt3 /\ getr regs2 (Z_to_bv 5 17) = w64 104 /\
getr regs2 (Z_to_bv 5 29) = w64 8 /\ getr regs2 (Z_to_bv 5 30) = w64 (-1) /\
getr regs2 (Z_to_bv 5 1) = w64 vra.

Ltac hl_lit := hb_sv; cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity.
Ltac hl_atom E :=
hb_sv; rewrite hb_denot0;
lazymatch goal with |- ew _ ?n = _ => lazymatch goal with En : ew _ n = Z_to_bv 64 _ |- _ => rewrite En; reflexivity end end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

Lemma hl_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R j n vra vt3 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 21) = w64 j -> getr regs (Z_to_bv 5 7) = w64 n ->
0 <= R -> R + 0xd8 <= 2 ^ 64 -> 0 <= j < 2 ^ 63 -> 0 <= n < 2 ^ 63 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc8) 8 (vra mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 (vt3 mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs HQ_LATCH regs memc mdc)
(fun W2 c2 =>
 (j < n /\ hb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_PAIR hl_kept (hl_RR vra vt3) W2 c2) \/
 (n <= j /\ hb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_RC hl_kept (hl_RR vra vt3) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R j n vra vt3 HJ H9 H21 H7 HR0 HR1 Hj Hn Vc8 Vd0.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hl_extra vra vt3) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E21 : ew (Ereg regs ex) 21 = Z_to_bv 64 j) by (rewrite (EA 21%nat (Z_to_bv 5 21) eq_refl); exact H21).
assert (E7 : ew (Ereg regs ex) 7 = Z_to_bv 64 n) by (rewrite (EA 7%nat (Z_to_bv 5 7) eq_refl); exact H7).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 vra) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 vt3) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (HS : st_ok rsegs (Ereg regs ex) hl_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HQ_LATCH) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hl_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor; [|constructor]].
    + exact (hb_slot_chunk _ _ _ R 0xc8 vra 33 E33 Vc8).
    + exact (hb_slot_chunk _ _ _ R 0xd0 vt3 34 E34 Vd0).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HQ_LATCH) with (Z_to_bv 64 HQ_LATCH).
(* 0x83474 .. 0x83484, stop at the `blt` *)
aj_run_tok hl_tbl_ok HS HJ SHOK HPgSteps.RTBspan; [awr_ok_tac | ]. hb_mem.
srr_branch_tok hl_tbl_ok HS SHOK HPgSteps.RTBspan;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end;
rewrite !hb_denot0, E21, E7, hb_blt in Hc by lia.
- (* taken: at < n_ent, to PAIR 0x8307c *)
  aj_run_to_tok hl_tbl_ok HS HJ SHOK HPgSteps.RTBspan HQ_PAIR; [awr_ok_tac | ]. hb_mem.
  apply SRr_ret; left. split; [apply Z.ltb_lt in Hc; exact Hc|].
  hb_post_intro B hl_kept.
  unfold hl_RR. lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  split; [hl_atom E|]. split; [hl_lit|]. split; [hl_lit|]. split; [hl_lit|]. hl_atom E.
- (* not taken: at >= n_ent, to RC 0x83694 *)
  aj_run_to_tok hl_tbl_ok HS HJ SHOK HPgSteps.RTBspan HQ_RC; [awr_ok_tac | ]. hb_mem.
  apply SRr_ret; right. split; [apply Z.ltb_ge in Hc; exact Hc|].
  hb_post_intro B hl_kept.
  unfold hl_RR. lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  split; [hl_atom E|]. split; [hl_lit|]. split; [hl_lit|]. split; [hl_lit|]. hl_atom E.
Qed.
End d.
End b.

(* ================================ the cuts ================================ *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem hb_latch_A : hq_piece_M3b_latch_stmt rsegs B MT.
Proof.
unfold hq_piece_M3b_latch_stmt. intros cx POST r ev j HS HP HRC.
unfold hq_from_LATCH. intros fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf Hcut.
pose proof Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hlive & Hn0 & Hjn & Hx & Hfold).
pose proof Hb3 as (Hcore & _).
pose proof Hcore as (HJ & _).
pose proof (hb_start_wf B cx r ev HS) as Hwf.
pose proof (proj1 (ents_wf r Hwf)) as Hn32.
pose proof (hb_start_R B cx r ev HS) as (HR0 & HR1 & _).
unfold hs_at_cx in Hat.
pose proof (hb_at_get _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(hb_in)) as R9.
pose proof (hb_at_get _ _ _ _ _ 21 (Z.of_nat j) Hat ltac:(hb_in)) as R21.
pose proof (hb_at_get _ _ _ _ _ 7 (hq_nent r) Hat ltac:(hb_in)) as R7.
pose proof (hb_at_get _ _ _ _ _ 31 (e_pp (x_e cx) + HQ_ENT0) Hat ltac:(hb_in)) as R31.
pose proof (hb_at_cell _ _ _ _ _ XR 0xc8 (e_pp (x_e cx) + HQ_ENT0) Hat ltac:(hb_in)) as Cc8.
pose proof (hb_at_cell _ _ _ _ _ XR 0xd0 (hq_nent r - 1) Hat ltac:(hb_in)) as Cd0.
cbn [hd_xv] in Cc8, Cd0.
unfold hq_nent in *.
eapply SRr_bind.
{ apply (hl_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (Z.of_nat j)
    (Z.of_nat (length (ents r))) (e_pp (x_e cx) + HQ_ENT0) (Z.of_nat (length (ents r)) - 1) HJ R9 R21 R7);
  try lia; [exact Cc8 | exact Cd0]. }
intros W3 c3 _ [(Hlt & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HRR)
              | (Hge & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HRR)].
- (* PAIR at the same index *)
  destruct HRR as (Q28 & Q17 & Q29 & Q30 & Q1).
  pose proof (hb_at_keep _ _ _ _ _ Hat regs3 hl_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  apply (HP fx2 ly2 S2 W2 regs3 mem2 md3 cs keys rf).
  split.
  { apply (hb_base3_regs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
    intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hl_kept; hb_kin. }
  split.
  { unfold hs_at_cx. apply hb_at_app; split; [hb_sub Hat3|].
    apply hb_at_app; split; [hb_sub Hat3|].
    unfold hq_L_loopr, hs_at. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - exact Q1.
    - rewrite Hk3 by (unfold hl_kept; hb_kin). exact R31.
    - exact Q29.
    - exact Q30.
    - exact Q17.
    - rewrite Hk3 by (unfold hl_kept; hb_kin). exact R21.
    - rewrite Hk3 by (unfold hl_kept; hb_kin). exact R7.
    - exact Q28. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|]. split; [exact Hn0|].
  split; [lia|]. split; [exact Hx | exact Hfold].
- (* RC: no pair is left, x holds expect_of's answer *)
  pose proof (hb_at_keep _ _ _ _ _ Hat regs3 hl_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  destruct (hb_fold_end cx r j cs keys rf Hfold ltac:(lia)) as (-> & -> & ->).
  apply (HRC fx2 ly2 S2 W2 regs3 mem2 md3).
  split.
  { apply (hb_base3_regs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
    intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hl_kept; hb_kin. }
  split; [unfold hs_at_cx; hb_sub Hat3|].
  split; [exact (proj1 (proj2 Hlive))|].
  split; [exact (hb_exp_rc cx r Hlive) | exact Hx].
Qed.
End c.

Print Assumptions hb_latch_A.
