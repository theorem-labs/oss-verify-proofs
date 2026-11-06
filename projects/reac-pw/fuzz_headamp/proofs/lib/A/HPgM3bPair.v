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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgScanHead.v, with its module paths changed; 133 of its 171 lines of code are new or changed and 993 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id): the piece "the pair
   loop's head" of the walk of LLVMFuzzerTestOneInput, lib/A/HPgSegM.v hq_piece_M3b_pair_stmt. Proves no function
   (kind: segment lemma).

   THE CODE (PAIR 0x8307c .. 0x8309c, pod_next_pair's set-up, pod.h:134-135, inlined into the `for` of
   fuzz_headamp.c:119)
     0x8307c  mv a0,s5              a0 := at
     0x83080  addi s5,s5,1          s5 := at + 1
     0x83084  mul a3,a0,a7          a3 := 104 at (a7 = 104)
     0x83088  mv a4,t6              a4 := &ent[0]
     0x8308c  ld a1,0xe8(s1)        a1 := &ent[0].size (R+0xe8)
     0x83090  ld a2,0xf8(s1)        a2 := &ent[0].body (R+0xf8)
     0x83094  ld a6,0x100(s1)       a6 := &ent[0].body (R+0x100)
     0x83098  mv a5,ra              a5 := &ent[0]
     0x8309c  mv s4,a0              s4 := at
   and falls through to the scan's head SCAN 0x830a0 with at0 = m = at. No store, no call, no instrumented check:
   the piece writes no byte and changes no float register.

   HOW. hp_blk is the piece as a block lemma over the machine state at PAIR (the registers as atoms, the three
   real-frame cells as one read-only region over three extra atoms); the engine runs it straight to SCAN.
   hb_pair_A reads the PAIR cut, runs hp_blk at the run's own float state, and rebuilds the SCAN cut at
   at0 = m = at: the five operand registers of the scan's turn are its entry table's addresses plus 104 (m - at0)
   = 0, and no entry lies in [at0, m). *)
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
(* the nine words 0x8307c .. 0x8309c; the end pc SCAN 0x830a0 lies outside it *)
Definition hp_tbl : ctable := build_table rsegs HQ_PAIR 9 TEmpty.
Lemma hp_tbl_ok : table_ok rsegs hp_tbl.
Proof. apply build_table_ok0. unfold HQ_PAIR. lia. Qed.

(* the registers the piece does not write: all but a0, a1, a2, a3, a4, a5, a6, s4, s5 *)
Definition hp_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 17; 18; 19; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

(* atom 32 is the token base of the kit's no-check runs (HPgSteps.rt_extra); atoms 33 .. 35 are the three cells *)
Definition hp_R : YP09.region := YP09.mkRegion (Some 9%nat) 0xe8 0x108 0 0
  [YP09.mkChunk 0xe8 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xf8 (CVal 8 (SOff 34 0));
   YP09.mkChunk 0x100 (CVal 8 (SOff 35 0))].
Definition hp_ss0 : sstate := mkSS HQ_PAIR sr_atoms [hp_R] None (mkFacts [] [] []).
Definition hp_extra (vsz vb1 vb2 : Z) : list word :=
  [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 vsz; Z_to_bv 64 vb1; Z_to_bv 64 vb2].

(* what the piece computes *)
Definition hp_RR (i A A' vsz vb1 vb2 : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 10) = w64 i /\ getr regs2 (Z_to_bv 5 21) = w64 (i + 1) /\
getr regs2 (Z_to_bv 5 13) = w64 (104 * i) /\ getr regs2 (Z_to_bv 5 14) = w64 A /\
getr regs2 (Z_to_bv 5 11) = w64 vsz /\ getr regs2 (Z_to_bv 5 12) = w64 vb1 /\
getr regs2 (Z_to_bv 5 16) = w64 vb2 /\ getr regs2 (Z_to_bv 5 15) = w64 A' /\
getr regs2 (Z_to_bv 5 20) = w64 i.

Ltac hp_atom :=
hb_sv; rewrite hb_denot0;
lazymatch goal with |- ew _ ?n = _ => lazymatch goal with En : ew _ n = Z_to_bv 64 _ |- _ => rewrite En; reflexivity end end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

Lemma hp_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R i A A' vsz vb1 vb2 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 21) = w64 i -> getr regs (Z_to_bv 5 17) = w64 104 ->
getr regs (Z_to_bv 5 31) = w64 A -> getr regs (Z_to_bv 5 1) = w64 A' ->
0 <= R -> R + 0x108 <= 2 ^ 64 -> 0 <= i <= 32 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 (vsz mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (vb1 mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 (vb2 mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs HQ_PAIR regs memc mdc)
(hb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_SCAN hp_kept (hp_RR i A A' vsz vb1 vb2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i A A' vsz vb1 vb2
  HJ H9 H21 H17 H31 H1 HR0 HR1 Hi Ve8 Vf8 V100.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hp_extra vsz vb1 vb2) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E21 : ew (Ereg regs ex) 21 = Z_to_bv 64 i) by (rewrite (EA 21%nat (Z_to_bv 5 21) eq_refl); exact H21).
assert (E17 : ew (Ereg regs ex) 17 = Z_to_bv 64 104) by (rewrite (EA 17%nat (Z_to_bv 5 17) eq_refl); exact H17).
assert (E31 : ew (Ereg regs ex) 31 = Z_to_bv 64 A) by (rewrite (EA 31%nat (Z_to_bv 5 31) eq_refl); exact H31).
assert (E1 : ew (Ereg regs ex) 1 = Z_to_bv 64 A') by (rewrite (EA 1%nat (Z_to_bv 5 1) eq_refl); exact H1).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 vsz) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 vb1) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew (Ereg regs ex) 35 = Z_to_bv 64 vb2) by (subst ex; exact (ew_Ereg_extra regs _ 3)).
assert (HS : st_ok rsegs (Ereg regs ex) hp_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HQ_PAIR) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hp_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor; [|constructor; [|constructor]]].
    + exact (hb_slot_chunk _ _ _ R 0xe8 vsz 33 E33 Ve8).
    + exact (hb_slot_chunk _ _ _ R 0xf8 vb1 34 E34 Vf8).
    + exact (hb_slot_chunk _ _ _ R 0x100 vb2 35 E35 V100).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HQ_PAIR) with (Z_to_bv 64 HQ_PAIR).
aj_run_to_tok hp_tbl_ok HS HJ SHOK HPgSteps.RTBspan HQ_SCAN; [awr_ok_tac | ]. hb_mem.
apply SRr_ret. hb_post_intro B hp_kept.
unfold hp_RR. lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
split; [hp_atom|].
split.
{ hb_sv. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 21 i 1 E21) by lia. reflexivity. }
split.
{ hb_sv. rewrite denot_lit_U. unfold w64. f_equal. rewrite U_SMd. cbn [zmd_raw].
  rewrite (U_atom E 21 i E21), (U_atom E 17 104 E17) by lia. unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
split; [hp_atom|]. split; [hp_atom|]. split; [hp_atom|]. split; [hp_atom|]. split; [hp_atom|]. hp_atom.
Qed.
End d.
End b.

(* ================================ the cuts ================================ *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem hb_pair_A : hq_piece_M3b_pair_stmt rsegs B MT.
Proof.
unfold hq_piece_M3b_pair_stmt. intros cx POST r ev i HS HSC.
unfold hq_from_PAIR. intros fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf Hcut.
pose proof Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hlive & Hn0 & Hil & Hx & Hfold).
pose proof Hb3 as (Hcore & _).
pose proof Hcore as (HJ & _).
pose proof (hb_start_wf B cx r ev HS) as Hwf.
pose proof (proj1 (ents_wf r Hwf)) as Hn32.
pose proof (hb_start_R B cx r ev HS) as (HR0 & HR1 & _).
pose proof (hb_start_pp B cx r ev HS) as (_ & _ & Hp4k & Hpc & Hceil).
unfold hs_at_cx in Hat.
pose proof (hb_at_get _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(hb_in)) as R9.
pose proof (hb_at_get _ _ _ _ _ 21 (Z.of_nat i) Hat ltac:(hb_in)) as R21.
pose proof (hb_at_get _ _ _ _ _ 17 104 Hat ltac:(hb_in)) as R17.
pose proof (hb_at_get _ _ _ _ _ 31 (e_pp (x_e cx) + HQ_ENT0) Hat ltac:(hb_in)) as R31.
pose proof (hb_at_get _ _ _ _ _ 1 (e_pp (x_e cx) + HQ_ENT0) Hat ltac:(hb_in)) as R1.
pose proof (hb_at_cell _ _ _ _ _ XR 0xe8 (e_pp (x_e cx) + HQ_ENT_SZ) Hat ltac:(hb_in)) as Ce8.
pose proof (hb_at_cell _ _ _ _ _ XR 0xf8 (e_pp (x_e cx) + HQ_ENT_BODY) Hat ltac:(hb_in)) as Cf8.
pose proof (hb_at_cell _ _ _ _ _ XR 0x100 (e_pp (x_e cx) + HQ_ENT_BODY) Hat ltac:(hb_in)) as C100.
cbn [hd_xv] in Ce8, Cf8, C100.
(* the facts the turn keeps *)
assert (Hat' : hs_at rsegs (w_H W2) mem2 regs2 (x_e cx)
  (hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_loopr rsegs cx ++
   [(LReg 7, hq_nent r); (LReg 28, hq_nent r - 1)])) by hb_sub Hat.
eapply SRr_bind.
{ apply (hp_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (Z.of_nat i)
    (e_pp (x_e cx) + HQ_ENT0) (e_pp (x_e cx) + HQ_ENT0) (e_pp (x_e cx) + HQ_ENT_SZ)
    (e_pp (x_e cx) + HQ_ENT_BODY) (e_pp (x_e cx) + HQ_ENT_BODY) HJ R9 R21 R17 R31 R1); try lia;
  [exact Ce8 | exact Cf8 | exact C100]. }
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HRR).
destruct HRR as (Q10 & Q21 & Q13 & Q14 & Q11 & Q12 & Q16 & Q15 & Q20).
pose proof (hb_at_keep _ _ _ _ _ Hat' regs3 hp_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
apply (HSC fx2 ly2 S2 W2 regs3 mem2 md3 cs keys rf).
split.
{ apply (hb_base3_regs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
  intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hp_kept; hb_kin. }
split.
{ unfold hs_at_cx. apply hb_at_app; split; [hb_sub Hat3|].
  apply hb_at_app; split; [hb_sub Hat3|].
  apply hb_at_app; split; [hb_sub Hat3|].
  apply hb_at_app; split; [|hb_sub Hat3].
  unfold hq_L_scan, hs_at. cbv zeta. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
  - exact Q13.
  - rewrite Q11. unfold w64. f_equal. lia.
  - rewrite Q12. unfold w64. f_equal. lia.
  - rewrite Q16. unfold w64. f_equal. lia.
  - rewrite Q14. unfold w64. f_equal. lia.
  - rewrite Q15. unfold w64. f_equal. lia.
  - exact Q20.
  - exact Q21. }
split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|].
split; [lia|]. split; [intros q Hq; lia|]. split; [exact Hx | exact Hfold].
Qed.
End c.

Print Assumptions hb_pair_A.
