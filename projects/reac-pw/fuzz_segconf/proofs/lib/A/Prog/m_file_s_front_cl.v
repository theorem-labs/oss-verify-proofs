(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 460 of its 517 lines of code are new or changed and 396 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_FRONT, piece cl: one pass of the comment loop 0x8616c-0x861c4
   (MF-CUTS-A.md section 4: the comment scan 0x86158-0x861dc). At index i of the line it checks the byte p[i] (the
   instrumented check at 0x86174: a load of the shadow byte at ((p + i) >> 3) + the shadow base and a compare; its
   error path, the call of errpath_load1 0x86f88, is not reached because the text is addressable), loads it, and on
   ';' or '#' ends the line there when i = 0 or the byte before (checked at 0x8619c the same way) is a tab or a
   space; else it goes on to i + 1, or ends at the line's end. FR_CL (S i) and FR_CX give FR_CL i.
   The run is over a state of the registers and the one or two text bytes the pass reads (as fuzz_command's
   mix_call.v byte loop, 501c0d516c69:proofs/plugin-hostd/fuzz_command/lib/A/Prog/mix_call.v:350-480): the pass
   stores nothing, so the head's facts are carried by fr_ctx_run. The FRONT segment lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_front_mdl m_file_s_front_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_front_g.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the pass's state: a2 (x12) is the cursor q = p + i, the bytes q[0] (atom 32) and, for i > 0, q[-1] (atom 33) *)
Definition fr_cl_text1 : YP09.region := YP09.mkRegion (Some 12%nat) (-1) 1 0 0
  [YP09.mkChunk (-1) (CVal 1 (SOff 33 0)); YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition fr_cl_text0 : YP09.region := YP09.mkRegion (Some 12%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition fr_cl_facts : facts :=
  mkFacts [(10%nat, PTR 0); (12%nat, PTR 0); (18%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)]
  [] [].
Definition ss_cl1 : sstate := mkSS FR_CL sr_atoms [fr_cl_text1] None fr_cl_facts.
Definition ss_cl0 : sstate := mkSS FR_CL sr_atoms [fr_cl_text0] None fr_cl_facts.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the write goal of a run: the pass's one region is read-only *)
Ltac fr_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* after a run: the reader is the pass's start reader (MEQ), byte for byte *)
Ltac fr_meq :=
  lazymatch goal with
  | HFr : frame_of _ ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1),
    MEQ : forall a, aview _ _ ?m0 a = aview _ _ ?mc a |- _ =>
    let M := fresh "M" in
    pose proof (fr_aview_ro _ rs H m0 m1 HFr ltac:(vm_compute; reflexivity)) as M;
    let MEQ' := fresh "MEQ" in
    assert (MEQ' : forall a, aview SEGS H m1 a = aview SEGS H mc a) by (intros a; rewrite M; apply MEQ);
    clear M MEQ HFr; rename MEQ' into MEQ end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Section iter.
(* one pass at index i = S i' > 0 *)
Variables (n i' : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z).
Hypothesis HCX : FR_CX_stmt B n.
Hypothesis HNX : FR_CL_stmt B n (S (S i')).
Hypothesis CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n.
Hypothesis SH : fr_short regs1 line p rest.
Hypothesis R27 : getr regs1 27 = w64 p.
Hypothesis R23 : getr regs1 23 = w64 (p + Z.of_nat (length (mf_line rest))).
Hypothesis R16 : getr regs1 16 = w64 59.
Hypothesis R12 : getr regs1 12 = w64 (p + Z.of_nat (S i')).
Hypothesis R10 : getr regs1 10 = w64 (p + Z.of_nat (S i')).
Hypothesis R13 : getr regs1 13 = w64 (- Z.of_nat (S i')).
Hypothesis Hi : (S i' < length (mf_line rest))%nat.
Hypothesis Hcut : forall k, (k < S i')%nat -> cut_at (mf_line rest) k = false.

Definition cl_bi : Z := nth (S i') (mf_line rest) 0.
Definition cl_bj : Z := nth (S i' - 1) (mf_line rest) 0.
Definition cl_E : env := Eimg (Ereg regs1 [Z_to_bv 64 cl_bi; Z_to_bv 64 cl_bj]).

Lemma cl_tf : 4096 <= p /\ p + Z.of_nat (length (mf_line rest)) + 1 <= alloc_ceiling /\
  0 <= p + Z.of_nat (S i') < 2 ^ 64 /\ 0 <= p + Z.of_nat (length (mf_line rest)) < 2 ^ 64 /\
  0 <= cl_bi < 256 /\ 0 <= cl_bj < 256 /\ (length (mf_line rest) < 512)%nat.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (H1 & H2 & BY & BR8 & RAD).
pose proof (fr_line_len rest) as HLL. pose proof alloc_ceiling_value as [[_ HAC] _].
pose proof SH as (_ & _ & HL512).
split; [exact H1|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [apply BR8; exact Hi|]. split; [apply BR8; lia | exact HL512].
Qed.
Lemma cl_bytes : rdW Wc memc (p + Z.of_nat (S i')) = Some cl_bi /\ rdW Wc memc (p + Z.of_nat i') = Some cl_bj.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & BY & _ & _).
split; [exact (BY _ Hi)|]. unfold cl_bj. replace (S i' - 1)%nat with i' by lia. apply BY. lia.
Qed.
Lemma cl_rad : forall x, p <= x < p + Z.of_nat (length (mf_line rest)) ->
  range_addressable (rdW Wc memc) SHADOW_OFF x 1.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & _ & _ & RAD).
pose proof (fr_line_len rest) as HLL. intros x Hx y Hy. apply RAD. lia.
Qed.
Lemma cl_EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew cl_E k = getr regs1 r.
Proof. intros k r Hk Hk32. unfold cl_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. Qed.
Lemma cl_HAE : env_agree 32 (Ereg regs1 [Z_to_bv 64 cl_bi; Z_to_bv 64 cl_bj]) cl_E.
Proof. unfold cl_E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
(* the atoms' values at any later environment of the pass (its fresh atoms are 1024 and up) *)
Lemma cl_UX : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew cl_E k) ->
  U Ex (SOff 32 0) = cl_bi /\ U Ex (SOff 33 0) = cl_bj /\ U Ex (SOff 13 0) = 2 ^ 64 - Z.of_nat (S i') /\
  U Ex (SOff 12 1) = p + Z.of_nat (S i') + 1 /\ U Ex (SOff 23 0) = p + Z.of_nat (length (mf_line rest)) /\
  U Ex (SOff 10 0) = p + Z.of_nat (S i') /\ U Ex (SOff 10 (-1)) = p + Z.of_nat (S i') - 1 /\
  U Ex (SOff 18 0) = SHADOW_OFF.
Proof.
intros Ex HEx. pose proof cl_tf as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof alloc_ceiling_value as [[_ HAC] _].
pose proof CTX as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & R18 & _) & _).
assert (E13 : ew cl_E 13 = Z_to_bv 64 (2 ^ 64 - Z.of_nat (S i'))).
{ rewrite (cl_EN 13%nat 13%bv eq_refl) by lia. rewrite R13. unfold w64. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite <- (Z_mod_plus_full (- Z.of_nat (S i')) 1). f_equal; lia. }
assert (E32 : ew cl_E 32 = Z_to_bv 64 cl_bi)
  by (unfold cl_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew cl_E 33 = Z_to_bv 64 cl_bj)
  by (unfold cl_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
split; [apply U_atom; [rewrite HEx by lia; exact E32 | lia]|].
split; [apply U_atom; [rewrite HEx by lia; exact E33 | lia]|].
split; [apply U_atom; [rewrite HEx by lia; exact E13 | lia]|].
split; [apply fr_U_atom_off; [rewrite HEx, (cl_EN 12%nat 12%bv eq_refl) by lia; exact R12 | lia | lia]|].
split; [apply U_atom; [rewrite HEx, (cl_EN 23%nat 23%bv eq_refl) by lia; exact R23 | lia]|].
split; [apply U_atom; [rewrite HEx, (cl_EN 10%nat 10%bv eq_refl) by lia; exact R10 | lia]|].
split; [apply fr_U_atom_off; [rewrite HEx, (cl_EN 10%nat 10%bv eq_refl) by lia; exact R10 | lia | lia]|].
apply U_atom; [rewrite HEx, (cl_EN 18%nat 18%bv eq_refl) by lia; exact R18 | unfold SHADOW_OFF; lia].
Qed.
(* the cut at i = S i' as the bytes decide it *)
Lemma cl_CUTP : (cl_bi = 59 \/ cl_bi = 35) -> (cl_bj = 9 \/ cl_bj = 32) -> cut_at (mf_line rest) (S i') = true.
Proof.
intros Hm Hs. unfold cut_at. fold cl_bi. fold cl_bj.
unfold is_mark, sp_tab. destruct Hm as [-> | ->]; destruct Hs as [-> | ->]; reflexivity.
Qed.
Lemma cl_CUTN1 : cl_bi <> 59 -> cl_bi <> 35 -> cut_at (mf_line rest) (S i') = false.
Proof.
intros H1 H2. unfold cut_at. fold cl_bi. unfold is_mark.
rewrite (proj2 (Z.eqb_neq cl_bi 35) H2), (proj2 (Z.eqb_neq cl_bi 59) H1). reflexivity.
Qed.
Lemma cl_CUTN2 : cl_bj <> 9 -> cl_bj <> 32 -> cut_at (mf_line rest) (S i') = false.
Proof.
intros H1 H2. unfold cut_at. fold cl_bj. unfold sp_tab.
rewrite (proj2 (Z.eqb_neq cl_bj 32) H2), (proj2 (Z.eqb_neq cl_bj 9) H1). apply andb_false_r.
Qed.
(* the pass's start state *)
Lemma cl_seed : st_ok_pi SEGS VAL cl_E
  (mkSS FR_CL (sr_set (sr_set sr_atoms (16%bv : bv 5) (SLit 59)) (19%bv : bv 5) (SLit 32)) [fr_cl_text1] None fr_cl_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + FR_CL)) memc (seg_rom SEGS))).
Proof.
pose proof cl_tf as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof cl_bytes as (BY1 & BY0).
pose proof CTX as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & R18 & R19 & _) & _).
rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL cl_E ss_cl1 (mkst regs1 (Z_to_bv 64 (BASE + FR_CL)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ unfold ss_cl1. apply pa_entry_st_ok_full.
  + unfold cl_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor]. unfold region_ok, fr_cl_text1.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite (cl_EN 12%nat 12%bv eq_refl), R12 by lia. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS cl_E _ (p + Z.of_nat (S i')) (-1) 1 (SOff 33 0) cl_bj);
      [cbn [sv_denot]; unfold cl_E; rewrite Eimg_low by (unfold A_TEXT; lia);
       rewrite (ew_Ereg_extra regs1 _ 1); cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      replace (p + Z.of_nat (S i') + -1) with (p + Z.of_nat i') by lia. exact (fr_val_mem1 _ _ _ _ BY0).
    * apply (chunk_ok_val SEGS cl_E _ (p + Z.of_nat (S i')) 0 1 (SOff 32 0) cl_bi);
      [cbn [sv_denot]; unfold cl_E; rewrite Eimg_low by (unfold A_TEXT; lia);
       rewrite (ew_Ereg_extra regs1 _ 0); cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (fr_val_mem1 _ _ _ _ BY1).
  + cbn [pairwise_disjoint all_disjoint]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [fr_cl_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite (cl_EN 10%nat 10%bv eq_refl), (cl_EN 12%nat 12%bv eq_refl), (cl_EN 18%nat 18%bv eq_refl) by lia.
    rewrite R10, R12, R18. unfold cl_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_extra regs1 _ 0), (ew_Ereg_extra regs1 _ 1). cbn [nth].
    unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
    pose proof alloc_ceiling_value as [[_ HAC] _].
    pose proof Hi as Hi'.
    clear - T1 T2 T3 T5 T6 HAC Hi'. repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity.
    all: lia. }
pose proof (st_ok_pi_pin_reg' cl_E _ _ (16%bv : bv 5) 59 HS0 R16 eq_refl) as HS1.
exact (st_ok_pi_pin_reg' cl_E _ _ (19%bv : bv 5) 32 HS1 R19 eq_refl).
Qed.

(* the pass's tactics over this Section's facts *)
Ltac cl_ux UXN :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
    pose proof (cl_UX Ex ltac:(intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity)) as UXN end.
Ltac cl_obl :=
  lazymatch goal with
  | MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- range_addressable _ (U ?Ex (SOff 18 0)) (U ?Ex ?x) _ =>
    let UXO := fresh "UXO" in cl_ux UXO;
    let UX10 := fresh "UX10" in let UX10m := fresh "UX10m" in let UX18 := fresh "UX18" in
    destruct UXO as (_ & _ & _ & _ & _ & UX10 & UX10m & UX18);
    rewrite <- (aview_rd_of SEGS);
    apply (fr_ra_eq (aview SEGS (w_H Wc) memc)); [intros; first [apply MEQ | reflexivity] |];
    rewrite ?UX18, ?UX10, ?UX10m; apply cl_rad; pose proof Hi; lia end.
Ltac cl_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Bspan; try (fr_awr; fail); try (cl_obl; fail); fr_meq end.
Ltac cl_runto stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; try (fr_awr; fail); try (cl_obl; fail); fr_meq end.
Ltac cl_branch := lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  psrr_branch_tok RUN BR HS SHOK Bspan end.
(* the branch condition Hc as a fact of the atoms' values *)
Ltac cl_cond :=
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = _ |- _ =>
    let UXc := fresh "UXc" in cl_ux UXc;
    let a1 := fresh "a" in let a2 := fresh "a" in let a3 := fresh "a" in let a4 := fresh "a" in
    let a5 := fresh "a" in let a6 := fresh "a" in let a7 := fresh "a" in let a8 := fresh "a" in
    destruct UXc as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8);
    rewrite ?branch_eq_U, ?branch_ne_U in Hc;
    rewrite ?a1, ?a2, ?a3, ?a4, ?a5, ?a6, ?a7, ?a8 in Hc;
    repeat match type of Hc with context [U Ex (SLit ?z)] => rewrite (U_lit Ex z) in Hc by lia end;
    clear a1 a2 a3 a4 a5 a6 a7 a8
  end.
(* a stop at FR_CX or FR_CL (H): the head's facts, s6, a7, s11 from the pass's start; K proves the rest *)
Ltac cl_leaf H K :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- _ =>
    let HAE2 := fresh "HAE2" in
    assert (HAE2 : env_agree 32 (Ereg regs1 [Z_to_bv 64 cl_bi; Z_to_bv 64 cl_bj]) Ecur) by (env_agree_chain cl_HAE);
    let HK := fresh "HK" in
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ (FR_KEPT ++ [17; 22; 23; 27]%bv) HS HAE2
      ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2;
    let R19x := fresh "R19x" in prreg HS (19%bv : bv 5) R19x;
    pmkst HS;
    let R22 := fresh "R22" in let R17 := fresh "R17" in let HL512 := fresh "HL512" in
    pose proof SH as (R22 & R17 & HL512);
    eapply H;
    [ eapply fr_ctx_run; [exact CTX | exact HJ | exact MEQ | intros ?r ?Hr; apply HK; apply in_or_app; left; assumption
      | rewrite R19x; reflexivity]
    | split; [rewrite (HK 22%bv ltac:(cbv; tauto)); exact R22 |
       split; [rewrite (HK 17%bv ltac:(cbv; tauto)); exact R17 | exact HL512]]
    | rewrite (HK 27%bv ltac:(cbv; tauto)); exact R27
    | .. ]; K HS HK
  end.
(* the two exits of a pass that found no cut at its index (HNC): the next index, or the line's end *)
Ltac cl_nomark HNC :=
  cl_run; cl_branch;
  [ cl_cond; lazymatch goal with Hc : negb _ = true |- _ => apply Bool.negb_true_iff, Z.eqb_neq in Hc end;
    cl_runto FR_CL;
    cl_leaf HNX ltac:(fun HS HK =>
      pose proof cl_tf as (T1 & T2 & T3 & T4 & T5 & T6 & T7);
      first
      [ rewrite (HK 23%bv ltac:(cbv; tauto)); exact R23
      | let R := fresh in prreg HS (16%bv : bv 5) R; rewrite R; reflexivity
      | let R := fresh in prreg HS (12%bv : bv 5) R; rewrite R, (cl_EN 12%nat 12%bv eq_refl), R12 by lia; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia
      | let R := fresh in prreg HS (10%bv : bv 5) R; rewrite R, (cl_EN 10%nat 10%bv eq_refl), R10 by lia; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia
      | let R := fresh in prreg HS (13%bv : bv 5) R; rewrite R, (cl_EN 13%nat 13%bv eq_refl), R13 by lia; unfold w64;
        apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
        rewrite Zplus_mod_idemp_l; f_equal; lia
      | lia
      | intros ?k ?Hk; destruct (Nat.eq_dec k (S i')) as [->|?]; [exact HNC | apply Hcut; lia] ])
  | cl_cond; lazymatch goal with Hc : negb _ = false |- _ => apply Bool.negb_false_iff, Z.eqb_eq in Hc end;
    let HALL := fresh "HALL" in
    assert (HALL : forall k, (k < length (mf_line rest))%nat -> cut_at (mf_line rest) k = false)
      by (intros ?k ?Hk; destruct (Nat.eq_dec k (S i')) as [->|?]; [exact HNC | apply Hcut; lia]);
    cl_runto FR_CX;
    cl_leaf HCX ltac:(fun HS HK =>
      let R := fresh in prreg HS (12%bv : bv 5) R; rewrite R, (cl_EN 23%nat 23%bv eq_refl), R23 by lia;
      unfold fr_C, fr_cut; rewrite (proj2 (fr_cut_all _ HALL)); reflexivity) ].
(* a cut at i: the stop at FR_CX with C = S i' *)
Ltac cl_cut HCT :=
  let HCL := fresh "HCL" in pose proof (fr_cut_at_first _ _ Hi Hcut HCT) as [_ HCL];
  cl_runto FR_CX;
  cl_leaf HCX ltac:(fun HS HK =>
    let R := fresh in prreg HS (12%bv : bv 5) R; rewrite R, (cl_EN 12%nat 12%bv eq_refl), R12 by lia;
    unfold fr_C, fr_cut; rewrite HCL; reflexivity).
(* a pass whose byte is ';' or '#' (HM): a3 = -i is not 0, so the byte before is checked and loaded *)
Ltac cl_mark HM :=
  cl_run; cl_branch;
  [ cl_cond; lazymatch goal with Hc : (_ =? _) = true |- _ => apply Z.eqb_eq in Hc end;
    exfalso; pose proof Hi; pose proof cl_tf as (_ & _ & _ & _ & _ & _ & ?T7); lia
  | cl_run; cl_branch;
    [ cl_cond; lazymatch goal with Hc : (_ =? _) = true |- _ => apply Z.eqb_eq in Hc;
        cl_cut (cl_CUTP HM (or_introl Hc)) end
    | cl_cond; lazymatch goal with Hc : (_ =? _) = false |- _ => apply Z.eqb_neq in Hc;
        let H9 := fresh "H9" in rename Hc into H9;
        cl_run; cl_branch;
        [ cl_cond; lazymatch goal with Hc : (_ =? _) = true |- _ => apply Z.eqb_eq in Hc;
            cl_cut (cl_CUTP HM (or_intror Hc)) end
        | cl_cond; lazymatch goal with Hc : (_ =? _) = false |- _ => apply Z.eqb_neq in Hc;
            cl_nomark (cl_CUTN2 H9 Hc) end ] end ] ].

Lemma cl_step_S : mf_at B v Wc regs1 memc mdc FR_CL.
Proof.
pose proof CTX as (_ & _ & _ & (HJ & _) & _).
pose proof cl_seed as HS.
assert (HEI : img_env VAL A_LIM cl_E) by (unfold cl_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] cl_E (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
unfold mf_at.
cl_run; cl_branch.
- cl_cond. apply Z.eqb_eq in Hc. cl_mark (or_introl (B := cl_bi = 35) Hc).
- cl_cond. apply Z.eqb_neq in Hc. rename Hc into H59.
  cl_run; cl_branch.
  + cl_cond. apply Bool.negb_true_iff, Z.eqb_neq in Hc. cl_nomark (cl_CUTN1 H59 Hc).
  + cl_cond. apply Bool.negb_false_iff, Z.eqb_eq in Hc. cl_mark (or_intror (A := cl_bi = 59) Hc).
Qed.
End iter.

Section iter0.
(* the pass at index 0: no byte before it; a3 = 0, so a mark is a cut at 0 *)
Variables (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z).
Hypothesis HCX : FR_CX_stmt B n.
Hypothesis HNX : FR_CL_stmt B n 1.
Hypothesis CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n.
Hypothesis SH : fr_short regs1 line p rest.
Hypothesis R27 : getr regs1 27 = w64 p.
Hypothesis R23 : getr regs1 23 = w64 (p + Z.of_nat (length (mf_line rest))).
Hypothesis R16 : getr regs1 16 = w64 59.
Hypothesis R12 : getr regs1 12 = w64 (p + Z.of_nat 0).
Hypothesis R10 : getr regs1 10 = w64 (p + Z.of_nat 0).
Hypothesis R13 : getr regs1 13 = w64 (- Z.of_nat 0).
Hypothesis Hi : (0 < length (mf_line rest))%nat.

Definition c0_b : Z := nth 0 (mf_line rest) 0.
Definition c0_E : env := Eimg (Ereg regs1 [Z_to_bv 64 c0_b; Z_to_bv 64 0]).

Lemma c0_tf : 4096 <= p /\ p + Z.of_nat (length (mf_line rest)) + 1 <= alloc_ceiling /\
  0 <= p + Z.of_nat (length (mf_line rest)) < 2 ^ 64 /\ 0 <= c0_b < 256 /\ (length (mf_line rest) < 512)%nat /\
  rdW Wc memc p = Some c0_b.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (H1 & H2 & BY & BR8 & RAD).
pose proof (fr_line_len rest) as HLL. pose proof alloc_ceiling_value as [[_ HAC] _].
pose proof SH as (_ & _ & HL512).
split; [exact H1|]. split; [lia|]. split; [lia|]. split; [apply BR8; exact Hi|]. split; [exact HL512|].
pose proof (BY 0%nat Hi) as B0. rewrite Z.add_0_r in B0. exact B0.
Qed.
Lemma c0_rad : forall x, p <= x < p + Z.of_nat (length (mf_line rest)) ->
  range_addressable (rdW Wc memc) SHADOW_OFF x 1.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & _ & _ & RAD).
pose proof (fr_line_len rest) as HLL. intros x Hx y Hy. apply RAD. lia.
Qed.
Lemma c0_EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew c0_E k = getr regs1 r.
Proof. intros k r Hk Hk32. unfold c0_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. Qed.
Lemma c0_HAE : env_agree 32 (Ereg regs1 [Z_to_bv 64 c0_b; Z_to_bv 64 0]) c0_E.
Proof. unfold c0_E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma c0_UX : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew c0_E k) ->
  U Ex (SOff 32 0) = c0_b /\ U Ex (SOff 12 1) = p + 1 /\ U Ex (SOff 23 0) = p + Z.of_nat (length (mf_line rest)) /\
  U Ex (SOff 10 0) = p /\ U Ex (SOff 18 0) = SHADOW_OFF.
Proof.
intros Ex HEx. pose proof c0_tf as (T1 & T2 & T3 & T4 & T5 & _).
pose proof alloc_ceiling_value as [[_ HAC] _].
pose proof CTX as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & R18 & _) & _).
split; [apply U_atom; [rewrite HEx by lia; unfold c0_E; rewrite Eimg_low by (unfold A_TEXT; lia);
  exact (ew_Ereg_extra regs1 _ 0) | lia]|].
split; [apply fr_U_atom_off; [rewrite HEx, (c0_EN 12%nat 12%bv eq_refl), R12 by lia; f_equal; lia | lia | lia]|].
split; [apply U_atom; [rewrite HEx, (c0_EN 23%nat 23%bv eq_refl) by lia; exact R23 | lia]|].
split; [apply U_atom; [rewrite HEx, (c0_EN 10%nat 10%bv eq_refl), R10 by lia; unfold w64; f_equal; lia | lia]|].
apply U_atom; [rewrite HEx, (c0_EN 18%nat 18%bv eq_refl) by lia; exact R18 | unfold SHADOW_OFF; lia].
Qed.
Lemma c0_CUTP : (c0_b = 59 \/ c0_b = 35) -> cut_at (mf_line rest) 0 = true.
Proof. intros Hm. unfold cut_at. fold c0_b. unfold is_mark. destruct Hm as [-> | ->]; reflexivity. Qed.
Lemma c0_CUTN : c0_b <> 59 -> c0_b <> 35 -> cut_at (mf_line rest) 0 = false.
Proof.
intros H1 H2. unfold cut_at. fold c0_b. unfold is_mark.
rewrite (proj2 (Z.eqb_neq c0_b 35) H2), (proj2 (Z.eqb_neq c0_b 59) H1). reflexivity.
Qed.
Lemma c0_seed : st_ok_pi SEGS VAL c0_E
  (mkSS FR_CL (sr_set (sr_set (sr_set sr_atoms (16%bv : bv 5) (SLit 59)) (19%bv : bv 5) (SLit 32)) (13%bv : bv 5) (SLit 0))
    [fr_cl_text0] None fr_cl_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + FR_CL)) memc (seg_rom SEGS))).
Proof.
pose proof c0_tf as (T1 & T2 & T3 & T4 & T5 & BY0).
pose proof CTX as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & R18 & R19 & _) & _).
rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL c0_E ss_cl0 (mkst regs1 (Z_to_bv 64 (BASE + FR_CL)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ unfold ss_cl0. apply pa_entry_st_ok_full.
  + unfold c0_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor]. unfold region_ok, fr_cl_text0.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite (c0_EN 12%nat 12%bv eq_refl), R12 by lia. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS c0_E _ (p + Z.of_nat 0) 0 1 (SOff 32 0) c0_b);
      [cbn [sv_denot]; unfold c0_E; rewrite Eimg_low by (unfold A_TEXT; lia);
       rewrite (ew_Ereg_extra regs1 _ 0); cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    replace (p + Z.of_nat 0 + 0) with p by lia. exact (fr_val_mem1 _ _ _ _ BY0).
  + cbn [pairwise_disjoint all_disjoint]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [fr_cl_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite (c0_EN 10%nat 10%bv eq_refl), (c0_EN 12%nat 12%bv eq_refl), (c0_EN 18%nat 18%bv eq_refl) by lia.
    rewrite R10, R12, R18. unfold c0_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_extra regs1 _ 0), (ew_Ereg_extra regs1 _ 1). cbn [nth].
    unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
    pose proof alloc_ceiling_value as [[_ HAC] _]. pose proof Hi as Hi'.
    clear - T1 T2 T3 T4 HAC Hi'. repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity.
    all: lia. }
pose proof (st_ok_pi_pin_reg' c0_E _ _ (16%bv : bv 5) 59 HS0 R16 eq_refl) as HS1.
pose proof (st_ok_pi_pin_reg' c0_E _ _ (19%bv : bv 5) 32 HS1 R19 eq_refl) as HS2.
exact (st_ok_pi_pin_reg' c0_E _ _ (13%bv : bv 5) 0 HS2 R13 eq_refl).
Qed.

Ltac c0_ux UXN :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
    pose proof (c0_UX Ex ltac:(intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity)) as UXN end.
Ltac c0_obl :=
  lazymatch goal with
  | MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- range_addressable _ (U ?Ex (SOff 18 0)) (U ?Ex ?x) _ =>
    let UXO := fresh "UXO" in c0_ux UXO;
    let UX10 := fresh "UX10" in let UX18 := fresh "UX18" in
    destruct UXO as (_ & _ & _ & UX10 & UX18);
    rewrite <- (aview_rd_of SEGS);
    apply (fr_ra_eq (aview SEGS (w_H Wc) memc)); [intros; first [apply MEQ | reflexivity] |];
    rewrite ?UX18, ?UX10; apply c0_rad; pose proof Hi; lia end.
Ltac c0_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Bspan; try (fr_awr; fail); try (c0_obl; fail); fr_meq end.
Ltac c0_runto stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; try (fr_awr; fail); try (c0_obl; fail); fr_meq end.
Ltac c0_branch := lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  psrr_branch_tok RUN BR HS SHOK Bspan end.
Ltac c0_cond :=
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = _ |- _ =>
    let UXc := fresh "UXc" in c0_ux UXc;
    let a1 := fresh "a" in let a2 := fresh "a" in let a3 := fresh "a" in let a4 := fresh "a" in let a5 := fresh "a" in
    destruct UXc as (a1 & a2 & a3 & a4 & a5);
    rewrite ?branch_eq_U, ?branch_ne_U in Hc;
    rewrite ?a1, ?a2, ?a3, ?a4, ?a5 in Hc;
    repeat match type of Hc with context [U Ex (SLit ?z)] => rewrite (U_lit Ex z) in Hc by lia end;
    clear a1 a2 a3 a4 a5
  end.
Ltac c0_leaf H K :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- _ =>
    let HAE2 := fresh "HAE2" in
    assert (HAE2 : env_agree 32 (Ereg regs1 [Z_to_bv 64 c0_b; Z_to_bv 64 0]) Ecur) by (env_agree_chain c0_HAE);
    let HK := fresh "HK" in
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ (FR_KEPT ++ [17; 22; 23; 27]%bv) HS HAE2
      ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2;
    let R19x := fresh "R19x" in prreg HS (19%bv : bv 5) R19x;
    pmkst HS;
    let R22 := fresh "R22" in let R17 := fresh "R17" in let HL512 := fresh "HL512" in
    pose proof SH as (R22 & R17 & HL512);
    eapply H;
    [ eapply fr_ctx_run; [exact CTX | exact HJ | exact MEQ | intros ?r ?Hr; apply HK; apply in_or_app; left; assumption
      | rewrite R19x; reflexivity]
    | split; [rewrite (HK 22%bv ltac:(cbv; tauto)); exact R22 |
       split; [rewrite (HK 17%bv ltac:(cbv; tauto)); exact R17 | exact HL512]]
    | rewrite (HK 27%bv ltac:(cbv; tauto)); exact R27
    | .. ]; K HS HK
  end.
Ltac c0_cut HCT :=
  let HCL := fresh "HCL" in
  pose proof (fr_cut_at_first _ _ Hi ltac:(intros ?k ?Hk; lia) HCT) as [_ HCL];
  c0_runto FR_CX;
  c0_leaf HCX ltac:(fun HS HK =>
    let R := fresh in prreg HS (12%bv : bv 5) R; rewrite R, (c0_EN 12%nat 12%bv eq_refl), R12 by lia;
    unfold fr_C, fr_cut; rewrite HCL; reflexivity).
Ltac c0_nomark HNC :=
  c0_run; c0_branch;
  [ c0_cond; lazymatch goal with Hc : negb _ = true |- _ => apply Bool.negb_true_iff, Z.eqb_neq in Hc end;
    c0_runto FR_CL;
    c0_leaf HNX ltac:(fun HS HK =>
      pose proof c0_tf as (T1 & T2 & T3 & T4 & T5 & _);
      first
      [ rewrite (HK 23%bv ltac:(cbv; tauto)); exact R23
      | let R := fresh in prreg HS (16%bv : bv 5) R; rewrite R; reflexivity
      | let R := fresh in prreg HS (12%bv : bv 5) R; rewrite R, (c0_EN 12%nat 12%bv eq_refl), R12 by lia; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia
      | let R := fresh in prreg HS (10%bv : bv 5) R; rewrite R, (c0_EN 10%nat 10%bv eq_refl), R10 by lia; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia
      | let R := fresh in prreg HS (13%bv : bv 5) R; rewrite R; unfold w64; apply bv_eq; vm_compute; reflexivity
      | lia
      | intros ?k ?Hk; replace k with 0%nat by lia; exact HNC ])
  | c0_cond; lazymatch goal with Hc : negb _ = false |- _ => apply Bool.negb_false_iff, Z.eqb_eq in Hc end;
    let HALL := fresh "HALL" in
    assert (HALL : forall k, (k < length (mf_line rest))%nat -> cut_at (mf_line rest) k = false)
      by (intros ?k ?Hk; replace k with 0%nat by lia; exact HNC);
    c0_runto FR_CX;
    c0_leaf HCX ltac:(fun HS HK =>
      let R := fresh in prreg HS (12%bv : bv 5) R; rewrite R, (c0_EN 23%nat 23%bv eq_refl), R23 by lia;
      unfold fr_C, fr_cut; rewrite (proj2 (fr_cut_all _ HALL)); reflexivity) ].

Lemma cl_step_0 : mf_at B v Wc regs1 memc mdc FR_CL.
Proof.
pose proof CTX as (_ & _ & _ & (HJ & _) & _).
pose proof c0_seed as HS.
assert (HEI : img_env VAL A_LIM c0_E) by (unfold c0_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] c0_E (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
unfold mf_at.
c0_run; c0_branch.
- c0_cond. apply Z.eqb_eq in Hc. c0_cut (c0_CUTP (or_introl Hc)).
- c0_cond. apply Z.eqb_neq in Hc. rename Hc into H59.
  c0_run; c0_branch.
  + c0_cond. apply Bool.negb_true_iff, Z.eqb_neq in Hc. c0_nomark (c0_CUTN H59 Hc).
  + c0_cond. apply Bool.negb_false_iff, Z.eqb_eq in Hc. c0_cut (c0_CUTP (or_intror Hc)).
Qed.
End iter0.

Lemma fr_cl_step : forall n i, FR_CX_stmt B n -> FR_CL_stmt B n (S i) -> FR_CL_stmt B n i.
Proof.
intros n i HCX HNX v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX SH R27 R23 R16 R12 R10 R13 Hi Hcut.
destruct i as [|i'].
- exact (cl_step_0 n v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest HCX HNX CTX SH R27 R23 R16 R12 R10 R13 Hi).
- exact (cl_step_S n i' v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest HCX HNX CTX SH R27 R23 R16 R12 R10 R13 Hi Hcut).
Qed.
(* every index of the comment loop, from its exit (by induction on 512 - i: a line here is shorter than 512) *)
Lemma fr_cl : forall n, FR_CX_stmt B n -> forall i, FR_CL_stmt B n i.
Proof.
intros n HCX.
assert (HD : forall d i, (512 - d <= i)%nat -> FR_CL_stmt B n i).
{ induction d as [|d IH]; intros i Hd.
  - intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX SH. destruct SH as (_ & _ & HL). intros. lia.
  - destruct (Nat.le_gt_cases (512 - d) i) as [Hle | Hlt]; [exact (IH i Hle)|].
    apply fr_cl_step; [exact HCX | apply IH; lia]. }
intros i. apply (HD 512%nat i). lia.
Qed.
End e.
End f.
End d.
