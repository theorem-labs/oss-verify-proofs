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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 126 of its 172 lines of code are new or changed and 407 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140): the segment S_MF_KDONE of its walk, 11
   instructions from the cut KDONE 0x86c1c (the image-B m_file segment table section 11, the image-B m_file cut map section 4).
   A walk lane of the image-B m_file-family owner's G2B. Adapted from image A's lib/A/Prog/m_file_s_tail.v mf_kdone_at (the image-A m_file-family lane,
   commit ba33778143e7) at image B's numbers. No call, no instrumented
   check, no UBSan trap.

   What the code does (B pc):
     0x86c1c          s10 = 152(s1), the next line's address (image A: a7 = 144(s1))
     0x86c20-0x86c40  low.i's 8 shadow bytes (shadow(FB) + 4 .. + 11, through s8 = shadow(FB); image A: s10) = 0xf8
                      (the bytes are marked unusable again: mf_core moves from MF_LOW_ON to MF_LOW_OFF)
     0x86c44          `j` TAIL 0x86820
   The run writes only the frame's shadow (mf_tx_core / mf_tx_cells / mf_tx_loop of the shared lib/B/Prog/m_file_k.v
   carry the rest). The seed is lib/B/Prog/m_file_sd.v's mf_seed (written by a walk lane) with 152(s1) = p (hnp) and the frame's
   shadow region writable; s8 is pinned to its atom 36. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the state's form, computed *)
Ltac mfk_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
(* one byte of low.i's shadow after the re-poisoning run: the final frame-shadow region's chunk *)
Ltac mfk_byte HR5 U36 :=
lazymatch goal with |- val_mem _ _ (?b + ?i) 1 _ =>
  let V := fresh "V" in
  pose proof (field_of_region_any _ _ 36 b _ 0 16 0 16 i 1%N _ HR5 U36
    ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
  lazymatch type of V with val_mem _ _ _ _ ?x => replace x with MF_LOW_OFF in V by (vm_compute; reflexivity) end;
  change (N.to_nat 1) with 1%nat in V; exact V
end.

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
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* S_MF_KDONE at one FP state *)
Lemma mf_kdone_at : forall n, MF_TAIL_stmt B n -> MF_KDONE_stmt B n.
Proof.
intros n TAIL. unfold MF_KDONE_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS RA Hn LOOP MOD NP R27 R20.
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_loop_blk B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc cur line p rest CX CORE LOOP)
  as (bt & mt & Hbt & Hbt1 & Hbt2 & Htp).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Bt4096 & Btceil & _).
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S1.
pose proof LOOP as (_ & _ & _ & _ & _ & Hcurok & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc cur CX CORE Hcurok) as Hcur.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
assert (Hp64 : 0 <= p < 2 ^ 64) by lia.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc cur p [] MF_KDONE true true [] false false
  [] true CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hp64 ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur p []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur p []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
pose proof (EX 6%nat ltac:(unfold A_TEXT; lia)) as E38.
cbn [Nat.add nth mf_extra map app] in E32, E36, E38.
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
(* the frame cells read-only *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. mfk_norm HS1.
(* s8 = shadow(FB) as the frame shadow's atom 36 *)
apply (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) (SOff 36 0)) in HS1;
  [| reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E36; cbn [ms_regs restrict mkst];
     rewrite R24; reflexivity].
mfk_norm HS1.
unfold mf_at.
(* the run 0x86c1c .. 0x86c44: s10 = 152(s1); low.i's 8 shadow bytes = 0xf8; `j` TAIL *)
paj_run_to_sh RUNTOP HS1 HJ MF_TAIL.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  do 5 (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 36%nat (SHADOW_OFF + frame_addr lyc 1 pos / 8));
    [reflexivity | exact U36 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, pos.
    split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd].
    change (fs_frame_bytes 1 / 8) with 16. lia. }
  apply awr_ok_nil. }
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a ->
    rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha HnW; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc)
      (mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos)) HFr _ a Ha HnW);
    intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw];
      [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U36 in Hr; right; left; lia] |]);
    destruct Hinw | ] end.
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
assert (G : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a; apply (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG)).
assert (VSH' : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_OFF).
{ pose proof (st_ok_pi_region_nth E _ _ 5 _ HS1 eq_refl) as HR5. cbn [restrict ms_mem] in HR5.
  intros i Hi. assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11) by lia.
  repeat (destruct Hc as [-> | Hc]; [mfk_byte HR5 U36 |]). subst i. mfk_byte HR5 U36. }
pose proof (mf_tx_core B v lyc Sc Wc memc mdc (ms_mem ms) mdw pos MF_LOW_ON MF_LOW_OFF mcc CX CORE HJ K G VSH')
  as CORE'.
pose proof (mf_tx_cells B v lyc Sc Wc memc mdc (ms_mem ms) pos MF_LOW_ON mcc cur CX CORE K CELLS) as CELLS'.
pose proof (mf_tx_loop B v lyc Sc Wc memc mdc (ms_mem ms) mdw pos MF_LOW_ON mcc mcc cur line p rest CX CORE
  (proj1 HJ) K G LOOP) as LOOP'.
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (23%bv : bv 5) Q23. prreg HS1 (24%bv : bv 5) Q24.
prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (22%bv : bv 5) Q22. prreg HS1 (25%bv : bv 5) Q25.
prreg HS1 (26%bv : bv 5) Q26. prreg HS1 (27%bv : bv 5) Q27. prreg HS1 (20%bv : bv 5) Q20.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q23. apply EE. reflexivity.
  - rewrite Q24, E36, R24. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q22. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity. }
pmkst HS1.
apply (TAIL v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos mcc cur line p rest CX LS FRM CORE' CELLS' RA' Hn LOOP' MOD).
+ rewrite Q26, E38. reflexivity.
+ rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
+ rewrite Q20, (EE 20%nat 20%bv eq_refl). exact R20.
Qed.
End e.
End f.
End d.

(* the segment at every FP state (m_file_m.v's S_MF_KDONE shape) *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Lemma S_MF_KDONE_ok : S_MF_KDONE (rc := rc) (SK := SK) (PI := PI) B.
Proof. intros n TAIL fx0. exact (mf_kdone_at (fx := fx0) B VOBJS n (TAIL fx0)). Qed.
(* inside the Sections: the segment's hypotheses as its assumptions *)
About S_MF_KDONE_ok. Print Assumptions S_MF_KDONE_ok.
End i.
End h.
End g.
About S_MF_KDONE_ok. Print Assumptions S_MF_KDONE_ok.
