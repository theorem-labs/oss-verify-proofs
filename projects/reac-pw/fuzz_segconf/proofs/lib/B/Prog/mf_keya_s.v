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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 255 of its 308 lines of code are new or changed and 400 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140), segment S_MF_KEYA
   (KEY 0x8661c -> KDISP 0x86714 or TAIL), the two strip calls. A walk lane of the image-B m_file-family owner's G2B (a piece agent,
   on a working branch).
   proves no function (kind: segment lemma of m_file's image-B walk, two pieces of S_MF_KEYA).

   kb_s1 : KB_S2_stmt B n -> KB_S1_stmt B n and kb_s2 : KB_Q_stmt B n -> KB_S2_stmt B n (the point statements of
   lib/B/Prog/mf_keya_d.v).
   THE CODE (the neutral listing of m_file in image B lines 328-331):
     0x86658 KB_S1  jal 879cc <strip>     strip(&k, &ke): a0 = s1 + 208, a1 = s1 + 200
     0x8665c KB_R1  addi a0,s1,192
     0x86660        addi a1,s1,184
     0x86664 KB_S2  jal 879cc <strip>     strip(&v, &ve): a0 = s1 + 192, a1 = s1 + 184
     0x86668 KB_Q   the second call's return
   No store, no instrumented check and no UBSan trap branch lies in 0x86658 .. 0x86664 (strip's own checks are
   inside strip_contract).
   THE WALK: each `jal` by m_file_rf.v's mf_jal_step (the listing slot PCall SS_strip 1 at AF_m_file + 0x518 /
   + 0x524); its target pa_sigma SS_strip is BASE + AF_strip by SIGP (lib/B/Prog/SegObj.v seg_sig_prog: the PAImg
   class links no call target to the text base); the call itself by m_file_strip.v's mf_strip_call (strip_contract
   through cl_callS_wide, every cut fact kept by mf_keep_callx). The first call is over the bytes [i, i + ei) of the
   text left (the key, before the first '=' of the line's slice [i, j)), the second over [i + ei + 1, j) (the
   value). strip's post names slice a b rest; the statements name the line L = mf_line rest, and slice a b rest =
   slice a b L for b <= |L| (ks_slice_line, from mf_keya_m.v's kb_line_firstn), so mf_keya_m.v's kb_key_strip /
   kb_val_strip give kb_key_at / kb_val_at at the stripped ends. The cells strip does not name keep their values
   (strip's kept set: every byte outside its window [s1 - 16, s1) and its two cells). The two `addi` by single
   machine steps (ks_addi_step: the listing slot PW w, the word decoded to OpImm ALU_ADD, YK14.step_addi_at); they
   write no byte, so every memory fact is the strip return's, and the journal is carried across the model's
   materialization (YCbq.ajournal_materialize, ks_core_mat).
   POSITIONAL NAMES (checked against the listing by what each is): the cells 208(s1) / 200(s1) are k / ke (stored
   0x86634 / 0x86638, strip's arguments at 0x86650 / 0x86654) and 192(s1) / 184(s1) are v / ve (stored 0x86648 /
   0x8664c, strip's arguments at 0x8665c / 0x86660), as the image-B m_file cut map's cell list C.1; a0 = x10, a1 = x11, s1 = x9,
   s11 = x27; the slots AF_m_file + 0x518 (0x86658, PCall SS_strip 1), + 0x51c (0x8665c, PW 0xc048513), + 0x520
   (0x86660, PW 0xb848593), + 0x524 (0x86664, PCall SS_strip 1), + 0x528 (0x86668); strip's entry BASE + AF_strip =
   0x879cc. 13 names checked, 0 pointing elsewhere.
   Section hypotheses: SIGP (the jal's target, the owner's 2026-10-30 decision, the image-B m_file segment table) and STRIP
   (strip_contract at BASE + AF_strip and SegInstB.STK_strip, at every FP state). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegObj SegPgBase SegBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k strip_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_iq m_file_rf m_file_strip.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_keya_m mf_keya_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================================== the line ===================================== *)
(* a slice inside the line is the same slice of the text left (the line is a prefix of it) *)
Lemma ks_slice_line : forall rest a b, (a <= b <= length (mf_line rest))%nat ->
  slice a b rest = slice a b (mf_line rest).
Proof.
intros rest a b H. transitivity (firstn (b - a) (skipn a rest)); [reflexivity|].
rewrite kb_line_firstn by lia. f_equal. lia.
Qed.

(* ===================================== registers ===================================== *)
(* a register inequality, by computation *)
Ltac ks_nz := let E := fresh "E" in intros E; vm_compute in E; discriminate E.

Lemma ks_getr_upd_z : forall (regs : bvmap 5 word) rdz (r : bv 5) x, 0 <= rdz < 32 -> bv_unsigned r <> rdz ->
  getr (regupd regs (Z_to_bv 5 rdz) x) r = getr regs r.
Proof.
intros regs rdz r x H1 H2. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. apply regupd_other.
intros E. apply H2. rewrite E. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.
Lemma ks_getr_upd_same_z : forall (regs : bvmap 5 word) rdz x, 0 < rdz < 32 ->
  getr (regupd regs (Z_to_bv 5 rdz) x) (Z_to_bv 5 rdz) = x.
Proof.
intros regs rdz x H.
assert (Hu : bv_unsigned (Z_to_bv 5 rdz) = rdz).
{ rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia. }
unfold getr. destruct (bv_eqb (Z_to_bv 5 rdz) 0) eqn:E; [|apply regupd_same].
exfalso. apply reg_eqb_eq in E. apply (f_equal bv_unsigned) in E. rewrite Hu in E. vm_compute in E. lia.
Qed.
(* addi of a register holding a 64-bit value, when it does not wrap *)
Lemma ks_addi_w64 : forall (x : word) z k, x = w64 z -> 0 <= z -> 0 <= k -> z + k < 2 ^ 64 -> v_addi x k = w64 (z + k).
Proof. intros x z k -> H0 Hk H. unfold v_addi, w64. rewrite unsigned_lit_small by lia. reflexivity. Qed.

(* the registers after 0x8665c addi a0,s1,k0 and 0x86660 addi a1,s1,k1 (the executor's form, ks_addi_step) *)
Local Notation ks_r3 regs k0 := (regupd regs (Z_to_bv 5 10) (v_addi (getr regs (Z_to_bv 5 9)) k0)) (only parsing).
Local Notation ks_r4 regs k0 k1 :=
  (regupd (ks_r3 regs k0) (Z_to_bv 5 11) (v_addi (getr (ks_r3 regs k0) (Z_to_bv 5 9)) k1)) (only parsing).
Lemma ks_a0a1 : forall (regs : bvmap 5 word) s k0 k1,
  getr regs (Z_to_bv 5 9) = w64 s -> 0 <= s -> 0 <= k0 -> 0 <= k1 -> s + k0 < 2 ^ 64 -> s + k1 < 2 ^ 64 ->
  getr (ks_r4 regs k0 k1) (Z_to_bv 5 10) = w64 (s + k0) /\
  getr (ks_r4 regs k0 k1) (Z_to_bv 5 11) = w64 (s + k1) /\
  (forall r, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> getr (ks_r4 regs k0 k1) r = getr regs r).
Proof.
intros regs s k0 k1 R9 H0 Hk0 Hk1 H1 H2.
assert (G9 : getr (ks_r3 regs k0) (Z_to_bv 5 9) = getr regs (Z_to_bv 5 9))
  by (apply ks_getr_upd_z; [lia | ks_nz]).
split; [|split].
- rewrite (ks_getr_upd_z _ 11 (Z_to_bv 5 10)) by first [lia | ks_nz].
  rewrite ks_getr_upd_same_z by lia. exact (ks_addi_w64 _ s k0 R9 H0 Hk0 H1).
- rewrite ks_getr_upd_same_z by lia. rewrite G9. exact (ks_addi_w64 _ s k1 R9 H0 Hk1 H2).
- intros r Hr10 Hr11. rewrite (ks_getr_upd_z _ 11 r) by lia. rewrite (ks_getr_upd_z _ 10 r) by lia. reflexivity.
Qed.
(* s11 across a call that keeps the callee-saved registers, from the `jal` (ra set) *)
Lemma ks_r27 : forall (regs1 regs2 : bvmap 5 word) x z,
  aregs_preserved (regupd regs1 1%bv x) regs2 -> getr regs1 27 = z -> getr regs2 27 = z.
Proof.
intros regs1 regs2 x z HP H. rewrite <- H.
transitivity (getr (regupd regs1 1%bv x) 27).
- exact (HP 27 ltac:(unfold acallee_saved; lia)).
- apply mf_getr_upd1. discriminate.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* `addi rd,rs,k` at listing offset j (the slot PW w, w decoding to OpImm ALU_ADD): one machine step to j', rd =
   rs + k, the memory unchanged (m_file_rf.v's mf_jal_step for a plain word, YK14.step_addi_at) *)
Lemma ks_addi_step : forall (W : world SEGS) (regs : bvmap 5 word) mem md Q j j' w (rd rs : bv 5) (imm : bv 12)
  rdz rsz k,
  plookup pl_tpi j = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4) ->
  bv_unsigned rd = rdz -> bv_unsigned rs = rsz -> bv_signed imm = k -> 0 < rdz < 32 -> 0 <= rsz < 32 ->
  j' = j + 4 -> j' < 2 ^ 40 ->
  (forall mat', SRr SEGS W (mkCfg (mkst (regupd regs (Z_to_bv 5 rdz) (v_addi (getr regs (Z_to_bv 5 rsz)) k))
    (Z_to_bv 64 (BASE + j')) mem (seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + j)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q j j' w rd rs imm rdz rsz k Hpl Hdec Hrd Hrs Himm Hrd32 Hrs32 Hj' Hj40 HK.
pose proof pa_B_ok as (HB0 & HB1 & HB4).
pose proof (pa_val_range A_TEXT) as HBr.
destruct (pa_lookup_pw j w Hpl) as (Hl & Hj0 & _).
assert (Hnz : bv_eqb rd 0 = false).
{ destruct (bv_eqb rd 0) eqn:E; [|reflexivity]. exfalso. apply reg_eqb_eq in E. subst rd. vm_compute in Hrd. lia. }
assert (Erd : rd = Z_to_bv 5 rdz).
{ apply bv_eq. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia). exact Hrd. }
assert (Ers : rs = Z_to_bv 5 rsz).
{ apply bv_eq. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia). exact Hrs. }
subst rd rs.
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  eapply (step_addi_at SEGS _ _ _ _ (Z_to_bv 32 w) (Z_to_bv 5 rdz) (Z_to_bv 5 rsz) imm).
  + exact (pa_fetch_ok _ _ Hl).
  + eapply not_ecall_of_decode; [exact Hdec | discriminate].
  + exact Hdec.
  + exact Hnz.
  + reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_regs ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
  assert (Ev : v_addi (Z_to_bv 64 (BASE + j)) 4 = Z_to_bv 64 (BASE + j')).
  { unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia. }
  rewrite Ev, Himm. exact (HK _).
Qed.

(* the step at a concrete slot: the decoded fields taken from the word by computation *)
Ltac ks_addi j j' w rdz rsz k :=
  let d := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
  lazymatch d with
  | Some (OpImm ALU_ADD ?rd ?rs ?imm, _) =>
      apply (ks_addi_step _ _ _ _ _ j j' w rd rs imm rdz rsz k);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity | ]
  end.

(* a scratch cell whose 8 bytes the reader keeps *)
Lemma ks_slot_keep : forall v (Wc W2 : world SEGS) memc mem2 off x,
  (forall y, mf_s1 (mv_sp v) + off <= y < mf_s1 (mv_sp v) + off + 8 -> rdW W2 mem2 y = rdW Wc memc y) ->
  mf_slot v memc Wc off x -> mf_slot v mem2 W2 off x.
Proof.
intros v Wc W2 memc mem2 off x K H. unfold mf_slot in *.
apply (iq_val_keep Wc W2 memc mem2 _ 8 x); [|exact H].
intros y Hy. apply K. change (Z.of_nat 8) with 8 in Hy. lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the jal's target (SegObj.v; the owner's decision, the image-B m_file segment table) *)
Hypothesis SIGP : seg_sig_prog.
(* the callee, at every FP state (the image-B m_file segment table's strip row) *)
Hypothesis STRIP : forall fx0 : YK11.FPState, @strip_contract fx0 rc SK SEGS B (BASE + AF_strip) SegInstB.STK_strip.

(* s1 and the frame cells lie well inside the address space *)
Lemma ks_s1_range : forall v, mf_cx B v -> 4096 <= mf_s1 (mv_sp v) /\ mf_s1 (mv_sp v) + 216 <= 2 ^ 47.
Proof.
intros v CX.
destruct (mf_s1_facts B v CX) as (Hs1 & _ & _).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CRlo & CRhi) & _). unfold YG0f.ASAN_CEIL in CRlo, CRhi.
destruct Hs1 as [E | E]; rewrite E; lia.
Qed.
(* mf_core at the model a machine step materializes *)
Lemma ks_core_mat : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc X,
  mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
  mf_core B v lyc Sc Wc memc (with_vm_backing (m_vm_lazy mdc) X mdc) pos lowsh mcc.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc X (HJ & R).
exact (conj (ajournal_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X HJ) R).
Qed.
(* the cut registers after the `jal` (only ra changed) *)
Lemma ks_regs_upd1 : forall v lyc pos (regs1 : bvmap 5 word) x,
  mf_regs_at B v lyc pos regs1 -> mf_regs_at B v lyc pos (regupd regs1 1%bv x).
Proof.
intros v lyc pos regs1 x RA.
apply (mf_regs_at_of B v lyc pos regs1 _ RA); apply mf_getr_upd1; discriminate.
Qed.
(* strip's entry *)
Lemma ks_sig_strip : pa_sigma SS_strip = BASE + AF_strip.
Proof.
rewrite (SIGP SS_strip) by (unfold seg_prog_syms; cbn [In]; tauto). f_equal; try (vm_compute; reflexivity).
Qed.

(* 0x86664 jal strip (&v, &ve): strip over the value [i + ei + 1, j); at its return KB_Q *)
Lemma kb_s2 : forall n, KB_Q_stmt B n -> KB_S2_stmt B n.
Proof.
intros n KQ. unfold KB_S2_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest i j ei a b CTX RG KEY S208 S200 S192 S184 R10 R11.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & Hn & Hr & LOOP & Hij & HjL & HMC & HFIN & NP).
pose proof RG as (RA & R27).
pose proof KEY as (Ka1 & Ka2 & Ka3 & _).
pose proof (kb_line_len rest) as HLr.
destruct (kb_memchr_some _ _ _ HMC) as (Hei & _ & _).
rewrite kb_slice_length in Hei by lia.
destruct (kb_val_strip (mf_line rest) i j ei ltac:(lia) Hei) as (Hlt & Hval).
destruct (ks_s1_range v CX) as (Hs1a & Hs1b).
replace (p + Z.of_nat (i + ei) + 1) with (p + Z.of_nat (i + S ei)) in S192 by lia.
(* 0x86664: jal strip *)
unfold mf_at.
apply (mf_jal_step Wc regs1 memc mdc _ KB_S2 SS_strip);
  [vm_compute; reflexivity | unfold KB_S2, AF_m_file; lia |].
intros mat'.
rewrite ks_sig_strip.
replace (KB_S2 + 4) with KB_Q by (unfold KB_S2, KB_Q; lia).
(* strip(s1 + 192, s1 + 184) over the bytes [i + ei + 1, j) of the text left *)
apply (mf_strip_call B STRIP v lyc Sc Wc (regupd regs1 1%bv (Z_to_bv 64 (BASE + KB_Q))) memc
  (with_vm_backing (m_vm_lazy mdc) mat' mdc) pos MF_LOW_OFF mcc (Some gi) line p rest (mf_next p rest)
  KB_Q 192 184 (i + S ei) j CX LS (ks_core_mat _ _ _ _ _ _ _ _ _ mat' CORE) CELLS LOOP NP
  (ks_regs_upd1 _ _ _ _ _ RA)).
- apply mf_getr_upd1_same.
- unfold KB_Q, AF_m_file; lia.
- vm_compute. reflexivity.
- lia.
- lia.
- vm_compute. reflexivity.
- lia.
- lia.
- vm_compute. reflexivity.
- lia.
- rewrite mf_getr_upd1 by discriminate. exact R10.
- rewrite mf_getr_upd1 by discriminate. exact R11.
- lia.
- exact S192.
- exact S184.
- intros S2 W2 regs2 mem2 md2 HWle LS2 CORE2 CELLS2 LOOP2 NP2 RA2 HPR V192 V184 K2.
  rewrite (ks_slice_line rest (i + S ei) j ltac:(lia)) in V192, V184.
  set (Y := slice (i + S ei) j (mf_line rest)) in *.
  replace (p + Z.of_nat (i + S ei) + Z.of_nat (strip_lead Y)) with (p + Z.of_nat (i + S ei + strip_lead Y))
    in V192 by lia.
  replace (p + Z.of_nat j - Z.of_nat (strip_trail Y)) with (p + Z.of_nat (j - strip_trail Y)) in V184 by lia.
  (* the key's cells 208 / 200, apart from strip's window and its two cells *)
  assert (V208 : mf_slot v mem2 W2 208 (p + Z.of_nat a)).
  { apply (ks_slot_keep v Wc W2 memc mem2 208); [intros y Hy; apply K2; lia | exact S208]. }
  assert (V200 : mf_slot v mem2 W2 200 (p + Z.of_nat b)).
  { apply (ks_slot_keep v Wc W2 memc mem2 200); [intros y Hy; apply K2; lia | exact S200]. }
  apply (KQ v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest i j ei a b (i + S ei + strip_lead Y)%nat
    (j - strip_trail Y)%nat).
  + exact (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj Hn (conj Hr (conj LOOP2 (conj Hij
      (conj HjL (conj HMC (conj HFIN NP2)))))))))))).
  + exact (conj RA2 (ks_r27 regs1 regs2 _ _ HPR R27)).
  + exact KEY.
  + split; [lia|]. split; [lia|]. split; [lia|]. exact Hval.
  + exact V208.
  + exact V200.
  + exact V192.
  + exact V184.
Qed.

(* 0x86658 jal strip (&k, &ke): strip over the key [i, i + ei); 0x8665c / 0x86660 a0 = s1 + 192, a1 = s1 + 184;
   KB_S2 *)
Lemma kb_s1 : forall n, KB_S2_stmt B n -> KB_S1_stmt B n.
Proof.
intros n KS2. unfold KB_S1_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest i j ei CTX RG S208 S200 S192 S184 R10 R11.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & Hn & Hr & LOOP & Hij & HjL & HMC & HFIN & NP).
pose proof RG as (RA & R27).
pose proof (kb_line_len rest) as HLr.
destruct (kb_memchr_some _ _ _ HMC) as (Hei & _ & _).
rewrite kb_slice_length in Hei by lia.
destruct (kb_key_strip (mf_line rest) i j ei ltac:(lia) Hei) as (Hlt & Hkey).
destruct (ks_s1_range v CX) as (Hs1a & Hs1b).
(* 0x86658: jal strip *)
unfold mf_at.
apply (mf_jal_step Wc regs1 memc mdc _ KB_S1 SS_strip);
  [vm_compute; reflexivity | unfold KB_S1, AF_m_file; lia |].
intros mat'.
rewrite ks_sig_strip.
replace (KB_S1 + 4) with KB_R1 by (unfold KB_S1, KB_R1; lia).
(* strip(s1 + 208, s1 + 200) over the bytes [i, i + ei) of the text left *)
apply (mf_strip_call B STRIP v lyc Sc Wc (regupd regs1 1%bv (Z_to_bv 64 (BASE + KB_R1))) memc
  (with_vm_backing (m_vm_lazy mdc) mat' mdc) pos MF_LOW_OFF mcc (Some gi) line p rest (mf_next p rest)
  KB_R1 208 200 i (i + ei) CX LS (ks_core_mat _ _ _ _ _ _ _ _ _ mat' CORE) CELLS LOOP NP
  (ks_regs_upd1 _ _ _ _ _ RA)).
- apply mf_getr_upd1_same.
- unfold KB_R1, AF_m_file; lia.
- vm_compute. reflexivity.
- lia.
- lia.
- vm_compute. reflexivity.
- lia.
- lia.
- vm_compute. reflexivity.
- lia.
- rewrite mf_getr_upd1 by discriminate. exact R10.
- rewrite mf_getr_upd1 by discriminate. exact R11.
- lia.
- exact S208.
- exact S200.
- intros S2 W2 regs2 mem2 md2 HWle LS2 CORE2 CELLS2 LOOP2 NP2 RA2 HPR V208 V200 K2.
  rewrite (ks_slice_line rest i (i + ei) ltac:(lia)) in V208, V200.
  set (X := slice i (i + ei) (mf_line rest)) in *.
  replace (p + Z.of_nat i + Z.of_nat (strip_lead X)) with (p + Z.of_nat (i + strip_lead X)) in V208 by lia.
  replace (p + Z.of_nat (i + ei) - Z.of_nat (strip_trail X)) with (p + Z.of_nat (i + ei - strip_trail X))
    in V200 by lia.
  pose proof RA2 as ((_ & _ & _ & _ & R9 & _) & _).
  (* the value's cells 192 / 184, apart from strip's window and its two cells *)
  assert (V192 : mf_slot v mem2 W2 192 (p + Z.of_nat (i + ei) + 1)).
  { apply (ks_slot_keep v Wc W2 memc mem2 192); [intros y Hy; apply K2; lia | exact S192]. }
  assert (V184 : mf_slot v mem2 W2 184 (p + Z.of_nat j)).
  { apply (ks_slot_keep v Wc W2 memc mem2 184); [intros y Hy; apply K2; lia | exact S184]. }
  pose proof (ks_r27 regs1 regs2 _ _ HPR R27) as R27'.
  (* 0x8665c addi a0,s1,192; 0x86660 addi a1,s1,184 *)
  ks_addi KB_R1 (KB_R1 + 4) 0xc048513 10 9 192. intros mat2.
  ks_addi (KB_R1 + 4) KB_S2 0xb848593 11 9 184. intros mat3.
  destruct (ks_a0a1 regs2 (mf_s1 (mv_sp v)) 192 184 ltac:(exact R9) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia)) as (A10 & A11 & AO).
  pose proof (ks_core_mat _ _ _ _ _ _ _ _ _ mat3 (ks_core_mat _ _ _ _ _ _ _ _ _ mat2 CORE2)) as CORE4.
  apply (KS2 v lyc S2 W2 _ mem2 _ pos mcc gi line p rest i j ei (i + strip_lead X)%nat
    (i + ei - strip_trail X)%nat).
  + exact (conj CX (conj LS2 (conj FRM (conj CORE4 (conj CELLS2 (conj Hn (conj Hr (conj LOOP2 (conj Hij
      (conj HjL (conj HMC (conj HFIN NP2)))))))))))).
  + split.
    * apply (mf_regs_at_of B v lyc pos regs2 _ RA2); apply AO; ks_nz.
    * transitivity (getr regs2 27); [apply AO; ks_nz | exact R27'].
  + split; [lia|]. split; [lia|]. split; [lia|]. exact Hkey.
  + exact V208.
  + exact V200.
  + exact V192.
  + exact V184.
  + exact A10.
  + exact A11.
Qed.
End e.
End f.
End d.
About kb_s1.
Print Assumptions kb_s1.
About kb_s2.
Print Assumptions kb_s2.
