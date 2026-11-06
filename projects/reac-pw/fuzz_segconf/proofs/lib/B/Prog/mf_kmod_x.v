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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 185 of its 234 lines of code are new or changed and 404 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_KMOD, piece x (a walk lane of the image-B m_file-family owner's G2B, a piece agent): the two cuts of lib/B/Prog/mf_kmod_m.v that end at KDONE.
   proves no function (kind: segment lemma of m_file's image-B walk, S_MF_KMOD piece x: MK_LI 0x86c18 and
   MK_REFUSE 0x86c08 to KDONE).
     mk_li_ok     : forall n, MF_KDONE_stmt B n -> MK_LI_stmt B n.
     mk_refuse_ok : forall n, MF_KDONE_F B n -> MK_REFUSE_stmt B n.
   Adapted from image A's lib/A/Prog/m_file_s_kmod_r.v mk_refuse_ok and m_file_s_krole_h.v kr_snpret_kdone
   (commit c1e1a58468c5 and image A's KROLE hit piece) and from image B's lib/B/Prog/mf_krole_x.v kr_s_miss /
   kr_miss_ret (commit b0b1535e42b0), which walks the same four instructions
   (0x867a0 .. 0x867ac) before the same continuation.

   THE CODE (listing m_file.fuzz_segconf.asan-ubsan.s lines 692-696):
     0x86c08  ld s9,112(s1)     s9 = c (mf_cells' 112(s1); a frame cell, no instrumented check)
     0x86c0c  mv a0,s9
     0x86c10  mv a1,s11         a1 = line + 1 (s11, mk_base)
     0x86c14  jal m_refuse      m_refuse(c, line + 1) (lib/B/Prog/m_file_rf.v mf_refuse_step, knock = false)
     0x86c18  li s4,511         MK_LI -> KDONE 0x86c1c
   No UBSan trap branch and no instrumented check in this code (the load at 0x86c08 reads m_file's own frame cell
   through s1; the code has no shadow load and no branch to `unimp`).
   POSITIONAL NAMES checked against image B: MK_REFUSE = AF_m_file + 0xac8 (0x86c08), the jal AF_m_file + 0xad4
   (0x86c14, listing slot `PCall SS_m_refuse 1` by vm_compute), MK_LI = AF_m_file + 0xad8 (0x86c18), MF_KDONE =
   AF_m_file + 0xadc (0x86c1c), the cell 112(s1) = c (mf_cells, the seed's chunk atom 33 = mv_c v), the registers
   x25 = s9, x27 = s11, x20 = s4 and mf_regs_at's eleven (m_file_m.v): 8 checked, 0 pointing elsewhere.
   THE PROOF. mk_li_ok: lib/B/Prog/m_file_sd.v's mf_seed at MK_LI (frame cells read-only), one token run of one
   instruction to KDONE writing no byte (m_file_k.v mf_keep_run0), s4 = 511, and MF_KDONE_stmt at the same state.
   mk_refuse_ok: the seed at MK_REFUSE, one token run of three instructions to the jal writing no byte, the shared
   m_refuse step with knock = false (its footprint premise from the cut's model equation by mf_kmod_t.v
   mkt_mf_fin_kept_mono); at the FP state fx1 the call returns the walk is at 0x86c18 = MK_LI, so mk_li_ok at fx1
   with (KD fx1) closes it: the model m_refuse mcc (line + 1) false, cur = Some gi, line + 1, the text after the
   line at mf_next p rest (m_file_k.v mf_loop_next; counters mf_kmod_t.v mkt_m_refuse_counters), s11 = line + 1
   and mf_regs_at kept (callee-saved; m_file_rf.v mf_regs_at_kept). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaFx SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_mdl.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_k m_file_rf mf_kmod_t mf_kmod_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the `jal m_refuse` of the block, 0x86c14 (listing offset AF_m_file + 0xad4); the walk goes on at + 4 = MK_LI *)
Definition MK_RF_JAL : Z := AF_m_file + 0xad4.

(* every region of the state is read-only: a run from it writes nothing *)
Ltac mkx_awr_ro :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the state's form, computed *)
Ltac mkx_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
(* the seed's frame cells (region 1) made read-only *)
Ltac mkx_ro_slots E HS0 HS1 :=
  let HR1 := fresh "HR1" in
  pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1;
  lazymatch type of HR1 with region_ok _ _ _ ?r =>
    pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
      (region_ok_rewindow _ E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end;
  clear HS0 HR1; mkx_norm HS1.
(* after a run of a read-only state: every byte keeps its view *)
Ltac mkx_keep0 sg H K0 :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
    assert (K0 : forall a, 0 <= a < 2 ^ 64 -> aview sg H (ms_mem msc) a = aview sg H m0 a);
    [ intros a Ha; refine (kept_of_frame Ex rs H m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw | ] end.

(* ============================ MK_LI 0x86c18: `li s4,511`, KDONE, at any FP state ============================ *)
Section d1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f1.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e1.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

Lemma mk_li_ok : forall n, MF_KDONE_stmt B n -> MK_LI_stmt B n.
Proof.
intros n KD. unfold MK_LI_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS RA Hn LOOP FIN NP R27.
pose proof CORE as (HJ & _).
pose proof LOOP as (_ & _ & _ & _ & _ & Hcur & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc cur CX CORE Hcur) as Hcurr.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
(* the seed at MK_LI *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc cur 0 [] MK_LI true false []
  false false [] false CX CORE RB (fun _ => CELLS) Hcurr
  ltac:(intros Hf; discriminate Hf) ltac:(lia) ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur 0 []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur 0 []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32.
cbn [Nat.add nth mf_extra map app] in E32.
mkx_ro_slots E HS0 HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
(* 0x86c18 li s4,511; stop at KDONE 0x86c1c *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_KDONE.
{ mkx_awr_ro. }
mkx_keep0 (@pa_segs _ seg_listing PI) (w_H Wc) K0.
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc cur (ms_mem ms) mdw CX CORE CELLS HJ K0)
  as (CORE' & CELLS' & NPf & LOOPf).
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
prreg HS (27%bv : bv 5) Q27. prreg HS (20%bv : bv 5) Q20.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q23. apply EE. reflexivity.
  - rewrite Q24. apply EE. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q22. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity. }
pmkst HS.
apply (KD v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos mcc cur line p rest CX LS FRM CORE' CELLS' RA' Hn
  (LOOPf _ _ _ _ _ LOOP) FIN (NPf _ NP)).
- rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
- rewrite Q20. reflexivity.
Qed.
End e1.
End f1.
End d1.

(* ====================== MK_REFUSE 0x86c08 .. the call m_refuse(c, line + 1) .. MK_LI ====================== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse) SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

Lemma mk_refuse_ok : forall n, MF_KDONE_F B n -> MK_REFUSE_stmt B n.
Proof.
intros n KD. unfold MK_REFUSE_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest BS MDL.
destruct BS as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hne & LOOP & NP & R27).
set (mc' := m_refuse mcc (line + 1) false) in *.
(* the model: the next lines from the refused line's model *)
assert (FIN' : fst (m_lines (mc', Some gi) (line + 1) (lines (mf_rest rest))) = mf_final v) by exact MDL.
assert (HKEPT : (length (mc_kept mc') <= length (mc_kept (mf_final v)))%nat).
{ rewrite <- MDL. exact (mkt_mf_fin_kept_mono (mc', Some gi) line rest). }
pose proof LOOP as (_ & _ & _ & _ & _ & Hcur & Hk0 & _).
pose proof CORE as (HJ & _).
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE Hcur) as Hcurr.
(* the seed at MK_REFUSE *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) 0 [] MK_REFUSE true false
  [] false false [] false CX CORE RB (fun _ => CELLS) Hcurr
  ltac:(intros Hf; discriminate Hf) ltac:(lia) ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos (Some gi) 0 []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) 0 []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33.
cbn [Nat.add nth mf_extra map app] in E32, E33.
mkx_ro_slots E HS0 HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
(* 0x86c08 .. 0x86c10: s9 = 112(s1) = c, a0 = s9, a1 = s11 = line + 1; up to the jal *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan MK_RF_JAL.
{ mkx_awr_ro. }
mkx_keep0 (@pa_segs _ seg_listing PI) (w_H Wc) K0.
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdw CX CORE CELLS HJ K0)
  as (CORE1 & CELLS1 & NPf & LOOPf).
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
prreg HS (27%bv : bv 5) Q27. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
(* the registers at the jal: mf_regs_at (s9 reloaded with c), s11 = line + 1 *)
assert (RA1 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q23. apply EE. reflexivity.
  - rewrite Q24. apply EE. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q22. apply EE. reflexivity.
  - rewrite Q25, E33, R25. reflexivity. }
assert (G27 : getr (ms_regs ms) 27 = w64 (line + 1)) by (rewrite Q27, (EE 27%nat 27%bv eq_refl); exact R27).
pmkst HS.
(* the call m_refuse(c, line + 1) *)
apply (mf_refuse_step B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos MF_LOW_ON mcc mcc false
  (Some gi) line p rest (mf_next p rest) MK_RF_JAL CX LS FRM
  (mf_corek_of_core B v lyc Sc Wc (ms_mem ms) mdw pos MF_LOW_ON mcc CORE1) CELLS1 (NPf _ NP)).
- rewrite Q2, (EE 2%nat 2%bv eq_refl). exact R2.
- rewrite Q3, (EE 3%nat 3%bv eq_refl). exact R3.
- rewrite Q4, (EE 4%nat 4%bv eq_refl). exact R4.
- rewrite Q8, (EE 8%nat 8%bv eq_refl). exact R8.
- exact (LOOPf _ _ _ _ _ LOOP).
- exact Hne.
- reflexivity.
- exact Hk0.
- vm_compute. reflexivity.
- unfold MK_RF_JAL. vm_compute. reflexivity.
- rewrite Q10, E33. reflexivity.
- rewrite Q11, (EE 27%nat 27%bv eq_refl). exact R27.
- exact HKEPT.
- (* after the call, at the FP state fx1 it returns: the walk is at 0x86c18 = MK_LI *)
  intros fx1 ly2 S2 W2 regs2 mem2 md2 FXR LS2 CORE2 CELLS2 NP2 LOOP2 KS.
  assert (Ely : ly2 = lyc) by (destruct LS as (El1 & _); destruct LS2 as (El2 & _); congruence). subst ly2.
  assert (K27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (KS 27 ltac:(unfold acallee_saved; lia)).
  pose proof (mf_regs_at_kept B v lyc pos (ms_regs ms) regs2 RA1 KS) as RA2.
  assert (FRM1 : sa_frm0 (fx := fx1)).
  { destruct FXR as (_ & [Ecsr | Ef]); unfold sa_frm0 in *; [rewrite Ecsr; exact FRM | exact Ef]. }
  (* the next line's loop facts: m_refuse moves refused by one, keeps overflow, keeps or grows kept *)
  pose proof (mkt_m_refuse_counters mcc (line + 1) false) as (Cr1 & Cr2 & Cr3 & _). fold mc' in Cr1, Cr2, Cr3.
  assert (LOOPn : mf_loop v W2 mem2 mc' (Some gi) (line + 1) (mf_next p rest) (mf_rest rest)).
  { apply (mf_loop_next v W2 mem2 mcc (Some gi) line p rest mc' (Some gi) LOOP2 Hne);
      [rewrite Cr1; lia | rewrite Cr2; lia | exact Cr3 | exact (mf_cur_ok_refuse mcc (Some gi) (line + 1) false Hcur)]. }
  assert (Hlt : (length (mf_rest rest) < n)%nat).
  { destruct (mf_break_snd rest) as (_ & Hl & _). specialize (Hl Hne). unfold mf_rest. lia. }
  replace (MK_RF_JAL + 4) with MK_LI by (unfold MK_RF_JAL, MK_LI; lia).
  exact (mk_li_ok (fx := fx1) B VOBJS n (KD fx1) v lyc S2 W2 regs2 mem2 md2 pos mc' (Some gi) (line + 1)
    (mf_next p rest) (mf_rest rest) CX LS2 FRM1 CORE2 CELLS2 RA2 Hlt LOOPn FIN' NP2
    ltac:(rewrite K27; exact G27)).
Qed.
End e.
End f.
End d.

About mk_li_ok. Print Assumptions mk_li_ok.
About mk_refuse_ok. Print Assumptions mk_refuse_ok.
