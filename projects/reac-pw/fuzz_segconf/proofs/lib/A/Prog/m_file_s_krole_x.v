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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 216 of its 257 lines of code are new or changed and 412 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), segment S_MF_KROLE, the piece kr_s_miss (lib/A/Prog/
   m_file_s_krole_m.v KR_MISS_stmt): no word of m_key.words matched the folded value, from the inner point KR_MISS
   0x86798 to the cut KDONE 0x86cd0. The KROLE segment lane of the G2 walk owner's G2, piece agent the KROLE miss sub-lane.

   THE CODE (listing m_file.fuzz_segconf.asan.s):
     0x86798  ld s5,128(s1)     s5 = c (mf_cells' 128(s1))
     0x8679c  mv a0,s5
     0x867a0  ld s6,96(s1)      s6 = line + 1 (kr_line_at)
     0x867a4  mv a1,s6
     0x867a8  jal m_refuse      m_refuse(c, line + 1) (lib/A/Prog/m_file_rf.v mf_refuse_step, knock = false)
     0x867ac  ld s8,104(s1)     s8 = FAKE = FB (mf_cells' 104(s1))
     0x867b0  ld s10,120(s1)    s10 = shadow(FB) (mf_cells' 120(s1))
     0x867b4  j 0x86cd0         KDONE
   THE MODEL: with ieq k "role" = true and h_role_word (h_fold v 64) = None, mk_disp is m_refuse c (line + 1) false
   (kr_mk_disp_role), so the cut's equation mf_fin (mk_disp ..) is KDONE's at the next line: the block holds
   m_refuse mcc (line + 1) false, cur = Some gi, the lines consumed line + 1, the text left mf_rest rest at
   mf_next p rest (mf_loop_next, m_file_k.v). The footprint premise of the step is m_file_mdl.v's mf_kept_le_refuse.
   THE RUNS: two runs of the token executor from lib/A/Prog/m_file_sd.v's mf_seed (the spill slots made read-only;
   96(s1) = line + 1 as the caller's chunk at atom 52), each writing no byte: the cut facts at the new memory come
   from m_file_k.v's mf_keep_run0. The call is m_file_rf.v's mf_refuse_step (Section hypotheses SIGP, SSP, RELRO,
   M_REFUSE, as the shared list states them); the walk after it goes on at the FP state fx1 the call returns
   (kr_miss_ret, at every FP state), and the step lifts the post. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaFx SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_mdl.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_k m_file_rf m_file_s_krole_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the `jal m_refuse` of the miss, 0x867a8 (listing offset AF_m_file + 0x8ec); the walk goes on at + 4, 0x867ac *)
Definition KR_MISS_JAL : Z := AF_m_file + 0x8ec.

(* every region of the state is read-only: a run from it writes nothing *)
Ltac kx_awr_ro :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the state's form, computed *)
Ltac kx_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
(* the seed's spill slots (region 1) made read-only *)
Ltac kx_ro_slots E HS0 HS1 :=
  let HR1 := fresh "HR1" in
  pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1;
  lazymatch type of HR1 with region_ok _ _ _ ?r =>
    pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
      (region_ok_rewindow _ E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end;
  clear HS0 HR1; kx_norm HS1.
(* after a run of a read-only state: every byte keeps its view *)
Ltac kx_keep0 sg H K0 :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
    assert (K0 : forall a, 0 <= a < 2 ^ 64 -> aview sg H (ms_mem msc) a = aview sg H m0 a);
    [ intros a Ha; refine (kept_of_frame Ex rs H m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw | ] end.

(* ============================ after the call: 0x867ac .. KDONE, at any FP state ============================ *)
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

(* the text after the line is shorter than the text left *)
Lemma kx_rest_lt : forall rest, rest <> [] -> (length (mf_rest rest) < length rest)%nat.
Proof.
intros [|b r] H; [contradiction|]. unfold mf_rest. pose proof (break_nl_len_cons b r) as L. cbn [length]. lia.
Qed.

(* 0x867ac at the FP state the call returned: s8 = 104(s1), s10 = 120(s1), `j` KDONE with the refused line done *)
Lemma kr_miss_ret : forall n, MF_KDONE_stmt B n ->
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON (m_refuse mcc (line + 1) false) ->
mf_cells v lyc pos memc Wc (Some gi) -> mf_np v memc Wc (mf_next p rest) ->
mf_loop v Wc memc mcc (Some gi) line p rest -> (length rest <= n)%nat -> rest <> [] ->
fst (m_lines (m_refuse mcc (line + 1) false, Some gi) (line + 1) (lines (mf_rest rest))) = mf_final v ->
kr_regs_b B v regs1 -> getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc (KR_MISS_JAL + 4).
Proof.
intros n KD v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS NP LOOP Hn Hne FIN RB R21 R22.
set (mc' := m_refuse mcc (line + 1) false) in *.
pose proof CORE as (HJ & _).
pose proof RB as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25).
assert (RBs : mf_regs_base v regs1) by (repeat split; assumption).
pose proof LOOP as (_ & _ & _ & _ & _ & Hcur & _).
assert (Hcur' : mf_cur_ok mc' (Some gi)) by exact (mf_cur_ok_refuse mcc (Some gi) (line + 1) false Hcur).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mc' (Some gi) CX CORE Hcur') as Hcurr.
(* the seed at 0x867ac *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mc' (Some gi) 0 [] (KR_MISS_JAL + 4) true false []
  false false [] false CX CORE RBs (fun _ => CELLS) Hcurr ltac:(intros Hf; discriminate Hf) ltac:(lia)
  ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos (Some gi) 0 []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) 0 []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34.
pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E34, E36.
kx_ro_slots E HS0 HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
(* 0x867ac .. 0x867b4: the two loads, `j` KDONE *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_KDONE.
{ kx_awr_ro. }
kx_keep0 (@pa_segs _ seg_listing PI) (w_H Wc) K0.
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mc' (Some gi) (ms_mem ms) mdw CX CORE CELLS HJ K0)
  as (CORE' & CELLS' & NPf & LOOPf).
(* the next line's loop facts: m_refuse moves refused by one, keeps overflow, adds at most one kept line *)
assert (LOOPn : mf_loop v Wc (ms_mem ms) mc' (Some gi) (line + 1) (mf_next p rest) (mf_rest rest)).
{ destruct (m_refuse_sizes mcc (line + 1) false) as [_ HK].
  apply (mf_loop_next v Wc (ms_mem ms) mcc (Some gi) line p rest mc' (Some gi) (LOOPf _ _ _ _ _ LOOP) Hne);
    [unfold mc', m_refuse; cbv zeta; cbn [mc_refused]; lia
    | unfold mc', m_refuse; cbv zeta; cbn [mc_overflow]; lia
    | unfold mc'; lia | exact Hcur']. }
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (24%bv : bv 5) Q24. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - rewrite Q2, (EE 2%nat 2%bv eq_refl). exact R2.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl). exact R3.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl). exact R4.
  - rewrite Q8, (EE 8%nat 8%bv eq_refl). exact R8.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl). exact R2.
  - rewrite Q18, E32. reflexivity.
  - rewrite Q19, (EE 19%nat 19%bv eq_refl). exact R19.
  - rewrite Q25, (EE 25%nat 25%bv eq_refl). exact R25.
  - rewrite Q26, E36. reflexivity. }
pmkst HS.
apply (KD v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos mc' (Some gi) (line + 1) (mf_next p rest) (mf_rest rest)
  CX LS FRM CORE' CELLS' RA').
- rewrite Q24, E34. reflexivity.
- pose proof (kx_rest_lt rest Hne). lia.
- exact LOOPn.
- exact FIN.
- exact (NPf _ NP).
- rewrite Q21, (EE 21%nat 21%bv eq_refl). exact R21.
- rewrite Q22, (EE 22%nat 22%bv eq_refl). exact R22.
Qed.
End e1.
End f1.
End d1.

(* ============================ the piece: KR_MISS 0x86798 .. the call .. KDONE ============================ *)
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
Let RUNTO := paj_run_to B LAWS.
(* the shared hypotheses (KROLE-PIECES.md section 2) the m_refuse step needs, verbatim *)
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse) SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.

Lemma kr_s_miss : forall n, MF_KDONE_F B n -> KR_MISS_stmt B n.
Proof.
intros n KD. unfold KR_MISS_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv KX RB LINE NONE.
destruct KX as (CX & LS & FRM & CORE & CELLS & Hn & Hne & LOOP & _ & FIN & NP & IEQ).
(* the model: the role branch with no word refuses the line *)
assert (FIN' : fst (m_lines (m_refuse mcc (line + 1) false, Some gi) (line + 1) (lines (mf_rest rest))) = mf_final v).
{ rewrite <- FIN. unfold mf_fin. rewrite (kr_mk_disp_role mcc gi k vv (line + 1) IEQ), NONE. reflexivity. }
pose proof LOOP as (_ & _ & _ & _ & _ & Hcur & Hk0 & Hl0 & Hl1 & _).
pose proof (mf_kept_le_refuse mcc (line + 1) false (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
  (mf_cur_ok_refuse mcc (Some gi) (line + 1) false Hcur) FIN') as HKEPT.
pose proof CORE as (HJ & _).
pose proof RB as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25).
assert (RBs : mf_regs_base v regs1) by (repeat split; assumption).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE Hcur) as Hcurr.
(* 96(s1) = line + 1 as the caller's chunk, atom 52 *)
assert (SLX : Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos (Some gi) 0 [line + 1]) (mrestrict (w_H Wc) memc)
  (mf_s1 (mv_sp v))) [YP09.mkChunk 96 (CVal 8 (SOff 52 0))]).
{ constructor; [|constructor].
  apply (mf_chunk_atom _ _ _ 96 52 0 (line + 1)).
  - exact (mfE_xs regs1 v lyc pos (Some gi) 0 [line + 1] 0 ltac:(unfold A_TEXT; lia)).
  - lia.
  - lia.
  - rewrite Z.add_0_r. exact LINE. }
(* the seed at KR_MISS *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) 0 [line + 1] KR_MISS true false
  [YP09.mkChunk 96 (CVal 8 (SOff 52 0))] false false [] false CX CORE RBs (fun _ => CELLS) Hcurr
  ltac:(intros Hf; discriminate Hf) ltac:(lia) ltac:(unfold MF_LOW_ON; lia) SLX (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
clear SLX.
remember (mfE regs1 v lyc pos (Some gi) 0 [line + 1]) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) 0 [line + 1]) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (E52 : ew E 52 = Z_to_bv 64 (line + 1))
  by (subst E; exact (mfE_xs regs1 v lyc pos (Some gi) 0 [line + 1] 0 ltac:(unfold A_TEXT; lia))).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33.
cbn [Nat.add nth mf_extra map app] in E32, E33.
kx_ro_slots E HS0 HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
(* 0x86798 .. 0x867a4: a0 = s5 = c, a1 = s6 = line + 1; up to the jal *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan KR_MISS_JAL.
{ kx_awr_ro. }
kx_keep0 (@pa_segs _ seg_listing PI) (w_H Wc) K0.
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdw CX CORE CELLS HJ K0)
  as (CORE1 & CELLS1 & NPf & LOOPf).
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (25%bv : bv 5) Q25.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
pmkst HS.
(* the call m_refuse(c, line + 1) *)
apply (mf_refuse_step B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos MF_LOW_ON mcc mcc false (Some gi) line p rest (mf_next p rest)
  KR_MISS_JAL CX LS FRM (mf_corek_of_core B v lyc Sc Wc (ms_mem ms) mdw pos MF_LOW_ON mcc CORE1) CELLS1 (NPf _ NP)).
- rewrite Q2, (EE 2%nat 2%bv eq_refl). exact R2.
- rewrite Q3, (EE 3%nat 3%bv eq_refl). exact R3.
- rewrite Q4, (EE 4%nat 4%bv eq_refl). exact R4.
- rewrite Q8, (EE 8%nat 8%bv eq_refl). exact R8.
- exact (LOOPf _ _ _ _ _ LOOP).
- exact Hne.
- reflexivity.
- exact Hk0.
- vm_compute. reflexivity.
- unfold KR_MISS_JAL. vm_compute. reflexivity.
- rewrite Q10, E33. reflexivity.
- rewrite Q11, E52. reflexivity.
- exact HKEPT.
- (* after the call, at the FP state fx1 it returns *)
  intros fx1 ly2 S2 W2 regs2 mem2 md2 FXR LS2 CORE2 CELLS2 NP2 LOOP2 KS.
  assert (K : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r))
    by exact KS.
  assert (K2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (K 2 ltac:(unfold acallee_saved; lia)).
  assert (K3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (K 3 ltac:(unfold acallee_saved; lia)).
  assert (K4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (K 4 ltac:(unfold acallee_saved; lia)).
  assert (K8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (K 8 ltac:(unfold acallee_saved; lia)).
  assert (K9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (K 9 ltac:(unfold acallee_saved; lia)).
  assert (K18 : getr regs2 18 = getr (ms_regs ms) 18) by exact (K 18 ltac:(unfold acallee_saved; lia)).
  assert (K19 : getr regs2 19 = getr (ms_regs ms) 19) by exact (K 19 ltac:(unfold acallee_saved; lia)).
  assert (K21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (K 21 ltac:(unfold acallee_saved; lia)).
  assert (K22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (K 22 ltac:(unfold acallee_saved; lia)).
  assert (K25 : getr regs2 25 = getr (ms_regs ms) 25) by exact (K 25 ltac:(unfold acallee_saved; lia)).
  assert (FRM1 : sa_frm0 (fx := fx1)).
  { destruct FXR as (_ & [Ecsr | Ef]); unfold sa_frm0 in *; [rewrite Ecsr; exact FRM | exact Ef]. }
  assert (RB2 : kr_regs_b B v regs2).
  { refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    - rewrite K2, Q2, (EE 2%nat 2%bv eq_refl). exact R2.
    - rewrite K3, Q3, (EE 3%nat 3%bv eq_refl). exact R3.
    - rewrite K4, Q4, (EE 4%nat 4%bv eq_refl). exact R4.
    - rewrite K8, Q8, (EE 8%nat 8%bv eq_refl). exact R8.
    - rewrite K9, Q9, (EE 2%nat 2%bv eq_refl). exact R2.
    - rewrite K18, Q18, E32. reflexivity.
    - rewrite K19, Q19, (EE 19%nat 19%bv eq_refl). exact R19.
    - rewrite K25, Q25, (EE 25%nat 25%bv eq_refl). exact R25. }
  exact (kr_miss_ret (fx := fx1) B VOBJS n (KD fx1) v ly2 S2 W2 regs2 mem2 md2 pos mcc gi
    line p rest CX LS2 FRM1 CORE2 CELLS2 NP2 LOOP2 Hn Hne FIN' RB2
    ltac:(rewrite K21, Q21, E33; reflexivity) ltac:(rewrite K22, Q22, E52; reflexivity)).
Qed.
End e.
End f.
End d.
About kr_s_miss.
Print Assumptions kr_s_miss.
