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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 144 of its 186 lines of code are new or changed and 411 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc): the m_refuse block of segment S_MF_KMOD, MK_REFUSE 0x86cc0 to
   KDONE 0x86cd0 (lib/A/Prog/m_file_s_kmod_m.v; also the end of S_MF_KIGNP's bad-value arm). The KMOD refusal sub-lane
   of the G2 walk owner's G2. Proves mk_refuse_ok : forall n, MF_KDONE_F B n -> MK_REFUSE_stmt B n.
   The code (listing m_file.fuzz_segconf.asan.s lines 899-903): 0x86cc0 ld s5,128(s1) (c, mf_cells' slot 128);
   0x86cc4 mv a0,s5; 0x86cc8 mv a1,s6 (line + 1); 0x86ccc jal m_refuse; the return point 0x86cd0 is MF_KDONE.
   The proof: m_file_sd.v's seed at 0x86cc0 with the spill slots read-only (the three instructions store nothing),
   one token run to the jal, every byte kept (m_file_k.v mf_carry_eq); the call is m_file_rf.v's shared m_refuse
   step with knock = false (its footprint premise from the cut's model equation, m_file_s_kmod_t.v
   mf_fin_kept_mono); at the FP state fx1 the call returns, MF_KDONE_stmt with the model m_refuse mcc (line + 1)
   false, cur = Some gi, line + 1, the text after the line (m_file_k.v mf_loop_next), s5 = c and s6 = line + 1 kept
   (callee-saved). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaFx PaNoChain SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_refuse_c m_file_c m_file_m m_file_s_kmod_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_sd m_file_k m_file_mdl m_file_s_kmod_t.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_rf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* every region of the state is read-only: a run from it writes nothing (the TAIL / EXIT segment lane's m_file_s_tail.v, after
   fuzz_command's check_reply_s7.v cr7_awr) *)
Ltac mkr_awr_ro :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the state's form, computed *)
Ltac mkr_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the shared Section hypotheses this piece uses, in their shared texts: VOBJS for m_file_sd.v's seed; SIGP, SSP,
   RELRO and M_REFUSE for m_file_rf.v's mf_refuse_step *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.
Let RUNTO := paj_run_to B LAWS.

(* KDONE at the FP state fx1 the call returns, from the state after m_refuse: the model is m_refuse mcc (line + 1)
   false, the line consumed (line + 1), the text left the one after the line at mf_next p rest *)
Lemma mkr_kdone : forall n (fx1 : YK11.FPState) v ly2 S2 W2 regs2 mem2 md2 pos (mcc : mconf) (gi : nat)
  (line p : Z) (rest : list Z),
MF_KDONE_F B n -> mf_cx B v -> mf_ls v ly2 S2 -> sa_frm0 (fx := fx1) ->
mf_core B v ly2 S2 W2 mem2 md2 pos MF_LOW_ON (m_refuse mcc (line + 1) false) ->
mf_cells v ly2 pos mem2 W2 (Some gi) -> mf_regs_at B v ly2 pos regs2 ->
getr regs2 24 = w64 (frame_addr ly2 1 pos) ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v W2 mem2 (m_refuse mcc (line + 1) false) (Some gi) (line + 1) (mf_next p rest) (mf_rest rest) ->
mf_fin (m_refuse mcc (line + 1) false, Some gi) line rest = mf_final v ->
mf_np v mem2 W2 (mf_next p rest) -> getr regs2 21 = w64 (mv_c v) -> getr regs2 22 = w64 (line + 1) ->
SRr SEGS W2 (mkCfg (@mkst fx1 regs2 (Z_to_bv 64 (BASE + MF_KDONE)) mem2 (seg_rom SEGS)) md2)
  (MF_POST (fx := fx1) B v).
Proof.
intros n fx1 v ly2 S2 W2 regs2 mem2 md2 pos mcc gi line p rest KD CX LS F0 CORE CELLS RA R24 Hn Hne LOOP MDL NP
  R21 R22.
exact (KD fx1 v ly2 S2 W2 regs2 mem2 md2 pos (m_refuse mcc (line + 1) false) (Some gi) (line + 1) (mf_next p rest)
  (mf_rest rest) CX LS F0 CORE CELLS RA R24
  ltac:(destruct (mf_break_snd rest) as (_ & Hlt & _); specialize (Hlt Hne); unfold mf_rest; lia) LOOP MDL NP R21 R22).
Qed.

Lemma mk_refuse_ok : forall n, MF_KDONE_F B n -> MK_REFUSE_stmt B n.
Proof.
intros n KD v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv BS MDL.
destruct BS as (CX & LS & F0 & CORE & CELLS & RA & Hn & Hne & LOOP & Hov & Hvv & NP & R24 & R22).
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1.
pose proof LOOP as (_ & _ & _ & _ & (PA1 & PA2 & PA3 & PRA & _) & Hcurok & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE Hcurok) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) []
  MK_REFUSE true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp
  ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos (Some gi) (mf_next p rest) []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat ->
  ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) (mf_next p rest) []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33.
cbn [Nat.add nth mf_extra map app] in E32, E33.
(* the spill slots read-only: the three instructions store nothing *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. mkr_norm HS1.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
(* 0x86cc0 ld s5,128(s1); 0x86cc4 mv a0,s5; 0x86cc8 mv a1,s6; stop at the jal 0x86ccc *)
paj_run_to_tok RUNTO HS1 HJ SHOK Bspan (AF_m_file + 0xe10).
{ mkr_awr_ro. }
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
    intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw | ] end.
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
destruct (mf_carry_eq B v lyc Sc Wc memc mdc (ms_mem ms) mdw pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE HJ
  K0 LOOP) as (CORE' & LOOP' & CELLSf & NPf).
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (25%bv : bv 5) Q25.
prreg HS1 (26%bv : bv 5) Q26. prreg HS1 (24%bv : bv 5) Q24. prreg HS1 (21%bv : bv 5) Q21. prreg HS1 (22%bv : bv 5) Q22.
prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11. prreg HS1 (1%bv : bv 5) Q1.
pmkst HS1.
set (rg := ms_regs ms) in *. set (mm := ms_mem ms) in *.
assert (RAq : mf_regs_at B v lyc pos rg).
{ apply (mf_regs_at_of B v lyc pos regs1 rg RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity.
  - rewrite Q26. apply EE. reflexivity. }
assert (G24 : getr rg 24 = w64 (frame_addr lyc 1 pos)) by (rewrite Q24, (EE 24%nat 24%bv eq_refl); exact R24).
assert (G21 : getr rg 21 = w64 (mv_c v)) by (rewrite Q21, E33; reflexivity).
assert (G22 : getr rg 22 = w64 (line + 1)) by (rewrite Q22, (EE 22%nat 22%bv eq_refl); exact R22).
assert (G10 : getr rg 10 = w64 (mv_c v)) by (rewrite Q10, E33; reflexivity).
assert (G11 : getr rg 11 = w64 (line + 1)) by (rewrite Q11, (EE 22%nat 22%bv eq_refl); exact R22).
pose proof (CELLSf (Some gi) CELLS) as CELLSq. pose proof (NPf _ NP) as NPq. clear CELLSf NPf.
(* the call's model premises: the line number, the refused counter, the footprint *)
pose proof LOOP as (_ & _ & _ & _ & _ & _ & Hk0 & Hl0 & Hl1 & Hrf & Hof).
assert (Hr1 : (1 <= length rest)%nat) by (destruct rest; [congruence | cbn [length]; lia]).
assert (Hln : 0 <= line + 1 <= 65536) by lia.
assert (Hrf1 : mc_refused mcc + 1 < 2 ^ 32) by lia.
assert (HKF : (length (mc_kept (m_refuse mcc (line + 1) false)) <= length (mc_kept (mf_final v)))%nat)
  by (rewrite <- MDL; exact (mf_fin_kept_mono (m_refuse mcc (line + 1) false, Some gi) line rest)).
(* 0x86ccc jal m_refuse(c, line + 1); the walk goes on at KDONE 0x86cd0 at the FP state the call returns *)
change (BASE + 8088) with (BASE + (AF_m_file + 0xe10)).
pose proof RAq as (A2 & A3 & A4 & A8 & _).
apply (mf_refuse_step B SIGP SSP RELRO M_REFUSE v lyc Sc Wc rg mm mdw pos MF_LOW_ON mcc mcc false (Some gi) line p
  rest (mf_next p rest) (AF_m_file + 0xe10)
  CX LS F0 (mf_corek_of_core B v lyc Sc Wc mm mdw pos MF_LOW_ON mcc CORE') CELLSq NPq A2 A3 A4 A8 LOOP' Hne eq_refl Hk0
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) G10 G11 HKF).
intros fx1 ly2 Sq W2 regs2 mem2 md2 FXR LS2 CORE2 CELLS2 NP2 LOOP2 HCS.
assert (Ely : ly2 = lyc) by (destruct LS as (E1 & _); destruct LS2 as (E2 & _); congruence). subst ly2.
assert (KS : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr rg (Z_to_bv 5 r)) by exact HCS.
assert (RA2 : mf_regs_at B v lyc pos regs2).
{ apply (mf_regs_at_of B v lyc pos rg regs2 RAq);
  first [ exact (KS 2 ltac:(unfold acallee_saved; lia)) | exact (KS 3 ltac:(unfold acallee_saved; lia))
        | exact (KS 4 ltac:(unfold acallee_saved; lia)) | exact (KS 8 ltac:(unfold acallee_saved; lia))
        | exact (KS 9 ltac:(unfold acallee_saved; lia)) | exact (KS 18 ltac:(unfold acallee_saved; lia))
        | exact (KS 19 ltac:(unfold acallee_saved; lia)) | exact (KS 25 ltac:(unfold acallee_saved; lia))
        | exact (KS 26 ltac:(unfold acallee_saved; lia)) ]. }
pose proof (m_refuse_counters mcc (line + 1) false) as (Cr1 & Cr2 & Cr3 & _).
pose proof (mf_loop_next v W2 mem2 mcc (Some gi) line p rest (m_refuse mcc (line + 1) false) (Some gi) LOOP2 Hne
  ltac:(lia) ltac:(lia) Cr3 (mf_cur_ok_refuse mcc (Some gi) (line + 1) false Hcurok)) as LOOPn.
unfold mf_at. replace (AF_m_file + 0xe10 + 4) with MF_KDONE by (unfold MF_KDONE; lia).
apply (mkr_kdone n fx1 v lyc Sq W2 regs2 mem2 md2 pos mcc gi line p rest KD CX LS2 (fxrel_frm0 fx fx1 F0 FXR) CORE2
  CELLS2 RA2).
- transitivity (getr rg 24); [exact (KS 24 ltac:(unfold acallee_saved; lia)) | exact G24].
- exact Hn.
- exact Hne.
- exact LOOPn.
- exact MDL.
- exact NP2.
- transitivity (getr rg 21); [exact (KS 21 ltac:(unfold acallee_saved; lia)) | exact G21].
- transitivity (getr rg 22); [exact (KS 22 ltac:(unfold acallee_saved; lia)) | exact G22].
Qed.

End e.
End f.
End d.

Check mk_refuse_ok.
Print Assumptions mk_refuse_ok.
