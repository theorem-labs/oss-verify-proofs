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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 309 of its 357 lines of code are new or changed and 405 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_KIGNP: the pieces KI_R2 0x86968 and KI_R4 0x869c4
   (lib/A/Prog/m_file_s_kign_m.v). The KIGNP segment lane of the G2 walk owner's G2.
   proves no function (kind: segment lemma of m_file's walk: S_MF_KIGNP's KI_R2 and KI_R4 pieces).

   KI_R2 (after ieq(v, vl, "yes")): 0x86968 `li s6,1`, `bnez a0,0x869e4`; a hit loads g = 136(s1) at 0x869e4 and
   reaches KI_HIT 0x869e8 with s6 = 1; a miss calls ieq(v, vl, "true") (0x86970 .. 0x86980) and returns to KI_R3.
   KI_R4 (after ieq(v, vl, "no")): 0x869c4 `bnez a0,0x869e0`; a hit sets s6 = 0 (0x869e0), loads g and reaches
   KI_HIT; a miss calls ieq(v, vl, "false") (0x869c8 .. 0x869d8) and returns to KI_R5.
   The seed (m_file_sd.v mf_seed) keeps one region, the 8-byte spill slot 136(s1) read only (ki_slot136), so the
   run writes no byte; the calls are m_file_iq.v's mf_ieq_call. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k ieq_c m_file_iq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_kign_t m_file_s_kign_m m_file_s_kign_1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the spill slot 136(s1), read only: the cursor g = mseg_addr c gi (atom 37) *)
Definition ki_slot136 : YP09.region := YP09.mkRegion (Some 2%nat) 136 144 0 0 [YP09.mkChunk 136 (CVal 8 (SOff 37 0))].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the registers in L a run left at the seed's atoms are the cut's *)
Lemma ki_keepl : forall E R regs1 v lyc pos cur np xs (rr : bvmap 5 word) (L : list (bv 5)),
  E = mfE regs1 v lyc pos cur np xs -> mf_regs_base v regs1 ->
  (forall r, getr rr r = sv_denot E (sr_get R r)) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get R r) (sr_get sr_mf r)) L = true ->
  forall r, In r L -> getr rr r = getr regs1 r.
Proof.
intros E R regs1 v lyc pos cur np xs rr L HE RB HR HC r Hin.
pose proof (mf_regs_ok v regs1 lyc pos cur np xs RB) as HO. rewrite <- HE in HO.
rewrite HR, HO. f_equal. apply sv_eqb_eq. exact (proj1 (forallb_forall _ _) HC _ Hin).
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstA.STK_ieq SegInstA.RLO_A SegInstA.RHI_A.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

(* the seed at a K cut's pc with the one region 136(s1) *)
Lemma ki_seed1 : forall v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest pc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
  mf_regs_at B v lyc pos regs1 -> mf_loop v Wc memc mcc (Some gi) line p rest -> mf_np v memc Wc (mf_next p rest) ->
  st_ok_pi SEGS VAL (mfE regs1 v lyc pos (Some gi) (mf_next p rest) []) (mkSS pc sr_mf [ki_slot136] None mf_facts)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest pc CX CORE CELLS RA LOOP NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & _). unfold mf_cur_ok in LCUR.
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) [] pc true true []
  false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
refine (st_ok_pi_submem _ (ss_mf pc true true [] false false [] false MF_LOW_ON) _ [ki_slot136] HS0 _ eq_refl).
cbn [ss_mf ss_mem mf_regions]. apply submem_drop. apply submem_keep; [|apply submem_nil].
unfold subregion, ki_slot136, mf_r_slots. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|].
intros ch [<- | []]. unfold mf_cell_chunks. cbn [app In]. repeat (first [left; reflexivity | right]).
Qed.

(* the cursor's value: atom 37 is mseg_addr c gi *)
Lemma ki_e37 : forall regs1 v lyc pos gi np,
  ew (mfE regs1 v lyc pos (Some gi) np []) 37 = w64 (seg_spec.mseg_addr (mv_c v) gi).
Proof.
intros regs1 v lyc pos gi np.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 5 ltac:(unfold A_TEXT; lia)) as E37.
cbn [Nat.add nth mf_extra map app] in E37. exact E37.
Qed.


(* the callee-saved registers but s6 (x22) *)
Definition KI_KL22 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%bv.

Lemma ki_st_reg_pi : forall E ss (H : word -> bool) ms (r : bv 5) (n : nat),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros E ss H ms r n HS Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* KI_R2 0x86968: `li s6,1`, `bnez a0`: "yes" to KI_HIT with s6 = 1, else ieq(v, vl, "true") and KI_R3 *)
Lemma ki_s_r2 : forall n, KI_HIT_stmt B n -> KI_R3_stmt B n -> KI_R2_stmt B n.
Proof.
intros n HIT NEXT v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv VB FIN A0.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & HOV & HVV & NP & R21 & R20 & R24).
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (ki_line_le rest) as Hml.
pose proof (ki_seed1 v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest KI_R2 CX CORE CELLS RA LOOP NP) as HS1.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof CORE as (HJ & _).
pose proof RA as (R2 & R3 & R4 & R8 & _).
destruct (ieq vv S_yes) eqn:EY; cbn [seg_spec.b2z] in A0.
- (* "yes": g = 136(s1), KI_HIT with b = true *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_HIT.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (HMEQ : forall x, ms_mem ms x = memc x)
    by (intros x; apply HF; intros (rr & Hin & Hw); destruct Hin as [<- | []]; cbn in Hw; lia).
  assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
  assert (KP : forall r, In r KI_KL22 -> getr (ms_regs ms) r = getr regs1 r).
  { eapply (ki_keepl E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) KI_KL22 eq_refl RB).
    - intros r. exact (st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS).
    - vm_compute. reflexivity. }
  assert (RA' : mf_regs_at B v lyc pos (ms_regs ms))
    by (apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA); apply KP; unfold KI_KL22;
        repeat (first [left; reflexivity | right])).
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
    as (CORE' & CELLS' & NPk & LPk).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with KI_HIT by (unfold KI_HIT, AF_m_file; reflexivity) end.
  apply (HIT v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv true).
  + unfold ki_vbase.
    refine (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj RA' (conj Hn (conj Hr
      (conj (LPk mcc (Some gi) line p rest LOOP) (conj HOV (conj HVV (conj (NPk _ NP) _)))))))))))).
    split; [rewrite (KP 21%bv ltac:(unfold KI_KL22; repeat (first [left; reflexivity | right]))); exact R21|].
    split; [rewrite (KP 20%bv ltac:(unfold KI_KL22; repeat (first [left; reflexivity | right]))); exact R20|].
    rewrite (KP 24%bv ltac:(unfold KI_KL22; repeat (first [left; reflexivity | right]))); exact R24.
  + unfold ki_val in FIN. rewrite (ki_dec_yes vv EY) in FIN. exact FIN.
  + rewrite (ki_st_reg_pi E _ (w_H Wc) ms 13%bv 37%nat HS) by (vm_compute; reflexivity). unfold E. apply ki_e37.
  + rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ ms 22%bv HS).
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
      replace (sr_get (ss_regs ss) 22%bv) with (SLit 1) by (vm_compute; reflexivity) end.
    reflexivity.
- (* not "yes": s6 = 1, ieq(v, vl, "true"), KI_R3 *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (HMEQ : forall x, ms_mem ms x = memc x)
    by (intros x; apply HF; intros (rr & Hin & Hw); destruct Hin as [<- | []]; cbn in Hw; lia).
  assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
  assert (KP : forall r, In r KI_KL22 -> getr (ms_regs ms) r = getr regs1 r).
  { eapply (ki_keepl E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) KI_KL22 eq_refl RB).
    - intros r. exact (st_ok_restrict_reg SEGS (w_H Wc) E _ ms r HS).
    - vm_compute. reflexivity. }
  assert (RA' : mf_regs_at B v lyc pos (ms_regs ms))
    by (apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA); apply KP; unfold KI_KL22;
        repeat (first [left; reflexivity | right])).
  assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (pose proof RA' as (X & _); exact X).
  assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (pose proof RA' as (_ & X & _); exact X).
  assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (pose proof RA' as (_ & _ & X & _); exact X).
  assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (pose proof RA' as (_ & _ & _ & X & _); exact X).
  assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ov)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 10%bv 21%nat HS) by (vm_compute; reflexivity).
    unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 21 (Z_to_bv 5 21) eq_refl). exact R21. }
  assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat vl)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 11%bv 20%nat HS) by (vm_compute; reflexivity).
    unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 20 (Z_to_bv 5 20) eq_refl). exact R20. }
  assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstA.seg_litA_fz S_true)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 12%bv (A_OBJ 22) HS) by (vm_compute; reflexivity).
    unfold E. rewrite (mfE_img regs1 v lyc pos (Some gi) np [] (A_OBJ 22) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    rewrite (mf_lit_obj VOBJS S_true 22 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
    reflexivity. }
  assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KI_R3)).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
    lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
      transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
    exact (codeptr_val E KI_R3 HEI). }
  rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
    as (CORE' & CELLS' & NPk & LPk).
  pose proof (NPk np NP) as NP'. pose proof (LPk mcc (Some gi) line p rest LOOP) as LOOP'.
  destruct (ki_slice_facts B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi) line p rest ov vl CX CORE' LOOP'
    ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
  rewrite HVV in SB, SZ, SL.
  refine (mf_ieq_call B RELRO IEQ v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi)
    line p rest np KI_R3 (p + Z.of_nat ov) (Z.of_nat vl) (seg_spec.zb vv) S_true CX LS CORE' CELLS' LOOP' NP'
    Q2 Q3 Q4 Q8 Q1 _ _ _ Q10 Q11 Q12 S0 SB SL SA SH _).
  + unfold KI_R3, AF_m_file; lia.
  + unfold KI_R3, AF_m_file; reflexivity.
  + unfold M_FILE_LITS; repeat (first [left; reflexivity | right]).
  + intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
    rewrite SZ in A02.
    pose proof (mf_regs_keep B v lyc pos (ms_regs ms) regs2 RA' HP2) as RA2.
    assert (KP2 : forall z, In (Z_to_bv 5 z) KI_KL22 -> acallee_saved z -> getr regs2 (Z_to_bv 5 z) = getr regs1 (Z_to_bv 5 z)).
    { intros z Hin Hcs. rewrite <- (KP _ Hin). exact (HP2 _ Hcs). }
    apply (NEXT v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ov vl vv).
    * unfold ki_vbase.
      refine (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj RA2 (conj Hn (conj Hr
        (conj LOOP2 (conj HOV (conj HVV (conj NP2 _)))))))))))).
      split; [transitivity (getr regs1 21); [exact (KP2 21 ltac:(unfold KI_KL22; repeat (first [left; apply bv_eq; reflexivity | right]))
        ltac:(unfold acallee_saved; lia)) | ]; exact R21|].
      split; [transitivity (getr regs1 20); [exact (KP2 20 ltac:(unfold KI_KL22; repeat (first [left; apply bv_eq; reflexivity | right]))
        ltac:(unfold acallee_saved; lia)) | ]; exact R20|].
      transitivity (getr regs1 24); [exact (KP2 24 ltac:(unfold KI_KL22; repeat (first [left; apply bv_eq; reflexivity | right]))
        ltac:(unfold acallee_saved; lia)) | ]; exact R24.
    * exact FIN.
    * exact EY.
    * exact A02.
    * transitivity (getr (ms_regs ms) 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia))|].
      rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 22%bv HS).
      lazymatch type of HS with st_ok _ _ ?ss _ =>
        replace (sr_get (ss_regs ss) 22%bv) with (SLit 1) by (vm_compute; reflexivity) end.
      reflexivity.
Qed.

(* KI_R4 0x869c4: `bnez a0`: "no" to 0x869e0 (s6 = 0) and KI_HIT, else ieq(v, vl, "false") and KI_R5 *)
Lemma ki_s_r4 : forall n, KI_HIT_stmt B n -> KI_R5_stmt B n -> KI_R4_stmt B n.
Proof.
intros n HIT NEXT v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv VB FIN NY NT N1 A0.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & HOV & HVV & NP & R21 & R20 & R24).
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (ki_line_le rest) as Hml.
pose proof (ki_seed1 v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest KI_R4 CX CORE CELLS RA LOOP NP) as HS1.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof CORE as (HJ & _).
pose proof RA as (R2 & R3 & R4 & R8 & _).
destruct (ieq vv S_no) eqn:EN; cbn [seg_spec.b2z] in A0.
- (* "no": s6 = 0, g = 136(s1), KI_HIT with b = false *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_HIT.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (HMEQ : forall x, ms_mem ms x = memc x)
    by (intros x; apply HF; intros (rr & Hin & Hw); destruct Hin as [<- | []]; cbn in Hw; lia).
  assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
  assert (KP : forall r, In r KI_KL22 -> getr (ms_regs ms) r = getr regs1 r).
  { eapply (ki_keepl E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) KI_KL22 eq_refl RB).
    - intros r. exact (st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS).
    - vm_compute. reflexivity. }
  assert (RA' : mf_regs_at B v lyc pos (ms_regs ms))
    by (apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA); apply KP; unfold KI_KL22;
        repeat (first [left; reflexivity | right])).
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
    as (CORE' & CELLS' & NPk & LPk).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with KI_HIT by (unfold KI_HIT, AF_m_file; reflexivity) end.
  apply (HIT v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv false).
  + unfold ki_vbase.
    refine (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj RA' (conj Hn (conj Hr
      (conj (LPk mcc (Some gi) line p rest LOOP) (conj HOV (conj HVV (conj (NPk _ NP) _)))))))))))).
    split; [rewrite (KP 21%bv ltac:(unfold KI_KL22; repeat (first [left; reflexivity | right]))); exact R21|].
    split; [rewrite (KP 20%bv ltac:(unfold KI_KL22; repeat (first [left; reflexivity | right]))); exact R20|].
    rewrite (KP 24%bv ltac:(unfold KI_KL22; repeat (first [left; reflexivity | right]))); exact R24.
  + unfold ki_val in FIN. rewrite (ki_dec_no vv NY NT N1 EN) in FIN. exact FIN.
  + rewrite (ki_st_reg_pi E _ (w_H Wc) ms 13%bv 37%nat HS) by (vm_compute; reflexivity). unfold E. apply ki_e37.
  + rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ ms 22%bv HS).
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
      replace (sr_get (ss_regs ss) 22%bv) with (SLit 0) by (vm_compute; reflexivity) end.
    reflexivity.
- (* not "no": ieq(v, vl, "false"), KI_R5 *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (HMEQ : forall x, ms_mem ms x = memc x)
    by (intros x; apply HF; intros (rr & Hin & Hw); destruct Hin as [<- | []]; cbn in Hw; lia).
  assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
  assert (KP : forall r, In r KI_KL22 -> getr (ms_regs ms) r = getr regs1 r).
  { eapply (ki_keepl E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) KI_KL22 eq_refl RB).
    - intros r. exact (st_ok_restrict_reg SEGS (w_H Wc) E _ ms r HS).
    - vm_compute. reflexivity. }
  assert (RA' : mf_regs_at B v lyc pos (ms_regs ms))
    by (apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA); apply KP; unfold KI_KL22;
        repeat (first [left; reflexivity | right])).
  assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (pose proof RA' as (X & _); exact X).
  assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (pose proof RA' as (_ & X & _); exact X).
  assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (pose proof RA' as (_ & _ & X & _); exact X).
  assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (pose proof RA' as (_ & _ & _ & X & _); exact X).
  assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ov)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 10%bv 21%nat HS) by (vm_compute; reflexivity).
    unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 21 (Z_to_bv 5 21) eq_refl). exact R21. }
  assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat vl)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 11%bv 20%nat HS) by (vm_compute; reflexivity).
    unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 20 (Z_to_bv 5 20) eq_refl). exact R20. }
  assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstA.seg_litA_fz S_false)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 12%bv (A_OBJ 24) HS) by (vm_compute; reflexivity).
    unfold E. rewrite (mfE_img regs1 v lyc pos (Some gi) np [] (A_OBJ 24) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    rewrite (mf_lit_obj VOBJS S_false 24 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
    reflexivity. }
  assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KI_R5)).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
    lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
      transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
    exact (codeptr_val E KI_R5 HEI). }
  rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
    as (CORE' & CELLS' & NPk & LPk).
  pose proof (NPk np NP) as NP'. pose proof (LPk mcc (Some gi) line p rest LOOP) as LOOP'.
  destruct (ki_slice_facts B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi) line p rest ov vl CX CORE' LOOP'
    ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
  rewrite HVV in SB, SZ, SL.
  refine (mf_ieq_call B RELRO IEQ v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi)
    line p rest np KI_R5 (p + Z.of_nat ov) (Z.of_nat vl) (seg_spec.zb vv) S_false CX LS CORE' CELLS' LOOP' NP'
    Q2 Q3 Q4 Q8 Q1 _ _ _ Q10 Q11 Q12 S0 SB SL SA SH _).
  + unfold KI_R5, AF_m_file; lia.
  + unfold KI_R5, AF_m_file; reflexivity.
  + unfold M_FILE_LITS; repeat (first [left; reflexivity | right]).
  + intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
    rewrite SZ in A02.
    pose proof (mf_regs_keep B v lyc pos (ms_regs ms) regs2 RA' HP2) as RA2.
    assert (KP2 : forall z, In (Z_to_bv 5 z) KI_KL22 -> acallee_saved z -> getr regs2 (Z_to_bv 5 z) = getr regs1 (Z_to_bv 5 z)).
    { intros z Hin Hcs. rewrite <- (KP _ Hin). exact (HP2 _ Hcs). }
    apply (NEXT v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ov vl vv).
    * unfold ki_vbase.
      refine (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj RA2 (conj Hn (conj Hr
        (conj LOOP2 (conj HOV (conj HVV (conj NP2 _)))))))))))).
      split; [transitivity (getr regs1 21); [exact (KP2 21 ltac:(unfold KI_KL22; repeat (first [left; apply bv_eq; reflexivity | right]))
        ltac:(unfold acallee_saved; lia)) | ]; exact R21|].
      split; [transitivity (getr regs1 20); [exact (KP2 20 ltac:(unfold KI_KL22; repeat (first [left; apply bv_eq; reflexivity | right]))
        ltac:(unfold acallee_saved; lia)) | ]; exact R20|].
      transitivity (getr regs1 24); [exact (KP2 24 ltac:(unfold KI_KL22; repeat (first [left; apply bv_eq; reflexivity | right]))
        ltac:(unfold acallee_saved; lia)) | ]; exact R24.
    * exact FIN.
    * exact NY.
    * exact NT.
    * exact N1.
    * exact EN.
    * exact A02.
Qed.

End e.
End f.
End d.
