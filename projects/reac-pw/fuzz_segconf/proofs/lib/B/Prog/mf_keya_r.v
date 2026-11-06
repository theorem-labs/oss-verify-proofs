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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 163 of its 212 lines of code are new or changed and 404 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_KEYA: the refusal of a key line to
   TAIL (mf_keya_d.v kb_ref : MF_TAIL_F n -> KB_REF_stmt n), in the form of plugin-hostd/fuzz_command's lib/A/Prog
   walks (origin/ossv/recipes 501c0d516c69):
     0x867dc  jal m_refuse (a0 = s9 = c, a1 = s11 = line + 1)    m_file_rf.v's MF_REFUSE_STEP (knock = false,
                                                                 mcl = mcc)
     0x867e0  li s4,511; ld s10,152(s1); j 0x86820 (MF_TAIL)     kb_ref_cont, at the FP state fx1 the call returns
   kb_ref_cont: a light seed at 0x867e0 (every register its own atom; one read-only region, the cell 152(s1) with
   base s1 = atom 9 and the next line's address as atom 32), one run to TAIL (s4 = 511, s10 = 152(s1)); the run
   writes no byte, so every cut fact crosses it by m_file_iq.v's iq_keep over an empty window, and TAIL's facts are
   the continuation's with the refusal's model m_refuse mcc (line + 1) false at the next line (line + 1,
   mf_next p rest, mf_rest rest). The call step is m_file_rf.v's mf_refuse_step under its shared
   hypotheses, the next line's loop facts m_file_k.v's mf_loop_next, the model's sizes m_file_mdl.v's
   mf_cur_ok_refuse / mf_kept_le_refuse / m_refuse_sizes. The template is image A's m_file_s_keya_rp.v
   (commit ddef332b859f) at image B's registers and cells.
   A walk lane of the image-B m_file-family owner's G2B. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_mdl m_file_k m_file_iq m_file_rf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_keya_m mf_keya_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the state at 0x867e0: the cell 152(s1) (base s1 = atom 9) holding the next line's address, atom 32 ---- *)
Definition kr_regions : smem := [ YP09.mkRegion (Some 9%nat) 152 160 0 0 [YP09.mkChunk 152 (CVal 8 (SOff 32 0))] ].
Definition kr_ss : sstate := mkSS (KB_JREF + 4) sr_atoms kr_regions None (mkFacts [ (18%nat, mkAF SB SB 0) ] [] []).
Definition kr_Bx : sv := SOff 18 0.
(* the registers the run keeps (it writes s4 = x20 and s10 = x26) *)
Definition KR_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 27]%bv.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition kr_E (regs1 : bvmap 5 word) (x : Z) : env := Eimg (Ereg regs1 [Z_to_bv 64 x]).
Lemma kr_ew_reg : forall regs1 x n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (kr_E regs1 x) n = getr regs1 r.
Proof.
intros regs1 x n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold kr_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma kr_ew32 : forall regs1 x, ew (kr_E regs1 x) 32 = Z_to_bv 64 x.
Proof. intros. unfold kr_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). Qed.
Lemma kr_env_agree : forall regs1 x, env_agree 32 (Ereg regs1 [Z_to_bv 64 x]) (kr_E regs1 x).
Proof. intros. split; [intros n Hn; unfold kr_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

(* the seed at 0x867e0 *)
Lemma kr_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc s1 np,
getr regs1 9 = w64 s1 -> getr regs1 18 = w64 SHADOW_OFF -> 0 <= s1 -> s1 + 160 <= 2 ^ 64 -> 0 <= np < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) memc) (s1 + 152) 8 np ->
st_ok_pi SEGS VAL (kr_E regs1 np) kr_ss
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + (KB_JREF + 4))) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc s1 np H9 H18 Hs0 Hs1 Hnp V152.
set (E := kr_E regs1 np).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (subst E; rewrite (kr_ew_reg regs1 np 9 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; rewrite (kr_ew_reg regs1 np 18 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 np) by (subst E; apply kr_ew32).
rewrite restrict_mkst_fx. unfold kr_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ s1 152 8 (SOff 32 0) np);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact V152].
- exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E18, unsigned_lit_small by (unfold SB; lia). rewrite Z.pow_0_r, Z.mod_1_r. unfold SB.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* a run over read-only regions keeps every view *)
Lemma kr_keep_step : forall E rs (m0 m m' : word -> option byte) (H : word -> bool),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall b wlo whi, In (b, wlo, whi) (windows rs) -> whi <= wlo) ->
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m a = aview SEGS H m0 a) ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E rs m0 m m' H HFr HW KM a Ha.
rewrite (kept_of_frame (segs := SEGS) E rs H m m' (fun _ => False) HFr); [exact (KM a Ha) | | exact Ha | intros []].
intros b wlo whi a' Hin Hr. pose proof (HW b wlo whi Hin). lia.
Qed.
Lemma kr_ag32 : forall (regs1 : bvmap 5 word) extra E0 E,
env_agree 32 (Ereg regs1 extra) E0 -> env_agree 34 E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

Ltac kr_after E0 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree 34 E0 En) by (env_agree_chain HAE);
    pose proof (kr_keep_step Eo rs _ _ _ _ HFr ltac:(intros b wlo whi Hin; vm_compute in Hin; repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin) KM) as KMn;
    clear HFr HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac kr_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyv own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac kr_kept := cbv [KR_KEPT In]; tauto.

(* 0x867e0 .. TAIL: the state after m_refuse's return, with the line's model and the next line in 152(s1) *)
Lemma kb_ref_cont : forall n, MF_TAIL_stmt B n ->
forall v lyc Sc Wc (regs1 : bvmap 5 word) memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_np v memc Wc p ->
mf_regs_at B v lyc pos regs1 ->
(length rest < n)%nat -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
getr regs1 27 = w64 line ->
mf_at B v Wc regs1 memc mdc (KB_JREF + 4).
Proof.
intros n TL v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS NP RG Hn LOOP HFIN R27.
pose proof CX as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S1.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
assert (Hs1b : alloc_ceiling + 16 <= mf_s1 (mv_sp v) /\ mf_s1 (mv_sp v) + 160 <= 2 ^ 47)
  by (unfold mf_s1; lia).
pose proof LOOP as (_ & _ & _ & _ & (Hp0 & Hp63 & _) & _).
pose proof CORE as (HJ & _).
pose proof RG as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (kr_entry Wc regs1 memc (mf_s1 (mv_sp v)) p R9 R18 ltac:(lia) ltac:(lia) ltac:(lia) NP) as HS.
assert (SHOK : sh_ok SEGS kr_Bx [] (kr_E regs1 p) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM (kr_E regs1 p)) by (unfold kr_E; apply Eimg_env).
pose proof (kr_env_agree regs1 p) as HA0.
pose proof (kr_ew32 regs1 p) as E32.
revert HS SHOK HEI HA0 E32. generalize (kr_E regs1 p) as E0. intros E0 HS SHOK HEI HA0 E32.
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
unfold mf_at.
(* `li s4,511`, `ld s10,152(s1)`, `j 0x86820` *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_TAIL. { kr_awr. }
kr_after E0 HAE KM.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KR_KEPT HS (kr_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (26%bv : bv 5) N26. prreg HS (20%bv : bv 5) N20.
pmkst HS.
destruct (iq_keep B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur line p rest p Sc Wc _ _
  (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) CX LS CORE CELLS LOOP NP HJ (Permutation_refl _)
  ltac:(intros a Ha _; exact (KM a Ha)) ltac:(lia) ltac:(lia)) as (CORE' & CELLS' & LOOP' & NP').
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
  refine (TL v lyc Sc Wc rg mm md pos mcc cur line p rest CX LS FRM CORE' CELLS' _ Hn LOOP' HFIN _ _ _) end.
- unfold mf_regs_at, mf_regs_ex. rewrite !HK by kr_kept. exact RG.
- rewrite N26, E32. reflexivity.
- rewrite HK by kr_kept. exact R27.
- rewrite N20. reflexivity.
Qed.
End e.
End f.
End d.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section i.
Variable B : asyms.
(* the shared hypotheses m_file_rf.v's mf_refuse_step needs, verbatim *)
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (aview SEGS (w_H W) mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
(* the callee, at every FP state (the image-B m_file segment table's m_refuse row) *)
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.

(* 0x867dc: m_refuse (c, line + 1), then TAIL with the next line *)
Lemma kb_ref : forall n, MF_TAIL_F B n -> KB_REF_stmt B n.
Proof.
intros n TL v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS RG Hn Hr LOOP HFIN NP
  R10 R11 R27.
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & LK0 & _).
pose proof (mf_regs_at_call B v lyc pos regs1 RG) as (R2 & R3 & R4 & R8).
pose proof (mf_cur_ok_refuse mcc cur (line + 1) false LCUR) as HCUR'.
apply (mf_refuse_step B SIGP SSP RELRO M_REFUSE v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc mcc false cur line p rest
  (mf_next p rest) KB_JREF CX LS FRM (mf_corek_of_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CORE) CELLS NP
  R2 R3 R4 R8 LOOP Hr eq_refl LK0
  ltac:(vm_compute; reflexivity) ltac:(unfold KB_JREF, AF_m_file; lia) R10 R11
  (mf_kept_le_refuse mcc (line + 1) false cur (line + 1) (lines (mf_rest rest)) (mf_final v) HCUR' HFIN)).
intros fx1 ly2 S2 W2 regs2 mem2 md2 Hrel LS2 CORE2 CELLS2 NP2 LOOP2 HKS.
pose proof (m_refuse_sizes mcc (line + 1) false) as (_ & HKL).
assert (LOOPn : mf_loop v W2 mem2 (m_refuse mcc (line + 1) false) cur (line + 1) (mf_next p rest) (mf_rest rest)).
{ eapply mf_loop_next; [exact LOOP2 | exact Hr | | | |].
  - unfold m_refuse. cbn [mc_refused]. lia.
  - unfold m_refuse. cbn [mc_overflow]. lia.
  - lia.
  - exact HCUR'. }
pose proof LS as (Ely & _). pose proof LS2 as (Ely2 & _).
assert (RG2 : mf_regs_at B v ly2 pos regs2).
{ pose proof (mf_regs_at_kept B v lyc pos regs1 regs2 RG HKS) as RG'. rewrite Ely in RG'. rewrite Ely2. exact RG'. }
assert (K27 : getr regs2 27 = getr regs1 27) by exact (HKS 27 ltac:(unfold acallee_saved; lia)).
exact (kb_ref_cont (fx := fx1) B n (TL fx1) v ly2 S2 W2 regs2 mem2 md2 pos (m_refuse mcc (line + 1) false) cur
  (line + 1) (mf_next p rest) (mf_rest rest) CX LS2 (PaFx.fxrel_frm0 fx fx1 FRM Hrel) CORE2 CELLS2 NP2 RG2
  ltac:(pose proof (kb_rest_lt rest Hr); lia) LOOPn HFIN ltac:(rewrite K27; exact R27)).
Qed.
End i.
End h.
End g.
