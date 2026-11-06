(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the fifth segment of check_reply's walk (fuzz_command.asan, 0x86d78), the
   strcmp call of the refusal path (0x86fb8) and the branch into the epilogue, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call and back) and A/ACh5.v (a segment that ends
   in another segment's statement), at c8557374ad2e.

   The code of the segment is
     0x86fb8  jal  wrapper_strcmp       a0 = g_rec.reply, a1 = s3 = F + 32, which holds "resp <code>"
     0x86fbc  beqz a0, 0x86ff8          equal: the epilogue; else j 0x870d8, the abort
   The entry facts give `xr = refusal_text (reply_code_a xr)` for a negative code (reply_okA), and the frame holds
   `refusal_text code ++ [0]` (the snprintf step of segment 4), so the two strings are equal, the interceptor
   returns 0, and the abort edge 0x86fc0 is not taken.

   The walk runs with the symbolic regions dropped (`st_ok_pi_submem` with []): the two instructions write no
   memory, so the engine's frame is empty and every byte the walk reads is the byte of the state the segment was
   entered in. The interceptor's own writes are the ones its contract allows, inside its scratch window below sp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 397 of its 441 lines of code are new or changed and 368 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (0x8a400), stage 9: M8 (0x8a62c) to M9
   (0x8a634), the call of hand_back on buf.

   `mv a0,s4` (buf = F + 64), `jal hand_back` (0x8a978, at 0x8a630; return address 0x8a634 = M9). hand_back's
   contract (lib/B/Prog/hand_back_c.v) is apost_base: it returns at the same FP state, so the rest of the walk is
   the next stage at the ambient fx. The call rule is PaNoChain.v's cl_callS_wide: hand_back's footprint holds
   g_rec.answer, a program static (awr_byte's static case), and the recorder's old answer block. The frame chain at
   the call is sup_add_lem.v's sa_chain_at (afn_pre's entry chain with sup_add's frame pushed). hand_back's text is
   "resp v" in buf (M8's astr_atR), an object of this call's class-1 frame whose four shadow bytes 8..11 are 0
   (sa_buf0); old is g_rec.answer (the recorder's representation). M9 takes sa_core at EV_SUP_ADD R (the journal
   is monotone in k) and sa_postQ: sup_add_m R .. = hand_back R2 (resp v) on either arm of sa_arm (RecModel.v
   sup_add_m), q = hand_back's returned copy, the block and recorder accounting against the entry from M8's
   sa_acct, the live bytes and the meter through the Z.max of LIVE_SUP_ADD / XM_SUP_ADD. The donor is the A walk's
   stage 6, second half (lib/A/Prog/sup_add_s6.v on a working branch 87f17ee4716). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaNoChain PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts PaCallPg RecBLemmas.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at 0x8a62c: every register its own atom, atom 32 the shadow base; no region (the two
   instructions this stage runs touch no memory) and no inline check *)
Definition sae_SB : Z := 0x7fff8000.
Definition sae_Bx : sv := SOff 32 0.
Definition sae9_facts : facts := mkFacts [ (32%nat, mkAF sae_SB sae_SB 0) ] [] [].
Definition ss_sae9 : sstate := mkSS L_M8 sr_atoms [] None sae9_facts.
Definition sae_Bspan : Z * Z := (sae_SB, sae_SB + 2 ^ 44 - 1).
Definition sae9_extra : list word := [Z_to_bv 64 sae_SB].
(* hand_back's footprint filters the recorder's blocks with a boolean predicate; the membership direction the walk
   needs *)
Lemma sae_filter_in : forall (f : Z * Z -> bool) (pn : Z * Z) (l : list (Z * Z)),
In pn (filter (fun q : Z * Z => f q) l) -> In pn l /\ f pn = true.
Proof.
intros f pn l. induction l as [|q l IH]; [intros []|].
cbn. destruct (decide (f q)) as [Hq|Hq].
- intros [Heq|Hin].
  + split; [left; exact Heq|]. subst q. destruct (f pn) eqn:Ef; [reflexivity | destruct Hq].
  + destruct (IH Hin) as [H1 H2]. split; [right; exact H1 | exact H2].
- intros Hin. destruct (IH Hin) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition sae9_E (regs : bvmap 5 word) : env := Eimg (Ereg regs sae9_extra).
Lemma sae9_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem,
st_ok_pi SEGS VAL (sae9_E regs) ss_sae9 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L_M8)) mem (seg_rom SEGS)))
/\ sh_ok SEGS sae_Bx [] (sae9_E regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem.
set (E := sae9_E regs).
assert (E32 : ew E 32 = Z_to_bv 64 sae_SB).
{ subst E. unfold sae9_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
split.
- unfold ss_sae9. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold sae9_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. first [exact I | repeat split].
  + split; [|split; [exact I | exact I]].
    cbn [sae9_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, unsigned_lit_small by (unfold sae_SB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. unfold sae_SB.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok. apply Forall_nil.
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the image's per-binary facts: CmdRecFacts.v's lemmas and cmd_img_facts' fields by exact from IMG *)
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
(* the statement's own (sup_add_c.v:104) *)
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS.

(* the recorder's blocks are live blocks (CmdRep.v rec_repA, RecBLemmas.v lay_blocks_in) *)
Lemma sae_owned : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof using Type.
intros ly S rd R O (Q & HQ & HO) pn Hpn. exact (lay_blocks_in _ _ _ _ _ _ HQ pn (proj1 (HO pn) Hpn)).
Qed.
(* g_rec.answer, as hand_back's statement reads it: 0 or the start of one of the recorder's blocks *)
Lemma sae_answer : forall ly S rd R O, rec_repA B ly S rd R O ->
  exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists n, In (old, n) O).
Proof using Type.
intros ly S rd R O (Q & HA & HO).
destruct HA as (_ & _ & _ & _ & HAn & _). revert HAn. unfold aanswer_at.
destruct (r_answer R) as [x|]; destruct (l_answer Q) as [[p n]|] eqn:EQ; intros HAn; try contradiction.
- destruct HAn as (Hv & _). exists p. split; [exact Hv|]. right. exists n. apply HO.
  unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  try rewrite EQ. cbn [oblk In]. left. reflexivity.
- exists 0. split; [exact HAn | left; reflexivity].
Qed.
(* a byte of g_rec is a program static (CmdBSyms' ts_prog) *)
Lemma sae_grec_prog : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) (as_prog_static B).
Proof using HB.
intros a Ha. rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. apply Exists_cons_hd.
unfold in_zr. cbn [fst snd]. unfold A_G_REC, REC_SIZE in Ha. lia.
Qed.
(* arodata_okP across the walk's journal (CmdRecRest.v cmd_rodata_kept: the footprint holds program statics and
   the recorder's blocks, live at the entry) *)
Lemma sae_aro_kept : forall STK sp0 ly S W mem md own lyc Sc Wc memc mdc k R O,
  AR SEGS B ly S W mem md ->
  ajournal SEGS B STK sp0 (sa_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  rec_repA B ly S (rdW W mem) R O ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof using LAWS HB IMG.
intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k R O HAR HJ HREP HR.
apply (CmdRecRest.cmd_rodata_kept SEGS B LAWS HB IMG ly S W mem md lyc Sc Wc memc mdc STK sp0 (sa_FP O) own k
  HAR HJ); [|exact HR].
intros a Ha. unfold sa_FP in Ha. rewrite !inFP_cons in Ha.
destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
  [ left; unfold TFIB_PROG_STATIC; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
    unfold A_G_REC, OFF_NCALLS in Ha; lia
  | left; unfold TFIB_PROG_STATIC; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
    unfold A_G_REC, OFF_CALLS, OFF_ANSWER in Ha; lia
  | left; unfold TFIB_PROG_STATIC; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
    unfold A_G_REC, OFF_STATE in Ha; lia
  | left; unfold TFIB_PROG_STATIC; apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
    unfold A_REC_SPILL, SC_SIZE in Ha; lia
  | ].
right. destruct (inFP_ablocks_fp_inv _ a Ha) as (q & m & Hqm & Hr). exists q, m.
split; [apply in_or_app; left; exact (sae_owned _ _ _ _ _ HREP _ Hqm) | exact Hr].
Qed.

Lemma sa_m8_ok : SA_M9_stmt B MT -> SA_M8_at B MT.
Proof using HB LAWS MTL SIGP IMG THAND_BACK.
intros M9. unfold SA_M8_at.
intros ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCX HFRM0 HM.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO.
pose proof pa_B_ok as (HBa & HBb & HBc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
assert (WS2 : HAND_BACK_STK + 144 <= SUP_ADD_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (WS3 : 0 <= HAND_BACK_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof HCX as HCXs.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & Hfr & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT & HC &
  HCT & HREP & Hev & Hlive & MOK).
unfold sa_M8m, sa_core in HM. cbv zeta in HM.
destruct HM as ((HJ & HFRM & HFLG & Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q23 & Q25 & Q26 & Q27) &
  Hs4 & HBUF & v & R2 & O6 & HARM & HSTR & HREP2 & HACCT & HMO6).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (sp0 := spZ regs) in *.
set (s1 := sa_s1 sp0) in *.
set (F := frame_addr lyc 1 pos) in *.
assert (Hs1 : s1 = sp0 - 128 \/ s1 = sp0 - 144) by (clear - Hal16; unfold s1, sa_s1; Z.div_mod_to_equations; lia).
assert (Hal1 : (s1 - sp0) mod 16 = 0).
{ destruct Hs1 as [E1 | E1]; rewrite E1;
  [replace (sp0 - 128 - sp0) with (-128) by lia | replace (sp0 - 144 - sp0) with (-144) by lia]; reflexivity. }
pose proof HJ as (HARc & Hlyc & Hsecsc & Hwlec & Hioc & Hfrsc & Hnevc & Hkc & JF1 & JF2 & JF3 & JF4 & JGone & JPres
  & JStk & JF5 & JQT).
assert (HFin : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HARc HFin) as (HF32 & HFapp & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc HFin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFapp, HFceil. fold F in HF32, HFapp, HF4096, HFceil.
assert (Hv : -2 ^ 31 <= v < 2 ^ 31) by (destruct HARM as [(-> & _) | (-> & ? & _)]; lia).
pose proof (resp_length v Hv) as HRL.
(* ---- the seed at 0x8a62c ---- *)
destruct (sae9_seed Wc regs1 memc) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (sae9_E regs1)) by (unfold sae9_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (sae9_E regs1) n = ew (Ereg regs1 sae9_extra) n)
  by (intros n Hn; unfold sae9_E; apply Eimg_low; exact Hn).
remember (sae9_E regs1) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
clear HE EL.
(* 0x8a62c .. 0x8a630: a0 := s4 (buf), jal to hand_back *)
paj_run_tok RUN HS HJ SHOK sae_Bspan.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (md2 := m) in *; clearbody md2 end.
pmkst HS.
rename ms into ms2.
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (8%bv : bv 5) U8. prreg HS (9%bv : bv 5) U9. prreg HS (10%bv : bv 5) U10.
prreg HS (18%bv : bv 5) U18. prreg HS (19%bv : bv 5) U19. prreg HS (23%bv : bv 5) U23.
prreg HS (25%bv : bv 5) U25. prreg HS (26%bv : bv 5) U26. prreg HS (27%bv : bv 5) U27.
assert (U2' : getr (ms_regs ms2) 2 = w64 s1) by (rewrite U2, (EEo 2%nat 2%bv eq_refl); exact Q2).
assert (U3' : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite U3, (EEo 3%nat 3%bv eq_refl); exact Q3).
assert (U4' : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite U4, (EEo 4%nat 4%bv eq_refl); exact Q4).
assert (U8' : getr (ms_regs ms2) 8 = w64 sp0) by (rewrite U8, (EEo 8%nat 8%bv eq_refl); exact Q8).
assert (U9' : getr (ms_regs ms2) 9 = w64 s1) by (rewrite U9, (EEo 9%nat 9%bv eq_refl); exact Q9).
assert (U10' : getr (ms_regs ms2) 10 = w64 (F + 64)) by (rewrite U10, (EEo 20%nat 20%bv eq_refl); exact Hs4).
assert (U18' : getr (ms_regs ms2) 18 = w64 F) by (rewrite U18, (EEo 18%nat 18%bv eq_refl); exact Q18).
assert (U19' : getr (ms_regs ms2) 19 = getr regs 11) by (rewrite U19, (EEo 19%nat 19%bv eq_refl); exact Q19).
assert (U23' : getr (ms_regs ms2) 23 = w64 (F + 32)) by (rewrite U23, (EEo 23%nat 23%bv eq_refl); exact Q23).
assert (U25' : getr (ms_regs ms2) 25 = w64 (SHADOW_OFF + F / 8))
  by (rewrite U25, (EEo 25%nat 25%bv eq_refl); exact Q25).
assert (U26' : getr (ms_regs ms2) 26 = w64 F) by (rewrite U26, (EEo 26%nat 26%bv eq_refl); exact Q26).
assert (U27' : getr (ms_regs ms2) 27 = w64 (-8)) by (rewrite U27, (EEo 27%nat 27%bv eq_refl); exact Q27).
assert (HB1 : alloc_ceiling + SUP_ADD_STK <= sp0) by lia.
assert (HB2 : sp0 <= 2 ^ 47) by lia.
assert (HspT2 : spZ (ms_regs ms2) = sp0 + (s1 - sp0))
  by (unfold spZ at 1; rewrite U2'; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hs0 : s0Z (ms_regs ms2) = sp0)
  by (unfold s0Z; rewrite U8'; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
(* the run writes no memory *)
assert (K2 : forall a, rdW Wc (ms_mem ms2) a = rdW Wc memc a).
{ intros a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & _). vm_compute in Hin. destruct Hin. }
pose proof (proj1 HJ) as HARc2.
assert (HBUF2 : sa_buf0 (rdW Wc (ms_mem ms2)) F) by (intros i Hi; rewrite K2; exact (HBUF i Hi)).
assert (HFRM2 : sa_frame (rdW Wc (ms_mem ms2)) sp0 regs) by (intros j r Hj k Hk; rewrite K2; exact (HFRM j r Hj k Hk)).
(* the recorder's view at the hand_back call *)
destruct HACCT as (HA1 & HA2 & HA3 & HA4 & HA5).
assert (HREP2' : rec_repA B lyc Sc (rdW Wc (ms_mem ms2)) R2 O6).
{ refine (rec_repA_kept B _ _ _ _ _ _ _ _ HREP2 HA4 _). intros a _. exact (K2 a). }
destruct (sae_answer lyc Sc (rdW Wc (ms_mem ms2)) R2 O6 HREP2') as (old & Hold & Holdv).
(* the text "resp v" in buf, as hand_back's string argument *)
assert (HSTRBUF : astr_atR (rdW Wc (ms_mem ms2)) (F + 64) (resp v)).
{ destruct HSTR as (HSb & HSnz). split; [|exact HSnz]. intros i Hi. rewrite K2. exact (HSb i Hi). }
(* hand_back's budgets *)
assert (HEVle : sa_ev6 R + EV_HAND_BACK <= EV_SUP_ADD R).
{ unfold EV_SUP_ADD, sa_ev6, sa_ev5, sa_ev4, sa_ev2, sa_ev1. pose proof (Z.le_max_r EV_ANSWER EV_HAND_BACK). lia. }
assert (HMODEL : sup_add_m R uri id placement client = hand_back R2 (resp v)).
{ unfold sup_add_m, sa_arm, sa_A in *. cbv zeta in *.
  destruct HARM as [(-> & Hb & ->) | (-> & (Hr1 & Hr2) & Hrf & ->)].
  - rewrite Hb. reflexivity.
  - replace ((id <? 0) || (10000 <=? id))%bool with false
      by (symmetry; apply orb_false_intro; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
    rewrite Hrf. cbn [Z.eqb negb]. reflexivity. }
rewrite HMODEL in Hlive, MOK. cbn [hand_back fst snd] in Hlive, MOK.
assert (HLIVEle : sa_live6 uri id placement client + LIVE_HAND_BACK (resp v) <=
  LIVE_SUP_ADD uri id placement client (resp v)).
{ unfold LIVE_SUP_ADD, sa_live6, sa_live5, sa_live4, sa_live2.
  pose proof (Z.le_max_r (LIVE_ANSWER (resp v)) (LIVE_HAND_BACK (resp v))). lia. }
assert (HXMle : sa_acc6 MT R uri id placement client + XM_HAND_BACK MT (resp v) <=
  XM_SUP_ADD MT R uri id placement client (resp v)).
{ unfold XM_SUP_ADD, sa_acc6, sa_acc5, sa_acc4, sa_acc2, sa_acc1.
  pose proof (Z.le_max_r (XM_ANSWER MT (resp v)) (XM_HAND_BACK MT (resp v))). lia. }
assert (HXMnn : 0 <= XM_HAND_BACK MT (resp v)).
{ unfold XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC. pose proof (mo_free_nonneg _ MTL).
  pose proof (mo_malloc_nonneg _ MTL (Z.max (Z.of_nat (length (resp v)) + 1) 1) ltac:(lia)). lia. }
assert (HMOB : mo_ok MT Sc (XM_HAND_BACK MT (resp v)))
  by (exact (mok_station MT S Sc _ _ _ MTL MOK HMO6 HXMnn HXMle)).
assert (HEVB : st_nev Sc + EV_HAND_BACK <= EV_MAX) by lia.
assert (HLIVEB : blocks_bytes Sc + LIVE_HAND_BACK (resp v) <= LIVE_MAX) by lia.
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms2)))
  by (exact (sae_aro_kept _ _ ly S W mem md _ lyc Sc Wc (ms_mem ms2) md2 _ R O HAR0 HJ HREP HROD)).
(* the frame object of the buffer *)
assert (HFOBJ : afobj SEGS B lyc Sc Wc (ms_mem ms2) (F + 64) (Z.of_nat (length (resp v)) + 1)).
{ split.
  - exists 1, pos. split; [exact HFin|]. split; [lia|].
    split; [fold F; Z.div_mod_to_equations; lia|].
    split; [fold F; lia | change (fs_frame_bytes 1) with 128; fold F; lia].
  - split; [Z.div_mod_to_equations; lia|].
    intros x Hx. exists 0. split; [|left; reflexivity].
    unfold shadow_of_addr.
    assert (Hi : 8 <= x / 8 - F / 8 < 12) by (clear - Hx HF32 HRL; Z.div_mod_to_equations; lia).
    replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 8 + (x / 8 - F / 8 - 8)) by lia.
    apply HBUF2. lia. }
(* hand_back's footprint and the frame chain *)
assert (HFP1lo : forall a, inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8)
  :: ablocks_fp (filter (fun pn => fst pn =? old) O6)) a -> a < alloc_ceiling).
{ intros a Ha. apply inFP_cons in Ha as [Hans | Hblk].
  - unfold A_G_REC, OFF_ANSWER in Hans. lia.
  - destruct (inFP_ablocks_fp_inv _ a Hblk) as (p & n0 & Hpn & Hr).
    destruct (sae_filter_in _ _ _ Hpn) as [Hino6 _].
    destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 p n0 HARc2 (HA4 (p, n0) Hino6)) as (_ & _ & Hpce & _).
    lia. }
assert (HFP1F : forall a, F <= a < F + 128 -> ~ inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8)
  :: ablocks_fp (filter (fun pn => fst pn =? old) O6)) a).
{ intros a Ha Hfp. apply inFP_cons in Hfp as [Hans | Hblk].
  - assert (HPG : inFP cmd_PG a)
      by (exists (A_G_REC, A_G_REC + 960); split; [cbn [In cmd_PG]; tauto | cbn [fst snd]; unfold OFF_ANSWER in Hans; lia]).
    destruct (al_client_img _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 a HARc2
      ltac:(right; left; exists 1, pos; split; [exact HFin | change (fs_frame_bytes 1) with 128; fold F; lia])) as (_ & Hni).
    exact (Hni (cif_prog_img a HPG)).
  - destruct (inFP_ablocks_fp_inv _ a Hblk) as (p & n0 & Hpn & Hr).
    destruct (sae_filter_in _ _ _ Hpn) as [Hino6 _].
    pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc (ms_mem ms2) md2 p n0 1 pos HARc2 (HA4 (p, n0) Hino6) HFin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. fold F in Hd. lia. }
assert (Hs1' : s1 + 16 <= sp0) by lia.
assert (HCH : exists ch1, achain lyc (rdW Wc (ms_mem ms2)) s1 sp0 ch1)
  by (exact (sa_chain_at B LAWS ly S W regs mem md ch R O lyc Sc Wc (ms_mem ms2) md2 (sa_ev6 R) pos s1
    HPRE HREP HJ HFRM2 Hs1')).
destruct HCH as (ch1 & Hch1).
(* hand_back's word arguments and its stack *)
assert (HsR : 0 <= F + 64 < 2 ^ 64) by lia.
assert (HoldR : 0 <= old < 2 ^ 64).
{ destruct Holdv as [-> | (n0 & Hino6)]; [lia|].
  destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 old n0 HARc2 (HA4 (old, n0) Hino6))
    as (_ & H4096 & Hpc0 & _ & _ & _ & Hn0).
  pose proof (req_size_pos n0 ltac:(lia)) as [Hrq _]. lia. }
assert (Hsig : SIG CS_hand_back = BASE + AF_hand_back).
{ rewrite (SIGP CS_hand_back ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])));
  try (f_equal; vm_compute; reflexivity). }
(* 0x8a630: hand_back(buf) *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS) with (STK1 := HAND_BACK_STK)
    (FP1 := ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8)
             :: ablocks_fp (filter (fun pn => fst pn =? old) O6)))
    (EV1 := EV_HAND_BACK) (o := s1 - sp0) (ch1 := ch1).
  - exact HJ.
  - exact HspT2.
  - exact Hal1.
  - lia.
  - exact WS3.
  - lia.
  - exact U3'.
  - exact U4'.
  - reflexivity.
  - rewrite U1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite U1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - replace (sp0 + (s1 - sp0)) with s1 by lia. rewrite Hs0. exact Hch1.
  - intros HFN. eapply SRr_mono.
    { try rewrite Hsig.
      apply (THAND_BACK fx lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 ch1 (F + 64) old (resp v) R2 O6
        HFN HROD2 U10' HsR HSTRBUF ltac:(unfold LMAX; lia) HFOBJ HREP2' Hold HoldR HEVB HLIVEB HMOB). }
    cbv beta. intros W' c' _ Hpost.
    destruct Hpost as (ly' & S' & regs' & mem' & md' & Hc' & HJx & HPx & HQx).
    exists ly', S', regs', mem', md'.
    split; [exact Hc'|]. split; [exact HJx|]. split; [exact HPx | exact HQx].
  - intros a Ha. apply inFP_cons in Ha as [Hans | Hblk].
    + right; right; right; right. left.
      assert (HPG : inFP cmd_PG a)
        by (exists (A_G_REC, A_G_REC + 960); split; [cbn [In cmd_PG]; tauto | cbn [fst snd]; unfold OFF_ANSWER in Hans; lia]).
      split; [|split; [apply sae_grec_prog; unfold OFF_ANSWER, REC_SIZE in *; lia | exact (cif_prog_img a HPG)]].
      exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8).
      split; [unfold sa_FP; cbn [In]; tauto | cbn [fst snd]; unfold OFF_CALLS, OFF_ANSWER in *; lia].
    + destruct (inFP_ablocks_fp_inv _ a Hblk) as (p & n0 & Hpn & Hr).
      destruct (sae_filter_in _ _ _ Hpn) as [Hino6 _].
      destruct (HA1 (p, n0) Hino6) as [HinO | Hnot].
      * right; left. split.
        -- exists (p, p + req_size n0). split; [|cbn [fst snd]; lia].
           unfold sa_FP. cbn [In]. right; right; right; right.
           apply in_map_iff. exists (p, n0). split; [reflexivity | exact HinO].
        -- exists p, n0. split; [exact (HA4 (p, n0) Hino6) | exact Hr].
      * right; right. left. exists p, n0. split; [exact (HA4 (p, n0) Hino6) | split; [exact Hnot | exact Hr]].
  - intros ly2 S2 W2 regs2 mem2 md5 _ a Ha Hw _. exfalso. pose proof (HFP1lo a Ha). lia. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJ4i & HP4 & HK4).
cbn [hand_back fst snd] in HK4.
destruct HK4 as (p1 & p2 & O' & HO10 & HO4096 & HOne & HFRESH & HBiff & HREP4 & HOiff & HSTR4 & HBB4 & HMO4).
(* the facts the epilogue stage asks at 0x8a634 *)
destruct (al_layout _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 ly4 HARc2 (proj1 (proj2 HJ4i))) as (Habl4 & Hfa & Hown4).
assert (HFeq : frame_addr ly4 1 pos = F) by (rewrite (Hfa 1 pos); reflexivity).
assert (HlyF : ly_F ly4 = ly_F lyc) by (pose proof (Hfa 1 pos) as HH; unfold frame_addr in HH; lia).
assert (HFLeq : flag_addr ly4 1 pos = flag_addr lyc 1 pos) by (unfold flag_addr; rewrite HlyF; reflexivity).
assert (KEEP4 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (s1 - HAND_BACK_STK <= a < s1) ->
  rdW W4 mem4 a = rdW Wc (ms_mem ms2) a).
{ intros a Ha Hw. pose proof HJ4i as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
  apply (G1 a Ha); [lia|].
  intros Hfp. pose proof (HFP1lo a Hfp). lia. }
assert (KEEPF : forall a, F <= a < F + 128 -> rdW W4 mem4 a = rdW Wc (ms_mem ms2) a).
{ intros a Ha. pose proof HJ4i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G4 & _).
  apply (G4 1 pos a HFin); [|exact (HFP1F a Ha)].
  left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia. }
assert (HSTART4 : forall p m1 m2, In (p, m1) (ablocks B ly4 S4) -> In (p, m2) (ablocks B ly4 S4) -> m1 = m2).
{ intros p m1 m2 H1 H2. destruct (Z.eq_dec m1 m2) as [->|Hne]; [reflexivity|]. exfalso.
  pose proof (proj1 HJ4) as HAR4.
  pose proof (sep_blocks SEGS B LAWS ly4 S4 W4 mem4 md4 p m1 p m2 HAR4 H1 H2 ltac:(intros Eq0; injection Eq0; lia)) as Hd.
  destruct (al_blocks _ _ LAWS ly4 S4 W4 mem4 md4 p m1 HAR4 H1) as (_ & _ & _ & _ & _ & _ & Hm1).
  destruct (al_blocks _ _ LAWS ly4 S4 W4 mem4 md4 p m2 HAR4 H2) as (_ & _ & _ & _ & _ & _ & Hm2).
  pose proof (req_size_pos m1 ltac:(lia)) as [Hr1 _]. pose proof (req_size_pos m2 ltac:(lia)) as [Hr2 _].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HSTARTc : forall p m1 m2, In (p, m1) (ablocks B lyc Sc) -> In (p, m2) (ablocks B lyc Sc) -> m1 = m2).
{ intros p m1 m2 H1 H2. destruct (Z.eq_dec m1 m2) as [->|Hne]; [reflexivity|]. exfalso.
  pose proof (sep_blocks SEGS B LAWS lyc Sc Wc (ms_mem ms2) md2 p m1 p m2 HARc2 H1 H2 ltac:(intros Eq0; injection Eq0; lia)) as Hd.
  destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 p m1 HARc2 H1) as (_ & _ & _ & _ & _ & _ & Hm1).
  destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 p m2 HARc2 H2) as (_ & _ & _ & _ & _ & _ & Hm2).
  pose proof (req_size_pos m1 ltac:(lia)) as [Hr1 _]. pose proof (req_size_pos m2 ltac:(lia)) as [Hr2 _].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
(* a block live at the entry and not the recorder's is live at the call and does not start at old: old is 0 or the
   start of one of the recorder's current blocks O6, and two live blocks with one start are one block *)
assert (HKEPT : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc) /\ fst pn <> old).
{ intros pn Hin Hnin. split; [exact (HA3 pn Hin Hnin)|].
  destruct pn as [pp0 pn0]. cbn [fst]. intros Heqold. subst pp0.
  destruct Holdv as [Hold0 | (n0 & Hino6)].
  - destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 old pn0 HARc2 (HA3 _ Hin Hnin)) as (_ & H4096 & _).
    lia.
  - assert (Heq : pn0 = n0)
      by (apply (HSTARTc old); [exact (HA3 _ Hin Hnin) | exact (HA4 (old, n0) Hino6)]).
    subst pn0. destruct (HA1 (old, n0) Hino6) as [HL | HR]; [exact (Hnin HL) | exact (HR Hin)]. }
rewrite U1.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
  change (Z_to_bv 64 (BASE + k)) with (Z_to_bv 64 (BASE + L_M9)) end.
apply (M9 fx ly S W regs mem md ch pu id pp pc uri placement client R O ly4 S4 W4 regs4 mem4 md4 pos HCXs HFRM0).
unfold sa_M9m, sa_core, sa_postQ. cbv zeta. rewrite HMODEL. cbn [hand_back fst snd].
fold sp0. fold s1.
assert (HPR : forall r : Z, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr (ms_regs ms2) (Z_to_bv 5 r)) by exact HP4.
split.
- (* the journal, the saved registers, the frame's flag and the kept registers *)
  split; [eapply ajournal_mono_k; [exact HJ4 | lia]|].
  split.
  { intros j r Hj k Hk.
    assert (Hjlt : (j < 13)%nat)
      by (change 13%nat with (length sa_saved); apply nth_error_Some; rewrite Hj; discriminate).
    rewrite KEEP4 by lia. exact (HFRM2 j r Hj k Hk). }
  split.
  { rewrite HFeq, HFLeq. change (fs_frame_bytes 1) with 128.
    rewrite (rdword_ext (rdW Wc (ms_mem ms2)) (rdW W4 mem4) (F + 128 - 8));
      [|intros k Hk; apply KEEPF; lia].
    rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms2)) (F + 128 - 8));
      [|intros k Hk; apply K2].
    change (fs_frame_bytes 1) with 128 in HFLG. exact HFLG. }
  split; [exact (eq_trans (HPR 2 ltac:(unfold acallee_saved; lia)) U2')|].
  split; [exact (eq_trans (HPR 3 ltac:(unfold acallee_saved; lia)) U3')|].
  split; [exact (eq_trans (HPR 4 ltac:(unfold acallee_saved; lia)) U4')|].
  split; [exact (eq_trans (HPR 8 ltac:(unfold acallee_saved; lia)) U8')|].
  split; [exact (eq_trans (HPR 9 ltac:(unfold acallee_saved; lia)) U9')|].
  split; [rewrite HFeq; exact (eq_trans (HPR 18 ltac:(unfold acallee_saved; lia)) U18')|].
  split; [exact (eq_trans (HPR 19 ltac:(unfold acallee_saved; lia)) U19')|].
  split; [rewrite HFeq; exact (eq_trans (HPR 23 ltac:(unfold acallee_saved; lia)) U23')|].
  split; [rewrite HFeq; exact (eq_trans (HPR 25 ltac:(unfold acallee_saved; lia)) U25')|].
  split; [rewrite HFeq; exact (eq_trans (HPR 26 ltac:(unfold acallee_saved; lia)) U26')|].
  exact (eq_trans (HPR 27 ltac:(unfold acallee_saved; lia)) U27').
- (* what the call leaves *)
  exists (set_answer R2 (Some (resp v))), O', p2.
  split; [reflexivity|].
  split; [exact HO10|].
  split; [exact HO4096|].
  split; [exact HREP4|].
  split.
  { intros pn Hpn. apply HOiff in Hpn. destruct Hpn as [[Hpn6 _] | ->]; [exact (HA1 pn Hpn6)|].
    destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec))
      (p1, Z.of_nat (length (resp v)) + 1) O) as [Hin|Hnin]; [left; exact Hin | right; intros Hin].
    destruct (HKEPT _ Hin Hnin) as [Hc Hne]. exact (proj1 (HFRESH _ Hc Hne) eq_refl). }
  split.
  { intros pn Hpn. apply HBiff in Hpn. destruct Hpn as [[Hpn1 Hpn2] | [-> | ->]].
    - destruct (HA2 pn Hpn1) as [HL | HR];
        [left; exact HL | right; left; apply HOiff; left; split; [exact HR | exact Hpn2]].
    - right; left. apply HOiff. right. reflexivity.
    - right; right. reflexivity. }
  split; [intros pn Hin Hnin; apply HBiff; left; exact (HKEPT pn Hin Hnin)|].
  split; [apply HBiff; right; right; reflexivity|].
  split; [intros pn Hin Hnin; destruct (HKEPT pn Hin Hnin) as [Hc Hne]; exact (proj2 (HFRESH pn Hc Hne))|].
  split.
  { intros Hinm. apply in_map_iff in Hinm as (b0 & Heqf & Hino').
    destruct b0 as [pq mq]. cbn [fst] in Heqf. subst pq.
    assert (Hin4 : In (p2, mq) (ablocks B ly4 S4)) by (exact (sae_owned _ _ _ _ _ HREP4 (p2, mq) Hino')).
    assert (Hin4' : In (p2, Z.of_nat (length (resp v)) + 1) (ablocks B ly4 S4))
      by (apply HBiff; right; right; reflexivity).
    assert (Hmq : mq = Z.of_nat (length (resp v)) + 1) by (exact (HSTART4 p2 mq _ Hin4 Hin4')).
    subst mq. apply HOiff in Hino'. destruct Hino' as [[Hino6 Hne] | Heq];
      [exact (proj2 (HFRESH _ (HA4 _ Hino6) Hne) eq_refl) | apply HOne; congruence]. }
  split; [exact HSTR4|].
  split; [clear - HBB4 HA5 HLIVEle; lia|].
  eapply mle_weaken; [exact MTL | eapply mle_station; [exact MTL | exact HMO6 | exact HMO4] | exact HXMle].
Qed.
End e.
End f.
End d.
Print Assumptions sa_m8_ok.
