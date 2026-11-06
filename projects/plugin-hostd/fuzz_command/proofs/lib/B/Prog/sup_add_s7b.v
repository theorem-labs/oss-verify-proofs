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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 328 of its 368 lines of code are new or changed and 372 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (0x8a400), the M6 stage's refused arm:
   0x8a5f0 (id in range, g_rec.refuse <> 0) to M9 (0x8a634).

   `mv a0,s8` (c = the slot record() filled), `li a1,0` (no shape), `li a2,0` (no changes), `jal answer` (0x8aa10,
   at 0x8a5fc; return address 0x8a600), then `j 0x8a634` (M9). answer's contract (lib/B/Prog/answer_c.v) is
   apost_baseF: it returns at SOME FP state fx1 with PaFx.v's fxrel against the entry's, so the last step is
   sup_add_s7a.v's sab_m9_jmp taken at fx1 (a lemma of a closed section, so it holds at every FP state) and the
   post is lifted with PaFx.v's srr_apost_baseF_lift. The call rule is PaFx.v's cl_callS_pgF: answer's footprint
   holds g_rec.answer and g_rec.state, two program statics, and the old answer's block. The frame chain at the call
   is sup_add_lem.v's sa_chain_at. On this arm the model is answer's own hand_back of "resp <g_rec.code>"
   (sup_add_s7a.v's sab_m_refused), so M9's sa_postQ is answer's post, with the block accounting of sab_ans_blocks
   against the entry. The donor is the A walk's stage 5, refused arm (lib/A/Prog/sup_add_s5.v on
   a working branch 87f17ee4716). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaNoChain PaLibF
PaLibG PaLibH PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0 sup_add_lem sup_add_s7a.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts RecBLemmas.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at 0x8a5f0: every register its own atom, atom 32 the shadow base; no region (the three
   instructions before the call touch no memory) and no inline check *)
Definition sabr_facts : facts := mkFacts [ (32%nat, mkAF sab_SB sab_SB 0) ] [] [].
Definition ss_sabr : sstate := mkSS (AF_sup_add + 0x1f0) sr_atoms [] None sabr_facts.
Definition sabr_Bx : sv := SOff 32 0.
Definition sabr_extra : list word := [Z_to_bv 64 sab_SB].
(* the recorder's blocks the call may free: those that start at the old answer *)
Lemma sabr_filter_in : forall (f : Z * Z -> bool) (pn : Z * Z) (l : list (Z * Z)),
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
Definition sabr_E (regs : bvmap 5 word) : env := Eimg (Ereg regs sabr_extra).
Lemma sabr_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem,
st_ok_pi SEGS VAL (sabr_E regs) ss_sabr
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_sup_add + 0x1f0))) mem (seg_rom SEGS)))
/\ sh_ok SEGS sabr_Bx [] (sabr_E regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem.
set (E := sabr_E regs).
assert (E32 : ew E 32 = Z_to_bv 64 sab_SB).
{ subst E. unfold sabr_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
split.
- unfold ss_sabr. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold sabr_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. first [exact I | repeat split].
  + split; [|split; [exact I | exact I]].
    cbn [sabr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, unsigned_lit_small by (unfold sab_SB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. unfold sab_SB.
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
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
(* the statement's own (sup_add_c.v) *)
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS.

Lemma sab_arm_refuse :
(forall fx1 : YK11.FPState, @SA_M9_at fx1 rc SK PI B MT) ->
forall ly S W (regs : bvmap 5 word) mem md ch pu id pp pc uri placement client R O
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc pos,
sa_cx B MT ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
sa_M6m B MT ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos ->
0 <= id < 10000 ->
r_refuse (rec_record R REC_ADD (sa_A uri id placement client)) <> 0 ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + (AF_sup_add + 0x1f0))) memc (seg_rom SEGS)) mdc)
(sa_final B MT ly S W regs mem md R O uri id placement client).
Proof using HB LAWS MTL SIGP IMG TANSWER.
intros HM9 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos
  HCXs HFRM0 HM HIN HREF.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO.
pose proof pa_B_ok as (HBa & HBb & HBc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
assert (WS2 : ANSWER_STK + 144 <= SUP_ADD_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (WS3 : 0 <= ANSWER_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof HCXs as HCX. unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & Hfr & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT & HC &
  HCT & HREP & Hev & Hlive & MOK).
pose proof HM as HMs. unfold sa_M6m, sa_core in HM. cbv zeta in HM.
destruct HM as ((HJ & HFRM & HFLG & Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q23 & Q25 & Q26 & Q27) &
  Hs4 & Hs8 & HBUF & O6 & HREP6 & HACCT & HMO6).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (sp0 := spZ regs) in *.
set (s1 := sa_s1 sp0) in *.
set (F := frame_addr lyc 1 pos) in *.
set (A := sa_A uri id placement client) in *.
set (R1 := rec_record R REC_ADD A) in *.
assert (Hs1 : s1 = sp0 - 128 \/ s1 = sp0 - 144) by (clear - Hal16; unfold s1, sa_s1; Z.div_mod_to_equations; lia).
assert (Hal1 : (s1 - sp0) mod 16 = 0).
{ destruct Hs1 as [E1 | E1]; rewrite E1;
  [replace (sp0 - 128 - sp0) with (-128) by lia | replace (sp0 - 144 - sp0) with (-144) by lia]; reflexivity. }
pose proof HJ as (HARc & Hlyc & Hsecsc & Hwlec & Hioc & Hfrsc & Hnevc & Hkc & JF1 & JF2 & JF3 & JF4 & JGone & JPres
  & JStk & JF5 & JQT).
assert (HFin : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc HFin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil. fold F in HF4096, HFceil.
assert (HFR8 : Z.of_nat (length (frames Sc)) <= 8) by (rewrite Hfrsc; cbn [app length]; lia).
destruct HACCT as (HA1 & HA2 & HA3 & HA4 & HA5).
(* ---- the seed at 0x8a5f0 ---- *)
destruct (sabr_seed Wc regs1 memc) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (sabr_E regs1)) by (unfold sabr_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (sabr_E regs1) n = ew (Ereg regs1 sabr_extra) n)
  by (intros n Hn; unfold sabr_E; apply Eimg_low; exact Hn).
remember (sabr_E regs1) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
clear HE EL.
(* 0x8a5f0 .. 0x8a5fc: a0 := s8, a1 := 0, a2 := 0, jal answer *)
paj_run_tok RUN HS HJ SHOK sab_Bspan.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (md2 := m) in *; clearbody md2 end.
pmkst HS.
rename ms into ms2.
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (8%bv : bv 5) U8. prreg HS (9%bv : bv 5) U9. prreg HS (10%bv : bv 5) U10.
prreg HS (11%bv : bv 5) U11. prreg HS (12%bv : bv 5) U12.
prreg HS (18%bv : bv 5) U18. prreg HS (19%bv : bv 5) U19. prreg HS (23%bv : bv 5) U23.
prreg HS (25%bv : bv 5) U25. prreg HS (26%bv : bv 5) U26. prreg HS (27%bv : bv 5) U27.
assert (U2' : getr (ms_regs ms2) 2 = w64 s1) by (rewrite U2, (EEo 2%nat 2%bv eq_refl); exact Q2).
assert (U3' : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite U3, (EEo 3%nat 3%bv eq_refl); exact Q3).
assert (U4' : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite U4, (EEo 4%nat 4%bv eq_refl); exact Q4).
assert (U8' : getr (ms_regs ms2) 8 = w64 sp0) by (rewrite U8, (EEo 8%nat 8%bv eq_refl); exact Q8).
assert (U9' : getr (ms_regs ms2) 9 = w64 s1) by (rewrite U9, (EEo 9%nat 9%bv eq_refl); exact Q9).
assert (U10' : getr (ms_regs ms2) 10 = w64 (rec_slot R))
  by (rewrite U10, (EEo 24%nat 24%bv eq_refl); exact Hs8).
assert (U11' : getr (ms_regs ms2) 11 = w64 0) by (rewrite U11; reflexivity).
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
assert (HFRM2 : sa_frame (rdW Wc (ms_mem ms2)) sp0 regs)
  by (intros j r Hj k Hk; rewrite K2; exact (HFRM j r Hj k Hk)).
assert (HREP2' : rec_repA B lyc Sc (rdW Wc (ms_mem ms2)) R1 O6).
{ refine (rec_repA_kept B _ _ _ _ _ _ _ _ HREP6 HA4 _). intros a _. exact (K2 a). }
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms2)))
  by (exact (sab_aro_kept B HB LAWS IMG SUP_ADD_STK sp0 ly S W mem md [(1, pos)] lyc Sc Wc (ms_mem ms2) md2
       (sa_ev6 R) R O HAR0 HJ HREP HROD)).
assert (HRO2 : cmd_ro_ok (rdW Wc (ms_mem ms2)))
  by (exact (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyc Sc Wc (ms_mem ms2) md2 (proj1 HJ) HROD2)).
(* g_rec.answer at the call *)
destruct (sab_rep_fields B lyc Sc (rdW Wc (ms_mem ms2)) R1 O6 HREP2')
  as (_ & _ & _ & _ & (old & Hold & Holdv) & HO6b).
assert (HoldR : 0 <= old < 2 ^ 64).
{ destruct Holdv as [-> | (n0 & Hino6)]; [lia|].
  destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 old n0 (proj1 HJ) (HA4 (old, n0) Hino6))
    as (_ & H4096 & Hpc0 & _ & _ & _ & Hn0).
  pose proof (req_size_pos n0 ltac:(lia)) as [Hrq _]. lia. }
assert (Hc64 : 0 <= rec_slot R < 2 ^ 64).
{ unfold rec_slot. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt; [apply Nat.ltb_lt in Elt|];
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL; lia. }
assert (HCHG : false = negb (bv_unsigned (getr (ms_regs ms2) 12) =? 0)) by (rewrite U12; vm_compute; reflexivity).
(* the model on this arm *)
assert (HMODEL : rec_answer R1 (REC_ADD, A) [] false = sup_add_m R uri id placement client)
  by (symmetry; exact (sab_m_refused R uri id placement client (REC_ADD, A) [] false HIN HREF)).
(* answer's budgets *)
assert (HEVle : sa_ev6 R + EV_ANSWER <= EV_SUP_ADD R).
{ unfold EV_SUP_ADD, sa_ev6, sa_ev5, sa_ev4, sa_ev2, sa_ev1. pose proof (Z.le_max_l EV_ANSWER EV_HAND_BACK). lia. }
assert (HLIVEle : sa_live6 uri id placement client +
  LIVE_ANSWER (snd (sup_add_m R uri id placement client)) <=
  LIVE_SUP_ADD uri id placement client (snd (sup_add_m R uri id placement client))).
{ unfold LIVE_SUP_ADD, sa_live6, sa_live5, sa_live4, sa_live2.
  pose proof (Z.le_max_l (LIVE_ANSWER (snd (sup_add_m R uri id placement client)))
    (LIVE_HAND_BACK (snd (sup_add_m R uri id placement client)))). lia. }
assert (HXMle : sa_acc6 MT R uri id placement client +
  XM_ANSWER MT (snd (sup_add_m R uri id placement client)) <=
  XM_SUP_ADD MT R uri id placement client (snd (sup_add_m R uri id placement client))).
{ unfold XM_SUP_ADD, sa_acc6, sa_acc5, sa_acc4, sa_acc2, sa_acc1.
  pose proof (Z.le_max_l (XM_ANSWER MT (snd (sup_add_m R uri id placement client)))
    (XM_HAND_BACK MT (snd (sup_add_m R uri id placement client)))). lia. }
assert (HXMnn : 0 <= XM_ANSWER MT (snd (sup_add_m R uri id placement client))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC. pose proof (mo_free_nonneg _ MTL).
  pose proof (mo_malloc_nonneg _ MTL
    (Z.max (Z.of_nat (length (snd (sup_add_m R uri id placement client))) + 1) 1) ltac:(lia)). lia. }
assert (HMOB : mo_ok MT Sc (XM_ANSWER MT (snd (sup_add_m R uri id placement client))))
  by (exact (mok_station MT S Sc _ _ _ MTL MOK HMO6 HXMnn HXMle)).
assert (HEVB : st_nev Sc + EV_ANSWER <= EV_MAX) by lia.
assert (HLIVEB : blocks_bytes Sc + LIVE_ANSWER (snd (sup_add_m R uri id placement client)) <= LIVE_MAX) by lia.
(* answer's footprint: below the allocator ceiling and apart from this call's frame *)
assert (HFP1lo : forall a, inFP (sab_ansFP old O6) a -> a < alloc_ceiling).
{ intros a Ha.
  exact (proj1 (sab_ansFP_cases B LAWS lyc Sc Wc (ms_mem ms2) md2 O6 old a (proj1 HJ) HA4 Ha)). }
assert (HFP1F : forall a, F <= a < F + 128 -> ~ inFP (sab_ansFP old O6) a).
{ intros a Ha. apply (sab_ansFP_not_frame B HB LAWS IMG lyc Sc Wc (ms_mem ms2) md2 O6 old a 1 pos
    (proj1 HJ) HA4 HFin). change (fs_frame_bytes 1) with 128. fold F. lia. }
assert (Hs1' : s1 + 16 <= sp0) by lia.
assert (HCH : exists ch1, achain lyc (rdW Wc (ms_mem ms2)) s1 sp0 ch1)
  by (exact (sa_chain_at B LAWS ly S W regs mem md ch R O lyc Sc Wc (ms_mem ms2) md2 (sa_ev6 R) pos s1
    HPRE HREP HJ HFRM2 Hs1')).
destruct HCH as (ch1 & Hch1).
assert (Hsig : SIG CS_answer = BASE + AF_answer).
{ rewrite (SIGP CS_answer ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])));
  try (f_equal; vm_compute; reflexivity). }
(* 0x8a5fc: answer(c, NULL, 0) *)
eapply SRr_bind.
{ eapply (cl_callS_pgF B LAWS) with (STK1 := ANSWER_STK) (FP1 := sab_ansFP old O6)
    (EV1 := EV_ANSWER) (o := s1 - sp0) (ch1 := ch1).
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
      apply (TANSWER fx lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 ch1 (rec_slot R) 0 old (REC_ADD, A) [] false
        R1 O6 HFN HFRM0 HFR8 HROD2 HRO2 U10' Hc64 U11' ltac:(lia) HCHG HREP2' Hold HoldR
        ltac:(intros HZ; exfalso; exact (HREF HZ)) ltac:(intros HZ; exfalso; exact (HREF HZ))
        HEVB ltac:(rewrite HMODEL; exact HLIVEB)
        ltac:(rewrite HMODEL; exact HMOB)). }
    cbv beta. intros W' c' _ Hpost.
    destruct Hpost as (fx' & ly' & S' & regs' & mem' & md' & Hc' & HFPr & HFPc & HJx & HPx & HQx).
    exists fx', ly', S', regs', mem', md'.
    split; [exact Hc'|]. split; [exact HFPr|]. split; [exact HFPc|]. split; [exact HJx|].
    split; [exact HPx | exact HQx].
  - intros a Ha. unfold sab_ansFP in Ha. apply inFP_cons in Ha as [Hans | Ha].
    + left. split.
      * exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8).
        split; [unfold sa_FP; cbn [In]; tauto | cbn [fst snd]; unfold OFF_CALLS, OFF_ANSWER in *; lia].
      * right. assert (HPG : inFP cmd_PG a)
          by (exists (A_G_REC, A_G_REC + 960);
              split; [cbn [In cmd_PG]; tauto | cbn [fst snd]; unfold OFF_ANSWER in Hans; lia]).
        split; [exact (sab_prog_static B HB a HPG) | exact (cif_prog_img a HPG)].
    + apply inFP_cons in Ha as [Hst | Hblk].
      * left. split.
        -- exists (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8).
           split; [unfold sa_FP; cbn [In]; tauto | cbn [fst snd]; lia].
        -- right. assert (HPG : inFP cmd_PG a)
             by (exists (A_G_REC, A_G_REC + 960);
                 split; [cbn [In cmd_PG]; tauto | cbn [fst snd]; unfold OFF_STATE in Hst; lia]).
           split; [exact (sab_prog_static B HB a HPG) | exact (cif_prog_img a HPG)].
      * destruct (inFP_ablocks_fp_inv _ a Hblk) as (p & n0 & Hpn & Hr).
        destruct (sabr_filter_in _ _ _ Hpn) as [Hino6 _].
        destruct (HA1 (p, n0) Hino6) as [HinO | Hnot].
        -- left. split.
           ++ exists (p, p + req_size n0). split; [|cbn [fst snd]; lia].
              unfold sa_FP. cbn [In]. right; right; right; right.
              apply in_map_iff. exists (p, n0). split; [reflexivity | exact HinO].
           ++ left. exists p, n0. split; [exact (HA4 (p, n0) Hino6) | exact Hr].
        -- right. exists p, n0. split; [exact (HA4 (p, n0) Hino6) | split; [exact Hnot | exact Hr]]. }
cbv beta. intros W4 c4 _ (fx1 & ly4 & S4 & regs4 & mem4 & md4 & HFX & -> & HJ4 & HJ4i & HP4 & HK4).
rewrite HMODEL in HK4.
destruct HK4 as (p1 & p2 & O' & HO10 & HO4096 & HOne & HFRESH & HBiff & HREP4 & HOiff & HSTR4 & HBB4 & HMO4).
(* the facts M9 asks at 0x8a600 *)
destruct (al_layout _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 ly4 (proj1 HJ) (proj1 (proj2 HJ4i)))
  as (Habl4 & Hfa & Hown4).
assert (HFeq : frame_addr ly4 1 pos = F) by (rewrite (Hfa 1 pos); reflexivity).
assert (HlyF : ly_F ly4 = ly_F lyc) by (pose proof (Hfa 1 pos) as HH; unfold frame_addr in HH; lia).
assert (HFLeq : flag_addr ly4 1 pos = flag_addr lyc 1 pos) by (unfold flag_addr; rewrite HlyF; reflexivity).
assert (KEEP4 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (s1 - ANSWER_STK <= a < s1) ->
  rdW W4 mem4 a = rdW Wc (ms_mem ms2) a).
{ intros a Ha Hw. pose proof HJ4i as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
  apply (G1 a Ha); [lia|]. intros Hfp. pose proof (HFP1lo a Hfp). lia. }
assert (KEEPF : forall a, F <= a < F + 128 -> rdW W4 mem4 a = rdW Wc (ms_mem ms2) a).
{ intros a Ha. pose proof HJ4i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G4 & _).
  apply (G4 1 pos a HFin); [|exact (HFP1F a Ha)].
  left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia. }
assert (H4096c : forall pn, In pn (ablocks B lyc Sc) -> 4096 <= fst pn).
{ intros [p n0] Hin.
  exact (proj1 (proj2 (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 p n0 (proj1 HJ) Hin))). }
destruct (sab_ans_blocks (ablocks B ly S) (ablocks B lyc Sc) (ablocks B ly4 S4) O O6 O' old p1 p2
  (Z.of_nat (length (snd (sup_add_m R uri id placement client))) + 1)
  HA1 HA2 HA3 HA4 Holdv H4096c
  (sab_uniq B LAWS lyc Sc Wc (ms_mem ms2) md2 (proj1 HJ))
  (sab_uniq B LAWS ly4 S4 W4 mem4 md4 (proj1 HJ4))
  HOne HFRESH HBiff HOiff) as (G1 & G2 & G3 & G4 & G5 & G6).
assert (HO'live : forall pn, In pn O' -> In pn (ablocks B ly4 S4)).
{ intros pn Hpn. apply HBiff. apply HOiff in Hpn as [[Hp1 Hp2] | ->];
  [left; split; [exact (HA4 _ Hp1) | exact Hp2] | right; left; reflexivity]. }
assert (HFRM4 : sa_frame (rdW W4 mem4) sp0 regs).
{ intros j r Hj k Hk.
  assert (Hjlt : (j < 13)%nat)
    by (change 13%nat with (length sa_saved); apply nth_error_Some; rewrite Hj; discriminate).
  rewrite KEEP4 by lia. exact (HFRM2 j r Hj k Hk). }
assert (HPR : forall r : Z, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr (ms_regs ms2) (Z_to_bv 5 r))
  by exact HP4.
(* back at 0x8a600, at the FP state answer returned *)
rewrite U1.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
  change (Z_to_bv 64 (BASE + k)) with (Z_to_bv 64 (BASE + (AF_sup_add + 0x200))) end.
unfold sa_final.
eapply (srr_apost_baseF_lift SEGS fx1); [exact HFX|].
apply (@sab_m9_jmp fx1 rc SK PI B MT HB LAWS (HM9 fx1) ly S W regs mem md ch pu id pp pc uri placement client
  R O ly4 S4 W4 regs4 mem4 md4 pos HCXs (fxrel_frm0 fx fx1 HFRM0 HFX)).
unfold sa_M9m, sa_core, sa_postQ. cbv zeta.
fold sp0. fold s1.
split.
- (* the journal, the saved registers, the frame's flag and the kept registers *)
  split; [eapply ajournal_mono_k; [exact HJ4 | lia]|].
  split; [exact HFRM4|].
  split.
  { rewrite HFeq, HFLeq. change (fs_frame_bytes 1) with 128.
    rewrite (rdword_ext (rdW Wc (ms_mem ms2)) (rdW W4 mem4) (F + 128 - 8));
      [|intros k Hk; apply KEEPF; lia].
    rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms2)) (F + 128 - 8)); [|intros k Hk; apply K2].
    change (fs_frame_bytes 1) with 128 in HFLG. fold F in HFLG. exact HFLG. }
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
  exists (fst (sup_add_m R uri id placement client)), O', p2.
  split; [apply surjective_pairing|].
  split; [exact HO10|].
  split; [exact HO4096|].
  split; [exact HREP4|].
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [exact G5|]. split; [exact G6|].
  split; [exact HSTR4|].
  split; [clear - HBB4 HA5 HLIVEle; lia|].
  eapply mle_weaken; [exact MTL | eapply mle_station; [exact MTL | exact HMO6 | exact HMO4] | exact HXMle].
Qed.
End e.
End f.
End d.
