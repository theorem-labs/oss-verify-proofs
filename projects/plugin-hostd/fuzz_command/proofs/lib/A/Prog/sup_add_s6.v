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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 585 of its 628 lines of code are new or changed and 369 lines of the source are left out. *)
(* sup_add's walk on the ASan build of plugin-hostd/fuzz_command, stage M3b (0x8a0b8) to M4 (0x8a0c4): the call of
   the snprintf wrapper on (buf, 32, "resp %d", v), a0 := buf, the call of hand_back on buf.

   The snprintf wrapper is the stream's shared contract (RtFormat.v's asnprintf_realizes = RtPFCmd.v's
   asnprintf_sh, window CMD_SNP_K), applied as in the pass-4/5 re-fit's printf call step: its read-only words by
   CmdRecImg.v's cmd_consts_view_snp, its post in art form by PaFx.v's srr_art_postF_of_pf, the journal step by
   PaFx.v's aj_art_own_atF (the destination is the 32-byte buffer of sup_add's own side-stack frame: a byte the
   walk's journal may write, awr_byte's in_frames case, lib/Reusable/YCbq.v:510-515). The wrapper returns at some FP
   state fx3 with fxrel fx fx3; the rest of the stage runs in place at fx3: the symbolic state
   carried to fx3 by PaFx.v's st_ok_restrict_xfx, the executor and hand_back's contract taken at fx3. The format
   "resp %d" (0x21d00, CmdRo.v RO_lit_21d00) is read from cmd_ro_ok (cmd_ro_ok_of_aro at the call); its shadow
   comes from cmd_aread_ok_chk on the record's checks cmd_addr_b / cmd_hull_b of (0x21d00, 8). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaNoChain PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdChk CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtPFShared RtPFSx RtPFCmd RtPFDog.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require PaLibH.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module RA := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.RecAns.

(* the symbolic state at 0x8a0b8: every register its own atom, atom 32 the shadow base; no region (the three
   instructions this stage runs touch no memory) and no inline check *)
Definition s6_SB : Z := 0x7fff8000.
Definition s6_Bx : sv := SOff 32 0.
Definition s6_facts : facts := mkFacts [ (32%nat, mkAF s6_SB s6_SB 0) ] [] [].
Definition ss_s6 : sstate := mkSS L_M3b sr_atoms [] None s6_facts.
Definition s6_Bspan : Z * Z := (s6_SB, s6_SB + 2 ^ 44 - 1).
Definition s6_extra : list word := [Z_to_bv 64 s6_SB].
Lemma s6_ro_end : In 0x21d07 cmd_ro_ends.
Proof. unfold cmd_ro_ends. repeat (first [left; reflexivity | right]). Qed.
(* hand_back's footprint filters the recorder's blocks with a boolean predicate through stdpp's filter; this is the
   membership direction the walk needs (the form of hand_back.v's hb_filter_in) *)
Lemma sa_s6_filter_in : forall (f : Z * Z -> bool) (pn : Z * Z) (l : list (Z * Z)),
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
Definition s6_E (regs : bvmap 5 word) : env := Eimg (Ereg regs s6_extra).
Lemma s6_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem,
st_ok_pi SEGS VAL (s6_E regs) ss_s6 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L_M3b)) mem (seg_rom SEGS)))
/\ sh_ok SEGS s6_Bx [] (s6_E regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem.
set (E := s6_E regs).
assert (E32 : ew E 32 = Z_to_bv 64 s6_SB).
{ subst E. unfold s6_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
split.
- unfold ss_s6. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold s6_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. first [exact I | repeat split].
  + split; [|split; [exact I | exact I]].
    cbn [s6_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, unsigned_lit_small by (unfold s6_SB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. unfold s6_SB.
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
Let cif_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a :=
  CmdRecBase.cif_relro_img _ _ IMG.
Let cif_prog_not_ro : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a :=
  CmdRecBase.cif_prog_not_ro _ _ IMG.
Let cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI) :=
  CmdRecRo.cmd_ro_in_img SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let cmd_tail_vis_at : forall ly S (W : world SEGS) mem md e, AR SEGS B ly S W mem md -> In e cmd_ro_ends ->
  atail_vis SEGS W mem e :=
  CmdRecRo.cmd_tail_vis_at SEGS B LAWS HB IMG.
Let cmd_rec_cells : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  rdW W mem 0xae8d5 = Some 1 /\ aguard_ok SEGS W mem 0xa7098 0x6045d8 /\ exists ev, rd32 (rdW W mem) (as_errno B) ev :=
  CmdRecCells.cmd_rec_cells SEGS B LAWS HB IMG.
Let cmd_aread_ok_chk : forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md ->
  cmd_addr_b a n = true -> cmd_hull_b a n = true ->
  range_addressable (rdW W mem) SHADOW_OFF a n /\ shadow_hull_vis (rdW W mem) a n :=
  CmdRecBase.cmd_aread_ok_chk SEGS B LAWS HB.
(* the rounding mode at this stage's FP state: the snprintf wrapper's premise *)
Hypothesis FXR : frm0 fx.
(* the statement's own (sup_add_c.v:92, :95) *)
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Let RUN := paj_run B LAWS.

(* the two fields of rec_repA_fields this stage uses, in a shape that does not depend on the argument list the
   shared lemma gets when its section closes *)
Lemma sa_s6_answer : forall ly S rd R O, rec_repA B ly S rd R O ->
  exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists n, In (old, n) O).
Proof. intros ly S rd R O H. eapply proj1. do 6 (eapply proj2). eapply rec_repA_fields; eassumption. Qed.
Lemma sa_s6_owned : forall ly S rd R O, rec_repA B ly S rd R O ->
  forall pn, In pn O -> In pn (ablocks B ly S) /\ 1 <= snd pn.
Proof.
intros ly S rd R O H pn Hpn.
assert (HH : forall pn, In pn O -> In pn (ablocks B ly S) /\ 1 <= snd pn /\
  iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE).
{ do 8 (eapply proj2). eapply rec_repA_fields; eassumption. }
destruct (HH pn Hpn) as (H1 & H2 & _). exact (conj H1 H2).
Qed.

(* the snprintf wrapper returns at some FP state fx3 (with fxrel fx fx3), and M4 is reached at fx3: this stage takes
   M4's statement at every FP state with rounding mode 0 *)
Lemma sa_m3b_ok : (forall fx1 : YK11.FPState, frm0 fx1 -> SA_M4_stmt (fx := fx1) B MT) -> SA_M3b_stmt B MT.
Proof.
intros M4. unfold SA_M3b_stmt.
intros ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCX HM.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO.
pose proof pa_B_ok as (HBa & HBb & HBc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS1 : 3 * ESTACK + 176 <= SUP_ADD_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (WS2 : HAND_BACK_STK + 176 <= SUP_ADD_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (WS3 : 0 <= HAND_BACK_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (WS4 : SUP_ADD_STK <= 65536) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof HCX as HCXs.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & Hfr & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT & HC &
  HCT & HREP & Hev & Hlive & MOK).
unfold sa_M3bm, sa_core in HM. cbv zeta in HM.
destruct HM as ((HJ & HFRM & HS16 & HS24 & HS48 & HFLG & Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q21 & Q25 & Q26) &
  Ha0 & Ha1 & Ha2 & Hs4 & HBUF & v & R2 & O3 & HARM & HREP2 & HACCT & HMO3).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (sp0 := spZ regs) in *.
set (s1 := sa_s1 sp0) in *.
set (F := frame_addr lyc 1 pos) in *.
assert (Hs1 : s1 = sp0 - 160 \/ s1 = sp0 - 176) by (clear - Hal16; unfold s1, sa_s1; Z.div_mod_to_equations; lia).
assert (Hs1al : s1 mod 32 = 0) by (clear - Hal16; unfold s1, sa_s1; Z.div_mod_to_equations; lia).
assert (Hal1 : (s1 - sp0) mod 16 = 0).
{ destruct Hs1 as [E1 | E1]; rewrite E1;
  [replace (sp0 - 160 - sp0) with (-160) by lia | replace (sp0 - 176 - sp0) with (-176) by lia]; reflexivity. }
pose proof HJ as (HARc & Hlyc & Hsecsc & Hwlec & Hioc & Hfrsc & Hnevc & Hkc & JF1 & JF2 & JF3 & JF4 & JGone & JPres & JStk & JF5 & JQT).
assert (HFin : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HARc HFin) as (HF32 & HFapp & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc HFin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFapp, HFceil. fold F in HF32, HFapp, HF4096, HFceil.
set (T := RA.RESP_HEAD ++ PF.pf_dec v).
assert (Hv : -2 ^ 31 <= v < 2 ^ 31) by (destruct HARM as [(-> & _) | (-> & ? & _)]; lia).
pose proof (RA.resp_len v Hv) as HTlen. fold T in HTlen.
(* ---- the seed at 0x8a0b8 ---- *)
destruct (s6_seed Wc regs1 memc) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (s6_E regs1)) by (unfold s6_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (s6_E regs1) n = ew (Ereg regs1 s6_extra) n)
  by (intros n Hn; unfold s6_E; apply Eimg_low; exact Hn).
assert (HED : ed (s6_E regs1) = ed (Ereg regs1 s6_extra)) by reflexivity.
remember (s6_E regs1) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HAE : env_agree 32 (Ereg regs1 s6_extra) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
clear HE EL HED.
(* 0x8a0b8: jal to the snprintf wrapper *)
paj_run_tok RUN HS HJ SHOK s6_Bspan.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (md1 := m) in *; clearbody md1 end.
rename ms into ms1.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
assert (HB1 : alloc_ceiling + SUP_ADD_STK <= sp0) by lia.
assert (HB2 : sp0 <= 2 ^ 47) by lia.
assert (HspT : spZ (ms_regs ms1) = sp0 + (s1 - sp0)).
{ unfold spZ at 1. rewrite P2, (EEo 2%nat 2%bv eq_refl), Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (P3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, (EEo 3%nat 3%bv eq_refl); exact Q3).
assert (P4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, (EEo 4%nat 4%bv eq_refl); exact Q4).
assert (P10' : getr (ms_regs ms1) 10 = w64 (F + 32)) by (rewrite P10, (EEo 10%nat 10%bv eq_refl); exact Ha0).
assert (P11' : getr (ms_regs ms1) 11 = w64 32) by (rewrite P11, (EEo 11%nat 11%bv eq_refl); exact Ha1).
assert (P12' : getr (ms_regs ms1) 12 = w64 0x21d00) by (rewrite P12, (EEo 12%nat 12%bv eq_refl); exact Ha2).
assert (P13' : getr (ms_regs ms1) 13 = getr regs1 13) by (rewrite P13, (EEo 13%nat 13%bv eq_refl); reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* the state at the call: the record's view, the read-only bytes, the frame, the buffer's shadow *)
pose proof (proj1 HJ) as HAR1.
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms1)))
  by (eapply sa_aro_kept with (ly := ly) (S := S) (W := W) (mem := mem) (md := md); eassumption).
pose proof (cmd_ro_ok_of_aro _ _ _ _ _ HAR1 HROD1) as HRO1.
destruct (cmd_rec_cells _ _ _ _ _ HAR1) as (_ & HGUARD1 & _).
(* the format's shadow: the record's checks on (0x21d00, 8), computed *)
destruct (cmd_aread_ok_chk _ _ _ _ _ 0x21d00 8 HAR1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
  as [HFA HFH].
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR1 HFin) as (_ & _ & HFpres1 & _).
change (fs_frame_bytes 1) with 128 in HFpres1. fold F in HFpres1.
assert (HLIT : abytes_atR (rdW Wc (ms_mem ms1)) 0x21d00 RO_lit_21d00).
{ clear - HRO1. destruct HRO1 as [HRO1 _]. unfold cmd_ro_bytes in HRO1.
  repeat match type of HRO1 with
  | abytes_atR _ 0x21d00 _ /\ _ => exact (proj1 HRO1)
  | _ /\ _ => apply proj2 in HRO1
  end. }
assert (K1 : forall a, rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & _). vm_compute in Hin. destruct Hin. }
assert (HBUF1 : sa_buf0 (rdW Wc (ms_mem ms1)) F) by (intros i Hi; rewrite K1; exact (HBUF i Hi)).
(* 0x8a0b8: the snprintf wrapper writes "resp <v>" and its terminator into buf and returns at some FP state fx3 *)
assert (HSN : sn_bytes (32 - 1) T = T ++ [0]).
{ unfold sn_bytes. rewrite firstn_all2 by (change (Z.to_nat (32 - 1)) with 31%nat; lia). reflexivity. }
assert (Hw : sn_len (32 - 1) T = Z.of_nat (length T) + 1).
{ unfold sn_len. rewrite HSN, length_app. cbn [length]. lia. }
assert (HKs : CMD_SNP_K = 2 * ESTACK) by reflexivity.
assert (HFlo1 : F + 128 <= s1 - 3 * ESTACK) by lia.
destruct (ecall_pre_stk_at SEGS B CMD_SNP_K SUP_ADD_STK sp0 (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc
  (ms_mem ms1) md1 (sa_ev3 R) (ms_regs ms1) (s1 - sp0) HJ HspT Hal1 ltac:(lia) ltac:(lia) ltac:(lia) HraT P3' P4')
  as (HPRE1 & HSLO1 & HSCR1).
destruct HGUARD1 as (HG1 & cval & HG2).
(* the frame lies above the image's range (RtPFDog.v's pa_frame_above_img) *)
pose proof (pa_frame_above_img B lyc Sc Wc (ms_mem ms1) md1 1 pos HAR1 HFin) as HFhi. fold F in HFhi.
unfold CMD_IMG_HI in HFhi.
assert (HCR : forall r, In r CMD_SNP_CR -> CMD_IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= CMD_IMG_HI).
{ intros r Hr. pose proof (proj1 (forallb_forall _ _) cmd_snp_cr_img r Hr) as Hb. unfold in_cmd_img in Hb.
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia. }
unfold sa_final.
eapply srr_after_artF.
{ eapply (aj_art_own_atF SEGS B LAWS Hsegs CMD_SNP_K (fun a => F + 32 <= a < F + 32 + sn_len (32 - 1) T)
    (SIG CS___interceptor_trampoline_snprintf) Wc (ms_regs ms1) (ms_mem ms1) SUP_ADD_STK sp0 (sa_FP O) ly S W mem md
    [(1, pos)] lyc Sc md1 (sa_ev3 R) (s1 - sp0) _ _ HJ HspT Hal1 ltac:(lia) ltac:(lia) ltac:(lia) P1).
  - intros a Ha. right; right; right; left. exists 1, pos. split; [left; reflexivity|]. left.
    unfold in_zr; cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia.
  - eapply srr_art_postF_of_pf; [exact HSCR1|].
    apply (ASNPRINTF fx lyc Sc Wc (ms_regs ms1) (ms_mem ms1) md1 (F + 32) 32 0x21d00 []
      (map (argZ (ms_regs ms1)) [3; 4; 5; 6; 7] ++ []) T cval).
    + exact HPRE1.
    + exact HSLO1.
    + exact HSCR1.
    + exact P10'.
    + exact P11'.
    + exact P12'.
    + exact (cmd_consts_view_snp SEGS B LAWS HB IMG RLO RHI Wc (ms_mem ms1) HROD1).
    + apply Forall_forall. intros r Hr. destruct (HCR r Hr) as (CR1 & CR2 & CR3).
      unfold CMD_IMG_LO, CMD_IMG_HI in *. lia.
    + apply Forall_forall. intros r Hr. destruct (HCR r Hr) as (CR1 & CR2 & CR3).
      unfold CMD_IMG_LO, CMD_IMG_HI in *. apply Forall_snp. unfold zdisjoint. cbn [fst snd]. rewrite HspT, Hw. lia.
    + exact HG1.
    + exact HG2.
    + lia.
    + lia.
    + lia.
    + lia.
    + apply Forall_snp. unfold zdisjoint. cbn [fst snd]. rewrite HspT, Hw. lia.
    + apply Forall_snp. unfold zdisjoint. cbn [fst snd]. rewrite HspT, Hw. lia.
    + split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia.
    + cbn [length]. rewrite HspT. lia.
    + apply Forall_snp. unfold zdisjoint. cbn [fst snd length]. rewrite HspT, Hw. lia.
    + apply (FR_cmd_intro _ _ _ _ _ RA.RESP_FMT RA.RESP_PS [PF.AInt v]).
      * unfold fmt_at. change (Z.of_nat (length RA.RESP_FMT)) with 7.
        split; [lia|]. split.
        { intros i Hi. replace (0x21d00 + i) with (0x21d00 + Z.of_nat (Z.to_nat i)) by lia.
          rewrite (HLIT (Z.to_nat i) ltac:(change (length RO_lit_21d00) with 8%nat; lia)). f_equal.
          assert (Hk : (Z.to_nat i < 8)%nat) by lia. revert Hk. generalize (Z.to_nat i). intros k Hk'.
          do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
        split; [apply Forall_snp; unfold zdisjoint; cbn [fst snd]; rewrite HspT, Hw; lia|].
        split; [unfold amem_range; left; unfold kLowMemEnd; lia|].
        split; [exact HFA | exact HFH].
      * exact RA.resp_parse.
      * cbn [map app arg_of pf_args_asan pf_arg_asan]. split; [|exact I]. split; [exact Hv|].
        unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite P13'.
        destruct HARM as [(-> & _ & _ & Hr13) | (-> & _ & _ & _ & Hr13)]; rewrite Hr13; [|rewrite H11];
          unfold w64; apply RA.lit_mod32.
      * exact (RA.resp_text v).
      * vm_compute. exact I.
      * vm_compute; reflexivity.
    + lia.
    + lia.
    + lia.
    + rewrite Hw. lia.
    + apply pairwise_snp. unfold zdisjoint. cbn [fst snd]. rewrite HspT, Hw. lia.
    + intros a Ha. rewrite Hw in Ha. destruct (HFpres1 a ltac:(lia)) as [Hp Hno].
      split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|]. rewrite HspT. lia.
    + (* the destination's 8 bytes of band slack: buf + w + 8 <= F + 72 stays inside the 128-byte frame
         (measured: 56 bytes of room at 0x8a0b8), so the frame's band bound gives it *)
      rewrite Hw. exact (PaLibH.amem_range_sub_app F 128 (F + 32) (Z.of_nat (length T) + 1 + 8) HFapp HFceil
        ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros x Hx. rewrite Hw in Hx. exists 0. split; [|left; reflexivity].
      unfold shadow_of_addr.
      assert (Hi : 4 <= x / 8 - F / 8 < 8) by (clear - Hx HF32 HTlen; Z.div_mod_to_equations; lia).
      replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 4 + (x / 8 - F / 8 - 4)) by lia.
      apply HBUF1. lia.
    + rewrite Hw. exact (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc (ms_mem ms1) md1 1 pos (F + 32)
        (Z.of_nat (length T) + 1) HAR1 HFin ltac:(fold F; lia) ltac:(change (fs_frame_bytes 1) with 128; fold F; lia)
        ltac:(lia)).
    + exact (pa_dest_off_globals_frame B lyc Sc Wc (ms_mem ms1) md1 1 pos (F + 32) _ HAR1 HFin ltac:(fold F; lia)).
    + exact FXR. }
cbv beta. intros fx3 regs3 mem3 md3 Hfx3 (HJ3 & HP3 & (HQa & HQb) & HK3).
(* back at 0x8a0bc, at fx3: the symbolic state carried to fx3 (PaFx.v's st_ok_restrict_xfx) *)
pose proof (st_ok_restrict_xfx fx fx3 _ _ _ _ _ HS eq_refl) as HSf. clear HS. rename HSf into HS.
jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H Wc) mem3) HP3 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS. rewrite <- (restrict_mkst_fx (fx := fx3)) in HS2. rename HS2 into HS.
pose proof (paj_run (fx := fx3) B LAWS) as RUN3.
remember (havoc E 40 (map (getr regs3) CLOB)) as Ec eqn:HEc.
assert (HEI3 : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 40)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
clear HEc.
assert (SHOK3 : sh_ok SEGS s6_Bx [] Ec (mrestrict (w_H Wc) mem3)) by (unfold sh_ok; apply Forall_nil).
(* 0x8a0bc .. 0x8a0c0: a0 := s4 (buf), jal to hand_back *)
paj_run_tok RUN3 HS HJ3 SHOK3 s6_Bspan.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (md2 := m) in *; clearbody md2 end.
pmkst HS.
rename ms into ms2.
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (8%bv : bv 5) U8. prreg HS (9%bv : bv 5) U9. prreg HS (10%bv : bv 5) U10.
prreg HS (18%bv : bv 5) U18. prreg HS (19%bv : bv 5) U19. prreg HS (21%bv : bv 5) U21.
prreg HS (25%bv : bv 5) U25. prreg HS (26%bv : bv 5) U26.
assert (U2' : getr (ms_regs ms2) 2 = w64 s1) by (rewrite U2, OLD3 by lia; rewrite (EEo 2%nat 2%bv eq_refl); exact Q2).
assert (U3' : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite U3, OLD3 by lia; rewrite (EEo 3%nat 3%bv eq_refl); exact Q3).
assert (U4' : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite U4, OLD3 by lia; rewrite (EEo 4%nat 4%bv eq_refl); exact Q4).
assert (U8' : getr (ms_regs ms2) 8 = w64 sp0) by (rewrite U8, OLD3 by lia; rewrite (EEo 8%nat 8%bv eq_refl); exact Q8).
assert (U9' : getr (ms_regs ms2) 9 = w64 s1) by (rewrite U9, OLD3 by lia; rewrite (EEo 9%nat 9%bv eq_refl); exact Q9).
assert (U10' : getr (ms_regs ms2) 10 = w64 (F + 32)) by (rewrite U10, OLD3 by lia; rewrite (EEo 20%nat 20%bv eq_refl); exact Hs4).
assert (U18' : getr (ms_regs ms2) 18 = w64 F) by (rewrite U18, OLD3 by lia; rewrite (EEo 18%nat 18%bv eq_refl); exact Q18).
assert (U19' : getr (ms_regs ms2) 19 = getr regs 11) by (rewrite U19, OLD3 by lia; rewrite (EEo 19%nat 19%bv eq_refl); exact Q19).
assert (U21' : getr (ms_regs ms2) 21 = w64 A_G_REC) by (rewrite U21, OLD3 by lia; rewrite (EEo 21%nat 21%bv eq_refl); exact Q21).
assert (U25' : getr (ms_regs ms2) 25 = w64 (SHADOW_OFF + F / 8)) by (rewrite U25, OLD3 by lia; rewrite (EEo 25%nat 25%bv eq_refl); exact Q25).
assert (U26' : getr (ms_regs ms2) 26 = w64 F) by (rewrite U26, OLD3 by lia; rewrite (EEo 26%nat 26%bv eq_refl); exact Q26).
assert (HspT2 : spZ (ms_regs ms2) = sp0 + (s1 - sp0))
  by (unfold spZ at 1; rewrite U2'; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hs0 : s0Z (ms_regs ms2) = sp0)
  by (unfold s0Z; rewrite U8'; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
(* the memory of the hand_back call state, against the entry of this stage *)
assert (K2 : forall a, rdW Wc (ms_mem ms2) a = rdW Wc mem3 a).
{ intros a. unfold aview, mbyte. rewrite (HFr0 (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & _). vm_compute in Hin. destruct Hin. }
assert (HFlo : F + 128 <= s1 - 3 * ESTACK) by lia.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (s1 - 3 * ESTACK <= a < s1) -> ~ (F + 32 <= a < F + 64) ->
  rdW Wc (ms_mem ms2) a = rdW Wc memc a).
{ intros a Ha Hs Hb. rewrite K2, (HK3 a Ha ltac:(rewrite HKs; lia) ltac:(cbv beta; rewrite Hw; lia)), K1. reflexivity. }
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (HLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (HCEIL : ASAN_CEIL = alloc_ceiling) by reflexivity.
unfold in_app in HFapp. destruct HFapp as (HFa & HFb).
assert (HSH : forall i, 0 <= i < 16 -> 0 <= SHADOW_OFF + F / 8 + i < 2 ^ 64 /\
  ~ (s1 - 3 * ESTACK <= SHADOW_OFF + F / 8 + i < s1) /\ ~ (F + 32 <= SHADOW_OFF + F / 8 + i < F + 64)).
{ intros i Hi. destruct HFb as [Hlow | [Hh1 Hh2]]; repeat split; Z.div_mod_to_equations; lia. }
assert (HBUF2 : sa_buf0 (rdW Wc (ms_mem ms2)) F).
{ intros i Hi. destruct (HSH (4 + i) ltac:(lia)) as (G1 & G2 & G3).
  replace (SHADOW_OFF + F / 8 + 4 + i) with (SHADOW_OFF + F / 8 + (4 + i)) by lia.
  rewrite KEEP by assumption. replace (SHADOW_OFF + F / 8 + (4 + i)) with (SHADOW_OFF + F / 8 + 4 + i) by lia.
  exact (HBUF i Hi). }
(* the recorder's view at the hand_back call *)
destruct HACCT as (HA1 & HA2 & HA3 & HA4 & HA5).
assert (HINREC : forall a, in_rec a -> 0 <= a < 2 ^ 64 /\ ~ (s1 - 3 * ESTACK <= a < s1) /\ ~ (F + 32 <= a < F + 64)).
{ intros a Ha.
  assert (HPG : inFP cmd_PG a).
  { destruct Ha as [Ha | Ha]; [exists (A_G_REC, A_G_REC + 960) | exists (A_REC_SPILL, A_REC_SPILL + 56)];
    (split; [cbn [In cmd_PG]; tauto | cbn [fst snd]; unfold REC_SIZE, SC_SIZE in Ha; lia]). }
  pose proof (cif_prog_img a HPG) as Himg. pose proof (Hsegs a Himg) as Hlow. unfold kLowMemEnd in Hlow.
  split; [lia|]. split; [lia|]. intros Hc.
  destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HARc
    ltac:(right; left; exists 1, pos; split; [exact HFin | change (fs_frame_bytes 1) with 128; fold F; lia])) as (_ & Hni).
  exact (Hni Himg). }
assert (HINBLK : forall p n0 i, In (p, n0) O3 -> 0 <= i < n0 ->
  0 <= p + i < 2 ^ 64 /\ ~ (s1 - 3 * ESTACK <= p + i < s1) /\ ~ (F + 32 <= p + i < F + 64)).
{ intros p n0 i Hin Hi.
  pose proof (HA4 (p, n0) Hin) as Hbin.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n0 HARc Hbin) as (_ & H4096 & Hpce & _ & _ & _ & Hn0).
  pose proof (req_size_pos n0 ltac:(lia)) as [_ Hrq].
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n0 1 pos HARc Hbin HFin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. fold F in Hd.
  split; [lia|]. split; [lia|]. lia. }
assert (RK1 : forall a, in_rec a -> rdW Wc (ms_mem ms2) a = rdW Wc memc a).
{ intros a Ha. destruct (HINREC a Ha) as (G1 & G2 & G3). apply KEEP; assumption. }
assert (RK2 : forall p n0 i, In (p, n0) O3 -> 0 <= i < n0 -> rdW Wc (ms_mem ms2) (p + i) = rdW Wc memc (p + i)).
{ intros p n0 i Hin Hi. destruct (HINBLK p n0 i Hin Hi) as (G1 & G2 & G3). apply KEEP; assumption. }
assert (HREP2' : rec_repA B lyc Sc (rdW Wc (ms_mem ms2)) R2 O3) by (eapply rec_repA_kept; eassumption).
destruct (sa_s6_answer lyc Sc (rdW Wc (ms_mem ms2)) R2 O3 HREP2') as (old & Hold & Holdv).
(* the text the wrapper wrote, as hand_back's string argument *)
assert (HB3 : abytes_atR (rdW Wc mem3) (F + 32) (resp v ++ [Z_to_bv 8 0])).
{ intros i Hi. rewrite <- (RA.pf_resp v Hv) in Hi |- *. fold T in Hi |- *. unfold PF.pf_bytes in Hi |- *.
  rewrite length_app, length_map in Hi. cbn [length] in Hi.
  pose proof (HQb (Z.of_nat i) ltac:(rewrite Hw; lia)) as Hb. rewrite Nat2Z.id, HSN in Hb.
  rewrite Hb. destruct (aview_byte SEGS _ _ _ _ Hb) as (b & _ & _ & Hbr). f_equal.
  replace (map (Z_to_bv 8) T ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (T ++ [0])) by (rewrite map_app; reflexivity).
  rewrite (map_nth (Z_to_bv 8) (T ++ [0]) 0 i). rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity. }
assert (HSTRBUF : astr_atR (rdW Wc (ms_mem ms2)) (F + 32) (resp v)).
{ split; [|exact (resp_no0 v)]. intros i Hi. rewrite K2. exact (HB3 i Hi). }
pose proof (resp_length v Hv) as HRL.
(* hand_back's budgets *)
assert (HEVle : sa_ev3 R + EV_HAND_BACK <= EV_SUP_ADD R).
{ unfold EV_SUP_ADD, sa_ev3, sa_ev2, sa_ev1. pose proof (Z.le_max_r EV_ANSWER EV_HAND_BACK). lia. }
assert (HMODEL : sup_add_m R uri id placement client = hand_back R2 (resp v)).
{ unfold sup_add_m, sa_A in *. cbv zeta.
  destruct HARM as [(-> & Hb & -> & _) | (-> & Hr & Hrf & -> & _)].
  - rewrite Hb. reflexivity.
  - replace ((id <? 0) || (10000 <=? id))%bool with false
      by (symmetry; apply orb_false_intro; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
    rewrite Hrf. cbn [Z.eqb negb]. reflexivity. }
rewrite HMODEL in Hlive, MOK. cbn [hand_back fst snd] in Hlive, MOK.
assert (HLIVEle : sa_live3 uri id placement client + LIVE_HAND_BACK (resp v) <=
  LIVE_SUP_ADD uri id placement client (resp v)).
{ unfold LIVE_SUP_ADD, sa_live3, sa_live2.
  pose proof (Z.le_max_r (LIVE_ANSWER (resp v)) (LIVE_HAND_BACK (resp v))). lia. }
assert (HXMle : sa_acc3 MT R uri id placement client + XM_HAND_BACK MT (resp v) <=
  XM_SUP_ADD MT R uri id placement client (resp v)).
{ unfold XM_SUP_ADD, sa_acc3, sa_acc2, sa_acc1.
  pose proof (Z.le_max_r (XM_ANSWER MT (resp v)) (XM_HAND_BACK MT (resp v))). lia. }
assert (HXMnn : 0 <= XM_HAND_BACK MT (resp v)).
{ unfold XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg _ MTL).
  pose proof (mo_malloc_nonneg _ MTL (Z.of_nat (length (resp v)) + 1) ltac:(lia)). lia. }
assert (HMOB : mo_ok MT Sc (XM_HAND_BACK MT (resp v)))
  by (exact (mok_station MT S Sc _ _ _ MTL MOK HMO3 HXMnn HXMle)).
pose proof HJ3 as (HARc2 & _ & _ & _ & _ & Hfrsc2 & Hnevc2 & _).
assert (HEVB : st_nev Sc + EV_HAND_BACK <= EV_MAX) by lia.
assert (HLIVEB : blocks_bytes Sc + LIVE_HAND_BACK (resp v) <= LIVE_MAX) by lia.
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms2)))
  by (eapply sa_aro_kept with (ly := ly) (S := S) (W := W) (mem := mem) (md := md); eassumption).
(* the frame object of the buffer *)
assert (HFOBJ : afobj SEGS B lyc Sc Wc (ms_mem ms2) (F + 32) (Z.of_nat (length (resp v)) + 1)).
{ split.
  - exists 1, pos. split; [exact HFin|]. split; [lia|].
    split; [fold F; Z.div_mod_to_equations; lia|].
    split; [fold F; lia | change (fs_frame_bytes 1) with 128; fold F; lia].
  - split; [Z.div_mod_to_equations; lia|].
    intros x Hx. exists 0. split; [|left; reflexivity].
    unfold shadow_of_addr.
    assert (Hi : 4 <= x / 8 - F / 8 < 8) by (clear - Hx HF32 HRL; Z.div_mod_to_equations; lia).
    replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 4 + (x / 8 - F / 8 - 4)) by lia.
    apply HBUF2. lia. }
(* hand_back's footprint and the frame chain *)
assert (HFP1lo : forall a, inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8)
  :: ablocks_fp (filter (fun pn => fst pn =? old) O3)) a -> a < alloc_ceiling).
{ intros a Ha. apply inFP_cons in Ha as [Hans | Hblk].
  - unfold A_G_REC, OFF_ANSWER in Hans. lia.
  - destruct (inFP_ablocks_fp_inv _ a Hblk) as (p & n0 & Hpn & Hr).
    destruct (sa_s6_filter_in _ _ _ Hpn) as [Hino3 _].
    destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 p n0 HARc2 (HA4 (p, n0) Hino3)) as (_ & _ & Hpce & _).
    lia. }
assert (HFP1F : forall a, F <= a < F + 128 -> ~ inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8)
  :: ablocks_fp (filter (fun pn => fst pn =? old) O3)) a).
{ intros a Ha Hfp. apply inFP_cons in Hfp as [Hans | Hblk].
  - assert (HPG : inFP cmd_PG a)
      by (exists (A_G_REC, A_G_REC + 960); split; [cbn [In cmd_PG]; tauto | cbn [fst snd]; unfold OFF_ANSWER in Hans; lia]).
    destruct (al_client_img _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 a HARc2
      ltac:(right; left; exists 1, pos; split; [exact HFin | change (fs_frame_bytes 1) with 128; fold F; lia])) as (_ & Hni).
    exact (Hni (cif_prog_img a HPG)).
  - destruct (inFP_ablocks_fp_inv _ a Hblk) as (p & n0 & Hpn & Hr).
    destruct (sa_s6_filter_in _ _ _ Hpn) as [Hino3 _].
    pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc (ms_mem ms2) md2 p n0 1 pos HARc2 (HA4 (p, n0) Hino3) HFin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. fold F in Hd. lia. }
assert (HFRM2 : sa_frame (rdW Wc (ms_mem ms2)) sp0 regs).
{ intros j r Hj k Hk.
  assert (Hjlt : (j < 13)%nat)
    by (change 13%nat with (length sa_saved); apply nth_error_Some; rewrite Hj; discriminate).
  rewrite KEEP by lia. exact (HFRM j r Hj k Hk). }
assert (HCH : exists ch1, achain lyc (rdW Wc (ms_mem ms2)) (sa_s1 (spZ regs)) (spZ regs) ch1)
  by (eapply sa_achain with (ly := ly) (S := S) (W := W) (mem := mem) (md := md); eassumption).
destruct HCH as (ch1 & Hch1).
(* hand_back's word arguments: buf in the frame, old 0 or a live block's start *)
assert (HsR : 0 <= F + 32 < 2 ^ 64) by lia.
assert (HoldR : 0 <= old < 2 ^ 64).
{ destruct Holdv as [-> | (n0 & Hino3)]; [lia|].
  destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 old n0 HARc2 (HA4 (old, n0) Hino3))
    as (_ & H4096 & Hpc0 & _ & _ & _ & Hn0).
  pose proof (req_size_pos n0 ltac:(lia)) as [Hrq _]. lia. }
assert (Hsig : SIG CS_hand_back = BASE + AF_hand_back).
{ rewrite (SIGP CS_hand_back ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])));
  try (f_equal; vm_compute; reflexivity). }
(* 0x8a0c0: hand_back(buf) *)
eapply SRr_bind.
{ eapply (cl_callS_wide (fx := fx3) B LAWS) with (STK1 := HAND_BACK_STK)
    (FP1 := ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8)
             :: ablocks_fp (filter (fun pn => fst pn =? old) O3)))
    (EV1 := EV_HAND_BACK) (o := s1 - sp0) (ch1 := ch1).
  - exact HJ3.
  - exact HspT2.
  - exact Hal1.
  - lia.
  - unfold HAND_BACK_STK. pose proof (Z.le_max_l ASTACK XSTRDUP_STK). unfold ASTACK in *. lia.
  - lia.
  - exact U3'.
  - exact U4'.
  - reflexivity.
  - rewrite U1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite U1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - replace (sp0 + (s1 - sp0)) with s1 by lia. rewrite Hs0. exact Hch1.
  - intros HFN. eapply SRr_mono.
    { rewrite Hsig.
      apply (THAND_BACK fx3 lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 ch1 (F + 32) old (resp v) R2 O3
        HFN HROD2 U10' HsR HSTRBUF ltac:(unfold LMAX; lia) HFOBJ HREP2' Hold HoldR HEVB HLIVEB HMOB). }
    cbv beta. intros W' c' _ Hpost.
    destruct Hpost as (ly' & S' & regs' & mem' & md' & Hc' & HJx & HPx & HQx).
    exists ly', S', regs', mem', md'.
    split; [exact Hc'|]. split; [exact HJx|]. split; [exact HPx | exact HQx].
  - intros a Ha. apply inFP_cons in Ha as [Hans | Hblk].
    + right; right; right; right. left.
      assert (HPG : inFP cmd_PG a)
        by (exists (A_G_REC, A_G_REC + 960); split; [cbn [In cmd_PG]; tauto | cbn [fst snd]; unfold OFF_ANSWER in Hans; lia]).
      split; [|split; [eapply sa_HPROG; eassumption | exact (cif_prog_img a HPG)]].
      exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8).
      split; [unfold sa_FP; cbn [In]; tauto | cbn [fst snd]; unfold OFF_CALLS, OFF_ANSWER in *; lia].
    + destruct (inFP_ablocks_fp_inv _ a Hblk) as (p & n0 & Hpn & Hr).
      destruct (sa_s6_filter_in _ _ _ Hpn) as [Hino3 _].
      destruct (HA1 (p, n0) Hino3) as [HinO | Hnot].
      * right; left. split.
        -- exists (p, p + req_size n0). split; [|cbn [fst snd]; lia].
           unfold sa_FP. cbn [In]. right; right; right; right.
           apply in_map_iff. exists (p, n0). split; [reflexivity | exact HinO].
        -- exists p, n0. split; [exact (HA4 (p, n0) Hino3) | exact Hr].
      * right; right. left. exists p, n0. split; [exact (HA4 (p, n0) Hino3) | split; [exact Hnot | exact Hr]].
  - intros ly2 S2 W2 regs2 mem2 md5 _ a Ha Hwin _. exfalso. pose proof (HFP1lo a Ha). lia. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJ4i & HP4 & HK4).
cbn [hand_back fst snd] in HK4.
destruct HK4 as (p1 & p2 & O' & HO10 & HO4096 & HOne & HFRESH & HBiff & HREP4 & HOiff & HSTR4 & HBB4 & HMO4).
(* the facts the epilogue stage asks at 0x8a0c4 *)
destruct (al_layout _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 ly4 HARc2 (proj1 (proj2 HJ4i))) as (Habl4 & Hfa & Hown4).
assert (HFeq : frame_addr ly4 1 pos = F) by (rewrite (Hfa 1 pos); reflexivity).
assert (HlyF : ly_F ly4 = ly_F lyc) by (pose proof (Hfa 1 pos) as HH; unfold frame_addr in HH; lia).
assert (HFLeq : flag_addr ly4 1 pos = flag_addr lyc 1 pos) by (unfold flag_addr; rewrite HlyF; reflexivity).
assert (KEEP4 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (s1 - HAND_BACK_STK <= a < s1) ->
  rdW W4 mem4 a = rdW Wc (ms_mem ms2) a).
{ intros a Ha Hwin. pose proof HJ4i as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
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
   start of one of the recorder's current blocks O3, and two live blocks with one start are one block *)
assert (HKEPT : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc) /\ fst pn <> old).
{ intros pn Hin Hnin. split; [exact (HA3 pn Hin Hnin)|].
  destruct pn as [pp0 pn0]. cbn [fst]. intros Heqold. subst pp0.
  destruct Holdv as [Hold0 | (n0 & Hino3)].
  - destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 old pn0 HARc2 (HA3 _ Hin Hnin)) as (_ & H4096 & _).
    lia.
  - assert (Heq : pn0 = n0)
      by (apply (HSTARTc old); [exact (HA3 _ Hin Hnin) | exact (HA4 (old, n0) Hino3)]).
    subst pn0. destruct (HA1 (old, n0) Hino3) as [HL | HR]; [exact (Hnin HL) | exact (HR Hin)]. }
rewrite U1. change (Z_to_bv 64 (BASE + 15328)) with (Z_to_bv 64 (BASE + L_M4)).
apply (M4 fx3 (fxrel_frm0 fx fx3 FXR Hfx3) ly S W regs mem md ch pu id pp pc uri placement client R O ly4 S4 W4
  regs4 mem4 md4 pos HCXs).
unfold sa_M4m, sa_core, sa_postQ. cbv zeta. rewrite HMODEL. cbn [hand_back fst snd].
fold sp0. fold s1.
assert (HPR : forall r : Z, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr (ms_regs ms2) (Z_to_bv 5 r)) by exact HP4.
split.
- (* the journal, the saved registers, the spills, the frame's flag and the kept registers *)
  split; [eapply ajournal_mono_k; [exact HJ4 | lia]|].
  split.
  { intros j r Hj k Hk.
    assert (Hjlt : (j < 13)%nat)
      by (change 13%nat with (length sa_saved); apply nth_error_Some; rewrite Hj; discriminate).
    rewrite KEEP4 by lia. exact (HFRM2 j r Hj k Hk). }
  split; [intros k Hk; rewrite KEEP4 by lia; rewrite KEEP by lia; exact (HS16 k Hk)|].
  split; [intros k Hk; rewrite KEEP4 by lia; rewrite KEEP by lia; exact (HS24 k Hk)|].
  split.
  { intros k Hk. rewrite KEEP4 by lia. rewrite KEEP by lia. rewrite HFeq. exact (HS48 k Hk). }
  split.
  { rewrite HFeq, HFLeq. change (fs_frame_bytes 1) with 128.
    rewrite (rdword_ext (rdW Wc (ms_mem ms2)) (rdW W4 mem4) (F + 128 - 8));
      [|intros k Hk; apply KEEPF; lia].
    rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms2)) (F + 128 - 8));
      [|intros k Hk; apply KEEP; lia].
    change (fs_frame_bytes 1) with 128 in HFLG. exact HFLG. }
  split; [exact (eq_trans (HPR 2 ltac:(unfold acallee_saved; lia)) U2')|].
  split; [exact (eq_trans (HPR 3 ltac:(unfold acallee_saved; lia)) U3')|].
  split; [exact (eq_trans (HPR 4 ltac:(unfold acallee_saved; lia)) U4')|].
  split; [exact (eq_trans (HPR 8 ltac:(unfold acallee_saved; lia)) U8')|].
  split; [exact (eq_trans (HPR 9 ltac:(unfold acallee_saved; lia)) U9')|].
  split; [rewrite HFeq; exact (eq_trans (HPR 18 ltac:(unfold acallee_saved; lia)) U18')|].
  split; [exact (eq_trans (HPR 19 ltac:(unfold acallee_saved; lia)) U19')|].
  split; [exact (eq_trans (HPR 21 ltac:(unfold acallee_saved; lia)) U21')|].
  split; [rewrite HFeq; exact (eq_trans (HPR 25 ltac:(unfold acallee_saved; lia)) U25')
         |rewrite HFeq; exact (eq_trans (HPR 26 ltac:(unfold acallee_saved; lia)) U26')].
- (* what the call leaves *)
  exists (set_answer R2 (Some (resp v))), O', p2.
  split; [reflexivity|].
  split; [exact HO10|].
  split; [exact HO4096|].
  split; [exact HREP4|].
  split.
  { intros pn Hpn. apply HOiff in Hpn. destruct Hpn as [[Hpn3 _] | ->]; [exact (HA1 pn Hpn3)|].
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
    assert (Hin4 : In (p2, mq) (ablocks B ly4 S4)) by (exact (proj1 (sa_s6_owned _ _ _ _ _ HREP4 (p2, mq) Hino'))).
    assert (Hin4' : In (p2, Z.of_nat (length (resp v)) + 1) (ablocks B ly4 S4))
      by (apply HBiff; right; right; reflexivity).
    assert (Hmq : mq = Z.of_nat (length (resp v)) + 1) by (exact (HSTART4 p2 mq _ Hin4 Hin4')).
    subst mq. apply HOiff in Hino'. destruct Hino' as [[Hino3 Hne] | Heq];
      [exact (proj2 (HFRESH _ (HA4 _ Hino3) Hne) eq_refl) | apply HOne; congruence]. }
  split; [exact HSTR4|].
  split; [clear - HBB4 HA5 HLIVEle; lia|].
  eapply mle_weaken; [exact MTL | eapply mle_station; [exact MTL | exact HMO3 | exact HMO4] | exact HXMle].
Qed.
End e.
End f.
End d.
