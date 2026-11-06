(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the second segment of check_reply's walk (fuzz_command.asan, 0x86d78), from the
   memchr call 0x86ef8 to the return of sup_reply_code 0x86f18, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close's call steps: cl_callS, the state
   after the return) at c8557374ad2e.

   The pieces: 0x86ef8 jal memchr (the reply holds no NUL, so the wrapper returns 0: the not-found contract
   through PaArt.v's aj_art_at); 0x86efc bnez a0 (not taken); 0x86f00 mv a0,s3; 0x86f04 jal check_reply_answer
   (cl_callS); 0x86f08 the inline check of &g_rec.reply (a shadow entry of g_rec makes it a literal 0); 0x86f10
   ld a0,928(s9); 0x86f14 jal sup_reply_code (cl_callS), whose return point 0x86f18 is CR_CODE_stmt's.
   After each call the mid-walk invariant cr_mid and the registers cr_regs_at are rebuilt from the callee's journal
   (the frame (1, pos) is among the caller's frames, the saved registers lie above the callee's stack pointer, g_rec
   is a program static), and the walk is seeded again with check_reply_sd.v's cr_seed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s2.v, with its module paths and module names changed; 923 of its 964 lines of code are new or changed and 544 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_add_s5.v, with its module paths and module names changed; 409 of its 482 lines of code are new or changed and 891 lines of the source are left out. *)
(* sup_add's walk on the ASan build of plugin-hostd/fuzz_command, stage M0S: the spill arm of record()
   (0x89ee8 .. 0x89f48): rec_calls_free(&record.spill, 1), then c->fn := 0 and c->nargs := 0 on c = &record.spill. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YI16 YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaLibF PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- list facts ---- *)
Lemma s2s_nodup_pw : forall l : list (Z * Z),
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> (forall b, In b l -> 0 <= snd b) -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hp Hn; [apply List.NoDup_nil|].
cbn [map pairwise] in Hp. destruct Hp as [Hx Hp]. apply List.NoDup_cons.
- intros Hin. pose proof (req_size_pos (snd x) (Hn x (or_introl eq_refl))) as [H1 _].
  rewrite Forall_forall in Hx. specialize (Hx (fst x, req_size (snd x)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hx. cbn [fst snd] in Hx. lia.
- apply IH; [exact Hp | intros b Hb; apply Hn; right; exact Hb].
Qed.
Lemma s2s_nodup_app : forall {X} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros X l1. induction l1 as [|y l1 IH]; intros l2 x Hnd H1 H2; [destruct H1|].
cbn [app] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hy Hnd'].
destruct H1 as [<-|H1]; [apply Hy; apply in_or_app; right; exact H2 | exact (IH l2 x Hnd' H1 H2)].
Qed.

(* ---- the footprint rec_calls_free(&record.spill, 1) declares ---- *)
Lemma s2s_inFP_rcf : forall c P a, inFP (rcf_fp c [P]) a ->
  (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) \/ (exists b n, In (b, n) P /\ b <= a < b + req_size n).
Proof.
intros c P a (r & Hin & Hr). unfold rcf_fp in Hin. cbn [length seq map app concat] in Hin.
rewrite app_nil_r in Hin. destruct Hin as [<- | Hin].
- left. cbn [fst snd] in Hr. unfold CALL_SIZE, CALL_OFF_NARGS in *. lia.
- right. unfold ablocks_fp in Hin. apply in_map_iff in Hin as ([b n] & <- & Hin). cbn [fst snd] in Hr.
  exists b, n. split; [exact Hin | lia].
Qed.
(* an argument block of a recorded call is a live block of at least one byte *)
Lemma s2s_acall_blocks : forall bl rd a c P pn, acall_at bl rd a c P -> In pn P -> In pn bl /\ 1 <= snd pn.
Proof.
intros bl rd a c P pn (H1 & H2 & HL & H4 & H5 & H6 & H7) Hin. apply In_nth_error in Hin as (k & Hk).
assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; congruence).
destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
destruct (H7 k s pn Hs Hk) as (_ & _ & Hin & Hn & _). split; [exact Hin | lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Section f. Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* The symbolic states. Every register is its own atom (s4, atom 20, is the shadow base); the run to the call
   touches no memory; after the call s6 (atom 22) is &record.spill, whose first 8 bytes (fn, nargs) are the one
   writable region and whose 56 bytes are the one shadow entry. *)
Definition s2s_E (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Definition s2s_Bx : sv := SOff 20 0.
Definition s2s_rg : YP09.region := YP09.mkRegion (Some 22%nat) 0 8 0 8 [].
Definition s2s_facts : facts := mkFacts [(20%nat, mkAF SB SB 0); (22%nat, mkAF A_REC_SPILL A_REC_SPILL 3)] [] [].
Definition s2s_SH : list shent := [mkSHE 22 0 56].

Lemma s2s_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS VAL (s2s_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS s2s_Bx [] (s2s_E regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem pc. split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold s2s_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + cbn. exact I.
  + split; [exact I | split; exact I].
- unfold sh_ok. apply Forall_nil.
Qed.

Lemma s2s_E_reg : forall regs n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew (s2s_E regs) n = getr regs r.
Proof. intros regs n r Hn H. unfold s2s_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs [] n r H). Qed.
Lemma s2s_aval_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem SEGS (mrestrict H m) a n v -> aval_mem (aview SEGS H m) a n v.
Proof.
intros H m a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
assert (Hb : 0 <= le_byte v n k < 256) by (unfold le_byte; apply Z.mod_pos_bound; lia).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hb.
Qed.

Section e. Variable B : asyms. Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO. #[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.                    Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
Let cif_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a :=
  CmdRecBase.cif_relro_img _ _ IMG.
Let cif_prog_not_ro : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a :=
  CmdRecBase.cif_prog_not_ro _ _ IMG.
Let cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI) :=
  CmdRecRo.cmd_ro_in_img SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let cmd_tail_vis_at : forall ly S (W : world SEGS) mem md e, AR SEGS B ly S W mem md -> In e cmd_ro_ends ->
  atail_vis SEGS W mem e :=
  CmdRecRo.cmd_tail_vis_at SEGS B LAWS HB IMG.
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

Lemma s2s_spill_ra : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  range_addressable (rdW W mem) SHADOW_OFF A_REC_SPILL SC_SIZE.
Proof.
intros ly S W mem md HAR.
apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0)); unfold A_REC_SPILL, SC_SIZE; cbn [fst snd];
  [exact HAR | | reflexivity | reflexivity | lia | lia].
unfold Tfib_zero_shadow. cbn [In]. repeat (first [left; reflexivity | right]).
Qed.

Lemma s2s_seed1 : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md pc,
  AR SEGS B ly S W mem md -> getr regs 20 = w64 SHADOW_OFF -> getr regs 22 = w64 A_REC_SPILL ->
  st_ok_pi SEGS VAL (s2s_E regs) (mkSS pc sr_atoms [s2s_rg] None s2s_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS s2s_Bx s2s_SH (s2s_E regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md pc HAR H20 H22.
assert (E20 : ew (s2s_E regs) 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (s2s_E_reg regs 20 20%bv) by (first [lia | reflexivity]); exact H20).
assert (E22 : ew (s2s_E regs) 22 = Z_to_bv 64 A_REC_SPILL) by (rewrite (s2s_E_reg regs 22 22%bv) by (first [lia | reflexivity]); exact H22).
assert (U20 : U (s2s_E regs) (SOff 20 0) = SHADOW_OFF) by (apply U_atom; [exact E20 | unfold SHADOW_OFF; lia]).
assert (U22 : U (s2s_E regs) (SOff 22 0) = A_REC_SPILL) by (apply U_atom; [exact E22 | unfold A_REC_SPILL; lia]).
assert (B22 : base_val (s2s_E regs) (Some 22%nat) = A_REC_SPILL).
{ cbn [base_val]. rewrite E22. apply unsigned_lit_small. unfold A_REC_SPILL. lia. }
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold s2s_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold s2s_rg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B22.
    split; [unfold A_REC_SPILL; lia|]. split; [unfold A_REC_SPILL; lia|]. split; [|apply Forall_nil].
    intros o Ho. apply PRW. apply (sa_HPROG B HB LAWS).
    exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity | cbn [fst snd]; lia].
  + cbn. split; exact I.
  + split; [|split; exact I]. unfold s2s_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E20, E22, !unsigned_lit_small by (unfold SHADOW_OFF, A_REC_SPILL; lia).
    unfold SB, SHADOW_OFF, A_REC_SPILL. repeat split; first [exact I | reflexivity | lia].
- unfold sh_ok, s2s_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem (s2s_E regs) s2s_Bx 22 A_REC_SPILL SC_SIZE A_REC_SPILL 0 56
    (s2s_spill_ra ly S W mem md HAR)); [exact U20 | exact U22 | lia | unfold SC_SIZE; lia |].
  intros x Hx. unfold A_REC_SPILL, SHADOW_OFF in *. cbn [Z.min Z.max] in Hx. lia.
Qed.

(* the recorder's blocks: live, nonempty, apart from g_rec and record.spill (rec_repA_fields' last conjunct) *)
Lemma s2s_fields : forall ly S rd R O, rec_repA B ly S rd R O ->
  forall pn, In pn O -> In pn (ablocks B ly S) /\ 1 <= snd pn /\
     iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE.
Proof.
intros ly S rd R O H.
destruct (rec_repA_fields B HB LAWS ly S rd R O H) as (_ & _ & _ & _ & _ & _ & _ & _ & HF). exact HF.
Qed.
Lemma s2s_pres : forall (regs regs' : bvmap 5 word) (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> bv_unsigned r = z -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz Hr. pose proof (HP z Hz) as H. rewrite <- Hr, Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac s2s_in := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma sa_m0s_ok : SA_M1_stmt B MT -> SA_M0S_stmt B MT.
Proof.
intros M1S. unfold SA_M0S_stmt.
intros ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCX HM0 H16.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCX as (HPRE & Hfr & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT & HC &
  HCT & HREP & Hev & Hlive & MOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HM0 as (HCORE & R10 & R11 & R20 & R24 & HREPc & HACC & HMLE).
pose proof HCORE as (HJ & HFR & HV16 & HV24 & HV48 & HFLAG & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G21 & G25 & G26).
(* 0x89ee8 .. 0x89ef8: s6 := &record.spill, a1 := 1, a0 := s6, the call of rec_calls_free *)
destruct (s2s_seed0 Wc regs1 memc L_M0S) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (s2s_E regs1)) by (unfold s2s_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew (s2s_E regs1) n = getr regs1 rr)
  by (intros n rr Hn Hr; exact (s2s_E_reg regs1 n rr Hn Hr)).
remember (s2s_E regs1) as E eqn:HE.
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- context [with_vm_backing ?a ?b ?c] => set (md1 := with_vm_backing a b c) in *; clearbody md1 end.
assert (EM1 : ms_mem ms = memc).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hr & _). cbn in Hr. exact Hr. }
rewrite EM1 in HJ |- *.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (20%bv : bv 5) P20.
prreg HS (22%bv : bv 5) P22.
assert (HAE1 : env_agree 32 (Ereg regs1 []) E).
{ rewrite HE. split; [intros n Hn; unfold s2s_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
pose proof (regs_kept_of_st_ok SEGS E _ _ regs1 [] ([2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%bv) HS HAE1
  ltac:(vm_compute; reflexivity)) as KR1.
cbn [ms_regs restrict] in KR1.
rewrite (EEo 2%nat 2%bv) in P2 by (first [lia | reflexivity]). rewrite (EEo 3%nat 3%bv) in P3 by (first [lia | reflexivity]).
rewrite (EEo 4%nat 4%bv) in P4 by (first [lia | reflexivity]). rewrite (EEo 8%nat 8%bv) in P8 by (first [lia | reflexivity]).
rewrite (EEo 20%nat 20%bv) in P20 by (first [lia | reflexivity]).
assert (E292 : ew E 292 = Z_to_bv 64 A_REC_SPILL).
{ pose proof (HEI 292%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H.
  change (VAL 292%nat) with (VAL (A_OBJ 51)) in H. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)) in H.
  apply bv_eq. rewrite H. rewrite unsigned_lit_small by (unfold A_REC_SPILL; lia). vm_compute. reflexivity. }
rewrite E292 in P10, P22.
assert (SIGR : SIG CS_rec_calls_free = BASE + AF_rec_calls_free).
{ rewrite (SIGP CS_rec_calls_free) by (unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])).
  f_equal; try (vm_compute; reflexivity). }
(* the frame: s1 = sp0 - 160 or sp0 - 176 *)
assert (Hs1 : sa_s1 (spZ regs) = spZ regs - 160 \/ sa_s1 (spZ regs) = spZ regs - 176).
{ unfold sa_s1. Z.div_mod_to_equations. lia. }
assert (HspC : spZ (ms_regs ms) = spZ regs + (sa_s1 (spZ regs) - spZ regs)).
{ unfold spZ at 1. rewrite P2, G2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Ho16 : (sa_s1 (spZ regs) - spZ regs) mod 16 = 0).
{ destruct Hs1 as [Hq|Hq]; rewrite Hq;
  [replace (spZ regs - 160 - spZ regs) with (-160) by lia | replace (spZ regs - 176 - spZ regs) with (-176) by lia]; reflexivity. }
assert (Ho0 : sa_s1 (spZ regs) - spZ regs <= 0) by lia.
assert (Hk1 : 0 <= REC_CALLS_FREE_STK) by (unfold REC_CALLS_FREE_STK, ASTACK; lia).
assert (Hbud : REC_CALLS_FREE_STK - (sa_s1 (spZ regs) - spZ regs) <= SUP_ADD_STK) by (unfold SUP_ADD_STK; lia).
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3; exact G3).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4; exact G4).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
destruct (sa_achain B HB LAWS ly S W regs mem md ch R O [(1, pos)] lyc Sc Wc memc md1 0 HPRE HREP HJ HFR)
  as [ch1 HCH].
assert (HCH' : achain lyc (rdW Wc memc) (spZ regs + (sa_s1 (spZ regs) - spZ regs)) (s0Z (ms_regs ms)) ch1).
{ replace (spZ regs + (sa_s1 (spZ regs) - spZ regs)) with (sa_s1 (spZ regs)) by lia.
  replace (s0Z (ms_regs ms)) with (spZ regs); [exact HCH|].
  unfold s0Z. rewrite P8, G8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
(* the recorder at M0S and the spill's argument blocks *)
destruct HREPc as (Q & HAREP & HOQ).
pose proof HAREP as (Hgr8 & Hsc8 & Hapart & HCALLS & HANS & HREPLY & HSCAL & HOWN).
pose proof HCALLS as (Hlen16 & HlenQ & Hnc & Htab & HSPILL & HSPILLlen).
pose proof HSPILL as (Hfn & Hn6 & HlenP & Hfnv & Hnargs & HNDP & Hargs).
assert (Hrsf : rec_spill_frees R = Z.of_nat (length (l_spill Q))).
{ unfold rec_spill_frees. rewrite H16. replace (Nat.ltb 16 16) with false by reflexivity. rewrite HlenP. reflexivity. }
assert (HinO : forall pn, In pn (l_spill Q) -> In pn O).
{ intros pn Hpn. apply HOQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
(* rec_calls_free's premises *)
assert (HAROc : arodata_okP SEGS RLO RHI B (rdW Wc memc))
  by exact (sa_aro_kept B HB LAWS IMG
    SUP_ADD_STK (spZ regs) ly S W mem md [(1, pos)] lyc Sc Wc memc md1 0 R O HAR HJ HREP HROD).
assert (P10' : getr (ms_regs ms) 10 = w64 A_REC_SPILL) by exact P10.
assert (P11' : getr (ms_regs ms) 11 = w64 (Z.of_nat (length [l_spill Q]))) by exact P11.
assert (HHOME : rcf_home B lyc Sc Wc memc A_REC_SPILL (CALL_SIZE * Z.of_nat (length [l_spill Q]))).
{ right; left. unfold CALL_SIZE, SC_SIZE. cbn [length Z.of_nat]. lia. }
assert (HPS : forall i P, nth_error [l_spill Q] i = Some P ->
  (length P <= 6)%nat /\
  aval_mem (rdW Wc memc) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P)) /\
  forall a pn, nth_error P a = Some pn ->
    aval_mem (rdW Wc memc) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\
    In pn (ablocks B lyc Sc)).
{ intros i P Hi. destruct i as [|i]; [|destruct i; cbn in Hi; discriminate Hi]. cbn in Hi. injection Hi as <-.
  cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. split; [lia|]. split; [rewrite HlenP; exact Hnargs|].
  intros a pn Ha. assert (Hk : (a < length (snd (r_spill R)))%nat) by (rewrite <- HlenP; apply nth_error_Some; congruence).
  destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
  destruct (Hargs a s pn Hs Ha) as (Hv & _ & Hin & _ & _). split; [exact Hv | exact Hin]. }
assert (HND : NoDup (map fst (concat [l_spill Q]))) by (cbn [concat]; rewrite app_nil_r; exact HNDP).
assert (HEVc : st_nev Sc + EV_REC_CALLS_FREE [l_spill Q] <= EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). unfold EV_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r, <- Hrsf.
  unfold EV_SUP_ADD, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in Hev. clear - Hnev Hev. lia. }
assert (MX : forall x : list byte, 0 <= XM_XSTRDUP MT x) by (intros x; unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
pose proof (mo_free_nonneg MT MTL) as MF.
assert (HMOc : mo_ok MT Sc (XM_REC_CALLS_FREE MT [l_spill Q])).
{ apply (mok_station MT S Sc _ 0 _ MTL MOK HMLE).
  - unfold XM_REC_CALLS_FREE. apply Z.mul_nonneg_nonneg; lia.
  - unfold XM_REC_CALLS_FREE, XM_SUP_ADD, XM_ARG_I, XM_ANSWER, XM_HAND_BACK. cbn [concat]. rewrite app_nil_r, <- Hrsf.
    repeat match goal with |- context [XM_XSTRDUP MT ?x] =>
      lazymatch goal with _ : 0 <= XM_XSTRDUP MT x |- _ => fail | _ => pose proof (MX x) end end.
    lia. }
(* the call: rec_calls_free(&record.spill, 1), composed into the journal *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc (ms_regs ms) memc _ SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc Sc md1 0
    REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Q]) (EV_REC_CALLS_FREE [l_spill Q]) (sa_s1 (spZ regs) - spZ regs)
    (getr (ms_regs ms) 1) ch1 _ HJ HspC Ho16 Ho0 Hk1 Hbud P3' P4' eq_refl HraT Hra4T HCH').
  - intros HPRE1.
    pose proof (TREC_CALLS_FREE fx lyc Sc Wc (ms_regs ms) memc md1 ch1 A_REC_SPILL [l_spill Q] HPRE1 HAROc P10' P11'
      ltac:(cbn; lia) HHOME ltac:(unfold A_REC_SPILL; reflexivity) HPS HND HEVc HMOc) as HCL.
    unfold cfg_at in HCL. rewrite SIGR. unfold apost_base in HCL. exact HCL.
  - intros a Ha. destruct (s2s_inFP_rcf A_REC_SPILL (l_spill Q) a Ha) as [Hn | (b & n & Hbn & Hba)].
    + unfold awr_byte, awr_prog_or_caller. right; right; right; right; left.
      assert (HPG : inFP cmd_PG a).
      { exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity | cbn [fst snd]; unfold CALL_OFF_NARGS in Hn; lia]. }
      split; [|split; [exact (sa_HPROG B HB LAWS a HPG) | exact (cif_prog_img a HPG)]].
      exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE).
      split; [unfold sa_FP; right; right; right; left; reflexivity | cbn [fst snd]; unfold CALL_OFF_NARGS, SC_SIZE in *; lia].
    + unfold awr_byte. right; left. destruct (s2s_acall_blocks _ _ _ _ _ _ HSPILL Hbn) as [Hbl _]. split.
      * exists (b, b + req_size n). split; [|cbn [fst snd]; lia].
        unfold sa_FP. right; right; right; right. unfold ablocks_fp. apply in_map_iff. exists (b, n).
        split; [reflexivity | exact (HinO _ Hbn)].
      * exists b, n. split; [exact Hbl | lia].
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    destruct (s2s_inFP_rcf A_REC_SPILL (l_spill Q) a Ha) as [Hn | (b & n & Hbn & Hba)].
    + unfold CALL_OFF_NARGS, A_REC_SPILL in Hn. lia.
    + destruct (s2s_acall_blocks _ _ _ _ _ _ HSPILL Hbn) as [Hbl _].
      destruct (al_blocks _ _ LAWS lyc Sc Wc memc md1 b n (proj1 HJ) Hbl) as (_ & _ & Hbc & _). lia. }
cbv beta. intros W2 c2 HWLE (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & HK2).
destruct HK2 as (HPERM & HNARGS & HTAB & HLIVEK & HGC & HSPC & HOTHC & HBB2 & HMLE2).
clear HS SHOK HF HFr HG. rename HJ into HJ1.
(* back at 0x89efc: the jump to 0x89f1c, the two inline checks on c = &record.spill, c->fn := 0, c->nargs := 0 *)
assert (Q20 : getr regs2 20 = w64 SHADOW_OFF)
  by (rewrite (s2s_pres _ _ 20%bv 20 HP2 ltac:(unfold acallee_saved; lia) eq_refl), P20; exact R20).
assert (Q22 : getr regs2 22 = w64 A_REC_SPILL)
  by (rewrite (s2s_pres _ _ 22%bv 22 HP2 ltac:(unfold acallee_saved; lia) eq_refl), P22; reflexivity).
rewrite P1.
destruct (s2s_seed1 ly2 S2 W2 regs2 mem2 md2 14872 (proj1 HJ2) Q20 Q22) as [HS SHOK].
assert (HEI2 : img_env VAL A_LIM (s2s_E regs2)) by (unfold s2s_E; apply Eimg_env).
assert (EEo2 : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew (s2s_E regs2) n = getr regs2 rr)
  by (intros n rr Hn Hr; exact (s2s_E_reg regs2 n rr Hn Hr)).
assert (U22b : bv_unsigned (ew (s2s_E regs2) 22) = A_REC_SPILL).
{ rewrite (EEo2 22%nat 22%bv) by (first [lia | reflexivity]). rewrite Q22. unfold w64. apply unsigned_lit_small. unfold A_REC_SPILL; lia. }
remember (s2s_E regs2) as E2 eqn:HE2.
paj_run_to_tok RUNTO HS HJ2 SHOK Bspan 14948.
{ eapply (awr_ok_cons_gen B E2 s2s_rg []); [reflexivity | exact U22b | | apply awr_ok_nil].
  intros a Ha. unfold s2s_rg in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  assert (HPG : inFP cmd_PG a)
    by (exists (A_REC_SPILL, A_REC_SPILL + 56); split; [unfold cmd_PG; right; left; reflexivity | cbn [fst snd]; lia]).
  unfold awr_byte, awr_prog_or_caller. right; right; right; right; left.
  split; [|split; [exact (sa_HPROG B HB LAWS a HPG) | exact (cif_prog_img a HPG)]].
  exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE).
  split; [unfold sa_FP; right; right; right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE; lia]. }
pmkst HS.
lazymatch goal with |- context [with_vm_backing ?a ?b ?c] => set (md3 := with_vm_backing a b c) in *; clearbody md3 end.
(* 0x89f48: the registers *)
assert (HAE2 : env_agree 32 (Ereg regs2 []) E2).
{ rewrite HE2. split; [intros n Hn; unfold s2s_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
pose proof (regs_kept_of_st_ok_pi E2 _ _ regs2 [] ([2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26]%bv) HS HAE2
  ltac:(vm_compute; reflexivity)) as KR3.
cbn [ms_regs restrict] in KR3.
assert (KRX : forall r : bv 5, In r ([2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26]%bv) -> getr (ms_regs ms0) r = getr regs1 r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr];
    [ lazymatch goal with |- getr _ ?r = getr _ ?r =>
        let z := eval vm_compute in (bv_unsigned r) in
        rewrite (KR3 r ltac:(s2s_in));
        rewrite (s2s_pres _ _ r z HP2 ltac:(unfold acallee_saved; lia) eq_refl);
        apply KR1; s2s_in end |]).
  destruct Hr. }
assert (E20b : ew E2 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo2 20%nat 20%bv) by (first [lia | reflexivity]); exact Q20).
assert (E22b : ew E2 22 = Z_to_bv 64 A_REC_SPILL) by (rewrite (EEo2 22%nat 22%bv) by (first [lia | reflexivity]); exact Q22).
prreg HS (23%bv : bv 5) T23.
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  pose proof (st_ok_pi_restrict_reg (w_H W2) E2 ss ms0 27%bv HS) as T27;
  let e := eval vm_compute in (sr_get (ss_regs ss) 27%bv) in change (sr_get (ss_regs ss) 27%bv) with e in T27 end.
rewrite (denot_shx E2 22 20 4 A_REC_SPILL SHADOW_OFF E22b E20b) in T27 by (unfold A_REC_SPILL, SHADOW_OFF; lia).
(* the memory: [spill, spill + 8) holds fn = 0 and nargs = 0; every other byte is the post-call memory's *)
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 8) -> rdW W2 (ms_mem ms0) a = rdW W2 mem2 a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E2 _ (w_H W2) mem2 (ms_mem ms0) (fun a => A_REC_SPILL <= a < A_REC_SPILL + 8) HFr);
  [|exact Ha|exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq|[]]. injection Hq as <- <- <-.
  cbn [base_val] in Hrr. rewrite U22b in Hrr. lia. }
pose proof (st_ok_region_nth E2 _ _ 0 _ HS eq_refl) as RG3.
pose proof (field_of_region_any E2 _ 22 A_REC_SPILL _ 0 8 0 8 0 4 (SLit 0) RG3 U22b ltac:(right; left; reflexivity) ltac:(lia)) as V0.
pose proof (field_of_region_any E2 _ 22 A_REC_SPILL _ 0 8 0 8 4 4 (SLit 0) RG3 U22b ltac:(left; reflexivity) ltac:(lia)) as V4.
cbn [ms_mem restrict] in V0, V4. change (N.to_nat 4) with 4%nat in V0, V4.
replace (bv_unsigned (sv_denot E2 (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in V0, V4 by (vm_compute; reflexivity).
pose proof (s2s_aval_of_val _ _ _ _ _ V0) as A0. pose proof (s2s_aval_of_val _ _ _ _ _ V4) as A4.
rewrite Z.add_0_r in A0.
(* the recorder after rec_calls_free, then after the store of fn *)
pose proof (HSPC R Q HAREP eq_refl eq_refl) as HREP2.
set (O1 := concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) in HREP2.
assert (RD1 : forall a, in_rec a -> ~ (A_REC_SPILL + CALL_OFF_FN <= a < A_REC_SPILL + CALL_OFF_FN + 4) ->
  rdW W2 (ms_mem ms0) a = rdW W2 mem2 a).
{ intros a Hr Hn. unfold CALL_OFF_FN in Hn.
  assert (Hr' : 0 <= a < 2 ^ 64) by (unfold in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hr; lia).
  destruct (Z_lt_le_dec a (A_REC_SPILL + 4)) as [Hlo|Hlo]; [apply KEEP3; [exact Hr' | lia]|].
  destruct (Z_lt_le_dec a (A_REC_SPILL + 8)) as [Hhi|Hhi]; [|apply KEEP3; [exact Hr' | lia]].
  pose proof (A4 (Z.to_nat (a - (A_REC_SPILL + 4))) ltac:(lia)) as X1.
  pose proof (HNARGS 0%nat ltac:(cbn; lia) (Z.to_nat (a - (A_REC_SPILL + 4))) ltac:(lia)) as X2.
  replace (A_REC_SPILL + 4 + Z.of_nat (Z.to_nat (a - (A_REC_SPILL + 4)))) with a in X1 by lia.
  replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS + Z.of_nat (Z.to_nat (a - (A_REC_SPILL + 4)))) with a in X2
    by (unfold CALL_SIZE, CALL_OFF_NARGS; lia).
  rewrite X1, X2. reflexivity. }
assert (RD2 : forall p n i, In (p, n) O1 -> 0 <= i < n -> rdW W2 (ms_mem ms0) (p + i) = rdW W2 mem2 (p + i)).
{ intros p n i Hin Hi. destruct (s2s_fields _ _ _ _ _ HREP2 (p, n) Hin) as (Hbl & H1 & _ & Hap). cbn [fst snd] in *.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n (proj1 HJc) Hbl) as (_ & H4096 & Hce & _).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
  apply KEEP3; [lia | unfold iv_apart, SC_SIZE in Hap; lia]. }
assert (HO1 : forall pn, In pn O1 -> In pn (ablocks B ly2 S2)) by (intros pn Hpn; exact (proj1 (s2s_fields _ _ _ _ _ HREP2 pn Hpn))).
assert (HFN3 : aval_mem (rdW W2 (ms_mem ms0)) (A_REC_SPILL + CALL_OFF_FN) 4 REC_ADD)
  by (unfold CALL_OFF_FN, REC_ADD; rewrite Z.add_0_r; exact A0).
pose proof (rec_repA_spill_fn B HB LAWS ly2 S2 (rdW W2 mem2) ly2 S2 (rdW W2 (ms_mem ms0)) R O1
  (fst (r_spill R)) HREP2 H16 RD1 RD2 HO1 HFN3) as HREP3.
(* the frame and the saved words, carried from M0S through the call and the stores *)
assert (HSTK176 : 176 <= SUP_ADD_STK) by (unfold SUP_ADD_STK; lia).
assert (TST : forall a, sa_s1 (spZ regs) <= a < spZ regs -> rdW W2 (ms_mem ms0) a = rdW Wc memc a).
{ intros a Ha. rewrite KEEP3 by (unfold A_REC_SPILL; lia).
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & HK9 & _).
  apply HK9; [lia | lia |].
  intros Hf. destruct (s2s_inFP_rcf A_REC_SPILL (l_spill Q) a Hf) as [Hn | (b & n & Hbn & Hba)].
  - unfold CALL_OFF_NARGS, A_REC_SPILL in Hn. lia.
  - destruct (s2s_acall_blocks _ _ _ _ _ _ HSPILL Hbn) as [Hbl _].
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc md1 b n (proj1 HJ1) Hbl) as (_ & _ & Hbc & _). lia. }
assert (Hfr1 : In (1, pos) (frames Sc)).
{ pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
assert (FB : fs_frame_bytes 1 = 128) by reflexivity.
assert (TFR : forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + fs_frame_bytes 1 -> rdW W2 (ms_mem ms0) a = rdW Wc memc a).
{ intros a Ha.
  pose proof (frm_img SEGS B LAWS lyc Sc Wc memc md1 1 pos a (proj1 HJ1) Hfr1 Ha) as Hni.
  assert (Hnw : ~ (A_REC_SPILL <= a < A_REC_SPILL + 8)).
  { intros Hw. apply Hni. apply cif_prog_img. exists (A_REC_SPILL, A_REC_SPILL + 56).
    split; [unfold cmd_PG; right; left; reflexivity | cbn [fst snd]; lia]. }
  destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc md1 1 pos (proj1 HJ1) Hfr1) as (HF0 & HFc & _).
  rewrite KEEP3 by (first [exact Hnw | lia]).
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK12 & _).
  apply (HK12 1 pos a Hfr1); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia|].
  intros Hf. destruct (s2s_inFP_rcf A_REC_SPILL (l_spill Q) a Hf) as [Hn | (b & n & Hbn & Hba)].
  - apply Hnw. unfold CALL_OFF_NARGS in Hn. lia.
  - destruct (s2s_acall_blocks _ _ _ _ _ _ HSPILL Hbn) as [Hbl _].
    pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc md1 b n 1 pos (proj1 HJ1) Hbl Hfr1) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HFa : frame_addr ly2 1 pos = frame_addr lyc 1 pos /\ flag_addr ly2 1 pos = flag_addr lyc 1 pos).
{ pose proof HJ2 as (_ & Hl2 & _). pose proof HJ1 as (_ & Hl1 & _).
  destruct Hl2 as (_ & _ & _ & _ & _ & EF2 & _). destruct Hl1 as (_ & _ & _ & _ & _ & EF1 & _).
  unfold frame_addr, flag_addr. rewrite EF2, EF1. split; reflexivity. }
destruct HFa as [HFa HFl].
assert (Hc : sa_c R = A_REC_SPILL) by (unfold sa_c; rewrite H16; reflexivity).
(* the block accounting *)
destruct HACC as (A1 & A2 & A3 & A4' & A5).
assert (NDc : forall pn, In pn (ablocks B lyc Sc) -> List.NoDup (ablocks B lyc Sc)).
{ intros [p n] Hpn. destruct (al_blocks _ _ LAWS lyc Sc Wc memc md1 p n (proj1 HJ1) Hpn) as (_ & _ & _ & _ & _ & Hpw & _).
  apply (s2s_nodup_pw _ Hpw). intros [b m] Hb.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc md1 b m (proj1 HJ1) Hb) as (_ & _ & _ & _ & _ & _ & Hm). cbn [snd]. lia. }
assert (HACC3 : sa_acct B ly S R O ly2 S2 O1 0).
{ split; [|split; [|split; [|split]]].
  - intros pn Hpn. left. apply HOQ. unfold lay_blocks. unfold O1 in Hpn.
    apply in_app_or in Hpn as [H1|H1]; [apply in_or_app; left; exact H1 | apply in_or_app; right; apply in_or_app; right; exact H1].
  - intros pn Hpn.
    assert (Hpq : In pn (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hpn).
    destruct (A2 pn Hpq) as [Hl | HO]; [left; exact Hl | right].
    apply HOQ in HO. unfold lay_blocks in HO. unfold O1.
    apply in_app_or in HO as [H1|HO]; [apply in_or_app; left; exact H1|].
    apply in_app_or in HO as [H2|H3]; [|apply in_or_app; right; exact H3].
    exfalso. apply (s2s_nodup_app (ablocks B ly2 S2) (concat [l_spill Q]) pn).
    + exact (Permutation_NoDup HPERM (NDc pn Hpq)).
    + exact Hpn.
    + cbn [concat]. rewrite app_nil_r. exact H2.
  - intros pn Hpn HnO. pose proof (A3 pn Hpn HnO) as Hpq.
    apply (Permutation_in _ HPERM) in Hpq. apply in_app_or in Hpq as [H1|H2]; [exact H1|].
    exfalso. apply HnO. apply HinO. cbn [concat] in H2. rewrite app_nil_r in H2. exact H2.
  - intros pn Hpn. exact (proj1 (s2s_fields _ _ _ _ _ HREP3 pn Hpn)).
  - unfold LIVE_REC_CALLS_FREE in HBB2. lia. }
assert (HMLE3 : mo_le MT S S2 (sa_acc1 MT R)).
{ eapply (mle_weaken MT S S2 _ _ MTL (mle_station MT S Sc S2 0 _ MTL HMLE HMLE2)).
  unfold sa_acc1, XM_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r, <- Hrsf. lia. }
(* the mid-state M1 at 0x89f48 *)
assert (HEV1 : 0 + EV_REC_CALLS_FREE [l_spill Q] = sa_ev1 R).
{ unfold sa_ev1, EV_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r, Hrsf. lia. }
rewrite HEV1 in HJ2.
assert (R23 : getr (ms_regs ms0) 23%bv = w64 (A_REC_SPILL + 4)) by (rewrite T23, U22b; reflexivity).
assert (R27 : getr (ms_regs ms0) 27%bv = w64 (SHADOW_OFF + (A_REC_SPILL + 4) / 8)) by exact T27.
assert (HM1m : sa_M1m B MT ly S W regs mem md R O ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) md3 pos).
{ unfold sa_M1m. cbv zeta. rewrite Hc. split.
  { unfold sa_core. cbv zeta. rewrite HFa, HFl. split; [exact HJ2|]. split.
    - intros j r Hj.
      assert (Hj13 : (j < length sa_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
      change (length sa_saved) with 13%nat in Hj13.
      apply (lem_aval_keep (rdW Wc memc) _ _ _ _ (sa_s1 (spZ regs)) (spZ regs) (HFR j r Hj)); [lia | lia | exact TST].
    - split; [apply (lem_aval_keep (rdW Wc memc) _ _ _ _ (sa_s1 (spZ regs)) (spZ regs) HV16); [lia | lia | exact TST]|].
      split; [apply (lem_aval_keep (rdW Wc memc) _ _ _ _ (sa_s1 (spZ regs)) (spZ regs) HV24); [lia | lia | exact TST]|].
      split; [apply (lem_aval_keep (rdW Wc memc) _ _ _ _ (sa_s1 (spZ regs)) (spZ regs) HV48); [lia | lia | exact TST]|].
      split.
      { rewrite <- HFLAG. apply rdword_ext. intros k Hk. apply TFR. rewrite FB. lia. }
      split; [rewrite (KRX 2%bv ltac:(s2s_in)); exact G2|].
      split; [rewrite (KRX 3%bv ltac:(s2s_in)); exact G3|].
      split; [rewrite (KRX 4%bv ltac:(s2s_in)); exact G4|].
      split; [rewrite (KRX 8%bv ltac:(s2s_in)); exact G8|].
      split; [rewrite (KRX 9%bv ltac:(s2s_in)); exact G9|].
      split; [rewrite (KRX 18%bv ltac:(s2s_in)); exact G18|].
      split; [rewrite (KRX 19%bv ltac:(s2s_in)); exact G19|].
      split; [rewrite (KRX 21%bv ltac:(s2s_in)); exact G21|].
      split; [rewrite (KRX 25%bv ltac:(s2s_in)); exact G25 | rewrite (KRX 26%bv ltac:(s2s_in)); exact G26]. }
  split; [rewrite (KRX 20%bv ltac:(s2s_in)); exact R20|].
  split; [rewrite (KR3 22%bv ltac:(s2s_in)); exact Q22|].
  split; [exact R23|].
  split; [rewrite (KRX 24%bv ltac:(s2s_in)); exact R24|].
  split; [exact R27|].
  exists O1. split; [exact HREP3|]. split; [exact HACC3 | exact HMLE3]. }
change (BASE + 14948) with (BASE + L_M1).
exact (M1S ly S W regs mem md ch pu id pp pc uri placement client R O ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) md3 pos
  HCX HM1m).
Qed.
End e.
End f.
End d.
