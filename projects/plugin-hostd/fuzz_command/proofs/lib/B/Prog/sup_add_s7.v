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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 248 of its 280 lines of code are new or changed and 380 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (0x8a400), stage 7: M6 (0x8a5bc) to M7
   (0x8a628) or M9 (0x8a634), the range check on id and the three arms it opens.

   `srliw a0,s3,4`, `li a1,625`, `bltu a0,a1,0x8a5e0`: the branch is taken exactly when 0 <= id < 10000
   (sup_add_s7a.v's sab_srliw / sab_in_range on the signed 32-bit id).
   - out of range (0x8a5c8): a2 := "resp %d" (0x21d40), a1 := 32, a3 := -1, a0 := s4 = buf, `j 0x8a628`: M7 with
     v = -1 and the recorder R1 untouched (sa_arm's left arm).
   - in range (0x8a5e0): s5 := g_rec (the listing's object atom 44), `lw a0,0(s5)` reads g_rec.refuse and
     `beqz a0,0x8a604` splits on it (sab_refuse_eq):
     - refused (0x8a5f0): sup_add_s7b.v's sab_arm_refuse (answer, then M9);
     - accepted (0x8a604): sup_add_s7c.v's sab_arm_accept (mix_call, the store into g_rec.state, then M7).
   The donor is the A walk's stage 5 (lib/A/Prog/sup_add_s5.v on a working branch 87f17ee4716). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s7a sup_add_s7b sup_add_s7c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts RecBLemmas.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at M6: the registers are atoms 0..31 and atom 32 is g_rec.refuse (as 32 bits); the field the
   stage loads is a read-only window on the listing's object atom for g_rec (A_OBJ 44) *)
Definition sabd_rg_refuse : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 44)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition sabd_regions : smem := [ sabd_rg_refuse ].
Definition sabd_facts : facts := mkFacts [] [] [].
Definition ss_sabd : sstate := mkSS L_M6 sr_atoms sabd_regions None sabd_facts.
Definition sabd_extra (rf : Z) : list word := [Z_to_bv 64 rf].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition sabd_E (regs : bvmap 5 word) (rf : Z) : env := Eimg (Ereg regs (sabd_extra rf)).

Lemma sabd_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem rf,
cmd_val_objs ->
aval_mem (rdW W mem) (A_G_REC + 0) 4 rf -> 0 <= rf < 2 ^ 32 ->
st_ok_pi SEGS VAL (sabd_E regs rf) ss_sabd
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L_M6)) mem (seg_rom SEGS)))
/\ sh_ok SEGS sab_Bx [] (sabd_E regs rf) (mrestrict (w_H W) mem).
Proof.
intros W regs mem rf VOBJS Hrf Hrf0.
set (E := sabd_E regs rf).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold sabd_E; apply Eimg_env).
assert (V44 : VAL (A_OBJ 44) = A_G_REC)
  by (rewrite (VOBJS 44%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 rf)
  by (subst E; unfold sabd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (B44 : base_val E (Some (A_OBJ 44)) = A_G_REC).
{ cbn [base_val]. rewrite (HEI (A_OBJ 44) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). exact V44. }
split.
- unfold ss_sabd. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold sabd_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold sabd_regions, sabd_rg_refuse. constructor; [|constructor].
    unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B44.
    split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC 0 4 (SOff 32 0) rf);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem _ 4 rf Hrf).
  + cbn [pairwise_disjoint all_disjoint sabd_regions]. first [exact I | repeat split].
  + split; [exact I | split; exact I].
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
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
(* the statement's own (sup_add_c.v) *)
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma sa_m6_ok : SA_M7_stmt B MT -> SA_M9_stmt B MT -> SA_M6_at B MT.
Proof using HB LAWS MTL SIGP PRW IMG TMIX_CALL TANSWER VOBJS.
intros HM7 HM9. unfold SA_M6_at.
intros ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCXs HFRM0 HMs.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO.
pose proof pa_B_ok as (HBa & HBb & HBc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HCXs as HCX. unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & Hfr & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT & HC &
  HCT & HREP & Hev & Hlive & MOK).
pose proof HMs as HM. unfold sa_M6m, sa_core in HM. cbv zeta in HM.
destruct HM as ((HJ & HFRM & HFLG & Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q23 & Q25 & Q26 & Q27) &
  Hs4 & Hs8 & HBUF & O6 & HREP6 & HACCT & HMO6).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (sp0 := spZ regs) in *.
set (F := frame_addr lyc 1 pos) in *.
set (A := sa_A uri id placement client) in *.
set (R1 := rec_record R REC_ADD A) in *.
pose proof HJ as (HARc & Hlyc & Hsecsc & Hwlec & Hioc & Hfrsc & Hnevc & Hkc & JF1 & JF2 & JF3 & JF4 & JGone & JPres
  & JStk & JF5 & JQT).
assert (HFin : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc HFin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil. fold F in HF4096, HFceil.
assert (HF8 : 0 <= F / 8 <= F) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
destruct HACCT as (HA1 & HA2 & HA3 & HA4 & HA5).
destruct (sab_rep_fields B lyc Sc (rdW Wc memc) R1 O6 HREP6) as (Hrf & Hrfr & _ & _ & _ & HO6b).
assert (Hrf' : aval_mem (rdW Wc memc) (A_G_REC + 0) 4 (r_refuse R1 mod 2 ^ 32)).
{ intros k Hk. pose proof (Hrf k Hk) as Hk'. unfold OFF_REFUSE in Hk'. rewrite Hk'. f_equal.
  cbv [YO0f.le_byte YG0f.le_byte]. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia.
  reflexivity. }
assert (V44 : VAL (A_OBJ 44) = A_G_REC)
  by (rewrite (VOBJS 44%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
(* ---- the seed at M6 ---- *)
destruct (sabd_seed Wc regs1 memc (r_refuse R1 mod 2 ^ 32) VOBJS Hrf' ltac:(apply Z.mod_pos_bound; lia))
  as [HS SHOK].
assert (HEI : img_env VAL A_LIM (sabd_E regs1 (r_refuse R1 mod 2 ^ 32)))
  by (unfold sabd_E; apply Eimg_env).
remember (sabd_E regs1 (r_refuse R1 mod 2 ^ 32)) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr).
{ intros n rr Hn. rewrite HE. unfold sabd_E. apply ew_Eimg_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 (r_refuse R1 mod 2 ^ 32))
  by (rewrite HE; unfold sabd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
clear HE.
(* 0x8a5bc .. 0x8a5c0: a0 := (id mod 2^32) >> 4, a1 := 625 *)
paj_run_tok RUN HS HJ SHOK sab_Bspan.
{ awr_ok_tac. }
lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (mdv1 := m) in *; clearbody mdv1 end.
sab_memeq Wc MEQ1. sab_clear_frames.
(* 0x8a5c4: bltu a0,a1 -- the range check on id *)
psrr_branch_tok RUN BR HS SHOK sab_Bspan.
- (* 0 <= id < 10000 *)
  assert (HIN : 0 <= id < 10000).
  { rewrite branch_ltu_U in Hc.
    rewrite (sab_srliw E id ltac:(rewrite (EEo 19%nat (19%bv : bv 5) eq_refl), Q19; exact H11) Hid), U_SLit in Hc.
    change (zcanon 625) with 625 in Hc. apply Z.ltb_lt in Hc. exact (sab_in_range id Hid Hc). }
  (* 0x8a5e0 .. 0x8a5e8: s5 := g_rec, a0 := g_rec.refuse *)
  paj_run_tok RUN HS HJ SHOK sab_Bspan.
  { awr_ok_tac. }
  lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (mdv2 := m) in *; clearbody mdv2 end.
  sab_memeq Wc MEQ2. sab_clear_frames.
  (* 0x8a5ec: beqz a0 -- the refusal *)
  psrr_branch_tok RUN BR HS SHOK sab_Bspan.
  + (* g_rec.refuse = 0: the accepted arm at 0x8a604 *)
    assert (HREF0 : r_refuse R1 = 0).
    { rewrite branch_eq_U, (sab_refuse_eq E (r_refuse R1) E32 Hrfr) in Hc0. apply Z.eqb_eq. exact Hc0. }
    paj_run_to_tok RUNTO HS HJ SHOK sab_Bspan (AF_sup_add + 0x204).
    { awr_ok_tac. }
    lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (mdv3 := m) in *; clearbody mdv3 end.
    sab_memeq Wc MEQ3. sab_clear_frames.
    pmkst HS.
    prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
    prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21.
    prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
    prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
    rewrite (EEo 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EEo 3%nat (3%bv : bv 5) eq_refl) in T3.
    rewrite (EEo 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EEo 8%nat (8%bv : bv 5) eq_refl) in T8.
    rewrite (EEo 9%nat (9%bv : bv 5) eq_refl) in T9. rewrite (EEo 18%nat (18%bv : bv 5) eq_refl) in T18.
    rewrite (EEo 19%nat (19%bv : bv 5) eq_refl) in T19. rewrite (EEo 20%nat (20%bv : bv 5) eq_refl) in T20.
    rewrite (EEo 23%nat (23%bv : bv 5) eq_refl) in T23. rewrite (EEo 24%nat (24%bv : bv 5) eq_refl) in T24.
    rewrite (EEo 25%nat (25%bv : bv 5) eq_refl) in T25. rewrite (EEo 26%nat (26%bv : bv 5) eq_refl) in T26.
    rewrite (EEo 27%nat (27%bv : bv 5) eq_refl) in T27.
    pose proof (img_env_atomP E 285%nat HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E285.
    change (VAL 285%nat) with (VAL (A_OBJ 44)) in E285. rewrite V44 in E285.
    rewrite E285 in T21.
    try rewrite unsigned_lit_small in T21 by (unfold A_G_REC; lia).
    try rewrite Z.add_0_r in T21.
    eapply (sab_arm_accept B MT HB LAWS SIGP PRW IMG TMIX_CALL VOBJS (HM7 fx)
      ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc _ _ _ pos);
      [exact HCXs | exact HFRM0 | | exact HIN | exact HREF0 | exact T21].
    eapply (sab_m6_kept B MT LAWS ly S W regs mem md O uri id placement client R lyc Sc Wc regs1 memc mdc pos);
      [exact HMs | exact HJ | |].
    { intros a Ha. rewrite MEQ3 by lia. rewrite MEQ2 by lia. apply MEQ1. lia. }
    { rewrite T2, T3, T4, T8, T9, T18, T19, T20, T23, T24, T25, T26, T27.
      repeat (split; [reflexivity|]). reflexivity. }
  + (* g_rec.refuse <> 0: the refused arm at 0x8a5f0 *)
    assert (HREF : r_refuse R1 <> 0).
    { rewrite branch_eq_U, (sab_refuse_eq E (r_refuse R1) E32 Hrfr) in Hc0. apply Z.eqb_neq. exact Hc0. }
    paj_run_to_tok RUNTO HS HJ SHOK sab_Bspan (AF_sup_add + 0x1f0).
    { awr_ok_tac. }
    lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (mdv3 := m) in *; clearbody mdv3 end.
    sab_memeq Wc MEQ3. sab_clear_frames.
    pmkst HS.
    prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
    prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
    prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
    prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
    rewrite (EEo 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EEo 3%nat (3%bv : bv 5) eq_refl) in T3.
    rewrite (EEo 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EEo 8%nat (8%bv : bv 5) eq_refl) in T8.
    rewrite (EEo 9%nat (9%bv : bv 5) eq_refl) in T9. rewrite (EEo 18%nat (18%bv : bv 5) eq_refl) in T18.
    rewrite (EEo 19%nat (19%bv : bv 5) eq_refl) in T19. rewrite (EEo 20%nat (20%bv : bv 5) eq_refl) in T20.
    rewrite (EEo 23%nat (23%bv : bv 5) eq_refl) in T23. rewrite (EEo 24%nat (24%bv : bv 5) eq_refl) in T24.
    rewrite (EEo 25%nat (25%bv : bv 5) eq_refl) in T25. rewrite (EEo 26%nat (26%bv : bv 5) eq_refl) in T26.
    rewrite (EEo 27%nat (27%bv : bv 5) eq_refl) in T27.
    eapply (sab_arm_refuse B MT HB LAWS MTL SIGP IMG TANSWER HM9
      ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc _ _ _ pos);
      [exact HCXs | exact HFRM0 | | exact HIN | exact HREF].
    eapply (sab_m6_kept B MT LAWS ly S W regs mem md O uri id placement client R lyc Sc Wc regs1 memc mdc pos);
      [exact HMs | exact HJ | |].
    { intros a Ha. rewrite MEQ3 by lia. rewrite MEQ2 by lia. apply MEQ1. lia. }
    { rewrite T2, T3, T4, T8, T9, T18, T19, T20, T23, T24, T25, T26, T27.
      repeat (split; [reflexivity|]). reflexivity. }
- (* id outside [0, 10000): 0x8a5c8 .. 0x8a5dc set a0 = buf, a1 = 32, a2 = "resp %d", a3 = -1, j 0x8a628 *)
  assert (HOUT : ((id <? 0) || (10000 <=? id))%bool = true).
  { rewrite branch_ltu_U in Hc.
    rewrite (sab_srliw E id ltac:(rewrite (EEo 19%nat (19%bv : bv 5) eq_refl), Q19; exact H11) Hid), U_SLit in Hc.
    change (zcanon 625) with 625 in Hc. apply Z.ltb_ge in Hc.
    apply Bool.orb_true_intro.
    destruct (Z_lt_le_dec id 0) as [Hlt|Hge]; [left; apply Z.ltb_lt; exact Hlt|].
    right. apply Z.leb_le. rewrite (Z.mod_small id (2 ^ 32)) in Hc by lia. exact (sab_div16 id Hc Hge). }
  paj_run_to_tok RUNTO HS HJ SHOK sab_Bspan L_M7.
  { awr_ok_tac. }
  lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (mdv2 := m) in *; clearbody mdv2 end.
  sab_memeq Wc MEQ2. sab_clear_frames.
  pmkst HS.
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
  prreg HS (19%bv : bv 5) T19. prreg HS (23%bv : bv 5) T23. prreg HS (25%bv : bv 5) T25.
  prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
  prreg HS (13%bv : bv 5) T13. prreg HS (20%bv : bv 5) T20. prreg HS (24%bv : bv 5) T24.
  rewrite (EEo 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EEo 3%nat (3%bv : bv 5) eq_refl) in T3.
  rewrite (EEo 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EEo 8%nat (8%bv : bv 5) eq_refl) in T8.
  rewrite (EEo 9%nat (9%bv : bv 5) eq_refl) in T9. rewrite (EEo 18%nat (18%bv : bv 5) eq_refl) in T18.
  rewrite (EEo 19%nat (19%bv : bv 5) eq_refl) in T19. rewrite (EEo 23%nat (23%bv : bv 5) eq_refl) in T23.
  rewrite (EEo 25%nat (25%bv : bv 5) eq_refl) in T25. rewrite (EEo 26%nat (26%bv : bv 5) eq_refl) in T26.
  rewrite (EEo 27%nat (27%bv : bv 5) eq_refl) in T27. rewrite (EEo 24%nat (24%bv : bv 5) eq_refl) in T24.
  rewrite (EEo 20%nat (20%bv : bv 5) eq_refl) in T10, T20.
  apply (HM7 fx ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc _ _ _ pos HCXs HFRM0).
  unfold sa_M7m. cbv zeta. fold F.
  split.
  { eapply sab_core_kept; [exact (proj1 HMs) | exact HJ | reflexivity | |].
    - intros a Ha. rewrite MEQ2 by (destruct Ha as [Ha | Ha]; lia).
      apply MEQ1. destruct Ha as [Ha | Ha]; lia.
    - rewrite T2, T3, T4, T8, T9, T18, T19, T23, T25, T26, T27.
      repeat (split; [reflexivity|]). reflexivity. }
  split; [rewrite T10; exact Hs4|].
  split; [rewrite T11; reflexivity|].
  split.
  { pose proof (img_env_atomP E 288%nat HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E288b.
    change (VAL 288%nat) with (VAL (A_OBJ 47)) in E288b.
    rewrite (VOBJS 47%nat ltac:(vm_compute; lia)) in E288b.
    rewrite T12. apply bv_eq. rewrite E288b. vm_compute. reflexivity. }
  split; [rewrite T20; exact Hs4|].
  split.
  { intros i Hi. rewrite MEQ2 by (unfold SHADOW_OFF; lia). rewrite MEQ1 by (unfold SHADOW_OFF; lia).
    exact (HBUF i Hi). }
  exists (-1), R1, O6.
  split.
  { unfold sa_arm. cbv zeta. left. split; [reflexivity|]. split; [exact HOUT | reflexivity]. }
  split; [rewrite T13; apply bv_eq; vm_compute; reflexivity|].
  split.
  { apply (rec_repA_kept B lyc Sc (rdW Wc memc) lyc Sc _ R1 O6 HREP6 HA4).
    intros a Ha. rewrite MEQ2; [apply MEQ1|]; (destruct Ha as [Ha | [Ha | Ha]];
      [unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia |];
      destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hr);
      pose proof (HO6b (p, n) Hpn) as Hbl;
      destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HARc Hbl)
        as (_ & Hp4096 & Hpceil & _ & _ & _ & Hn1);
      pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]; lia). }
  split; [repeat (split; [assumption|]); assumption | exact HMO6].
Qed.
End e.
End f.
End d.
Print Assumptions sa_m6_ok.
