(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of descriptors_get (plugin-hostd/fuzz_command.asan) from the join of
   record()'s arms to the tail jump into answer, after proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v and ACh2.v (a walk
   segment: run, call out by cl_callS, resume) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/descriptors_get_s3.v, with its module paths and module names changed; 166 of its 212 lines of code are new or changed and 967 lines of the source are left out. *)
(* Segment lemmas of sup_host_setting's ASan+UBSan walk (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan), on the
   points and statements of sup_host_setting_s0.v:
   - hs_seg_as1: from AS1 (0x8b684, back from arg_s(c, b)) the poison of b again (`sb s2,4(s9); sb s2,5(s9)`,
     s2 = f8), `blez s5` (not taken: 1 <= ntok, the executor decides it from the fact on s5; so the ntok <= 0 arm
     0x8b7d8 .. 0x8b7f4 with its store1 check 0x8b7f0 -> report 0x8b8e0 is not reached), the spills of c, F, F to the
     realigned stack (0x8b690 .. 0x8b698), and the length loop's init (`mv s4,zero; snez s2,s8; andi a0,s8,7;
     seqz a0,a0; and s7,a0,s2; mv s11,s5; mv s3,s8; mv s6,s8`), to the loop's head L1H at token 0 (0x8b6bc).
   The B twin of the ASan walk's hs_seg_ai (lib/A/Prog/sup_host_setting_s4.v on e323bbe76d2), with B's frame shadow
   store and spills; the run stores shadow, so it is the plain run (SRr_run_to_pi_AJ, the brief's speed rule). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c rec_canonical_c record_c arg_line_c arg_s_c xmalloc_c mix_call_c sup_host_setting_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_host_setting_aux sup_host_setting_s1 sup_host_setting_s0 sup_host_setting_s3.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the regions of the AS1 run: the frame's 8 shadow bytes (s9), the realigned stack's spill slots (s1 + 8 .. 32) *)
Definition hs4_rsh : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 4 6 [].
Definition hs4_rstk : YP09.region := YP09.mkRegion (Some 9%nat) 8 32 8 32 [].
Definition hs4_ssA : sstate :=
  mkSS HS_AS1 sr_atoms [hs4_rsh; hs4_rstk] None (mkFacts [(21%nat, mkAF 1 64 0); (26%nat, mkAF HS_SB HS_SB 0)] [] []).

Lemma hs4_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.


(* the frame's shadow lies in the shadow gap: above every low application byte, below every high one *)
Lemma hs4_sh_bounds : forall F, 0 <= F -> F + 64 <= alloc_ceiling ->
  HS_SB + F / 8 + 6 <= 0x10007fff8000 /\ 0x7fff8000 <= HS_SB + F / 8.
Proof.
intros F H0 H1. pose proof (@ASAN_CEIL_range rc) as [C1 _]. unfold ASAN_CEIL in C1.
assert (H3 : F / 8 <= 0xffffff00000) by (apply Z.div_le_upper_bound; lia).
assert (H4 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (H5 : forall q, 0 <= q <= 0xffffff00000 -> HS_SB + q + 6 <= 0x10007fff8000 /\ 0x7fff8000 <= HS_SB + q)
  by (intros q Hq; unfold HS_SB; lia).
exact (H5 (F / 8) (conj H4 H3)).
Qed.

(* a byte of an application range below the allocator's ceiling is in neither window the AS1 run writes *)
Lemma hs4_app_apart : forall F sp1, 0 <= F -> F + 64 <= alloc_ceiling -> alloc_ceiling < sp1 ->
  forall p len a, in_app p len -> p <= a < p + len -> p + len <= alloc_ceiling ->
  ~ (HS_SB + F / 8 + 4 <= a < HS_SB + F / 8 + 6) /\ ~ (sp1 + 8 <= a < sp1 + 32).
Proof.
intros F sp1 H0 H1 H2 p len a Hap Ha Hc. destruct (hs4_sh_bounds F H0 H1) as [S1 S2].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap. lia.
Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ (L := cmd_listing) B LAWS.

(* ---- AS1 0x8b684 .. L1H 0x8b6bc ---- *)
Lemma hs_seg_as1 : forall x, ST_L1H B MT x 0 -> ST_AS1 B MT x.
Proof.
intros x L1. unfold ST_AS1.
intros fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 CX FXR MID REP RG R27.
pose proof CX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10 & H11 & H12 & HNT & HLINE & Hp0 & Hp8 & HTA & HLPS & HPS &
  HTOKS & HWL & HREP0 & HFRM & HEV & HLIVE & HMO & HTAIL & HRM0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof RG as ((K2 & K9 & K8 & K3 & K4 & K24 & K25 & K26) & R18 & R19 & R20 & R21 & R22 & R23).
pose proof MID as (HJ & Hk & HMLE & HBB & HFR & HFL & HBA).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (hs3_sp1 (spZ (i_regs x)) Hal16 ltac:(lia)) as (S1a & S1b & S1c).
pose proof hs3_stk as FS.
destruct (hs3_frame_facts B MT x fpos lyc Sc Wc memc mdc k CX HJ) as (HFin & EFA & EFL & HF4096 & HFceil & HF64).
pose proof HJ as (HARc & _ & _ & _ & _ & HFRSc & HNEVc & _ & _ & _ & _ & _ & _ & HJpres & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HARc HFin) as (_ & HFapp & HFpres & HFSpres).
rewrite EFA in HFapp, HFpres, HFSpres. change (fs_frame_bytes 0) with 64 in HFapp, HFpres, HFSpres. change (64 / 8) with 8 in HFSpres.
set (F := hs_F x fpos) in *.
set (sp0 := spZ (i_regs x)) in *.
set (sp1 := hs_sp1 sp0) in *.
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (ESH : shadow_addr F = HS_SB + F / 8) by (unfold shadow_addr, HS_SB, SHADOW_OFF; reflexivity).
pose (E := Eimg (Ereg regs1 [])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (V25 : bv_unsigned (ew E 25) = HS_SB + F / 8)
  by (rewrite (EE 25%nat 25%bv eq_refl), K25; unfold w64; apply unsigned_lit_small; unfold HS_SB; lia).
assert (V9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), K9; unfold w64; apply unsigned_lit_small; lia).
assert (V21 : bv_unsigned (ew E 21) = Z.of_nat (length (i_toks x)))
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
assert (V26 : bv_unsigned (ew E 26) = HS_SB)
  by (rewrite (EE 26%nat 26%bv eq_refl), K26; unfold w64; apply unsigned_lit_small; unfold HS_SB; lia).
assert (HS : st_ok_pi SEGS VAL E hs4_ssA (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_AS1)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold hs4_ssA. apply pa_entry_st_ok_full.
  - exact (regs_ok_Eimg_Ereg regs1 []).
  - reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, hs4_rsh, hs4_rstk;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite V25. split; [unfold HS_SB; lia|]. split; [unfold HS_SB; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). rewrite <- ESH. exact (proj1 (HFSpres o ltac:(lia))).
    + rewrite V9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HJpres. rewrite FS. lia.
  - apply pairwise_disjoint_of_extents. unfold hs4_rsh, hs4_rstk, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite V25, V9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold HS_SB. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite V21, V26. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold HS_SB. lia. }
clearbody E.
(* 0x8b684 .. 0x8b6b8: b poisoned again, blez (not taken), the spills, the loop's init.
   0x8b68c `blez s5` (to 0x8b7d8, the ntok <= 0 arm with the store1 check 0x8b7f0 -> report 0x8b8e0): refuted by
   paj_run_to_sh at sup_host_setting_s4.v:147 (SRr_run_to_pi_AJ; the run stops only at L1H, so the branch is decided
   not taken), from
   the seed fact s5 in [1, 64] (hs4_ssA, atom 21), that is hs_cx's 1 <= length toks <= 64 *)
paj_run_to_sh RUNTOP HS HJ HS_L1H.
{ unfold hs4_ssA. cbn [ss_mem].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 25%nat); [reflexivity | exact V25 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi hs4_rsh] in Ha. right; right; right; left. exists 0, fpos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite EFA. rewrite ESH.
    change (fs_frame_bytes 0 / 8) with 8. lia. }
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 9%nat) (d := sp1 - sp0);
    [reflexivity | rewrite V9; lia | cbn [YP09.r_wlo hs4_rstk]; rewrite FS; lia | cbn [YP09.r_whi hs4_rstk]; lia |].
  apply (awr_ok_nil SEGS B). }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
cbn [ms_mem] in HFr.
rewrite (EE 2%nat 2%bv eq_refl), K2 in P2. rewrite (EE 3%nat 3%bv eq_refl), K3 in P3. rewrite (EE 4%nat 4%bv eq_refl), K4 in P4.
rewrite (EE 8%nat 8%bv eq_refl), K8 in P8. rewrite (EE 9%nat 9%bv eq_refl), K9 in P9.
rewrite (EE 24%nat 24%bv eq_refl), K24 in P18, P19, P22, P23, P24.
rewrite (EE 21%nat 21%bv eq_refl), R21 in P21, P27.
rewrite (EE 25%nat 25%bv eq_refl), K25 in P25. rewrite (EE 26%nat 26%bv eq_refl), K26 in P26.
(* the bytes the run did not write are kept: only the frame's shadow bytes 4..5 and the spill slots sp1 + 8 .. 32 *)
assert (KEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (HS_SB + F / 8 + 4 <= a < HS_SB + F / 8 + 6) -> ~ (sp1 + 8 <= a < sp1 + 32) ->
  rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha H1 H2. apply aview_eq_of. apply HFr. rewrite (unsigned_lit_small a) by lia.
  intros (r & Hr & Hrw). unfold hs4_ssA in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi hs4_rsh hs4_rstk] in Hrw;
    [rewrite V25 in Hrw | rewrite V9 in Hrw]; lia. }
(* the windows the run wrote lie away from the frame, the saved registers, the recorder's statics and the heap *)
assert (HSP1 : alloc_ceiling < sp1) by (clear - S1a Hceil Hslo FS; rewrite FS in Hslo; lia).
assert (HF0 : 0 <= F) by (clear - HF4096; lia).
pose proof (hs4_app_apart F sp1 HF0 HFceil HSP1) as Kapp.
destruct (hs4_sh_bounds F HF0 HFceil) as [Fsh1 Fsh2].
assert (KFR : forall b, sp0 - 104 <= b < sp0 -> rdW Wc (ms_mem ms) b = rdW Wc memc b).
{ intros b Hb. apply KEQ.
  - clear - Hb Hceil Hslo Hstk0 Hshi H47 C1. lia.
  - clear - Hb Fsh1 HSP1 S1a C1. lia.
  - clear - Hb S1a. lia. }
apply (L1 fpos lyc Sc Wc (ms_mem ms) mdv (ms_regs ms) k O1 Rest b0 b1).
- lia.
- exact CX.
- exact FXR.
- refine (conj HJ (conj Hk (conj HMLE (conj HBB (conj _ (conj _ HBA)))))).
  + apply (hs3_frame_kept_on (rdW Wc memc)); [|exact HFR].
    exact KFR.
  + apply (hs3_aval_on (rdW Wc memc)); [|exact HFL].
    intros b Hb. cbn in Hb. fold F in Hb.
    destruct (Kapp F 64 b HFapp ltac:(lia) ltac:(lia)) as [Kb1 Kb2]. apply KEQ; [lia | exact Kb1 | exact Kb2].
- apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc (ms_mem ms)) _ _ REP);
    [| intros pn H; exact (proj1 (hs_rec_own B _ _ _ _ _ REP pn H))].
  intros a [Ha | (pn & Hpn & Ha)].
  + apply KEQ; unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, HS_SB in *; lia.
  + destruct pn as [p n]. cbn [fst snd] in Ha.
    destruct (hs_rec_own B _ _ _ _ _ REP (p, n) Hpn) as (Hin & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & Hp4096 & Hpc & Happ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
    destruct (Kapp p (req_size n) a Happ ltac:(lia) Hpc) as [Ka1 Ka2]. apply KEQ; [lia | exact Ka1 | exact Ka2].
- (* the spills: c, F, F at sp1 + 8, 16, 24 *)
  pose proof (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) as HRs. cbn [ms_mem restrict] in HRs.
  pose proof (field_of_region_any E _ 9%nat sp1 _ _ _ _ _ 8 8 (SOff 27 0) HRs V9 ltac:(cbn; tauto) ltac:(cbn; lia)) as F8.
  pose proof (field_of_region_any E _ 9%nat sp1 _ _ _ _ _ 16 8 (SOff 20 0) HRs V9 ltac:(cbn; tauto) ltac:(cbn; lia)) as F16.
  pose proof (field_of_region_any E _ 9%nat sp1 _ _ _ _ _ 24 8 (SOff 19 0) HRs V9 ltac:(cbn; tauto) ltac:(cbn; lia)) as F24.
  rewrite hs4_denot_off0 in F8, F16, F24.
  rewrite (EE 27%nat 27%bv eq_refl), R27 in F8. rewrite (EE 20%nat 20%bv eq_refl), R20 in F16.
  rewrite (EE 19%nat 19%bv eq_refl), R19 in F24.
  pose proof (hs_slot_bounds (i_R x)) as (SL1 & SL2 & _).
  unfold w64 in F8, F16, F24. rewrite unsigned_lit_small in F8 by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia).
  rewrite unsigned_lit_small in F16, F24 by lia.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in F8, F16, F24.
  rewrite Z.mod_small in F8 by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia).
  rewrite Z.mod_small in F16, F24 by lia.
  unfold hs_spill. cbv zeta.
  split; [exact (aval_mem_view SEGS _ _ _ _ _ F8)|].
  split; [exact (aval_mem_view SEGS _ _ _ _ _ F16) | exact (aval_mem_view SEGS _ _ _ _ _ F24)].
- (* the length loop's registers at token 0 *)
  assert (Q1 : getr (ms_regs ms) 18 = w64 1).
  { rewrite P18. unfold w64. rewrite (hsb_sltu 0 (i_ptok x)) by lia.
    replace (0 <? i_ptok x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  assert (Q7 : getr (ms_regs ms) 23 = w64 1).
  { rewrite P23. unfold w64. rewrite (hsb_and7 (i_ptok x)) by lia. rewrite Hp8.
    rewrite (hsb_sltu 0 (i_ptok x)) by lia. replace (0 <? i_ptok x) with true by (symmetry; apply Z.ltb_lt; lia).
    apply bv_eq. vm_compute. reflexivity. }
  split; [split|].
  { exact P2. }
  split; [exact P9|]. split; [exact P8|]. split; [exact P3|]. split; [exact P4|]. split; [exact P24|].
  split; [exact P25 | exact P26].
  split; [exact Q1|]. split; [exact Q7|]. split; [exact P21|].
  split; [rewrite P19; f_equal; lia|]. split; [rewrite P22; f_equal; lia|].
  split; [rewrite P20; reflexivity|].
  rewrite P27, Nat.sub_0_r. reflexivity.
Qed.

End e.
End f.
End d.
