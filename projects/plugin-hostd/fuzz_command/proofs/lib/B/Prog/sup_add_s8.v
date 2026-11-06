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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 173 of its 209 lines of code are new or changed and 376 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (0x8a400), stage 8: M7 (0x8a628) to M8
   (0x8a62c), the call of the snprintf wrapper on (buf, 32, "resp %d", v).

   `jal 0x451d0` at 0x8a628 (the interceptor trampoline of snprintf; return address 0x8a62c = M8) with a0 = buf =
   F + 64, a1 = 32, a2 = "resp %d" (0x21d40, CmdRo.v RO_lit_21d40) and a3 = v, all set by M7 (sa_M7m). The wrapper
   returns at an FP state fx1 (RtPFShared.v's sh_asnprintf_realizes); sup_add_sn.v's sas_snp_call carries the call
   (the contract, PaFx.v's art step, srr_after_artF) and the rest is the next stage at fx1. M8 takes buf's bytes
   from the wrapper's post: RecAns.v's pf_resp turns its text RESP_HEAD ++ pf_dec v into resp v (6 <= |resp v| <= 16
   < 32, so nothing is cut), and every other fact of M7 in memory from sas_kept: the wrapper writes only its stack
   window and [buf, buf + |resp v| + 1). The donor is the A walk's stage 6, first half (lib/A/Prog/sup_add_s6.v on
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaNoChain PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtPFPf RtPFShared RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0 sup_add_sn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts CmdSnText.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module RA := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.RecAns.

(* the symbolic state at 0x8a628: every register its own atom, atom 32 the shadow base; no region (the `jal` touches
   no memory) and no inline check *)
Definition sas8_SB : Z := 0x7fff8000.
Definition sas8_Bx : sv := SOff 32 0.
Definition sas8_facts : facts := mkFacts [ (32%nat, mkAF sas8_SB sas8_SB 0) ] [] [].
Definition ss_sas8 : sstate := mkSS L_M7 sr_atoms [] None sas8_facts.
Definition sas8_Bspan : Z * Z := (sas8_SB, sas8_SB + 2 ^ 44 - 1).
Definition sas8_extra : list word := [Z_to_bv 64 sas8_SB].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition sas8_E (regs : bvmap 5 word) : env := Eimg (Ereg regs sas8_extra).
Lemma sas8_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem,
st_ok_pi SEGS VAL (sas8_E regs) ss_sas8 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L_M7)) mem (seg_rom SEGS)))
/\ sh_ok SEGS sas8_Bx [] (sas8_E regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem.
set (E := sas8_E regs).
assert (E32 : ew E 32 = Z_to_bv 64 sas8_SB).
{ subst E. unfold sas8_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
split.
- unfold ss_sas8. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold sas8_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. first [exact I | repeat split].
  + split; [|split; [exact I | exact I]].
    cbn [sas8_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, unsigned_lit_small by (unfold sas8_SB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. unfold sas8_SB.
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
(* the image's per-binary facts: CmdRecFacts.v's lemmas and cmd_img_facts' fields by exact from IMG *)
Hypothesis IMG : cmd_img_facts SEGS B.
(* the statement's own (sup_add_c.v), at every FP state *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Let RUN := paj_run B LAWS.

Lemma sa_m7_ok : SA_M8_stmt B MT -> SA_M7_at B MT.
Proof using HB LAWS IMG ASNPRINTF.
intros M8. unfold SA_M7_at.
intros ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCX HFRM0 HM.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO.
pose proof pa_B_ok as (HBa & HBb & HBc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCX as HCXs.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & Hfr & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT & HC &
  HCT & HREP & Hev & Hlive & MOK).
unfold sa_M7m, sa_core in HM. cbv zeta in HM.
destruct HM as ((HJ & HFRM & HFLG & Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q23 & Q25 & Q26 & Q27) &
  Ha0 & Ha1 & Ha2 & Q20 & HBUF & v & R2 & O6 & HARM & Ha3 & HREP2 & HACCT & HMO6).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (sp0 := spZ regs) in *.
set (s1 := sa_s1 sp0) in *.
set (F := frame_addr lyc 1 pos) in *.
assert (Hs1 : s1 = sp0 - 128 \/ s1 = sp0 - 144) by (clear - Hal16; unfold s1, sa_s1; Z.div_mod_to_equations; lia).
pose proof HJ as HJ0.
pose proof HACCT as (_ & _ & _ & HA4 & _).
assert (Hv : -2 ^ 31 <= v < 2 ^ 31) by (destruct HARM as [(-> & _) | (-> & ? & _)]; lia).
pose proof (RA.resp_len v Hv) as HTL.
(* ---- the seed at 0x8a628 ---- *)
destruct (sas8_seed Wc regs1 memc) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (sas8_E regs1)) by (unfold sas8_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (sas8_E regs1) n = ew (Ereg regs1 sas8_extra) n)
  by (intros n Hn; unfold sas8_E; apply Eimg_low; exact Hn).
remember (sas8_E regs1) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
clear HE EL.
(* 0x8a628: jal to the snprintf wrapper's trampoline *)
paj_run_tok RUN HS HJ SHOK sas8_Bspan.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (md1 := m) in *; clearbody md1 end.
pmkst HS.
rename ms into ms1.
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (8%bv : bv 5) U8. prreg HS (9%bv : bv 5) U9. prreg HS (10%bv : bv 5) U10. prreg HS (11%bv : bv 5) U11.
prreg HS (12%bv : bv 5) U12. prreg HS (13%bv : bv 5) U13.
prreg HS (18%bv : bv 5) U18. prreg HS (19%bv : bv 5) U19. prreg HS (20%bv : bv 5) U20. prreg HS (23%bv : bv 5) U23.
prreg HS (25%bv : bv 5) U25. prreg HS (26%bv : bv 5) U26. prreg HS (27%bv : bv 5) U27.
assert (U2' : getr (ms_regs ms1) 2 = w64 s1) by (rewrite U2, (EEo 2%nat 2%bv eq_refl); exact Q2).
assert (U3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite U3, (EEo 3%nat 3%bv eq_refl); exact Q3).
assert (U4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite U4, (EEo 4%nat 4%bv eq_refl); exact Q4).
assert (U8' : getr (ms_regs ms1) 8 = w64 sp0) by (rewrite U8, (EEo 8%nat 8%bv eq_refl); exact Q8).
assert (U9' : getr (ms_regs ms1) 9 = w64 s1) by (rewrite U9, (EEo 9%nat 9%bv eq_refl); exact Q9).
assert (U10' : getr (ms_regs ms1) 10 = w64 (F + 64)) by (rewrite U10, (EEo 10%nat 10%bv eq_refl); exact Ha0).
assert (U11' : getr (ms_regs ms1) 11 = w64 32) by (rewrite U11, (EEo 11%nat 11%bv eq_refl); exact Ha1).
assert (U12' : getr (ms_regs ms1) 12 = w64 SA_FMT_RESP) by (rewrite U12, (EEo 12%nat 12%bv eq_refl); exact Ha2).
assert (U13' : getr (ms_regs ms1) 13 = w64 v) by (rewrite U13, (EEo 13%nat 13%bv eq_refl); exact Ha3).
assert (U18' : getr (ms_regs ms1) 18 = w64 F) by (rewrite U18, (EEo 18%nat 18%bv eq_refl); exact Q18).
assert (U19' : getr (ms_regs ms1) 19 = getr regs 11) by (rewrite U19, (EEo 19%nat 19%bv eq_refl); exact Q19).
assert (U20' : getr (ms_regs ms1) 20 = w64 (F + 64)) by (rewrite U20, (EEo 20%nat 20%bv eq_refl); exact Q20).
assert (U23' : getr (ms_regs ms1) 23 = w64 (F + 32)) by (rewrite U23, (EEo 23%nat 23%bv eq_refl); exact Q23).
assert (U25' : getr (ms_regs ms1) 25 = w64 (SHADOW_OFF + F / 8))
  by (rewrite U25, (EEo 25%nat 25%bv eq_refl); exact Q25).
assert (U26' : getr (ms_regs ms1) 26 = w64 F) by (rewrite U26, (EEo 26%nat 26%bv eq_refl); exact Q26).
assert (U27' : getr (ms_regs ms1) 27 = w64 (-8)) by (rewrite U27, (EEo 27%nat 27%bv eq_refl); exact Q27).
assert (HRA : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite U1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* the run writes no memory *)
assert (K1 : forall a, rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & _). vm_compute in Hin. destruct Hin. }
(* 0x8a628: the wrapper writes "resp <v>" and its terminator into buf; the rest is M8 at the FP state it returns *)
eapply (sas_snp_call B MT HB LAWS IMG ASNPRINTF ly S W regs mem md ch pu id pp pc uri placement client R O
  lyc Sc Wc (ms_regs ms1) (ms_mem ms1) md1 pos (sa_ev6 R) 64 32 SA_FMT_RESP v RO_lit_21d40 RA.RESP_FMT
  (RA.RESP_HEAD ++ PF.pf_dec v) RA.RESP_PS HCXs HFRM0 HJ U2' U3' U4' HRA U10' U11' U12' U13' Hv
  ltac:(lia) eq_refl ltac:(lia) eq_refl ltac:(lia)).
- (* buf's four shadow bytes *)
  intros i Hi. change (32 / 8) with 4 in Hi. change (64 / 8) with 8. rewrite K1. exact (HBUF i Hi).
- (* the format "resp %d", a literal of CmdRo.v *)
  intros rd Hro. destruct Hro as [Hro _]. unfold cmd_ro_bytes in Hro.
  repeat match type of Hro with
  | abytes_atR _ 0x21d40 _ /\ _ => exact (proj1 Hro)
  | _ /\ _ => apply proj2 in Hro
  end.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- unfold SA_FMT_RESP. lia.
- apply Z.leb_le. vm_compute. reflexivity.
- exact RA.resp_parse.
- exact (RA.resp_text v).
- vm_compute. exact I.
- lia.
- (* back at 0x8a62c, at the FP state fx1 the wrapper returned *)
  intros fx1 regs2 mem2 md2 H01 HFRM1 HJ2 HP2 HBY HKP.
  rewrite U1.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    change (Z_to_bv 64 (BASE + k)) with (Z_to_bv 64 (BASE + L_M8)) end.
  apply (M8 fx1 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs2 mem2 md2 pos HCXs HFRM1).
  (* the bytes M7 holds in memory: the wrapper wrote its window and buf's text only *)
  destruct (sas_kept B MT LAWS ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc memc mdc pos
    (sa_ev6 R) mem2 (F + 64) (F + 64 + Z.of_nat (length (RA.RESP_HEAD ++ PF.pf_dec v)) + 1) R2 O6 HCXs HJ0
    ltac:(fold F; lia) ltac:(fold F; lia)
    ltac:(intros a Ha Hw Hd _; rewrite (HKP a Ha Hw Hd); apply K1)
    HFRM HFLG HBUF HREP2 HA4) as (HFRM2 & HFLG2 & HBUF2 & HREP3).
  assert (HPR : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms1) (Z_to_bv 5 r))
    by exact HP2.
  unfold sa_M8m, sa_core. cbv zeta.
  split.
  { split; [exact HJ2|].
    split; [exact HFRM2|].
    split; [exact HFLG2|].
    split; [exact (eq_trans (HPR 2 ltac:(unfold acallee_saved; lia)) U2')|].
    split; [exact (eq_trans (HPR 3 ltac:(unfold acallee_saved; lia)) U3')|].
    split; [exact (eq_trans (HPR 4 ltac:(unfold acallee_saved; lia)) U4')|].
    split; [exact (eq_trans (HPR 8 ltac:(unfold acallee_saved; lia)) U8')|].
    split; [exact (eq_trans (HPR 9 ltac:(unfold acallee_saved; lia)) U9')|].
    split; [exact (eq_trans (HPR 18 ltac:(unfold acallee_saved; lia)) U18')|].
    split; [exact (eq_trans (HPR 19 ltac:(unfold acallee_saved; lia)) U19')|].
    split; [exact (eq_trans (HPR 23 ltac:(unfold acallee_saved; lia)) U23')|].
    split; [exact (eq_trans (HPR 25 ltac:(unfold acallee_saved; lia)) U25')|].
    split; [exact (eq_trans (HPR 26 ltac:(unfold acallee_saved; lia)) U26')|].
    exact (eq_trans (HPR 27 ltac:(unfold acallee_saved; lia)) U27'). }
  split; [exact (eq_trans (HPR 20 ltac:(unfold acallee_saved; lia)) U20')|].
  split; [exact HBUF2|].
  exists v, R2, O6.
  split; [exact HARM|].
  split.
  { exact (snt_astr_of_text SEGS (w_H Wc) mem2 (F + 64) (RA.RESP_HEAD ++ PF.pf_dec v) (resp v)
      (RA.pf_resp v Hv) (resp_no0 v) HBY). }
  split; [exact HREP3|].
  split; [exact HACCT | exact HMO6].
Qed.
End e.
End f.
End d.
Print Assumptions sa_m7_ok.
