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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 223 of its 257 lines of code are new or changed and 378 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (0x8a400), stage 3: M2 (0x8a554) to M3
   (0x8a574), the inlined arg_i's call of the snprintf wrapper on (b, 16, "%d", id).

   0x8a554 .. 0x8a570: `sb zero,4(s9)`, `sb zero,5(s9)` (b's two shadow bytes 4 and 5 of the frame's 16 at s9 =
   SHADOW_OFF + F / 8 marked usable: sa_b0), `auipc a0` / `addi a2,a0` (a2 := "%d", 0x21f40 = A_OBJ 51, VOBJS),
   `li a1,16`, `mv a0,s7` (b = F + 32), `mv a3,s3` (id), `jal 0x451d0` (the interceptor trampoline of snprintf,
   return address 0x8a574 = M3). The two stores run on a fresh symbolic state whose one region is the frame's shadow
   at the atom of s9 (the plain runner, PaCallRun.v's paj_run_shc; the stores are the call's own frame-shadow bytes,
   in_frames); the region's chunks after the run give the two zero bytes. The call is sup_add_sn.v's sas_snp_call
   (RtPFCmd.v's asnprintf_sh at FR_cmd: the text of "%d" on id is printf_facts_c's pf_dec id, which CmdSnText.v's
   snt_pf_dec turns into RecFacts' dec id, 1 <= |dec id| <= 11 < 16); the rest is the next stage at the FP state fx1
   the wrapper returns. M3's other facts in memory come from sas_kept: the step writes only b's two shadow bytes, the
   wrapper's stack window and [b, b + |dec id| + 1). The donor is the pre-pass-4 A walk's snprintf step
   (lib/A/Prog/sup_add_s6.v on a working branch 87f17ee4716) and its stage 7 for the shadow stores. *)
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
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaNoChain PaLibF PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtPFPf RtPFShared RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
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

(* the symbolic state at 0x8a554: every register its own atom; one region, the frame's 16 shadow bytes at the atom of
   s9 (25), of which the run may write b's two (offsets 4 and 5; CmdSnText.v's snt_b_shadow); no fact *)
Definition ss_sas3 : sstate := mkSS L_M2 sr_atoms [snt_b_shadow] None (mkFacts [] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Lemma sas3_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem sb,
  getr regs 25 = w64 sb -> 0 <= sb -> sb + 16 <= 2 ^ 64 ->
  (forall o, 4 <= o < 6 -> writable_at SEGS (mrestrict (w_H W) mem) (sb + o)) ->
  st_ok_pi SEGS VAL (snt_E regs) ss_sas3 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L_M2)) mem (seg_rom SEGS))).
Proof.
intros W regs mem sb H25 Hsb0 Hsb1 Hw.
assert (E25 : ew (snt_E regs) 25 = getr regs 25).
{ unfold snt_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 25 25%bv eq_refl). }
unfold ss_sas3. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold snt_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold snt_b_shadow, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E25, H25. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [exact Hw | apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- vm_compute. repeat split.
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
Hypothesis VOBJS : cmd_val_objs.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

Lemma sa_m2_ok : SA_M3_stmt B MT -> SA_M2_at B MT.
Proof using HB LAWS IMG ASNPRINTF VOBJS.
intros M3. unfold SA_M2_at.
intros ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCX HFRM0 HM.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO.
pose proof pa_B_ok as (HBa & HBb & HBc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (HCEIL : ASAN_CEIL = alloc_ceiling) by reflexivity.
assert (HSTK : SUP_ADD_STK = 16736) by reflexivity.
assert (HK2 : CMD_SNP_K = 8192) by reflexivity.
pose proof HCX as HCXs.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & Hfr & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT & HC &
  HCT & HREP & Hev & Hlive & MOK).
unfold sa_M2m, sa_core in HM. cbv zeta in HM.
destruct HM as ((HJ & HFRM & HFLG & Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q23 & Q25 & Q26 & Q27) &
  Q20 & Q21 & Q24 & HBUF & O2 & HREP2 & HACCT & HMO2).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (sp0 := spZ regs) in *.
set (s1 := sa_s1 sp0) in *.
set (F := frame_addr lyc 1 pos) in *.
assert (Hs1 : s1 = sp0 - 128 \/ s1 = sp0 - 144) by (clear - Hal16; unfold s1, sa_s1; Z.div_mod_to_equations; lia).
pose proof HJ as HJ0.
pose proof HACCT as (_ & _ & _ & HA4 & _).
(* the frame and its shadow *)
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrsc & _).
assert (HFin : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HARc HFin) as (HF32 & HFapp & _ & HFSpres).
change (fs_frame_bytes 1 / 8) with 16 in HFSpres. unfold shadow_addr in HFSpres. fold F in HF32, HFapp, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc HFin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFapp, HFceil. fold F in HF4096, HFceil.
unfold in_app in HFapp. destruct HFapp as (HFa & HFb).
assert (HFdiv : 8 * (F / 8) <= F /\ 0 <= F / 8) by (split; [apply Z.mul_div_le; lia | apply Z.div_pos; lia]).
(* the frame's shadow bytes lie below the stack and outside the frame *)
assert (SHN : forall j, 0 <= j < 16 ->
  SHADOW_OFF + F / 8 + j < alloc_ceiling /\ ~ (F <= SHADOW_OFF + F / 8 + j < F + 128)).
{ intros j Hj. destruct HFb as [Hl | [Hh1 Hh2]]; split; lia. }
(* the text of "%d" on id *)
pose proof (dec_length id Hid) as HDL.
pose proof (snt_pf_dec id Hid) as HPD.
assert (HTLen : length (PF.pf_dec id) = length (dec id))
  by (rewrite <- HPD; unfold PF.pf_bytes; rewrite length_map; reflexivity).
(* ---- the seed at 0x8a554 ---- *)
pose proof (sas3_seed Wc regs1 memc (SHADOW_OFF + F / 8) Q25 ltac:(lia) ltac:(lia)
  (fun o Ho => apresent_writable SEGS _ _ _ (proj1 (HFSpres o ltac:(lia))))) as HS.
assert (HEI : img_env VAL A_LIM (snt_E regs1)) by (unfold snt_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (snt_E regs1) n = ew (Ereg regs1 []) n)
  by (intros n Hn; unfold snt_E; apply Eimg_low; exact Hn).
remember (snt_E regs1) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
clear HE EL.
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF + F / 8).
{ rewrite (EEo 25%nat 25%bv eq_refl), Q25. unfold w64. apply unsigned_lit_small. lia. }
(* 0x8a554 .. 0x8a570: b's two shadow bytes, a2 := "%d", a1 := 16, a0 := b, a3 := id, jal to the wrapper *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U25 in Hr.
  right; right; right; left. exists 1, pos. split; [left; reflexivity|]. right.
  unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. fold F. lia. }
lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (md1 := m) in *; clearbody md1 end.
pmkst HS.
rename ms into ms1.
(* b's two shadow bytes after the stores: the region's chunks *)
assert (HB0 : forall i, 0 <= i < 2 -> rdW Wc (ms_mem ms1) (SHADOW_OFF + F / 8 + 4 + i) = Some 0).
{ destruct (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HFA & _).
  rewrite Forall_forall in HFA.
  lazymatch type of HFA with forall x, In x ?rs0 -> _ =>
    let rs := eval vm_compute in rs0 in
    lazymatch rs with context [YP09.mkRegion (Some 25%nat) ?lo ?hi ?wlo ?whi ?cs] =>
      pose proof (HFA (YP09.mkRegion (Some 25%nat) lo hi wlo whi cs) ltac:(vm_compute; tauto)) as HR25
    end end.
  cbn [ms_mem restrict] in HR25.
  intros i Hi. assert (Hi2 : i = 0 \/ i = 1) by lia.
  destruct Hi2 as [-> | ->].
  - pose proof (field_of_region_any (segs := SEGS) E _ 25 (SHADOW_OFF + F / 8) _ _ _ _ _ 4 1%N (SLit 0) HR25 U25
      ltac:(vm_compute; tauto) ltac:(lia)) as Hv.
    lazymatch type of Hv with val_mem _ _ _ _ ?y => replace y with 0 in Hv by (vm_compute; reflexivity) end.
    rewrite Z.add_0_r. exact (aview_of_val_mem1 SEGS (w_H Wc) (ms_mem ms1) _ 0 Hv ltac:(lia)).
  - pose proof (field_of_region_any (segs := SEGS) E _ 25 (SHADOW_OFF + F / 8) _ _ _ _ _ 5 1%N (SLit 0) HR25 U25
      ltac:(vm_compute; tauto) ltac:(lia)) as Hv.
    lazymatch type of Hv with val_mem _ _ _ _ ?y => replace y with 0 in Hv by (vm_compute; reflexivity) end.
    replace (SHADOW_OFF + F / 8 + 4 + 1) with (SHADOW_OFF + F / 8 + 5) by lia.
    exact (aview_of_val_mem1 SEGS (w_H Wc) (ms_mem ms1) _ 0 Hv ltac:(lia)). }
(* the run writes b's two shadow bytes only *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 6) ->
  rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha Hs.
  refine (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms1)
    (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 6) HFr _ a Ha Hs).
  intros b wlo whi x Hwin Hx. vm_compute in Hwin.
  destruct Hwin as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hx. rewrite U25 in Hx. exact Hx. }
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (8%bv : bv 5) U8. prreg HS (9%bv : bv 5) U9. prreg HS (10%bv : bv 5) U10. prreg HS (11%bv : bv 5) U11.
prreg HS (12%bv : bv 5) U12. prreg HS (13%bv : bv 5) U13.
prreg HS (18%bv : bv 5) U18. prreg HS (19%bv : bv 5) U19. prreg HS (20%bv : bv 5) U20. prreg HS (21%bv : bv 5) U21.
prreg HS (23%bv : bv 5) U23. prreg HS (24%bv : bv 5) U24.
prreg HS (25%bv : bv 5) U25r. prreg HS (26%bv : bv 5) U26. prreg HS (27%bv : bv 5) U27.
assert (U2' : getr (ms_regs ms1) 2 = w64 s1) by (rewrite U2, (EEo 2%nat 2%bv eq_refl); exact Q2).
assert (U3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite U3, (EEo 3%nat 3%bv eq_refl); exact Q3).
assert (U4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite U4, (EEo 4%nat 4%bv eq_refl); exact Q4).
assert (U8' : getr (ms_regs ms1) 8 = w64 sp0) by (rewrite U8, (EEo 8%nat 8%bv eq_refl); exact Q8).
assert (U9' : getr (ms_regs ms1) 9 = w64 s1) by (rewrite U9, (EEo 9%nat 9%bv eq_refl); exact Q9).
assert (U10' : getr (ms_regs ms1) 10 = w64 (F + 32)) by (rewrite U10, (EEo 23%nat 23%bv eq_refl); exact Q23).
assert (U11' : getr (ms_regs ms1) 11 = w64 16) by (rewrite U11; reflexivity).
assert (U12' : getr (ms_regs ms1) 12 = w64 SA_FMT_D) by (rewrite U12; exact (snt_fmt_d VOBJS E HEI)).
assert (U13' : getr (ms_regs ms1) 13 = w64 id)
  by (rewrite U13, (EEo 19%nat 19%bv eq_refl), Q19; exact H11).
assert (U18' : getr (ms_regs ms1) 18 = w64 F) by (rewrite U18, (EEo 18%nat 18%bv eq_refl); exact Q18).
assert (U19' : getr (ms_regs ms1) 19 = getr regs 11) by (rewrite U19, (EEo 19%nat 19%bv eq_refl); exact Q19).
assert (U20' : getr (ms_regs ms1) 20 = getr regs 13) by (rewrite U20, (EEo 20%nat 20%bv eq_refl); exact Q20).
assert (U21' : getr (ms_regs ms1) 21 = getr regs 12) by (rewrite U21, (EEo 21%nat 21%bv eq_refl); exact Q21).
assert (U23' : getr (ms_regs ms1) 23 = w64 (F + 32)) by (rewrite U23, (EEo 23%nat 23%bv eq_refl); exact Q23).
assert (U24' : getr (ms_regs ms1) 24 = w64 (rec_slot R)) by (rewrite U24, (EEo 24%nat 24%bv eq_refl); exact Q24).
assert (U25' : getr (ms_regs ms1) 25 = w64 (SHADOW_OFF + F / 8))
  by (rewrite U25r, (EEo 25%nat 25%bv eq_refl); exact Q25).
assert (U26' : getr (ms_regs ms1) 26 = w64 F) by (rewrite U26, (EEo 26%nat 26%bv eq_refl); exact Q26).
assert (U27' : getr (ms_regs ms1) 27 = w64 (-8)) by (rewrite U27, (EEo 27%nat 27%bv eq_refl); exact Q27).
assert (HRA : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite U1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* 0x8a570: the wrapper writes the decimal text of id and its terminator into b; the rest is M3 at the FP state it
   returns *)
eapply (sas_snp_call B MT HB LAWS IMG ASNPRINTF ly S W regs mem md ch pu id pp pc uri placement client R O
  lyc Sc Wc (ms_regs ms1) (ms_mem ms1) md1 pos (sa_ev2 R) 32 16 SA_FMT_D id RO_lit_21f40 [37; 100]
  (PF.pf_dec id) [PF.Pd] HCXs HFRM0 HJ U2' U3' U4' HRA U10' U11' U12' U13' Hid
  ltac:(lia) eq_refl ltac:(lia) eq_refl ltac:(lia)).
- (* b's two shadow bytes *)
  intros i Hi. change (16 / 8) with 2 in Hi. change (32 / 8) with 4. exact (HB0 i Hi).
- (* the format "%d", a literal of CmdRo.v *)
  intros rd Hro. destruct Hro as [Hro _]. unfold cmd_ro_bytes in Hro.
  repeat match type of Hro with
  | abytes_atR _ 0x21f40 _ /\ _ => exact (proj1 Hro)
  | _ /\ _ => apply proj2 in Hro
  end.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- unfold SA_FMT_D. lia.
- apply Z.leb_le. vm_compute. reflexivity.
- exact snt_parse_d.
- exact (snt_text_d id).
- vm_compute. exact I.
- rewrite HTLen. lia.
- (* back at 0x8a574, at the FP state fx1 the wrapper returned *)
  intros fx1 regs2 mem2 md2 H01 HFRM1 HJ2 HP2 HBY HKP.
  rewrite U1.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    change (Z_to_bv 64 (BASE + k)) with (Z_to_bv 64 (BASE + L_M3)) end.
  apply (M3 fx1 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs2 mem2 md2 pos HCXs HFRM1).
  (* the bytes M2 holds in memory: the step wrote b's shadow, the wrapper's window and b's text only *)
  destruct (sas_kept B MT LAWS ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc memc mdc pos
    (sa_ev2 R) mem2 (F + 32) (F + 32 + Z.of_nat (length (PF.pf_dec id)) + 1) (rec_record R REC_ADD [sarg uri]) O2
    HCXs HJ0 ltac:(fold F; lia) ltac:(fold F; lia)
    ltac:(intros a Ha Hw Hd Hs; rewrite (HKP a Ha Hw Hd); exact (K1 a Ha Hs))
    HFRM HFLG HBUF HREP2 HA4) as (HFRM2 & HFLG2 & HBUF2 & HREP3).
  (* b's shadow is still 0: the wrapper writes neither the shadow nor below the stack *)
  assert (HB02 : sa_b0 (rdW Wc mem2) F).
  { intros i Hi. pose proof (SHN (4 + i) ltac:(lia)) as [N1 N2].
    rewrite HKP; [exact (HB0 i Hi) | lia | fold sp0 s1; destruct Hs1; lia | fold F; lia]. }
  assert (HPR : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms1) (Z_to_bv 5 r))
    by exact HP2.
  unfold sa_M3m, sa_core. cbv zeta.
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
  split; [exact (eq_trans (HPR 21 ltac:(unfold acallee_saved; lia)) U21')|].
  split; [exact (eq_trans (HPR 24 ltac:(unfold acallee_saved; lia)) U24')|].
  split; [exact HBUF2|].
  split; [exact HB02|].
  split.
  { exact (snt_astr_of_text SEGS (w_H Wc) mem2 (F + 32) (PF.pf_dec id) (dec id) HPD (dec_no0 id) HBY). }
  exists O2.
  split; [exact HREP3|].
  split; [exact HACCT | exact HMO2].
Qed.
End e.
End f.
End d.
Print Assumptions sa_m2_ok.
