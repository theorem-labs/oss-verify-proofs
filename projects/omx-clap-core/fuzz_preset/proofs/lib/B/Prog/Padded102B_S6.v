(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 366 of its 406 lines of code are new or changed and 664 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Padded102B.v, with its module paths and module names changed; 127 of its 176 lines of code are new or changed and 357 lines of the source are left out. *)
(* Written by Theorem Labs, 2026-10 (row PDB-S6 of the internal file FREE-PIECES-102.md), segment S6 of padded, image B' (#102 asan-ubsan). *)
(* fuzz_preset, image B': segment S6 of padded, the EPILOGUE. From the cut PD_EPI (B' 0x83118, `mv a0, s0`) through the
   `ret` at 0x83134 (Listing_prog.v :1698-1705, slots PD_SLOT + 28 .. PD_SLOT + 35): a0 := s0, the five loads of
   ra / s0 / s1 / s2 / s3 from the frame, `addi sp, sp, 48`, `ret`. The obligation is pd_s6_stmt of Padded102B.v,
   proved as stated. S6 writes no memory: the arm pd_at_epi carries passes to pd_Q unchanged (res := b), and the
   image record pd_img that heads the statement is not needed.
   THE SEAT, built here at PD_EPI: the environment pd_E and the frame pd_frame of Padded102B.v (the five saved words
   of pd_saved as the extra atoms 32 .. 36), and the one fact on the body sp (atom 2) the frame needs. It is not
   Padded102B.v's pd_ss / pd_seat_stmt: pd_seat_stmt is a statement no file proves, so citing it would add a
   premise to pd_s6_stmt, and the epilogue needs none of pd_facts' other atoms nor its alias hints (no instrumented
   access, so no shadow entry either). The run is YC1fPx's paj_run_x at Padded102B.v's closed listing tables PL_pd_B
   (PAImg_prog.v, the image instance, is not Required), the ret YC1fP's paj_ret_at.
   Numerals: 48 (LENGTH: the frame, `addi sp, sp, 48`); 16 / 4 (LENGTH: the stack alignment and its log); 2 ^ 46 / 2 ^ 47
   (DERIVED: stack bounds, as pd_facts); atom indices 32 .. 36 (DERIVED: the engine's extra atoms, pd_frame's);
   register numbers (RISC-V). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcallx YGcallcf YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG01cf YG00cf YG0ncf YG0dcf YG0sshcf YGcfRoomPre YG0lawscf YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos PresetRun
  PresetReqAt PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnReader
  PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Padded102B.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- S6's seat at PD_EPI: the frame pd_frame (Padded102B.v) and the body sp's fact (pd_facts' first entry) ---- *)
Definition pd6_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46 - 48) (2 ^ 47) 4)] [] [].
Definition pd6_ss : sstate := mkSS (pd_koff PD_EPI) sr_atoms [pd_frame] None pd6_facts.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instance prh_img_B.
#[local] Notation CP := CfParams_preset.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
Variable B : asyms.
#[local] Notation ARc := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARc).
(* the allocator's laws at ARc: AR_laws_ok_cf (YG0lawscf.v), lifted by YGcallcf.v's AR_laws_x_xs *)
Let LAWS_cf : AR_laws_cf (cp := CP) SEGS B := AR_laws_ok_cf (cp := CP) SEGS B.
Let LAWS : AR_laws_x SEGS B ARc (@cf_head CP) := AR_laws_x_xs (cp := CP) SEGS B LAWS_cf.

Lemma pd_s6 : pd_s6_stmt (SK := SK) (PA := PA) B.
Proof.
unfold pd_s6_stmt.
intros _ D ly S Hp W regs mem md k b (own' & HB & HARM & HDEAD).
destruct HB as (Hra & HJ & HSV & HRG & _ & _ & HROD & HMN & HHp & HLED & HRL & HSRC & _ & _ & HHU).
pose proof HSRC as (HBY & _). clear HSRC.
destruct HRG as (G2 & G8 & G9 & G18 & G19 & G3 & G4 & G20).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
unfold pd_J in HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (Rsp : 2 ^ 46 <= pd_sp0 D <= 2 ^ 47) by lia.
(* the five saved words *)
unfold pd_saved in HSV. rewrite Forall_forall in HSV.
pose proof (HSV (40, 1%bv) ltac:(repeat (first [left; reflexivity | right]))) as VRA.
pose proof (HSV (32, 8%bv) ltac:(repeat (first [left; reflexivity | right]))) as VS0.
pose proof (HSV (24, 9%bv) ltac:(repeat (first [left; reflexivity | right]))) as VS1.
pose proof (HSV (16, 18%bv) ltac:(repeat (first [left; reflexivity | right]))) as VS2.
pose proof (HSV (8, 19%bv) ltac:(repeat (first [left; reflexivity | right]))) as VS3.
cbn [fst snd] in VRA, VS0, VS1, VS2, VS3. clear HSV.
(* ---- the seat ---- *)
set (E := pd_E (PA := PA) D regs).
set (X := map (getr (din_regs D)) [1%bv; 8%bv; 9%bv; 18%bv; 19%bv]).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs X) n)
  by (intros n Hn; subst E X; unfold pd_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2%bv) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8%bv) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (QFX : forall j0, (j0 < 5)%nat -> ew E (32 + j0) = nth j0 X (Z_to_bv 64 0)).
{ intros j0 Hj0. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (Usp : bv_unsigned (ew E 2) = pd_sp0 D - 48) by (rewrite E2, G2; unfold w64; apply unsigned_lit_small; lia).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pd_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs X) E)
  by (split; [intros n Hn; subst E X; unfold pd_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E pd6_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pd_koff PD_EPI)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pd6_ss. apply pa_entry_st_ok_full.
  - subst E X. unfold pd_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, pd_frame.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ (pd_sp0 D - 48) 8 8 (SOff 36 0) (bv_unsigned (getr (din_regs D) 19%bv)));
        [cbn [sv_denot]; change (ew E 36) with (ew E (32 + 4)); rewrite (QFX 4%nat) by lia; cbn [nth X map];
         rewrite Z.add_0_r; reflexivity
        | apply bv_unsigned_in_range | lia |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ VS3).
    + apply (chunk_ok_val SEGS E _ (pd_sp0 D - 48) 16 8 (SOff 35 0) (bv_unsigned (getr (din_regs D) 18%bv)));
        [cbn [sv_denot]; change (ew E 35) with (ew E (32 + 3)); rewrite (QFX 3%nat) by lia; cbn [nth X map];
         rewrite Z.add_0_r; reflexivity
        | apply bv_unsigned_in_range | lia |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ VS2).
    + apply (chunk_ok_val SEGS E _ (pd_sp0 D - 48) 24 8 (SOff 34 0) (bv_unsigned (getr (din_regs D) 9%bv)));
        [cbn [sv_denot]; change (ew E 34) with (ew E (32 + 2)); rewrite (QFX 2%nat) by lia; cbn [nth X map];
         rewrite Z.add_0_r; reflexivity
        | apply bv_unsigned_in_range | lia |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ VS1).
    + apply (chunk_ok_val SEGS E _ (pd_sp0 D - 48) 32 8 (SOff 33 0) (bv_unsigned (getr (din_regs D) 8%bv)));
        [cbn [sv_denot]; change (ew E 33) with (ew E (32 + 1)); rewrite (QFX 1%nat) by lia; cbn [nth X map];
         rewrite Z.add_0_r; reflexivity
        | apply bv_unsigned_in_range | lia |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ VS0).
    + apply (chunk_ok_val SEGS E _ (pd_sp0 D - 48) 40 8 (SOff 32 0) (bv_unsigned (getr (din_regs D) 1%bv)));
        [cbn [sv_denot]; change (ew E 32) with (ew E (32 + 0)); rewrite (QFX 0%nat) by lia; cbn [nth X map];
         rewrite Z.add_0_r; reflexivity
        | apply bv_unsigned_in_range | lia |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ VRA).
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split; [exact I | exact I]].
    cbn [pd6_facts f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. split; [lia|]. split; [|lia].
    replace (pd_sp0 D - 48) with (pd_sp0 D + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (SHOK : sh_ok SEGS PD_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
(* the five saved words as atoms *)
assert (Q32 : ew E 32 = getr (din_regs D) 1%bv) by (change (ew E 32) with (ew E (32 + 0)); rewrite (QFX 0%nat) by lia; reflexivity).
assert (Q33 : ew E 33 = getr (din_regs D) 8%bv) by (change (ew E 33) with (ew E (32 + 1)); rewrite (QFX 1%nat) by lia; reflexivity).
assert (Q34 : ew E 34 = getr (din_regs D) 9%bv) by (change (ew E 34) with (ew E (32 + 2)); rewrite (QFX 2%nat) by lia; reflexivity).
assert (Q35 : ew E 35 = getr (din_regs D) 18%bv) by (change (ew E 35) with (ew E (32 + 3)); rewrite (QFX 3%nat) by lia; reflexivity).
assert (Q36 : ew E 36 = getr (din_regs D) 19%bv) by (change (ew E 36) with (ew E (32 + 4)); rewrite (QFX 4%nat) by lia; reflexivity).
clearbody E X. clear QFX EL.
replace (pd_pc PD_EPI) with (BASE + pd_koff PD_EPI) by (unfold pd_pc, pd_koff; lia).
pose (RUN := @paj_run_x fx rc SK B_prog_listing PL_pd_B PA B PST ARc _ LAWS).
pose (RET := @paj_ret_at fx rc B_prog_listing PL_pd_B PA).
(* ---- slots 28 .. 34: a0 = s0, the five loads, sp += 48; the run stops at the ret ---- *)
paj_run_tok_x RUN HS HJ SHOK PD_Bspan.
{ intros a (r & Hin & Hr). cbn [pd6_ss ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [pd_frame YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
(* ---- after the run: no byte written (pd_frame's write window is empty) ---- *)
assert (EM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Hr). cbn [pd6_ss ss_mem In] in Hin.
  destruct Hin as [<- | []]. cbn [pd_frame YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9.
prreg HS (10%bv : bv 5) R10. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
(* x3, x4, x20 .. x27: the run does not touch them *)
assert (KR : forall r0, In r0 (map (Z_to_bv 5) [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]) ->
  getr (ms_regs ms) r0 = getr regs r0).
{ intros r0 Hr0.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs _ (map (Z_to_bv 5) [3; 4; 20; 21; 22; 23; 24; 25; 26; 27])
    HS HAE) as K3.
  specialize (K3 ltac:(vm_compute; reflexivity) r0 Hr0). cbn [ms_regs restrict] in K3. exact K3. }
(* ---- slot 35: the ret, to the entry's ra ---- *)
eapply (RET W _ _ _ _ _ HS eq_refl); [vm_compute; reflexivity|].
intros mat'. unfold pd_post, fpostm, fpost, apost_base_x.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, Hp, r, m, d, k end.
split; [rewrite R1, Q32; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARc LAWS Hsegs); exact HJ|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R2, Usp. replace (pd_sp0 D - 48 + 48) with (pd_sp0 D) by lia. unfold pd_sp0, spZ.
    apply Z_to_bv_bv_unsigned.
  - rewrite (KR (Z_to_bv 5 3) ltac:(apply in_map; cbn [In]; lia)).
    replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact G3.
  - rewrite (KR (Z_to_bv 5 4) ltac:(apply in_map; cbn [In]; lia)).
    replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). exact G4.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8, Q33. reflexivity.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9, Q34. reflexivity.
  - assert (Hr' : r = 18 \/ r = 19 \/ 20 <= r <= 27) by lia.
    destruct Hr' as [-> | [-> | Hr']].
    + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18, Q35. reflexivity.
    + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19, Q36. reflexivity.
    + rewrite (KR (Z_to_bv 5 r) ltac:(apply in_map; cbn [In]; lia)). exact (G20 r Hr'). }
(* ---- the kit's post: the arm passes through, res := b, the hull use carried from S1, the outcome clause from
   the arm and its NULL-arm death (Padded102B.v pd_outc_of_arms); and the keep of memnorm ---- *)
unfold fQmn, pd_Q. rewrite EM. split.
- exists b, own'.
  split; [rewrite R10, E8, G8; reflexivity|].
  split; [exact HRL|]. split; [exact HHp|]. split; [exact HHU|]. split; [exact HLED|].
  split; [exact HBY|]. split; [exact (pd_outc_of_arms B D ly S W mem b own' HARM HDEAD) | exact HARM].
- exact HMN.
Qed.
End d.
