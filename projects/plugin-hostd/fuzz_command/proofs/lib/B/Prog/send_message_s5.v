(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from this harness's lib/A/Prog/send_message_s5.v (the ASan walk,
   a working branch 4f5a539710b, re-fitted d0af25245f3) to the ASan+UBSan build fuzz_command.asan-ubsan
   (lib/B): B's program points (the same offsets from the entry 0x86bf8); the record fact cmd_prog_unowned and the
   transport lemmas from a Theorem Labs lane's kit (lib/B/Prog/CmdRecImg.v, PaCallPg.v); a Theorem Labs lane's statement passes 4, 4b and 5
   (a working branch f490061c104): the free entry at every FP state (forall fx0), and the post apost_baseF (no
   printf-reaching code after verbs_receive, so its left disjunct). *)
(* Modified by Theorem Labs, 2026-10: send_message's last walk segment on plugin-hostd/fuzz_command's ASan+UBSan image, from
   verbs_receive's return (0x86d60) to the `ret`: the copy freed through the free wrapper, the inline release of the
   class-1 side-stack frame (shadow 0xf8, the retired magic, shadow 0xf5, the flag byte cleared), the epilogue and the
   contract's post. Ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close's
   segment chain and post assembly, ACh2.v) at origin/ossv/recipes c8557374ad2e, with the free call of A/ACho.v
   (flushFrame) and the frame release of A/AChx.v and A/ACk5.v (exitR). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaJournal CmdPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YE00 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c verbs_receive_c send_message_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import send_message_k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import send_message_l PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the symbolic state at 0x86d60
   Atoms 0..31 are the registers at verbs_receive's return; atoms 32..42 the entry values of the eleven registers the
   prologue saved (ra, s0..s9, in sm_saved_list's order), 43 the copy's block res, 44 the frame's flag address. s2 is
   aliased to s8 (both hold the frame F), so that `ld a0,120(s2)` reads the frame region. *)
Definition sm5_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25].
Definition sm5_extra (regs : bvmap 5 word) (res FL : Z) : list word :=
map (fun r => getr regs (Z_to_bv 5 r)) sm5_saved_regs ++ [Z_to_bv 64 res; Z_to_bv 64 FL].
Definition sm5_stack_chunks : list YP09.chunk :=
[ YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0)); YP09.mkChunk (-24) (CVal 8 (SOff 34 0));
  YP09.mkChunk (-32) (CVal 8 (SOff 35 0)); YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0)); YP09.mkChunk (-72) (CVal 8 (SOff 40 0));
  YP09.mkChunk (-80) (CVal 8 (SOff 41 0)); YP09.mkChunk (-88) (CVal 8 (SOff 42 0)) ].
(* the frame (s8, writable), its 16 shadow bytes (s7, writable) and the saved registers below the entry sp (s0) *)
Definition sm5_regions : smem :=
[ fframe_region 24 44 1 [YP09.mkChunk 40 (CVal 8 (SOff 43 0))]; fshadow_region 23 1 0 16 [];
  YP09.mkRegion (Some 8%nat) (-96) 0 0 0 sm5_stack_chunks ].
Definition sm5_atoms : list (nat * afact) := [ (24%nat, HPTR 5) ].
Definition ss_sm5 : sstate :=
mkSS SM_RET_VR (sr_set sr_atoms 18 (SOff 24 0)) sm5_regions None (mkFacts sm5_atoms [] []).
(* the flag byte, added before the release *)
Definition sm5_flag_region : YP09.region := YP09.mkRegion (Some 44%nat) 0 1 0 1 [].
Lemma sm5_div8 : forall F, F mod 32 = 0 -> F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32).
Proof.
intros F H. pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. split; [exact D|].
rewrite D at 1. replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia. apply Z.div_mul. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
(* the per-binary record (RULING-STMT.md §1 HB), the image facts (CmdRecBase.v cmd_img_facts), and a Theorem Labs lane's
   per-binary record fact cmd_prog_unowned (CmdRecImg.v) they give *)
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Let cmd_prog_unowned := CmdRecImg.cmd_prog_unowned SEGS B LAWS HB IMG.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.

(* the seed at verbs_receive's return (sm_entry's form, send_message_k.v:178-250) *)
Lemma sm5_seed : forall ly S W (regs : bvmap 5 word) mem md ch FP lyc Sc Wc (regs1 : bvmap 5 word) memc mdc k fpos n src res,
afn_pre SEGS B SEND_MESSAGE_STK ly S W regs mem md ch ->
sm_jr B FP ly S W regs mem md fpos lyc Sc Wc memc mdc k ->
sm_regs_core regs regs1 (frame_addr ly 1 fpos) n src ->
sm_saved regs (mrestrict (w_H Wc) memc) ->
sm_frame (mrestrict (w_H Wc) memc) (frame_addr ly 1 fpos) (flag_addr ly 1 fpos) ->
val_mem SEGS (mrestrict (w_H Wc) memc) (frame_addr ly 1 fpos + 40) 8 res -> 0 <= res < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (sm5_extra regs res (flag_addr ly 1 fpos)))) ss_sm5
(restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + SM_RET_VR)) memc (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch FP lyc Sc Wc regs1 memc mdc k fpos n src res HPRE HJR HRC HSV HFR HV40 Hres.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJR as (HJ & Hfrs).
pose proof HRC as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R27).
destruct HFR as (V120 & _ & _ & _ & _).
pose proof (proj1 HJ) as HARc.
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR (proj1 (proj2 HJ))) as (_ & EFA & _).
assert (EFL : forall c p, flag_addr lyc c p = flag_addr ly c p)
by (intros c p; unfold flag_addr; pose proof (EFA c p) as X; unfold frame_addr in X; lia).
assert (Hfin : In (1, fpos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HARc Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds _ _ LAWS _ _ _ _ _ 1 fpos HARc Hfin) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ 1 fpos HARc Hfin) as (_ & _ & _ & (HFL4096 & _ & HFLceil)).
change (fs_frame_bytes 1) with 128 in HFapp, HFpres, HFSpres, HFceil. change (128 / 8) with 16 in HFSpres.
rewrite !EFA in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil. rewrite !EFL in HFL4096, HFLceil.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
destruct (sm5_div8 F HFal) as (HFq & HF8).
assert (HSTK : 112 <= SEND_MESSAGE_STK) by (vm_compute; discriminate).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (sm5_extra regs res FL))).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
by (intros nn r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (sm5_extra regs res FL) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (UF : bv_unsigned (ew E 24) = F) by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 23) = SB + F / 8)
by (rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64, SB_F; apply unsigned_lit_small; unfold SB; lia).
assert (Usp : bv_unsigned (ew E 8) = spZ regs) by (rewrite (EE 8%nat 8%bv eq_refl), R8; reflexivity).
assert (HS0 : st_ok_pi SEGS VAL E (mkSS SM_RET_VR sr_atoms sm5_regions None (mkFacts sm5_atoms [] []))
  (mkst regs1 (Z_to_bv 64 (BASE + SM_RET_VR)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold sm5_regions, fframe_region, fshadow_region.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val app].
    + rewrite UF. change (fs_frame_bytes 1) with 128. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres (F + o) ltac:(lia))). }
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E _ F 40 8 (SOff 43 0) res); [| zside | zside | exact HV40].
        rewrite sv_denot_SOff0. exact (EX 11%nat ltac:(lia)).
      * apply (chunk_ok_val SEGS E _ F (128 - 8) 8 (SOff 44 0) FL); [| zside | zside |].
        { rewrite sv_denot_SOff0. exact (EX 12%nat ltac:(lia)). }
        replace (F + (128 - 8)) with (F + 120) by lia. exact V120.
    + rewrite USB. change (fs_frame_bytes 1 / 8) with 16. split; [unfold SB; lia|]. split; [unfold SB; lia|].
      split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres.
      apply (proj1 (HFSpres o ltac:(lia))).
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold sm5_stack_chunks.
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?j 0))) =>
        let jj := eval compute in (j - 32)%nat in
        let r := eval compute in (nth jj sm5_saved_regs 0) in
        apply (chunk_ok_val SEGS E _ (spZ regs) o 8 (SOff j 0) (bv_unsigned (getr regs (Z_to_bv 5 r))));
        [ rewrite sv_denot_SOff0; change j with (32 + jj)%nat; rewrite (EX jj ltac:(lia));
          cbn [nth sm5_extra sm5_saved_regs map app]; symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; zside
        | zside
        | apply HSV; cbn; tauto ] end.
  - apply pairwise_disjoint_of_extents.
    unfold sm5_regions, fframe_region, fshadow_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UF, USB, Usp.
    change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold SB.
    repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok sm5_atoms]. split; [|exact I]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite UF. change (2 ^ 5) with 32. split; [lia|]. split; [exact HFal | lia]. }
exact (ast_ok_pi_set_reg_fp E _ _ 18%bv (SOff 24 0) HS0 eq_refl
  ltac:(cbn [ms_regs mkst]; rewrite sv_denot_SOff0, (EE 24%nat 24%bv eq_refl), R24, R18; reflexivity)).
Qed.

(* P4 (verbs_receive's return, 0x86d60) to the contract's post at the `ret` *)
Theorem sm_s5 : SM_P4_stmt B MT.
Proof.
intros ly S W regs mem md ch src n D R O rest lyc Sc Wc regs1 memc mdc k fpos res
HCX HJR Hk HRC H21 H22 HSV HFR HV40 Hres Hnin HQ HBB MLE.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HCX as (HPRE & HFRM & Hfr3 & HROD & Hro & Hvobj & H10 & Hsrcr & H11 & Hn & HlenD & HD & Hsrc & HPerm
& HREP & Hcalls & Hdecl & Hev & Hlive & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJR as (HJ & Hfrs).
pose proof HRC as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R27).
assert (HSTK : 112 + ASTACK <= SEND_MESSAGE_STK) by (vm_compute; discriminate).
assert (Has : ASTACK = 16384) by reflexivity.
destruct (vr_runA (RecModel.rec_clear R) D) as [[R' x] quit] eqn:Evr.
cbv beta iota in HQ. destruct HQ as (O' & HREP' & HQUIT & HPermO & HninO).
assert (Hinres : In (res, Z.max n 1) (ablocks B lyc Sc))
by (eapply Permutation_in; [apply Permutation_sym; exact HPermO | apply in_or_app; right; left; reflexivity]).
pose proof (proj1 HJ) as HARc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (Z.max n 1) HARc Hinres) as (_ & Hres4096 & Hresceil & Hresapp & Hrespres & _ & _).
pose proof (sm5_seed ly S W regs mem md ch (ablocks_fp O ++ cmd_PG) lyc Sc Wc regs1 memc mdc k fpos n src res
HPRE HJR HRC HSV HFR HV40 ltac:(pose proof (req_size_pos (Z.max n 1) ltac:(lia)); lia)) as HS.
remember (Eimg (Ereg regs1 (sm5_extra regs res (flag_addr ly 1 fpos)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
by (intros nn r Hn'; subst E; apply ew_Eimg_Ereg_nat; exact Hn').
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (sm5_extra regs res (flag_addr ly 1 fpos)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear HE.
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR (proj1 (proj2 HJ))) as (_ & EFA & _).
assert (EFL : forall c p, flag_addr lyc c p = flag_addr ly c p)
by (intros c p; unfold flag_addr; pose proof (EFA c p) as X; unfold frame_addr in X; lia).
assert (Hfin : In (1, fpos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HARc Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds _ _ LAWS _ _ _ _ _ 1 fpos HARc Hfin) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ 1 fpos HARc Hfin) as (HFLp & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
change (fs_frame_bytes 1) with 128 in HFapp, HFpres, HFSpres, HFceil. change (128 / 8) with 16 in HFSpres.
rewrite !EFA in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil.
rewrite !EFL in HFLp, HFLown, HFLapp, HFLimg, HFL4096, HFLz, HFLceil.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
destruct (sm5_div8 F HFal) as (HFq & HF8).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39. pose proof (EX 8%nat ltac:(lia)) as E40.
pose proof (EX 9%nat ltac:(lia)) as E41. pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44.
cbn [Nat.add nth sm5_extra sm5_saved_regs map app] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44.
clear EX.
replace (Z_to_bv 5 1) with (1%bv : bv 5) in E32 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 8) with (8%bv : bv 5) in E33 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 9) with (9%bv : bv 5) in E34 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 18) with (18%bv : bv 5) in E35 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 19) with (19%bv : bv 5) in E36 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 20) with (20%bv : bv 5) in E37 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 21) with (21%bv : bv 5) in E38 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 22) with (22%bv : bv 5) in E39 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 23) with (23%bv : bv 5) in E40 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 24) with (24%bv : bv 5) in E41 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 25) with (25%bv : bv 5) in E42 by (apply bv_eq; reflexivity).
assert (Usp1 : sm_sp1 (spZ regs) + 16 <= spZ regs - 96 + 16 /\ spZ regs - 112 <= sm_sp1 (spZ regs) /\ (sm_sp1 (spZ regs) - spZ regs) mod 16 = 0).
{ unfold sm_sp1. pose proof (sp1_facts (spZ regs - 96) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (Q1 & Q2 & Q3).
  split; [lia|]. split; [lia|]. rewrite Zminus_mod, Q3, Hal16. reflexivity. }
assert (UF : bv_unsigned (ew E 24) = F) by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 23) = SB + F / 8)
by (rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64, SB_F; apply unsigned_lit_small; unfold SB; lia).
assert (Usp : bv_unsigned (ew E 8) = spZ regs) by (rewrite (EE 8%nat 8%bv eq_refl), R8; reflexivity).
pose proof HJ as (_ & HLY & _ & _ & _ & _ & Hnevc & _).
assert (HEVc : st_nev Sc < EV_MAX) by (unfold EV_SEND_MESSAGE in Hev; lia).
(* the reload of the copy's pointer and the call of the free wrapper *)
paj_run_shc RUNP RUNC HS HJ.
{ unfold ss_sm5, sm5_regions, fframe_region, fshadow_region. cbn [ss_mem app].
  eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 24%nat); [reflexivity | exact UF | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. change (fs_frame_bytes 1) with 128 in Ha.
    right; right; right; left. exists 1, fpos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. rewrite EFA. fold F. lia. }
  eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 23%nat); [reflexivity | exact USB | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right; right; right; left. exists 1, fpos. split; [left; reflexivity|]. right.
    unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. rewrite EFA. fold F.
    rewrite <- SB_SHADOW_OFF. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS. ppcs.
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
(* the frame chain at the realigned sp, read through the memory at the call *)
assert (HFPhi : forall a, alloc_ceiling <= a -> ~ inFP (ablocks_fp O ++ cmd_PG) a).
{ intros a Ha (r & Hr & Hra'). apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p m] & <- & Hpm). cbn [fst snd] in Hra'.
    assert (Hpm0 : In (p, m) (ablocks B ly S))
    by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | apply in_or_app; left; exact Hpm]).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hpm0) as (_ & _ & Hpc & _). lia.
  - unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra'; lia. }
destruct (sm_achain B (ablocks_fp O ++ cmd_PG) ly S W regs mem md ch fpos lyc Sc Wc memc mdc k HPRE HJR HFPhi HSV)
as (ch1 & Hch1).
assert (UN1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 128 \/ SB + F / 8 <= a < SB + F / 8 + 16) ->
  aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ apply (kept_of_frame (segs:=SEGS) E (ss_mem ss_sm5) (w_H Wc) memc (ms_mem ms) _ HFr).
  intros b wlo whi a Hin Hab. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hab; rewrite ?UF, ?USB, ?Usp in Hab; lia |]).
  destruct Hin. }
clear HF HFr HG.
assert (Hch1' : achain lyc (aview SEGS (w_H Wc) (ms_mem ms)) (sm_sp1 (spZ regs)) (spZ regs) ch1).
{ apply (achain_kept lyc (aview SEGS (w_H Wc) memc) _ _ _ _ (sm_sp1 (spZ regs)) Hch1); [lia | |].
  - pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). rewrite Etop. lia.
  - intros a Ha. apply UN1; [lia|]. unfold SB. lia. }
assert (Hspm : spZ (ms_regs ms) = sm_sp1 (spZ regs)).
{ unfold spZ at 1. rewrite Rsp, (EE 2%nat 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
(* the free wrapper frees the copy *)
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE4 fx) Wc (ms_regs ms) (ms_mem ms) SEND_MESSAGE_STK (spZ regs)
    (ablocks_fp O ++ cmd_PG) ly S W mem md [(1, fpos)] lyc Sc _ k res (Z.max n 1) (sm_sp1 (spZ regs) - spZ regs)
    (Z_to_bv 64 (BASE + 2104)) ch1 HJ Hinres).
  - rewrite Ra0, E43. reflexivity.
  - rewrite Hspm. lia.
  - exact (proj2 (proj2 Usp1)).
  - lia.
  - lia.
  - rewrite Rgp, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
  - rewrite Rtp, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HEVc.
  - apply (achain_chain_pre lyc _ (sm_sp1 (spZ regs)) (spZ regs) ch1 _ Hch1').
    + rewrite Hspm. lia.
    + unfold s0Z. rewrite Rs0, (EE 8%nat 8%bv eq_refl), R8. reflexivity.
    + unfold raZ. rewrite Rra. rewrite unsigned_lit_small by lia. lia.
  - intros Hin. exfalso. exact (Hnin Hin).
  - eapply (mok_station MT S Sc _ _ (mo_free MT) MTL HMOK MLE (mo_free_nonneg MT MTL)). unfold XM_SEND_MESSAGE. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfrs2 & HK & MLE2 & _).
(* the state after the free: the frame, its shadow and the saved registers are kept *)
pose proof (proj1 HJ2) as HAR2.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR (proj1 (proj2 HJ2))) as (_ & EFA2 & _).
assert (EFL2 : forall c p, flag_addr ly2 c p = flag_addr ly c p)
by (intros c p; unfold flag_addr; pose proof (EFA2 c p) as X; unfold frame_addr in X; lia).
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (_ & _ & HFpres2 & HFSpres2).
destruct (FFL _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFLp2 & HFLown2 & _ & _).
change (fs_frame_bytes 1) with 128 in HFpres2, HFSpres2. change (128 / 8) with 16 in HFSpres2.
rewrite !EFA2 in HFpres2, HFSpres2. rewrite !EFL2 in HFLp2, HFLown2. fold F in HFpres2, HFSpres2. fold FL in HFLp2, HFLown2.
unfold shadow_addr in HFSpres, HFSpres2. rewrite <- SB_SHADOW_OFF in HFSpres, HFSpres2.
pose proof (sep_block_frame _ _ LAWS lyc Sc Wc memc mdc res (Z.max n 1) 1 fpos HARc Hinres Hfin) as HdRF.
unfold zdisjoint in HdRF. cbn [fst snd] in HdRF. change (fs_frame_bytes 1) with 128 in HdRF. rewrite EFA in HdRF. fold F in HdRF.
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [| specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil].
  - eapply (region_kept_ownframe_aj SEGS B); [exact HK | exact UF | exact Hfin
    | left; rewrite EFA; fold F; change (fs_frame_bytes 1) with 128; lia
    | intros a Ha Hx; cbn beta in Hx; lia | intros a Ha; exact (proj1 (HFpres2 a ltac:(lia)))].
  - eapply (region_kept_ownframe_aj SEGS B); [exact HK | exact USB | exact Hfin
    | right; unfold shadow_addr; rewrite EFA; fold F; change (fs_frame_bytes 1 / 8) with 16; rewrite <- SB_SHADOW_OFF; lia
    | intros a Ha Hx; cbn beta in Hx; exact (fshadow_not_app F 16 res (req_size (Z.max n 1)) a HF4096 ltac:(lia) Hresapp ltac:(unfold SB in Ha; lia) Hx)
    | intros a Ha; replace a with (SB + F / 8 + (a - (SB + F / 8))) by lia; exact (proj1 (HFSpres2 (a - (SB + F / 8)) ltac:(lia)))].
  - eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (OLD2 : forall nn, (nn < 1024)%nat -> ew E2 nn = ew E nn) by (intros nn Hnn; rewrite HE2; apply ew_havoc_old; exact Hnn).
clear HE2.
assert (UF2 : bv_unsigned (ew E2 24) = F) by (rewrite OLD2 by lia; exact UF).
assert (USB2 : bv_unsigned (ew E2 23) = SB + F / 8) by (rewrite OLD2 by lia; exact USB).
assert (Usp2 : bv_unsigned (ew E2 8) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (UFL2 : bv_unsigned (ew E2 44) = FL) by (rewrite OLD2 by lia; rewrite E44; apply unsigned_lit_small; lia).
(* the flag byte *)
pose proof (st_ok_pi_add_region E2 _ _ sm5_flag_region HS eq_refl) as HS3.
lazymatch type of HS3 with ?A -> ?Bd -> _ => assert (HA : A); [| assert (HBd : Bd); [| specialize (HS3 HA HBd); clear HA HBd]] end.
{ unfold region_ok, sm5_flag_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite UFL2. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). replace (FL + o) with FL by lia. exact HFLp2. }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
  cbn [all_disjoint]. unfold extent_disjoint, sm5_flag_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite UFL2, UF2, USB2, Usp2.
  split; [| split; [| split; [| exact I]]].
  - destruct (Z_lt_ge_dec FL F); [left; lia|]. destruct (Z_lt_ge_dec FL (F + 128)); [| right; lia].
    exfalso. exact (proj2 (HFpres2 FL ltac:(lia)) HFLown2).
  - destruct (Z_lt_ge_dec FL (SB + F / 8)); [left; lia|]. destruct (Z_lt_ge_dec FL (SB + F / 8 + 16)); [| right; lia].
    exfalso. pose proof (proj2 (HFSpres2 (FL - (SB + F / 8)) ltac:(lia))) as X.
    replace (SB + F / 8 + (FL - (SB + F / 8))) with FL in X by lia. exact (X HFLown2).
  - left. lia. }
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* the shadow 0xf8 stores, the retired magic, `beqz s2` (not taken), the shadow 0xf5 stores, the flag byte cleared,
   the epilogue up to `ret` *)
paj_run_flag_sh RUNF HS HJ2; [lia | | |].
{ intros a (r & Hin & Hr). cbn [ss_mem In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?UFL2, ?UF2, ?USB2, ?Usp2 in Hr;
    first
    [ right; rewrite EFL2; fold FL; lia
    | left; right; right; right; left; exists 1, fpos; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
      change (fs_frame_bytes 1) with 128; rewrite EFA2; fold F; lia
    | left; right; right; right; left; exists 1, fpos; split; [left; reflexivity|]; right; unfold in_zr, shadow_addr; cbn [fst snd];
      change (fs_frame_bytes 1 / 8) with 16; rewrite EFA2; fold F; rewrite <- SB_SHADOW_OFF; lia
    | exfalso; lia ] |]).
  destruct Hin. }
{ intros msr HSr. rewrite EFL2. fold FL.
  pose proof (st_ok_pi_region_nth E2 _ msr 0 _ HSr eq_refl) as HR.
  pose proof (field_of_region (segs:=SEGS) E2 (ms_mem msr) 44%nat FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR UFL2
    ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0. exact V0. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (msF := msx) in * end.
cbn [ms_mem mkst] in HF, HFr, HG, HJ2.
assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ (a = FL \/ F <= a < F + 128 \/ SB + F / 8 <= a < SB + F / 8 + 16) ->
  aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem2 a).
{ apply (kept_of_frame (segs:=SEGS) E2 _ (w_H W2) mem2 (ms_mem msF) _ HFr).
  intros b wlo whi a Hin Hab. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hab; rewrite ?UFL2, ?UF2, ?USB2, ?Usp2 in Hab; lia |]).
  destruct Hin. }
clear HF HFr HG.
(* what the post reads, kept from verbs_receive's return: the program statics and the recorder's blocks *)
assert (HKimg : forall a, inFP cmd_PG a -> aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. destruct (cmd_prog_unowned a Ha) as (Himg & Hno & Herr).
  pose proof (Hsegs a Himg) as Hlow.
  assert (HnF : ~ (F <= a < F + 128)).
  { intros Hf. refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HARc _) Himg). right; left. exists 1, fpos.
    split; [exact Hfin|]. rewrite EFA. change (fs_frame_bytes 1) with 128. fold F. exact Hf. }
  rewrite (UN2 a ltac:(lia)) by (intros [-> | [Hf | Hsh]]; [exact (HFLimg Himg) | exact (HnF Hf) | unfold SB in Hsh; lia]).
  pose proof HK as (_ & _ & K3 & _). rewrite (K3 a Himg Hno Herr).
  rewrite (UN1 a ltac:(lia)) by (intros [Hf | Hsh]; [exact (HnF Hf) | unfold SB in Hsh; lia]).
  reflexivity. }
assert (HKblk : forall b m i, In (b, m) O' -> 0 <= i < req_size m ->
  aview SEGS (w_H W2) (ms_mem msF) (b + i) = aview SEGS (w_H Wc) memc (b + i)).
{ intros b m i Hbm Hi.
  assert (Hbm1 : In (b, m) (ablocks B lyc Sc))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPermO | apply in_or_app; left; exact Hbm]).
  assert (Hne : (b, m) <> (res, Z.max n 1)) by (intros Heq; apply HninO; rewrite <- Heq; exact Hbm).
  pose proof (sep_blocks _ _ LAWS _ _ _ _ _ b m res (Z.max n 1) HARc Hbm1 Hinres Hne) as Hdbr.
  unfold zdisjoint in Hdbr. cbn [fst snd] in Hdbr.
  pose proof (sep_block_frame _ _ LAWS _ _ _ _ _ b m 1 fpos HARc Hbm1 Hfin) as Hdbf.
  unfold zdisjoint in Hdbf. cbn [fst snd] in Hdbf. change (fs_frame_bytes 1) with 128 in Hdbf. rewrite EFA in Hdbf. fold F in Hdbf.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hbm1) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & _).
  assert (HnFL : b + i <> FL) by (intros Heq; apply (proj2 (Hbpres (b + i) ltac:(lia))); rewrite Heq; exact HFLown).
  rewrite (UN2 (b + i) ltac:(lia)) by (intros [Heq | [Hf | Hsh]]; [exact (HnFL Heq) | lia
    | exact (fshadow_not_app F 16 b (req_size m) (b + i) HF4096 ltac:(lia) Hbapp ltac:(unfold SB in Hsh; lia) ltac:(lia))]).
  pose proof HK as (_ & K2 & _). rewrite (K2 b m i Hbm1 Hi ltac:(cbn beta; lia)).
  rewrite (UN1 (b + i) ltac:(lia)) by (intros [Hf | Hsh]; [lia
    | exact (fshadow_not_app F 16 b (req_size m) (b + i) HF4096 ltac:(lia) Hbapp ltac:(unfold SB in Hsh; lia) ltac:(lia))]).
  reflexivity. }
(* the return *)
lazymatch goal with |- SRr _ ?Wx _ _ => eapply (paj_ret_at (PL := PL_cmd) Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
(* no printf-reaching code after verbs_receive: the FP state is kept, apost_baseF's left disjunct *)
intros matR. unfold sm_post. apply apost_baseF_of_base. unfold apost_base.
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end.
split.
{ prreg HS (1%bv : bv 5) RF1. rewrite RF1, (OLD2 32%nat) by lia. rewrite E32.
  unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ2 | unfold EV_SEND_MESSAGE; lia]. }
split.
{ apply aregs_preserved_eqs.
  all: lazymatch goal with |- getr _ ?r = getr _ _ => let Rr := fresh "Rr" in prreg HS r Rr; rewrite Rr; clear Rr end.
  all: rewrite ?OLD2 by lia.
  all: first [ rewrite E33 | rewrite E34 | rewrite E35 | rewrite E36 | rewrite E37 | rewrite E38 | rewrite E39 | rewrite E40
    | rewrite E41 | rewrite E42 | rewrite (EE 8%nat 8%bv eq_refl), R8 | rewrite (EE 3%nat 3%bv eq_refl), R3
    | rewrite (EE 4%nat 4%bv eq_refl), R4 | rewrite (EE 26%nat 26%bv eq_refl), R26 | rewrite (EE 27%nat 27%bv eq_refl), R27 ];
    reflexivity. }
rewrite Evr. cbv beta iota. exists O'.
assert (EblF : ablocks B ly2 (stack_free_state 1 fpos S2) = l1 ++ l2)
by (unfold ablocks; rewrite blocks_stack_free_state; exact Ebl2).
split.
{ apply (rec_repA_kept B lyc Sc (rdW Wc memc) ly2 (stack_free_state 1 fpos S2) _ R' O' HREP').
  - intros pn Hpn. rewrite EblF.
    assert (Hpn1 : In pn (ablocks B lyc Sc))
    by (eapply Permutation_in; [apply Permutation_sym; exact HPermO | apply in_or_app; left; exact Hpn]).
    rewrite Ebl in Hpn1. apply in_app_or in Hpn1. apply in_or_app.
    destruct Hpn1 as [H1 | [H1 | H1]]; [left; exact H1 | subst pn; exfalso; exact (HninO Hpn) | right; exact H1].
  - intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
    + apply HKimg. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia].
    + apply HKimg. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia].
    + destruct (inFP_ablocks_fp_inv _ a Ha) as (p & m & Hpm & Hpa). replace a with (p + (a - p)) by lia.
      apply (HKblk p m); [exact Hpm | lia]. }
split.
{ apply (aval_mem_kept_r (rdW Wc memc)); [| exact HQUIT].
  intros y Hy. change (Z.of_nat 4) with 4 in Hy. apply HKimg. exists (A_G_QUITTING, A_G_QUITTING + 4).
  split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
split.
{ rewrite EblF. rewrite Ebl in HPermO. exact (Permutation_app_inv l1 l2 O' rest (res, Z.max n 1) HPermO). }
split.
{ (* the live bytes: the copy's block is freed, so this call's peak is the one P4 carries *)
  assert (EbF : blocks_bytes (stack_free_state 1 fpos S2) = bsum (ablocks B ly2 (stack_free_state 1 fpos S2)))
  by apply blocks_bytes_bsum.
  assert (EbC : blocks_bytes Sc = bsum (ablocks B lyc Sc)) by apply blocks_bytes_bsum.
  rewrite EblF, bsum_app in EbF. rewrite Ebl, bsum_app, bsum_cons in EbC. cbn [snd] in EbC.
  unfold LIVE_SEND_MESSAGE. lia. }
unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL).
apply (mle_weaken MT S S2 _ _ MTL (mle_station MT S Sc S2 _ _ MTL MLE MLE2)). unfold XM_SEND_MESSAGE. lia.
Qed.

End e.
End f.
End d.
