(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the second segment of sup_pool_config's ASan walk (plugin-hostd/fuzz_command): from
   the point where record()'s two arms meet (0x8bd78) to the call of xstrdup (0x8bdb4): the slot gets fn := 14 and
   nargs := 0, and s2 keeps the name (the statement's name is a string, so the fall-through that sets s2 to "(null)"
   is unreachable), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a seed and the symbolic run to the next segment's seed). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d YG0q YI67.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c rec_shape_of_c answer_c hand_back_c mix_call_c sup_pool_config_c PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas sup_pool_config_s1 sup_pool_config_s2 sup_pool_config_s3 sup_pool_config_s4 sup_pool_config_s5
sup_pool_config_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HY : spc_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a run of the mid-walk regions writes only the slot: any region list with their skeleton (the token executor's
   literal copy after a run, or the seed's) *)
Lemma spc_wslot : forall E c rs a, base_val E (Some 34%nat) = c -> in_wrange E rs a ->
YP09.skeleton rs = YP09.skeleton [spc_frame; spc_slot_rg []] -> c <= a < c + CALL_SIZE.
Proof.
intros E c rs a Hc Hw Hsk. exact (spc_wrange_slot E c [] a Hc (YP09.in_wrange_skeleton E rs _ a Hsk Hw)).
Qed.

(* the state at 0x8bdb4 from the state at 0x8bd78: the blocks, the meter, the recorder state rdB and the frame are
   those of the join; the memory differs from the join's only in the slot, which holds fn = 14 and nargs = 0; s2
   holds the string s to copy *)
Lemma spc_midD_of_J : forall ly S W (regs : bvmap 5 word) mem md R O pn name max lyB SBs rdB lyc Sc (Wc : world SEGS)
  memc mdc (regs1 : bvmap 5 word) O0 F memd mdd (regsd : bvmap 5 word) s,
rec_repA B ly S (rdW W mem) R O -> 2 ^ 46 <= spZ regs - 64 -> spZ regs <= 2 ^ 47 ->
spc_midJ B MT ly S W regs mem md R O pn name max lyB SBs rdB lyc Sc Wc memc mdc regs1 O0 F ->
ajournal SEGS B SUP_POOL_CONFIG_STK (spZ regs) (spc_FP O) ly S W mem md [] lyc Sc Wc memd mdd (rec_spill_frees R) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc_slot R <= a < spc_slot R + CALL_SIZE) -> rdW Wc memd a = rdW Wc memc a) ->
aval_mem (rdW Wc memd) (spc_slot R) 4 REC_POOL_CONFIG -> aval_mem (rdW Wc memd) (spc_slot R + 4) 4 0 ->
astr_argA B lyc Sc (rdW Wc memd) (in_roP SEGS RLO RHI) [] s (Some (sarg name)) ->
atail_vis SEGS Wc memd (s + Z.of_nat (length (sarg name))) ->
getr regsd 2 = w64 (spZ regs - 64) -> getr regsd 8 = w64 max -> getr regsd 9 = w64 (spc_slot R) ->
getr regsd 18 = w64 s -> getr regsd 19 = w64 (spc_slot R + 4) -> getr regsd 20 = w64 SB ->
getr regsd 21 = w64 (SB + (spc_slot R + 4) / 8) ->
(forall r, In r [3; 4; 22; 23; 24; 25; 26; 27] -> getr regsd (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
spc_midD B MT ly S W regs mem md R O name max lyB SBs rdB lyc Sc Wc memd mdd regsd s O0 F.
Proof.
intros ly S W regs mem md R O pn name max lyB SBs rdB lyc Sc Wc memc mdc regs1 O0 F memd mdd regsd s
  HREP Hsp46 Hsp47 HMID HJd KS VFN VNA HSTRd HTAILd D2 D8 D9 D18 D19 D20 D21 DK.
spc_unpack HY.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HMID as (HJ & HBL & HFO & HO0 & HFS & HBB & HMLE & HFRM & HREPB & HKB & HKO & HNC & HSTRc & HTAILc &
  R2 & R8 & R9 & R18 & R20 & RK).
pose proof HJ as (HARc & _).
destruct (spc_rep_ncalls B ly S _ R O HREP) as [_ Hlen16].
pose proof (spc_slot_okR R Hlen16) as HCK.
destruct (spc_slot_bounds _ HCK) as [Hcb _].
set (c := spc_slot R) in *.
assert (HcR : 6174544 <= c <= 6175712) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb; lia).
assert (HCS : CALL_SIZE = 56) by reflexivity.
unfold spc_midD.
split; [exact HJd|]. split; [exact HBL|]. split; [exact HFO|]. split; [exact HO0|]. split; [exact HFS|].
split; [exact HBB|]. split; [exact HMLE|].
split.
{ apply (spc_frame_kept (w_H Wc) (w_H Wc) memc memd (spZ regs) regs HFRM). intros a Ha. apply KS; lia. }
split; [exact HREPB|].
split.
{ intros a Ha Hnc Hns.
  assert (Ha' : 0 <= a < 2 ^ 64) by (pose proof Ha as Ha2; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha2; lia).
  rewrite (KS a Ha' Hns). exact (HKB a Ha Hnc Hns). }
split.
{ intros [p n] i Hpn Hi. cbn [fst snd] in Hi |- *.
  destruct (proj1 (HO0 (p, n)) Hpn) as [HpO HpF].
  assert (Hin : In (p, n) (ablocks B lyc Sc)) by (apply HBL; split; [exact (spc_rep_in B ly S _ R O HREP _ HpO) | exact HpF]).
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HARc Hin) as (_ & H4096 & Hbc & _ & _ & _ & Hk).
  destruct (req_size_pos n ltac:(lia)) as [_ Hreq].
  destruct (spc_blk_off B cmd_prog_img lyc Sc Wc memc mdc p n (p + i) HARc Hin ltac:(lia)) as [_ HnPG].
  rewrite KS; [exact (HKO (p, n) i Hpn Hi) | lia | intros Hs; exact (HnPG (spc_slot_PG c (p + i) HCK Hs))]. }
split.
{ intros Hl k Hk. rewrite KS; [exact (HNC Hl k Hk) | unfold A_G_REC, OFF_NCALLS; lia | unfold A_G_REC, OFF_NCALLS; lia]. }
split; [exact VFN|]. split; [exact VNA|]. split; [exact HSTRd|]. split; [exact HTAILd|].
split; [exact D2|]. split; [exact D8|]. split; [exact D9|]. split; [exact D18|].
split; [exact D19|]. split; [exact D20|]. split; [exact D21|].
intros r Hr. rewrite (DK r Hr). exact (RK r Hr).
Qed.

Lemma spc_seg_join : forall ly S W regs mem md ch pn max name R O,
spc_pre B MT ly S W regs mem md ch pn max name R O ->
spc_cont_D B MT ly S W regs mem md R O name max ->
spc_cont_J B MT ly S W regs mem md R O pn name max.
Proof.
intros ly S W regs mem md ch pn max name R O HPRE HCD.
unfold spc_cont_J. intros lyB SBs rdB lyc Sc Wc memc mdc regs1 O0 F HMID.
spc_unpack HY.
destruct HPRE as (HFN & HFR0 & HROD & HRO & H10 & Hpn & H11 & Hmax & HSTR & HREP & HFR8 & HEV & HLIVE & HMOK).
(* the name is a string: NULL is not a premise case *)
destruct HSTR as (x & -> & _).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hsp46 : 2 ^ 46 <= spZ regs - 64) by lia.
assert (Hsp47 : spZ regs <= 2 ^ 47) by lia.
pose proof HMID as (HJ & _ & _ & _ & _ & _ & _ & HFRM & _ & _ & _ & _ & HSTRc & HTAILc & R2 & R8 & R9 & R18 & R20 & RK).
pose proof HJ as (HARc & _).
destruct (spc_rep_ncalls B ly S _ R O HREP) as [_ Hlen16].
pose proof (spc_slot_okR R Hlen16) as HCK.
destruct (spc_slot_bounds _ HCK) as [Hcb Hc8].
set (c := spc_slot R) in *.
assert (HcR : 6174544 <= c <= 6175712) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb; lia).
assert (HCS : CALL_SIZE = 56) by reflexivity.
(* the seed at 0x8bd78: s1 = c, s4 = the shadow base, the slot writable and empty of chunks *)
destruct (spc_seed B LAWS HB SPC_JOIN spc_regsJ [] Wc regs regs1 memc (spZ regs) 0 c lyc Sc mdc HARc
  ltac:(vm_compute; reflexivity) Hsp46 Hsp47 Hsp16 HCK
  ltac:(rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)) as [HS SHOK].
{ exact (spc_regs_okJ regs regs1 c Hcb R9 R20). }
{ exact HFRM. }
{ intros a Ha. apply (cmd_prog_writable lyc Sc Wc memc mdc a HARc). exact (spc_slot_PG c a HCK Ha). }
{ constructor. }
set (E := Eimg (Ereg regs1 (spc_extra regs 0 c))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by exact (spc_E_reg regs regs1 0 c).
destruct (spc_E_lit regs regs1 0 c) as (E32 & _ & E34). fold E in E32, E34.
assert (B34 : base_val E (Some 34%nat) = c) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
(* 0x8bd78 .. 0x8bda8: the shadow checks of c and c + 4, fn := 14, nargs := 0, then bnez s2 *)
paj_run_tok RUN HS HJ SHOK SPC_SPAN.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact B34 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi spc_slot_rg] in Ha.
  exact (spc_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ c a HCK ltac:(unfold CALL_SIZE in *; lia)). }
spc_md. rename ms into ms1. rename HFr into HFr1. clear HF HG.
assert (KS1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha Hn. apply (recb_run_keeps_m E _ (w_H Wc) memc (ms_mem ms1) a HFr1 Ha).
  intros Hw. apply Hn. exact (spc_wslot E c _ a B34 Hw ltac:(vm_compute; reflexivity)). }
clear HFr1.
assert (E18 : ew E 18 = Z_to_bv 64 pn) by (rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity).
psrr_branch_tok RUN BR HS SHOK SPC_SPAN.
- (* s2 <> 0: the branch to 0x8bdb4 with s2 = the name *)
  paj_run_to_tok RUNTO HS HJ SHOK SPC_SPAN SPC_DUP.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen; [reflexivity | exact B34 | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi spc_slot_rg] in Ha.
    exact (spc_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ c a HCK ltac:(unfold CALL_SIZE in *; lia)). }
  pmkst HS. spc_md.
  assert (KS : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha Hn. rewrite <- (KS1 a Ha Hn). apply (recb_run_keeps_m E _ (w_H Wc) (ms_mem ms1) (ms_mem ms) a HFr Ha).
    intros Hw. apply Hn. exact (spc_wslot E c _ a B34 Hw ltac:(vm_compute; reflexivity)). }
  assert (VFN : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (c + 0) 4 14)
    by exact (st_chunk_val SEGS E _ _ 1 _ 34 0 4 (SLit 14) c 14 HS eq_refl eq_refl ltac:(cbn; tauto) B34 eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (VNA : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (c + 4) 4 0)
    by exact (st_chunk_val SEGS E _ _ 1 _ 34 4 4 (SLit 0) c 0 HS eq_refl eq_refl ltac:(cbn; tauto) B34 eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)).
  rewrite Z.add_0_r in VFN.
  prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  assert (P21 : getr (ms_regs ms) 21 = sv_denot E spc_shx4) by exact (st_ok_pi_restrict_reg (w_H Wc) E _ ms 21%bv HS).
  assert (D2 : getr (ms_regs ms) 2 = w64 (spZ regs - 64)) by (rewrite P2, (EE 2%nat 2%bv eq_refl); exact R2).
  assert (D8 : getr (ms_regs ms) 8 = w64 max) by (rewrite P8, (EE 8%nat 8%bv eq_refl); exact R8).
  assert (D9 : getr (ms_regs ms) 9 = w64 c) by (rewrite P9, E34; reflexivity).
  assert (D18 : getr (ms_regs ms) 18 = w64 pn) by (rewrite P18, (EE 18%nat 18%bv eq_refl); exact R18).
  assert (D19 : getr (ms_regs ms) 19 = w64 (c + 4)) by (rewrite P19, E34, unsigned_lit_small by lia; reflexivity).
  assert (D20 : getr (ms_regs ms) 20 = w64 SB) by (rewrite P20, E32; reflexivity).
  assert (D21 : getr (ms_regs ms) 21 = w64 (SB + (c + 4) / 8))
    by (rewrite P21, denot_lit_U, (spc_U_shx4 E c E32 E34) by lia; reflexivity).
  assert (DK : forall r, In r [3; 4; 22; 23; 24; 25; 26; 27] -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
  { intros r Hr. cbv [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [lazymatch goal with |- getr _ ?rr = _ => let P := fresh "P" in prreg HS rr P; rewrite P; apply EE; reflexivity end|]).
    destruct Hr. }
  destruct (spc_argA_slot B RLO RHI LAWS cmd_prog_img cmd_ro_prog_apart lyc Sc Wc memc (ms_mem ms) mdc c pn x HARc HCK KS
    HSTRc (HTAILc x eq_refl)) as [HSTRd HTAILd].
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?k)) _ _) _) _ => change k with SPC_DUP end.
  exact (HCD lyB SBs rdB lyc Sc Wc (ms_mem ms) _ (ms_regs ms) pn O0 F
    (spc_midD_of_J ly S W regs mem md R O pn (Some x) max lyB SBs rdB lyc Sc Wc memc mdc regs1 O0 F (ms_mem ms) _ (ms_regs ms) pn
      HREP Hsp46 Hsp47 HMID HJ KS (aval_mem_view SEGS (w_H Wc) (ms_mem ms) c 4 14 VFN) (aval_mem_view SEGS (w_H Wc) (ms_mem ms) (c + 4) 4 0 VNA)
      HSTRd HTAILd D2 D8 D9 D18 D19 D20 D21 DK)).
- (* s2 = 0: impossible, the name is a string at pn <> 0 *)
  exfalso. destruct HSTRc as (Hpn0 & _).
  rewrite branch_ne_U, (U_atom E 18 pn E18), U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc. exact (Hpn0 Hc).
Qed.

End e.
End f.
End d.
