(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the middle of the sup_broadcast walk on fuzz_command.asan-ubsan and its call of
   arg_line: the run from record's return 0x8b50c to `jal arg_line` (0x8b514: `mv s1,a0`, `mv a1,s0`) over the
   verified symbolic executor, the state at arg_line's entry (sbb_at_al: the slot's nargs field is 0 by RecBridge.v's
   rec_bridge_slot), the call through PaCallPg.v's cl_callS_pg with arg_line_c.v's contract at nargs 0, and the
   state at its return (0x8b518, sbb_ret_al: the recorder rebuilt by RecBridge.v's rec_bridge_add with the new
   argument block). The call is the shape of a Theorem Labs lane's A walk (lib/A/Prog/sup_broadcast_s4.v at a5a5ff08765). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts PaNoChain PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas RecBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_canonical_c hand_back_c record_c arg_line_c answer_c sup_broadcast_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_broadcast_s1 sup_broadcast_s2 sup_broadcast_s3 sup_broadcast_s4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at record's return: registers only; the run reads and writes no memory *)
Definition ss_sbb_m : sstate := mkSS SBB_RET_REC sr_atoms [] None (mkFacts [] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a reader at an address is the reader at its 64-bit residue (A: sup_broadcast_s3.v sb_aview_mod), so a run that
   keeps every byte below 2 ^ 64 keeps every address *)
Lemma sbb_aview_mod : forall (H : word -> bool) (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte, mrestrict.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma sbb_keep_all : forall (H : word -> bool) (m m' : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' K a. rewrite (sbb_aview_mod H m' a), (sbb_aview_mod H m a). apply K. apply Z.mod_pos_bound. lia. Qed.

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
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS.

(* the call target of arg_line *)
Lemma sbb_sig_arg_line : SIGMA CS_arg_line = BASE + AF_arg_line.
Proof. rewrite (SIGP CS_arg_line); [reflexivity | cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right])]. Qed.

(* the run 0x8b50c .. `jal arg_line`: the facts at arg_line's entry go to the continuation *)
Lemma sbb_reach_al : forall ly S W regs mem md O ly1 S1 (W1 : world SEGS) regs1 mem1 md1 k (Qk : world SEGS -> config -> Prop),
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly1 S1 W1 mem1 md1 k ->
(forall regsX memX mdX,
 ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly1 S1 W1 memX mdX k ->
 getr regsX 1 = Z_to_bv 64 (BASE + SBB_RET_AL) ->
 getr regsX 9 = getr regs1 10 -> getr regsX 11 = getr regs1 8 ->
 (forall r, In r [2; 3; 4; 8; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr regsX (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
 (forall a, 0 <= a < 2 ^ 64 -> rdW W1 memX a = rdW W1 mem1 a) ->
 SRr SEGS W1 (mkCfg (mkst regsX (Z_to_bv 64 (SIGMA CS_arg_line)) memX (seg_rom SEGS)) mdX) Qk) ->
SRr SEGS W1 (cfg_at SEGS (BASE + SBB_RET_REC) regs1 mem1 md1) Qk.
Proof.
intros ly S W regs mem md O ly1 S1 W1 regs1 mem1 md1 k Qk HJ HK.
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 []) E) by (rewrite HE; split; [intros n Hn'; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HS : st_ok_pi SEGS VAL E ss_sbb_m
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + SBB_RET_REC)) mem1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_sbb_m. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. repeat split.
  - cbn. repeat split. }
assert (SHOK : sh_ok SEGS sbb_Bx sbb_SH E (mrestrict (w_H W1) mem1)) by (unfold sh_ok, sbb_SH; apply Forall_nil).
clear HE.
unfold cfg_at. change (w64 (BASE + SBB_RET_REC)) with (Z_to_bv 64 (BASE + SBB_RET_REC)).
paj_run_tok RUN HS HJ SHOK sbb_Bspan.
{ awr_ok_tac. }
pmkst HS.
lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv := with_vm_backing x y z) in *; clearbody mdv end.
prreg HS (1%bv : bv 5) P1. prreg HS (9%bv : bv 5) P9. prreg HS (11%bv : bv 5) P11.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> rdW W1 (ms_mem ms) a = rdW W1 mem1 a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) E _ (w_H W1) mem1 (ms_mem ms) (fun _ => False) HFr).
  - intros b wlo whi a' Hin Hr. vm_compute in Hin. destruct Hin.
  - exact Ha.
  - intros []. }
pose proof (regs_kept_of_st_ok SEGS E _ _ regs1 [] (map (Z_to_bv 5) [2; 3; 4; 8; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
clear HF HFr HG.
apply HK.
- exact HJ.
- rewrite P1. unfold SBB_RET_AL, AF_sup_broadcast. reflexivity.
- rewrite P9. exact (EE 10%nat 10%bv eq_refl).
- rewrite P11. exact (EE 8%nat 8%bv eq_refl).
- intros r Hr. apply KR. apply in_map. exact Hr.
- exact KEEP.
Qed.

(* arg_line's entry state *)
Lemma sbb_at_al_of : forall ly S W regs mem md ch pl line R O ly1 S1 (W1 : world SEGS) regs1 mem1 md1 F O1 regsX memX mdX,
sbb_ent B MT ly S W regs mem md ch pl line R O ->
sbb_ret_rec B MT ly S W regs mem md pl line R O ly1 S1 W1 regs1 mem1 md1 F O1 ->
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly1 S1 W1 memX mdX (EV_RECORD R) ->
getr regsX 1 = Z_to_bv 64 (BASE + SBB_RET_AL) ->
getr regsX 9 = getr regs1 10 -> getr regsX 11 = getr regs1 8 ->
(forall r, In r [2; 3; 4; 8; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
 getr regsX (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
(forall a, 0 <= a < 2 ^ 64 -> rdW W1 memX a = rdW W1 mem1 a) ->
sbb_at_al B MT ly S W regs mem md pl line R O ly1 S1 W1 regsX memX mdX F O1.
Proof.
intros ly S W regs mem md ch pl line R O ly1 S1 W1 regs1 mem1 md1 F O1 regsX memX mdX HENT HRET HJX X1 X9 X11 XR KEEP.
destruct HRET as (HJ1 & Hsp1 & R8 & R10 & RCS & (Vra & Vs0 & Vs1) & HROD1 & HREC1 & HO1 & HP0 & HFO & HF & HBLK & HSTR & HBB & HMLE).
pose proof (proj1 HJ1) as HAR1.
pose proof (sbb_keep_all (w_H W1) mem1 memX KEEP) as KR.
pose proof (rec_bridge_slot B ly1 S1 (rdW W1 mem1) R REC_BROADCAST [] O1 HREC1) as (Hsl & Hn0 & _).
assert (Hslr : A_G_REC + 16 <= rec_slot R <= A_REC_SPILL) by exact (sb_slot_range _ Hsl).
assert (E2 : getr regsX 2 = getr regs1 2) by exact (XR 2 ltac:(cbn; tauto)).
assert (E8 : getr regsX 8 = getr regs1 8) by exact (XR 8 ltac:(cbn; tauto)).
assert (E10 : getr regsX 10 = getr regs1 10) by exact (XR 10 ltac:(cbn; tauto)).
split; [exact HJX|].
split; [unfold spZ; rewrite E2; exact Hsp1|].
split; [exact X1|].
split; [rewrite E8; exact R8|].
split; [rewrite X9; exact R10|].
split; [rewrite E10; exact R10|].
split; [rewrite X11; exact R8|].
split.
{ intros r Hr H2 H8 H9. rewrite (XR r); [exact (RCS r Hr H2 H8)|].
  unfold acallee_saved in Hr. cbn [In]. lia. }
split; [split; [|split]; intros kk Hkk; rewrite KR; [exact (Vra kk Hkk) | exact (Vs0 kk Hkk) | exact (Vs1 kk Hkk)]|].
split.
{ intros a H1 H2 H3. rewrite KR. exact (HROD1 a H1 H2 H3). }
split.
{ apply (rec_repA_kept B ly1 S1 (rdW W1 mem1) ly1 S1 (rdW W1 memX) _ O1 HREC1).
  - intros pn Hpn. exact (proj2 (sbb_rep_pos B _ _ _ _ _ pn HREC1 Hpn)).
  - intros a _. apply KR. }
split; [exact HO1|]. split; [exact HP0|]. split; [exact HFO|]. split; [exact HF|]. split; [exact HBLK|].
split.
{ pose proof HSTR as HSTR'.
  destruct HSTR as [HSb HSn]. split; [intros ii Hii | exact HSn].
  rewrite length_app in Hii; cbn [length] in Hii.
  rewrite KR. exact (HSb ii ltac:(rewrite length_app; cbn [length]; lia)). }
split; [exact HBB|]. split; [exact HMLE|]. split; [exact Hsl|].
intros kk Hkk. rewrite KR. exact (Hn0 kk Hkk).
Qed.

(* every byte of arg_line's footprint at nargs 0 is a byte of the slot's nargs and args[0] fields: program statics
   of the image in the walk's footprint *)
Lemma sbb_al_fp_slot : forall c a, inFP (sbb_al_FP c) a -> c + 4 <= a < c + 16.
Proof.
intros c a Ha. unfold sbb_al_FP in Ha. change (0 <? REC_ARGS_MAX) with true in Ha. cbv iota in Ha.
apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS in Ha; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS in Ha; lia | exfalso; exact (inFP_nil a Ha)].
Qed.
Lemma sbb_al_fp_ok : forall ly S lyc Sc O c, sb_slot c ->
forall a, inFP (sbb_al_FP c) a ->
(inFP (sb_FP O) a /\ ((exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a))) \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a.
Proof.
intros ly S lyc Sc O c Hsl a Ha. pose proof (sbb_al_fp_slot c a Ha) as Hc. left. split.
- exact (sb_slot_fp c a O Hsl ltac:(lia)).
- right. apply (sbb_pg_prog B HB IMG). apply (sb_slot_pg c a Hsl). unfold CALL_SIZE. lia.
Qed.

(* the call of arg_line: cl_callS_pg with arg_line's contract at nargs 0 and the walk's FP state *)
Lemma sbb_call_arg_line : forall ly S W regs mem md ch pl line R O ly1 S1 (W1 : world SEGS) regsX memX mdX F O1,
sbb_ent B MT ly S W regs mem md ch pl line R O ->
sbb_at_al B MT ly S W regs mem md pl line R O ly1 S1 W1 regsX memX mdX F O1 ->
SRr SEGS W1 (mkCfg (mkst regsX (Z_to_bv 64 (SIGMA CS_arg_line)) memX (seg_rom SEGS)) mdX)
(sbb_post_al B MT ly S W regs mem md line R O ly1 S1 W1 regsX memX mdX).
Proof.
intros ly S W regs mem md ch pl line R O ly1 S1 W1 regsX memX mdX F O1 HENT HAT.
destruct HENT as (HPRE & HFRM & Hfr8 & HROD & H10 & Hpl & HBLK0 & HAP & HSTR0 & HLEN & HREC & Hev & Hlive & HMOK).
destruct HAT as (HJ & Hsp & X1 & X8 & X9 & X10 & X11 & XCS & VF & HROD1 & HREC1 & HO1 & HP0 & HFO & HF & HBLK & HSTR & HBB
  & HMLE & Hsl & Hn0).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & Hnev1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (sbb_stk) as (WSTK & WREC & WAL & WANS).
destruct HBLK as (pb & kb & Hinb & Hpb1 & Hpb2).
destruct (sbb_blk B LAWS ly1 S1 W1 memX mdX pb kb HAR1 Hinb) as (Hb4 & Hbc & _ & _ & Hkbr).
assert (HXA : 0 <= XM_ANSWER MT (snd (sup_broadcast_m R line))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length (snd (sup_broadcast_m R line))) + 1))
    ltac:(unfold LIVE_XMALLOC; lia)). lia. }
assert (HXL : 0 <= XM_ARG_LINE MT line)
  by (unfold XM_ARG_LINE, XM_REC_CANONICAL, XM_XMALLOC; apply (mo_malloc_nonneg MT MTL); unfold LIVE_XMALLOC; lia).
assert (HEVL : st_nev S1 + EV_ARG_LINE <= EV_MAX).
{ unfold EV_SUP_BROADCAST, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in Hev. lia. }
assert (HLIVEL : blocks_bytes S1 + LIVE_ARG_LINE line <= LIVE_MAX).
{ unfold LIVE_SUP_BROADCAST, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC in Hlive. lia. }
assert (HMOKL : mo_ok MT S1 (XM_ARG_LINE MT line)).
{ apply (mok_station MT S S1 (XM_SUP_BROADCAST MT R line (snd (sup_broadcast_m R line))) (XM_RECORD MT R) _ MTL HMOK HMLE HXL).
  unfold XM_SUP_BROADCAST. lia. }
unfold sbb_post_al.
eapply SRr_mono.
{ eapply (cl_callS_pg B LAWS W1 regsX memX (Z_to_bv 64 (SIGMA CS_arg_line))
    SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly1 S1 mdX (EV_RECORD R)
    ARG_LINE_STK (sbb_al_FP (rec_slot R)) EV_ARG_LINE (-32) (Z_to_bv 64 (BASE + SBB_RET_AL)) []
    (sbb_al_Q B MT ly1 S1 line (rec_slot R)) HJ).
  - lia.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - etransitivity; [exact (XCS 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) | exact Hgp].
  - etransitivity; [exact (XCS 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) | exact Htp].
  - exact X1.
  - apply ret_ok_codeptr_v; [unfold SBB_RET_AL, AF_sup_broadcast; lia | reflexivity].
  - unfold SBB_RET_AL, AF_sup_broadcast. rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite X8. unfold w64. rewrite unsigned_lit_small by lia.
    pose proof (req_size_pos kb ltac:(lia)) as [_ Hkr]. lia.
  - intros HPRE2. rewrite sbb_sig_arg_line.
    eapply SRr_mono.
    { exact (TARG_LINE fx ly1 S1 W1 regsX memX mdX [] (rec_slot R) pl 0 line HPRE2 HROD1 X10 X11 Hpl Hsl Hn0
        ltac:(unfold REC_ARGS_MAX; lia) (ex_intro _ pb (ex_intro _ kb (conj Hinb (conj Hpb1 Hpb2)))) HSTR HLEN
        HEVL HLIVEL HMOKL). }
    cbv beta. unfold apost_base. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2).
    exists ly2, S2, regs2, mem2, md2. split; [rewrite X1; reflexivity|]. split; [exact HJ2|]. split; [exact HP2 | exact HK2].
  - exact (sbb_al_fp_ok ly S ly1 S1 O (rec_slot R) Hsl). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & HJc & HP2 & HK2).
exists ly2, S2, regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|]. split; [exact HJc|]. split; [exact HP2 | exact HK2].
Qed.

(* arg_line's return (0x8b518): the frame survives, the recorder holds (5, [canon line]) and owns the new block *)
Lemma sbb_ret_al_of : forall ly S W regs mem md ch pl line R O ly1 S1 (W1 : world SEGS) regsX memX mdX F O1
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
sbb_ent B MT ly S W regs mem md ch pl line R O ->
sbb_at_al B MT ly S W regs mem md pl line R O ly1 S1 W1 regsX memX mdX F O1 ->
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly2 S2 W2 mem2 md2 (EV_RECORD R + EV_ARG_LINE) ->
ajournal SEGS B ARG_LINE_STK (spZ regs + -32) (sbb_al_FP (rec_slot R)) ly1 S1 W1 memX mdX [] ly2 S2 W2 mem2 md2 EV_ARG_LINE ->
aregs_preserved regsX regs2 ->
sbb_al_Q B MT ly1 S1 line (rec_slot R) ly2 S2 W2 regs2 mem2 md2 ->
exists p, sbb_ret_al B MT ly S W regs mem md line R O ly1 S1 F O1 ly2 S2 W2 regs2 mem2 md2 p.
Proof.
intros ly S W regs mem md ch pl line R O ly1 S1 W1 regsX memX mdX F O1 ly2 S2 W2 regs2 mem2 md2 HENT HAT HJ2 HJc HP2 HK2.
destruct HENT as (HPRE & HFRM & Hfr8 & HROD & H10 & Hpl & HBLK0 & HAP & HSTR0 & HLEN & HREC & Hev & Hlive & HMOK).
destruct HAT as (HJ & Hsp & X1 & X8 & X9 & X10 & X11 & XCS & (Vra & Vs0 & Vs1) & HROD1 & HREC1 & HO1 & HP0 & HFO & HF & HBLK
  & HSTR & HBB & HMLE & Hsl & Hn0).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR1 & _).
pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (sbb_stk) as (WSTK & WREC & WAL & WANS).
pose proof (sb_slot_range _ Hsl) as Hslr.
destruct HK2 as (Hbb2 & Hmle2 & [(Hm6 & _) | (_ & p & HK2)]); [unfold REC_ARGS_MAX in Hm6; lia|].
cbv zeta in HK2. destruct HK2 as (Hp4096 & HPm & HAp & Hn1 & Ha0 & Hcan).
set (k := Z.of_nat (length line) + 1) in *.
assert (HO1b : forall pn, In pn O1 -> In pn (ablocks B ly1 S1)) by (intros pn Hpn; exact (proj2 (sbb_rep_pos B _ _ _ _ _ pn HREC1 Hpn))).
assert (Hin2 : In (p, k) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPm)); left; reflexivity).
assert (Hb12 : forall pn, In pn (ablocks B ly1 S1) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPm)); right; exact Hpn).
assert (HoffP : off_img p (req_size k)) by exact (blk_off_imgP B ly2 S2 W2 mem2 md2 p k HAR2 Hin2).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreqk].
pose proof (canon_length line) as Hcanl.
assert (HSO : ~ YI16.sink_open_fp (sbb_al_FP (rec_slot R))).
{ unfold sbb_al_FP. change (0 <? REC_ARGS_MAX) with true. cbv iota.
  apply sink_closed_pos. repeat constructor; cbn [fst]; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_G_REC in *; lia. }
assert (FPLOW : forall a, inFP (sbb_al_FP (rec_slot R)) a -> A_G_REC <= a < A_REC_SPILL + SC_SIZE).
{ intros a Ha. pose proof (sbb_al_fp_slot _ a Ha). unfold A_G_REC, A_REC_SPILL, SC_SIZE in *. lia. }
(* the frame survives the call *)
assert (KF : forall a, spZ regs - 32 <= a < spZ regs -> rdW W2 mem2 a = rdW W1 memX a).
{ intros a Ha. apply G1; [lia | lia | intros Hf; pose proof (FPLOW a Hf); unfold A_REC_SPILL, SC_SIZE in *; lia]. }
assert (E2 : getr regs2 2 = getr regsX 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
assert (E9 : getr regs2 9 = getr regsX 9) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
(* the recorder after the append (RecBridge.v rec_bridge_add) *)
assert (HREC2 : rec_repA B ly2 S2 (rdW W2 mem2) (rec_record R REC_BROADCAST [canon line]) ((p, k) :: O1)).
{ change [canon line] with ([] ++ [canon line]).
  apply (rec_bridge_add B ly1 S1 ly2 S2 (rdW W1 memX) (rdW W2 mem2) R REC_BROADCAST [] O1 (canon line) p k HREC1).
  - cbn. lia.
  - intros a Ha Hn Ha'. cbn [length Z.of_nat] in Ha'.
    assert (Hpg : inFP cmd_PG a).
    { destruct Ha as [Ha | Ha]; [exists (A_G_REC, A_G_REC + 960) | exists (A_REC_SPILL, A_REC_SPILL + 56)];
      (split; [cbn [cmd_PG In]; tauto | cbn [fst snd]; unfold REC_SIZE, SC_SIZE in Ha; lia]). }
    destruct (cmd_prog_unowned SEGS B LAWS HB IMG a Hpg) as (Hi & Ho & He).
    apply G3; [exact Hi | exact Ho | exact He |]. apply fp_spares_closed; [exact HSO|].
    intros Hf. unfold sbb_al_FP in Hf. change (0 <? REC_ARGS_MAX) with true in Hf. cbv iota in Hf.
    apply inFP_cons in Hf as [Hf | Hf]; [exact (Hn Hf)|].
    apply inFP_cons in Hf as [Hf | Hf]; [apply Ha'; lia | exact (inFP_nil a Hf)].
  - intros [b m] Hpn. split; [exact (Hb12 _ (HO1b _ Hpn))|].
    intros j Hj. cbn [fst snd] in *.
    pose proof (HO1b _ Hpn) as HbX.
    destruct (sbb_blk B LAWS ly1 S1 W1 memX mdX b m HAR1 HbX) as (_ & _ & _ & _ & Hm).
    apply (G2 b m j); [exact HbX | exact (Hb12 _ HbX) | lia |].
    intros Hf. apply (blk_img SEGS B LAWS ly1 S1 W1 memX mdX b m (b + j) HAR1 HbX ltac:(lia)).
    apply (cif_prog_img _ _ IMG). apply (sb_slot_pg (rec_slot R) _ Hsl). pose proof (sbb_al_fp_slot _ _ Hf).
    unfold CALL_SIZE. lia.
  - exact Hin2.
  - intros Hin. apply in_map_iff in Hin as ([b m] & Eb & Hin). cbn [fst] in Eb. subst b.
    pose proof (proj1 (Forall_forall _ _) HAp _ (HO1b _ Hin)) as Hd. cbn [fst snd] in Hd.
    pose proof (proj1 (sbb_rep_pos B _ _ _ _ _ _ HREC1 Hin)) as Hm. cbn [snd] in Hm.
    unfold iv_apart in Hd. lia.
  - unfold iv_apart, off_img, A_G_REC, REC_SIZE in *. lia.
  - unfold iv_apart, off_img, A_REC_SPILL, SC_SIZE in *. lia.
  - lia.
  - unfold k. unfold LMAX in *. lia.
  - unfold LMAX in *. lia.
  - exact Hn1.
  - exact Ha0.
  - exact Hcan. }
exists p.
split; [exact HJ2|].
split; [unfold spZ; rewrite E2; exact Hsp|].
split; [rewrite E9; exact X9|].
split; [intros r Hr H2' H8' H9'; rewrite (HP2 r Hr); exact (XCS r Hr H2' H8' H9')|].
split; [split; [|split]; intros kk Hkk; rewrite KF by (cbn in Hkk; lia); [exact (Vra kk Hkk) | exact (Vs0 kk Hkk) | exact (Vs1 kk Hkk)]|].
split.
{ intros a H1 H2 H3. destruct (sbb_ro_low B IMG a H1) as (Hi & Ha).
  rewrite (G3 a Hi H2 H3); [exact (HROD1 a H1 H2 H3)|].
  apply fp_spares_closed; [exact HSO|]. intros Hf.
  apply (cif_prog_not_ro _ _ IMG a); [|exact H1].
  apply (sb_slot_pg (rec_slot R) a Hsl). pose proof (sbb_al_fp_slot _ _ Hf). unfold CALL_SIZE. lia. }
split; [exact HREC2|]. split; [exact HO1|]. split; [exact HP0|]. split; [exact HFO|]. split; [exact HO1b|].
split; [exact HPm|]. split; [exact HAp|]. split; [exact Hp4096|].
split; [exact Hbb2|]. split; [exact HBB|].
exact (mle_station MT S S1 S2 _ _ MTL HMLE Hmle2).
Qed.

End e.
End f.
End d.
