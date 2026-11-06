(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the segment of sup_instance_verb's ASan walk (plugin-hostd/fuzz_command) from the
   join of record()'s two arms (0x8b42c) through the slot's two inline checks and the stores of c->fn and c->nargs to
   the call of arg_line and its return (0x8b468), after proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v and the template
   walk's lib/A/Prog/sup_worker_list.v (an earlier version), whose swl_awr_grec / swl_awr_slot are copied here as
   siv_awr_grec / siv_awr_slot. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaArt PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  rec_calls_free_c arg_line_c arg_i_c rec_shape_of_c answer_c sup_instance_verb_c hand_back_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  RecBTemplateSiv sup_instance_verb_s2 sup_instance_verb_s3 sup_instance_verb_s4 sup_instance_verb_s5 sup_instance_verb_s6 sup_instance_verb_s7 sup_instance_verb_s8 sup_instance_verb_s9 sup_instance_verb_s10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strspn_c strcspn_c.
(* the plain proof's lemmas on the line's first word (lib/Prog/sup_instance_verb.v:210-276); its module shares the
   base name of the walk, so it is named by its full path *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require sup_instance_verb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the slot at the join, with the write window of the two words this segment stores (c->fn and c->nargs): the
   region of siv_rsJ (lib/A/Prog/sup_instance_verb_s2.v) narrowed, so that the run keeps every other byte of the
   slot, which record()'s step over the recorder's representation needs *)
Definition siv_slotw : YP09.region := YP09.mkRegion (Some RB_C) 0 CALL_SIZE 0 8 [].
Definition siv_rsJw : YP09.smem := [siv_frame; siv_slotw].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
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
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the seed of the join, siv_seed_join of lib/A/Prog/sup_instance_verb_s2.v over siv_rsJw *)
Lemma siv_seed_joinw : CmdBSyms B -> cmd_val_objs ->
(forall ly S (W : world SEGS) mem md a, AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG ->
   writable_at SEGS (mrestrict (w_H W) mem) a) ->
forall ly1 S1 (W1 : world SEGS) mem1 md1 (regs regs1 : bvmap 5 word) sp0 n c,
AR SEGS B ly1 S1 W1 mem1 md1 ->
2 ^ 46 <= sp0 - 48 <= 2 ^ 47 -> sp0 mod 16 = 0 -> 0 <= n <= 16 -> rbs_slot_ok c ->
spZ regs1 = sp0 - 48 -> getr regs1 8 = Z_to_bv 64 c -> getr regs1 19 = Z_to_bv 64 SB ->
siv_frame_ok (mrestrict (w_H W1) mem1) sp0 regs ->
st_ok_pi SEGS VAL (siv_E regs regs1 n c) (mkSS SIV_J siv_regsJ siv_rsJw None rbs_facts)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + SIV_J)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS Bxr rbs_SH (siv_E regs regs1 n c) (mrestrict (w_H W1) mem1).
Proof.
intros HB VOBJS PWR ly1 S1 W1 mem1 md1 regs regs1 sp0 n c HAR Hsp Hsp16 Hn Hc Hsp1 R8 R19 HF.
pose proof (siv_env regs regs1 n c) as HE. rewrite Hsp1 in HE.
pose proof HE as (HEI & E2 & ESB & EN & EC).
destruct (rbs_slot_bounds c Hc) as [Hcb Hc8].
assert (Hc56 : c + CALL_SIZE <= A_REC_SPILL + SC_SIZE /\
  forall o, 0 <= o < CALL_SIZE -> Exists (in_zr (c + o)) recb_PG).
{ destruct Hc as [(H1 & H2 & H3) | ->].
  - split; [unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia|].
    intros o Ho. apply recb_grec_in. unfold CALL_SIZE, OFF_CALLS in *. lia.
  - split; [unfold CALL_SIZE, SC_SIZE; lia|]. intros o Ho. apply recb_spill_in. unfold CALL_SIZE, SC_SIZE in *. lia. }
split; [| exact (rbs_sh_ok B LAWS HB ly1 S1 W1 mem1 md1 _ (sp0 - 48) n c HAR HE Hc)].
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply siv_regsJ_ok; assumption.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (siv_frame_region_ok _ _ sp0 regs);
    [ rewrite E2; apply unsigned_lit_small; lia | lia | lia | intros j r Hj; apply siv_E_saved; exact Hj | exact HF ].
  + unfold siv_slotw, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite EC, unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
    split; [unfold A_G_REC, OFF_CALLS in *; lia|]. split; [unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia|].
    split; [intros o Ho; apply (PWR ly1 S1 W1 mem1 md1);
      [exact HAR | apply (proj2 Hc56); unfold CALL_SIZE in *; lia]|].
    apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold siv_rsJw, siv_frame, siv_slotw, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2, EC, !unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, SC_SIZE in *. repeat split; lia.
- apply (rbs_facts_ok VOBJS _ (sp0 - 48) n c HE); [lia | | exact Hn | exact Hc].
  replace (sp0 - 48) with (sp0 + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
Qed.

(* the two writes of the segment go to g_rec or to record.spill, which the contract's footprint names: the
   template walk's swl_awr_grec / swl_awr_slot (an earlier version of lib/A/Prog/sup_worker_list.v, lines 190-213) over
   siv_FP *)
Lemma siv_inFP_grec : forall O a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP (siv_FP O) a.
Proof. intros O a Ha. exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha]. Qed.

Lemma siv_inFP_spill : forall O a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP (siv_FP O) a.
Proof.
intros O a Ha. exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE).
split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

Lemma siv_awr_grec : CmdBSyms B -> (forall a, Exists (in_zr a) recb_PG -> in_img SEGS a) ->
forall STK sp0 O bl0 blc fr0 lyc own a,
A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp0 (siv_FP O) bl0 blc fr0 lyc own a.
Proof.
intros HB PIMG STK sp0 O bl0 blc fr0 lyc own a Ha.
right; right; right; right. left.
split; [exact (siv_inFP_grec O a Ha)|].
split; [rewrite (recb_ts_prog_m B HB); exact (recb_grec_in a Ha) | exact (PIMG a (recb_grec_in a Ha))].
Qed.

Lemma siv_awr_slot : CmdBSyms B -> (forall a, Exists (in_zr a) recb_PG -> in_img SEGS a) ->
forall STK sp0 O bl0 blc fr0 lyc own c a,
rbs_slot_ok c -> c <= a < c + CALL_SIZE ->
awr_byte SEGS B STK sp0 (siv_FP O) bl0 blc fr0 lyc own a.
Proof.
intros HB PIMG STK sp0 O bl0 blc fr0 lyc own c a Hc Ha.
destruct Hc as [(H1 & H2 & _) | ->].
- apply (siv_awr_grec HB PIMG). unfold CALL_SIZE, OFF_CALLS in *. lia.
- right; right; right; right. left.
  assert (Hin : A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) by (unfold CALL_SIZE, SC_SIZE in *; lia).
  split; [exact (siv_inFP_spill O a Hin)|].
  split; [rewrite (recb_ts_prog_m B HB); exact (recb_spill_in a Hin)
         | exact (PIMG a (recb_spill_in a Hin))].
Qed.

(* the run of the segment writes only the slot's first two words, so every other byte is the join's *)
Lemma siv_kept_outside : forall (H : word -> bool) (m m' : word -> option byte) E0 c0,
frame_of E0 siv_rsJw (mrestrict H m) (mrestrict H m') -> bv_unsigned (ew E0 RB_C) = c0 ->
forall a, 0 <= a < 2 ^ 64 -> ~ (c0 <= a < c0 + 8) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' E0 c0 HFR HC a Ha Hn.
apply (kept_of_frame (segs := SEGS) E0 siv_rsJw H m m' (fun x => c0 <= x < c0 + 8) HFR); [| exact Ha | exact Hn].
intros b wlo whi x Hin Hr. cbv beta. rewrite <- HC.
cbn [windows siv_rsJw siv_frame siv_slotw map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
destruct Hin as [Hq | [Hq | []]]; inversion Hq; subst; cbn [base_val] in Hr; lia.
Qed.

Lemma siv_seg_J : siv_hyps B MT -> siv_L_goal B MT -> siv_J_goal B MT.
Proof.
intros HY HL. unfold siv_J_goal.
intros ly S W regs mem md ch pl ledger line R O lyc Sc Wc memc mdc regs1 kk R0 Q0 rd0
  CX HFRM HJ Hkk HFO HRG R9 R18 R19 HARM HAREP0 HG0 HB0 HNC I1 I2 I3 HMLE HLV.
pose proof HY as HY0.
destruct HY as [TRCF TARG_LINE TARG_I TRSO TANSWER ASTRSPN ASTRCSPN VOBJS TL HB MTL PIMG PWR SIGP ROK RRO RELRO HTV
  RECC ROMV ZSH HULLL ROPA].
pose proof CX as (HPRE & HROD & HRO & H10 & Hpl64 & H11 & Hled & HLB & HLSTR0 & HLL & HLAP & HREP & HFR8 & HEV
  & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof alloc_ceiling_value as [HACm HAC].
pose proof HRG as (Rsp & Rgp & Rtp & R8 & Rhi).
assert (WS : SUP_INSTANCE_VERB_STK = 16592) by reflexivity.
assert (WAL : ARG_LINE_STK = 16464) by reflexivity.
assert (WEV : EV_ARG_LINE = 1) by reflexivity.
assert (WLV : LIVE_ARG_LINE line = Z.of_nat (length line) + 1) by reflexivity.
assert (WXM : XM_ARG_LINE MT line = mo_malloc MT (Z.of_nat (length line) + 1)) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hsp46 : 2 ^ 46 <= sp0 - 48 <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328. clear - Hceil Hslo Hshi H47 Hstk0 C1 WS. lia. }
assert (HrepE : rec_repA B ly S (rdW W mem) R O) by exact HREP.
pose proof HAREP0 as (_ & _ & _ & (Hlen16' & HlenQ & _ & HCALLS & HSPILL & _) & _).
assert (HcallsR : r_calls R0 = r_calls R) by (destruct HARM as [(-> & _) | (_ & ->)]; reflexivity).
assert (Hlen16 : (length (r_calls R) <= 16)%nat) by (rewrite <- HcallsR; exact Hlen16').
set (n := Z.of_nat (length (r_calls R))) in *.
assert (Hn : 0 <= n <= 16) by (unfold n; lia).
assert (Hc : rbs_slot_ok (siv_slot R)) by (apply siv_slot_ok; exact Hlen16).
assert (Hcb : A_G_REC + OFF_CALLS <= siv_slot R <= A_REC_SPILL)
  by (destruct (rbs_slot_bounds (siv_slot R) Hc) as [H _]; exact H).
assert (R8' : getr regs1 8 = Z_to_bv 64 (siv_slot R)) by exact R8.
assert (R19' : getr regs1 19 = Z_to_bv 64 SB) by exact R19.
assert (EC' : bv_unsigned (ew (siv_E regs regs1 n (siv_slot R)) RB_C) = siv_slot R).
{ unfold RB_C. rewrite siv_E_C. apply unsigned_lit_small.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia. }
assert (Hsp46L : 70368744177664 <= sp0 - 48 <= 140737488355328).
{ change (2 ^ 46) with 70368744177664 in Hsp46. change (2 ^ 47) with 140737488355328 in Hsp46. exact Hsp46. }
(* record()'s two arms agree on the slot, on the layout and on the call they record *)
assert (HARMF : siv_slot R0 = siv_slot R /\ slot_lay Q0 R0 [] = slot_lay Q0 R [] /\
  rec_record R0 REC_INSTANCE_VERB [] = rec_record R REC_INSTANCE_VERB [] /\
  ((16 <= length (r_calls R0))%nat -> snd (r_spill R0) = [])).
{ destruct HARM as [(HR0 & Hlt) | (H16 & HR0)]; rewrite HR0.
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros Hx. exfalso. lia.
  - split; [apply siv_slot_spill_clear|]. split; [apply slot_lay_spill_clear|].
    split; [apply rec_record_spill_clear; lia | intros _; reflexivity]. }
destruct HARMF as (HSL0 & HSLQ & HRR & HSPE).
(* the spill holds no argument block when the table is full, so its layout is empty *)
assert (HSP0 : (16 <= length (r_calls R))%nat -> l_spill Q0 = []).
{ intros H16. pose proof HSPILL as (_ & _ & HLsp & _).
  rewrite (HSPE ltac:(rewrite HcallsR; exact H16)) in HLsp. apply length_zero_iff_nil. exact HLsp. }
assert (I4 : forall pn, In pn (lay_blocks Q0) -> In pn (ablocks B lyc Sc))
  by exact (rec_repA_in B lyc Sc rd0 R0 (lay_blocks Q0) (ex_intro _ Q0 (conj HAREP0 (fun x => iff_refl _)))).
assert (LBt : lay_blocks (RLay (l_calls Q0 ++ [[]]) (l_spill Q0) (l_answer Q0) (l_reply Q0)) = lay_blocks Q0).
{ unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite !app_nil_r. reflexivity. }
assert (LBs : (16 <= length (r_calls R))%nat ->
  lay_blocks (RLay (l_calls Q0) [] (l_answer Q0) (l_reply Q0)) = lay_blocks Q0).
{ intros H16. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite (HSP0 H16). reflexivity. }
assert (LB0 : lay_blocks (slot_lay Q0 R []) = lay_blocks Q0).
{ unfold slot_lay. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl]; [exact LBt | apply LBs; lia]. }
destruct (siv_seed_joinw HB VOBJS PWR lyc Sc Wc memc mdc regs regs1 sp0 n (siv_slot R) (proj1 HJ)
  Hsp46 Hal16 Hn Hc Rsp R8' R19' HFO) as [HS SHOK].
pose proof (siv_env regs regs1 n (siv_slot R)) as HE. pose proof HE as (HEI & _).
set (E := siv_E regs regs1 n (siv_slot R)) in *.
assert (HAE : env_agree 32 (Ereg regs1 (rbs_extra regs n (siv_slot R))) E).
{ split; [intros k Hk; unfold E, siv_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
paj_run_tok RUN HS HJ SHOK siv_Bspan.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := RB_C).
  - reflexivity.
  - exact EC'.
  - intros a Ha. cbn [siv_slotw YP09.r_wlo YP09.r_whi] in Ha.
    eapply (siv_awr_slot HB PIMG); [exact Hc | unfold CALL_SIZE in *; lia].
  - apply awr_ok_nil. }
pmkst HS.
assert (Hin_al : In CS_arg_line cmd_prog_syms)
  by (unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])).
rewrite (siv_sig CS_arg_line SIGP Hin_al).
replace (cmd_af CS_arg_line) with AF_arg_line by (vm_compute; reflexivity).
(* the run wrote the slot's first two words and nothing else *)
lazymatch goal with HFR : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?m2)) |- _ =>
  pose proof (siv_kept_outside (w_H Wc) memc (ms_mem m2) E (siv_slot R) HFR EC') as RDQ end.
(* the registers at the call *)
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros k r Hk; apply siv_E_reg; exact Hk).
assert (EC2 : ew E RB_C = Z_to_bv 64 (siv_slot R)) by (unfold RB_C; apply siv_E_C).
assert (T2 : getr (ms_regs ms) 2 = getr regs1 2) by (rewrite P2; apply EE; reflexivity).
assert (Tsp : spZ (ms_regs ms) = sp0 + -48) by (unfold spZ; rewrite T2; fold (spZ regs1); lia).
assert (T3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact Rgp).
assert (T4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact Rtp).
assert (T8 : getr (ms_regs ms) 8 = w64 (siv_slot R)) by (rewrite P8; exact EC2).
assert (T9 : getr (ms_regs ms) 9 = w64 pl) by (rewrite P9, (EE 9%nat 9%bv eq_refl); exact R9).
assert (T18 : getr (ms_regs ms) 18 = w64 ledger) by (rewrite P18, (EE 18%nat 18%bv eq_refl); exact R18).
assert (T10 : getr (ms_regs ms) 10 = w64 (siv_slot R)) by (rewrite P10; exact EC2).
assert (T11 : getr (ms_regs ms) 11 = w64 pl) by (rewrite P11, (EE 9%nat 9%bv eq_refl); exact R9).
assert (Thi : forall r, 20 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hr. assert (Hr8 : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  (rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS); cbn [ms_regs];
   lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
     let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
   cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EE; reflexivity). }
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & _).
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms)))
  by exact (siv_aro_kept B RRO RELRO ROPA ly S W mem md _ R O lyc Sc Wc (ms_mem ms) _ _ _ _ _ HAR HrepE HJ HROD).
assert (HROc : cmd_ro_ok (rdW Wc (ms_mem ms))) by exact (ROK lyc Sc Wc (ms_mem ms) _ HARc HRODc).
destruct (siv_line_kept B HB PIMG HTV ly S W mem md R O pl line lyc Sc Wc (ms_mem ms) _ _ _ kk
  HAR HrepE HLB HLAP HLSTR0 HJ I2) as (HLSTR & HLHOME & HLTAIL).
(* the two words the segment stored, read back from the slot's region *)
assert (HR1 : region_ok SEGS E (mrestrict (w_H Wc) (ms_mem ms))
   (YP09.mkRegion (Some RB_C) 0 CALL_SIZE 0 8
      [YP09.mkChunk 4 (CVal 4 (SLit 0)); YP09.mkChunk 0 (CVal 4 (SLit 7))])).
{ refine (st_ok_region_nth E _ _ 1%nat _ HS _). vm_compute. reflexivity. }
assert (HFN : aval_mem (rdW Wc (ms_mem ms)) (siv_slot R + CALL_OFF_FN) 4 7).
{ apply (aval_mem_view SEGS).
  pose proof (field_of_region_any E (mrestrict (w_H Wc) (ms_mem ms)) RB_C (siv_slot R) _ 0 CALL_SIZE 0 8 0 4%N (SLit 7)
    HR1 EC' ltac:(cbn [In]; right; left; reflexivity) ltac:(cbn; lia)) as HV.
  replace (bv_unsigned (sv_denot E (SLit 7)) mod 2 ^ (8 * Z.of_N 4)) with 7 in HV by (vm_compute; reflexivity).
  change (N.to_nat 4) with 4%nat in HV. unfold CALL_OFF_FN. exact HV. }
assert (HNARGS : aval_mem (rdW Wc (ms_mem ms)) (siv_slot R + CALL_OFF_NARGS) 4 0).
{ apply (aval_mem_view SEGS).
  pose proof (field_of_region_any E (mrestrict (w_H Wc) (ms_mem ms)) RB_C (siv_slot R) _ 0 CALL_SIZE 0 8 4 4%N (SLit 0)
    HR1 EC' ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as HV.
  replace (bv_unsigned (sv_denot E (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in HV by (vm_compute; reflexivity).
  change (N.to_nat 4) with 4%nat in HV. unfold CALL_OFF_NARGS. exact HV. }
(* the premises of arg_line's contract at the call *)
assert (Hslot : (exists i, 0 <= i < REC_CALLS_MAX /\ siv_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * i)
   \/ siv_slot R = A_REC_SPILL).
{ unfold siv_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl];
  [left; exists (Z.of_nat (length (r_calls R))); split; [unfold REC_CALLS_MAX; lia | reflexivity]
  | right; reflexivity]. }
assert (HEVc : st_nev Sc + EV_ARG_LINE <= EV_MAX).
{ unfold EV_SUP_INSTANCE_VERB, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV. lia. }
assert (HLIVEc : blocks_bytes Sc + LIVE_ARG_LINE line <= LIVE_MAX).
{ unfold LIVE_SUP_INSTANCE_VERB, LIVE_ARG_I, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in HLIVE.
  pose proof (Nat2Z.is_nonneg (length (dec ledger))).
  pose proof (Nat2Z.is_nonneg (length (snd (sup_instance_verb_m R line ledger)))). lia. }
assert (HXL : 0 <= XM_ARG_LINE MT line).
{ rewrite WXM. pose proof (Nat2Z.is_nonneg (length line)).
  exact (mo_malloc_nonneg MT MTL (Z.of_nat (length line) + 1) ltac:(lia)). }
assert (HXrest : 0 <= XM_ARG_I MT ledger + XM_ANSWER MT (snd (sup_instance_verb_m R line ledger))).
{ unfold XM_ARG_I, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
  pose proof (mo_free_nonneg MT MTL).
  pose proof (Nat2Z.is_nonneg (length (dec ledger))).
  pose proof (Nat2Z.is_nonneg (length (snd (sup_instance_verb_m R line ledger)))).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec ledger)) + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_instance_verb_m R line ledger))) + 1) ltac:(lia)).
  lia. }
assert (HMOKc : mo_ok MT Sc (XM_ARG_LINE MT line)).
{ apply (mok_station MT S Sc (XM_SUP_INSTANCE_VERB MT R line ledger) (rec_spill_frees R * mo_free MT)
    (XM_ARG_LINE MT line) MTL HMOK HMLE HXL). unfold XM_SUP_INSTANCE_VERB. lia. }
(* the line at the call: inside a live block *)
assert (HLBc : in_blockA (ablocks B lyc Sc) pl (Z.of_nat (length line) + 1)).
{ destruct HLHOME as (q & k & Hqk & Hq1 & Hq2). exists q, k. split; [exact Hqk | lia]. }
(* no block of the recorder meets the slot: a block's bytes are not image bytes, the slot's are *)
assert (HBLKNI : forall q m i, In (q, m) (ablocks B lyc Sc) -> 0 <= i < m ->
   ~ (siv_slot R <= q + i < siv_slot R + CALL_SIZE)).
{ intros q m i Hin Hi Hx.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc Hin) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
  apply (recb_heap_noimg_m B lyc Sc Wc (ms_mem ms) _ q m (q + i) HARc Hin ltac:(lia)).
  apply PIMG. destruct Hc as [(H1 & H2 & _) | Hsp'];
  [apply recb_grec_in; unfold A_G_REC, REC_SIZE, OFF_CALLS, CALL_SIZE in *; lia
  | rewrite Hsp' in Hx; apply recb_spill_in; unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia]. }
assert (HNCc : aval_mem (rdW Wc (ms_mem ms)) (A_G_REC + OFF_NCALLS) 4
   (Z.of_nat (length (r_calls (rec_record R REC_INSTANCE_VERB []))))).
{ apply (aval_mem_kept (rdW Wc memc)); [exact HNC|].
  intros k Hk. apply RDQ; unfold A_G_REC, OFF_NCALLS, OFF_CALLS in *; lia. }
(* record() over the recorder's representation *)
assert (HREC : arep_at (ablocks B lyc Sc) (rdW Wc (ms_mem ms)) A_G_REC A_REC_SPILL
   (rec_record R REC_INSTANCE_VERB []) (slot_lay Q0 R [])).
{ rewrite <- HRR, <- HSLQ.
  apply (siv_record_step (ablocks B lyc Sc) rd0 R0 Q0 (ablocks B lyc Sc) (rdW Wc (ms_mem ms)) REC_INSTANCE_VERB
    HAREP0 HSPE ltac:(unfold REC_INSTANCE_VERB, REC_FN_COUNT; lia) I4).
  - intros a Ha Hns Hnc. rewrite HSL0 in Hns.
    rewrite (RDQ a ltac:(unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia) Hns).
    exact (HG0 a Ha Hnc).
  - intros pn i Hpn Hi. destruct pn as [q m]. cbn [fst snd] in *.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc (I4 _ Hpn)) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
    rewrite (RDQ (q + i) ltac:(lia)
      ltac:(intros Hx; apply (HBLKNI q m i (I4 _ Hpn) Hi); unfold CALL_SIZE in *; lia)).
    exact (HB0 (q, m) i Hpn Hi).
  - rewrite HRR. exact HNCc.
  - rewrite HSL0. exact HFN.
  - rewrite HSL0. exact HNARGS. }
(* the call of arg_line *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_arg_line)) SUP_INSTANCE_VERB_STK sp0
    (siv_FP O) ly S W mem md [] lyc Sc _ kk ARG_LINE_STK _ EV_ARG_LINE (-48) (getr (ms_regs ms) 1) [] _ HJ).
  - exact Tsp.
  - reflexivity.
  - lia.
  - clear - WAL; lia.
  - clear - WAL WS; lia.
  - exact T3.
  - exact T4.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite T8. unfold w64.
    rewrite unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
    unfold A_REC_SPILL in Hcb. lia.
  - intros HPRE1.
    eapply (TARG_LINE fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ _ (siv_slot R) pl 0 line HPRE1 HRODc T10 T11
      Hpl64 Hslot HNARGS ltac:(unfold REC_ARGS_MAX; lia) HLBc HLSTR HLL HEVc HLIVEc HMOKc).
  - intros a Ha. replace (0 <? REC_ARGS_MAX) with true in Ha by reflexivity.
    destruct Ha as (r & Hr & Har). cbn [In] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Har;
    (eapply (siv_awr_slot HB PIMG); [exact Hc | unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia]).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw Hnw. exfalso.
    replace (0 <? REC_ARGS_MAX) with true in Ha by reflexivity.
    destruct Ha as (r & Hr & Har). cbn [In] in Hr. rewrite WS in Hw.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Har;
    (unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2i & HP2 & HK2).
rewrite P1. change (Z_to_bv 64 (BASE + 20356)) with (Z_to_bv 64 (BASE + SIV_L_RET)).
destruct HK2 as (HLV2 & HMLE2 & [(Hm6 & _) | (_ & p & HKp)]); [exfalso; unfold REC_ARGS_MAX in Hm6; lia|].
cbv zeta in HKp.
destruct HKp as ((Hp4096 & Hp64) & HPerm & HAP & HNARGS2 & HARGS2 & HSTR2).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
assert (Hlinenn : 0 <= Z.of_nat (length line)) by apply Nat2Z.is_nonneg.
assert (Hin1 : In (p, Z.of_nat (length line) + 1) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HPerm)); left; reflexivity).
assert (KEEPF : forall a, sp0 - 48 <= a < sp0 -> rdW W2 mem2 a = rdW Wc (ms_mem ms) a).
{ intros a Ha. apply G1.
  - rewrite WS in Hslo. lia.
  - lia.
  - intros Hin. replace (0 <? REC_ARGS_MAX) with true in Hin by reflexivity.
    destruct Hin as (r & Hr & Har). cbn [In] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Har;
    (unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia). }
assert (KEEPG : forall a, Exists (in_zr a) recb_PG ->
   ~ (siv_slot R + CALL_OFF_NARGS <= a < siv_slot R + CALL_OFF_NARGS + 4) ->
   ~ (siv_slot R + CALL_OFF_ARGS <= a < siv_slot R + CALL_OFF_ARGS + 8) ->
   rdW W2 mem2 a = rdW Wc (ms_mem ms) a).
{ intros a Ha Hn1 Hn2. destruct (siv_prog_unowned B HB a Ha) as [Hown Herr].
  apply G3; [exact (PIMG a Ha) | exact Hown | exact Herr |].
  apply fp_spares_closed.
  - replace (0 <? REC_ARGS_MAX) with true by reflexivity.
    apply sink_closed_pos. repeat apply Forall_cons; try apply Forall_nil;
    cbn [fst]; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_G_REC, OFF_CALLS in *; lia.
  - intros Hin. replace (0 <? REC_ARGS_MAX) with true in Hin by reflexivity.
    destruct Hin as (r & Hr & Har). cbn [In] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Har;
    [exact (Hn1 Har) | apply Hn2; unfold CALL_OFF_ARGS in *; lia]. }
(* the argument block arg_line made, appended to the call *)
assert (HARG2 : arep_at (ablocks B ly2 S2) (rdW W2 mem2) A_G_REC A_REC_SPILL
   (rec_record R REC_INSTANCE_VERB [canon line]) (slot_lay Q0 R [(p, Z.of_nat (length line) + 1)])).
{ apply (siv_arg_step (ablocks B lyc Sc) (rdW Wc (ms_mem ms)) R REC_INSTANCE_VERB [] Q0 []
    (ablocks B ly2 S2) (rdW W2 mem2) p (Z.of_nat (length line) + 1) (canon line) HREC ltac:(cbn; lia)).
  - rewrite LB0. intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPerm)). right. exact (I4 _ Hpn).
  - exact Hin1.
  - intros a Ha Hn1 Hn2. apply KEEPG.
    + destruct Ha as [Hx|Hx]; [apply recb_grec_in | apply recb_spill_in]; exact Hx.
    + exact Hn1.
    + intros Hx. apply Hn2. cbn [length]. lia.
  - intros pn i Hpn Hi. rewrite LB0 in Hpn. destruct pn as [q m]. cbn [fst snd] in *.
    assert (Hpnc : In (q, m) (ablocks B lyc Sc)) by exact (I4 _ Hpn).
    assert (Hpn2 : In (q, m) (ablocks B ly2 S2))
      by (apply (Permutation_in _ (Permutation_sym HPerm)); right; exact Hpnc).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc Hpnc) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
    apply (G2 q m i Hpnc Hpn2); [lia|].
    intros Hin. replace (0 <? REC_ARGS_MAX) with true in Hin by reflexivity.
    destruct Hin as (r & Hr & Har). cbn [In] in Hr.
    apply (HBLKNI q m i Hpnc ltac:(lia)).
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Har;
    (unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia).
  - exact HNARGS2.
  - exact HARGS2.
  - exact HSTR2.
  - lia.
  - pose proof (canon_length line). unfold LMAX in *. lia.
  - pose proof (canon_length line). unfold LMAX in *. lia.
  - rewrite LB0. intros Hq. apply in_map_iff in Hq as ([q m] & Hqe & Hqm). cbn [fst] in Hqe. subst q.
    assert (Hpnc : In (p, m) (ablocks B lyc Sc)) by exact (I4 _ Hqm).
    assert (Hpn2 : In (p, m) (ablocks B ly2 S2))
      by (apply (Permutation_in _ (Permutation_sym HPerm)); right; exact Hpnc).
    pose proof (siv_block_start B ly2 S2 W2 mem2 md2 p m (Z.of_nat (length line) + 1) HAR2 Hpn2 Hin1) as Hme.
    rewrite Hme in Hpnc.
    pose proof (proj1 (Forall_forall _ _) HAP _ Hpnc) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap. lia.
  - unfold iv_apart.
    destruct (Z.le_gt_cases (p + (Z.of_nat (length line) + 1)) A_G_REC) as [Hx|Hx]; [left; exact Hx|].
    destruct (Z.le_gt_cases (A_G_REC + REC_SIZE) p) as [Hy|Hy]; [right; exact Hy|]. exfalso.
    pose proof (req_size_pos (Z.of_nat (length line) + 1) ltac:(lia)) as [_ Hreq].
    apply (recb_heap_noimg_m B ly2 S2 W2 mem2 md2 p (Z.of_nat (length line) + 1) (Z.max p A_G_REC) HAR2 Hin1
      ltac:(unfold A_G_REC, REC_SIZE in *; lia)).
    apply PIMG. apply recb_grec_in. unfold A_G_REC, REC_SIZE in *. lia.
  - unfold iv_apart.
    destruct (Z.le_gt_cases (p + (Z.of_nat (length line) + 1)) A_REC_SPILL) as [Hx|Hx]; [left; exact Hx|].
    destruct (Z.le_gt_cases (A_REC_SPILL + SC_SIZE) p) as [Hy|Hy]; [right; exact Hy|]. exfalso.
    pose proof (req_size_pos (Z.of_nat (length line) + 1) ltac:(lia)) as [_ Hreq].
    apply (recb_heap_noimg_m B ly2 S2 W2 mem2 md2 p (Z.of_nat (length line) + 1) (Z.max p A_REC_SPILL) HAR2 Hin1
      ltac:(unfold A_REC_SPILL, SC_SIZE in *; lia)).
    apply PIMG. apply recb_spill_in. unfold A_REC_SPILL, SC_SIZE in *. lia. }
(* the blocks of the layout the segment hands on *)
assert (LB1 : Permutation (lay_blocks (slot_lay Q0 R [(p, Z.of_nat (length line) + 1)]))
   (lay_blocks Q0 ++ [(p, Z.of_nat (length line) + 1)])).
{ unfold slot_lay. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl].
  - rewrite <- LBt.
    apply (siv_lay_perm_lt (l_calls Q0) [] (l_spill Q0) (l_answer Q0) (l_reply Q0) (p, Z.of_nat (length line) + 1)).
  - rewrite <- (LBs ltac:(lia)).
    apply (siv_lay_perm_full (l_calls Q0) [] (l_answer Q0) (l_reply Q0) (p, Z.of_nat (length line) + 1)). }
assert (I1' : forall pn, In pn (lay_blocks (slot_lay Q0 R [(p, Z.of_nat (length line) + 1)])) ->
   In pn O \/ ~ In pn (ablocks B ly S)).
{ intros pn Hpn. apply (Permutation_in _ LB1) in Hpn. apply in_app_iff in Hpn as [Hpn | Hpn].
  - exact (I1 pn Hpn).
  - cbn [In] in Hpn. destruct Hpn as [<- | []].
    destruct (siv_in_dec (p, Z.of_nat (length line) + 1) (ablocks B ly S)) as [Hin|Hnin]; [|right; exact Hnin].
    destruct (siv_in_dec (p, Z.of_nat (length line) + 1) O) as [Ho|Hno]; [left; exact Ho|]. exfalso.
    pose proof (proj1 (Forall_forall _ _) HAP _ (I2 _ Hin Hno)) as Hap. cbn [fst snd] in Hap.
    unfold iv_apart in Hap. lia. }
assert (I2' : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly2 S2)).
{ intros pn Hpn Hno. apply (Permutation_in _ (Permutation_sym HPerm)). right. exact (I2 pn Hpn Hno). }
assert (I3' : forall pn, In pn (ablocks B ly2 S2) ->
   (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks (slot_lay Q0 R [(p, Z.of_nat (length line) + 1)]))).
{ intros pn Hpn. apply (Permutation_in _ HPerm) in Hpn. cbn [In] in Hpn. destruct Hpn as [<- | Hpn].
  - right. apply (Permutation_in _ (Permutation_sym LB1)). apply in_app_iff. right. left. reflexivity.
  - destruct (I3 pn Hpn) as [Hl | Hq]; [left; exact Hl|].
    right. apply (Permutation_in _ (Permutation_sym LB1)). apply in_app_iff. left. exact Hq. }
assert (HFOc : siv_frame_ok (mrestrict (w_H Wc) (ms_mem ms)) sp0 regs).
{ apply (siv_frame_kept (w_H Wc) (w_H Wc) memc (ms_mem ms) sp0 regs HFO).
  intros a Ha. apply RDQ; [lia | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia]. }
assert (R9' : getr regs2 9 = w64 pl) by exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) T9).
assert (R18' : getr regs2 18 = w64 ledger) by exact (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) T18).
apply (HL ly S W regs mem md ch pl ledger line R O ly2 S2 W2 mem2 md2 regs2 (kk + EV_ARG_LINE) Q0 p
  (Z.of_nat (length line) + 1) CX HFRM); [| exact R9' | exact R18'].
split; [exact HJ2|].
split; [lia|].
split; [exact (siv_frame_kept (w_H Wc) (w_H W2) (ms_mem ms) mem2 sp0 regs HFOc KEEPF)|].
split.
{ assert (U2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  split; [unfold spZ at 1; rewrite U2; exact Tsp|].
  split; [exact (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) T3)|].
  split; [exact (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) T4)|].
  split; [exact (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) T8)|].
  intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)), (Thi r Hr). exact (Rhi r Hr). }
split; [exact HARG2|].
split; [exact I1'|].
split; [exact I2'|].
split; [exact I3'|].
split; [exact (mle_station MT S Sc S2 _ _ MTL HMLE HMLE2)|].
lia.
Qed.

End e.
End f.
End d.
