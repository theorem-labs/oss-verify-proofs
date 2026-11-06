(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: one part of sup_connect's ASan walk (plugin-hostd/fuzz_command),
   `scn_seg_b : SB1_stmt -> SCN_B_stmt`: the walk from the join of record()'s two arms 0x8adac to the first
   meeting point 0x8ade8. At the join the slot c (atom 8) gets c->fn := REC_CONNECT and c->nargs := 0 (the two
   inline checks of the stores are removed by the slot's shadow entry scn_SH_m); then `bnez s5` at 0x8addc
   checks the verb for NULL, and its two arms (s5 kept, or s5 := "(null)" at 0x22480) meet at 0x8ade8 in
   sup_connect_s4.v's sb_C1, where a0 and s5 become the atoms 41, 42 (sb_canon_ok). There the walk hands over
   to SB1_stmt.

   The seed at the join is sup_connect_s6.v's s6_seed. The join hands the recorder over as a fact about any
   reader that differs from its memory only inside the slot and holds the two fields (scn_mid,
   sup_connect_s0.v:434-436); the walk takes s6_rd, which reads the memory at 0x8ade8 inside the slot and the
   join's memory outside it, and sb_inv's agreement clause holds because the walk writes the slot only. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaSB PaDenot PaLibG PaLibF PaLibH PaCall PaNoChain PaArt CmdBase CmdRep CmdObj CmdZsh CmdAddr CmdRo CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c rec_canonical_c hand_back_c xstrdup_c arg_line_c answer_c sup_connect_c sup_connect_s0 sup_connect_s2
sup_connect_s4 sup_connect_s6.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Ltac s7_name_ms HS nm :=
lazymatch type of HS with
| st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into nm
| st_ok _ _ _ (restrict _ ?m) => rename m into nm
end.
Ltac s7_set_md nm :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (nm := mdx) in *; clearbody nm end.

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
(* the statement pass fixed the read-only range (CmdGlob.v) *)
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary record *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
(* interim CmdRecFacts facts, under CmdRecFacts.v's names; each becomes a lemma of
   lib/A/Prog/CmdRecFacts.v when statement pass 3 lands *)
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis PROG_WRITABLE : forall (m : word -> option byte) a, inFP cmd_PG a -> writable_at SEGS m a.
Hypothesis RRO : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis RPG : forall a, inFP cmd_PG a -> ~ in_roP SEGS RLO RHI a.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the hand-over at the first meeting point 0x8ade8: given sb_C1 there, a journal of the walk that wrote
   nothing outside the slot, and the environment, every premise of SB1_stmt holds *)
Lemma s7_close : SB1_stmt B MT ->
forall ly S (W : world SEGS) regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc (Wc : world SEGS) regsc
  memc mdc k c O1 E1 regs1 mem1 md1,
let t := snd (sup_connect_m R verb line port_a port_b) in
scn_pre B MT ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
scn_mid B MT ly S W regs mem md R O lyc Sc Wc regsc memc mdc k c O1 ->
st_ok_pi SEGS VAL E1 sb_C1 (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + SB_M1)) mem1 (seg_rom SEGS))) ->
sb_env E1 regsc regs -> ew E1 42 = Z_to_bv 64 (if pv =? 0 then 0x22480 else pv) ->
ajournal SEGS B SUP_CONNECT_STK (spZ regs) (scn_FP O) ly S W mem md [] lyc Sc Wc mem1 md1 k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> rdW Wc mem1 a = rdW Wc memc a) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SB_M1)) mem1 (seg_rom SEGS)) md1)
  (scn_post B MT ly S W regs mem md verb line port_a port_b R O t).
Proof.
intros SB1 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1
  E1 regs1 mem1 md1 t HPRE HMID HC HENV E42 HJ1 KEEP.
pose proof HPRE as (HPRE0 & HFRM & Hfr8 & HROD & HRO & H10 & Hpv64 & H11 & Hpl64 & H12 & Hpa64 & H13 & Hpb64 &
  HSV & HSVT & HSL & HSA & HSB & HREP0 & Hev & Hlive & HMOK).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HMID as (HJc & Hk & Hslot & Hpos & HRJ & HFR & HREC & HO1O & HO1c & HOO1 & HcS & HSc & Hfrsc & Hbbc & MLEc).
pose proof HRJ as (Rsp & R8 & R22 & R21 & R20 & R19 & R9 & R3 & R4 & Rhi).
pose proof (sb_O_facts B LAWS ly S W mem md _ R O HAR HREP0) as HOf.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn H; exact (proj1 (HOf pn H))).
assert (HOpos : Forall (fun pn => 0 < fst pn) O) by (apply Forall_forall; intros pn H; pose proof (HOf pn H); lia).
destruct (scn_slot_facts c Hslot) as (Hc8 & Hcr & Hcin).
assert (Hcr' : 0x5e3740 <= c < 0x5e3c18) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcr; lia).
pose proof (proj1 HJ1) as HAR1.
(* the two fields the join stored, from the slot's region at sb_C1 *)
assert (U81 : bv_unsigned (ew E1 8) = c).
{ destruct HENV as (_ & HE0). rewrite HE0 by lia. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regsc _ 8 8%bv eq_refl), R8. apply unsigned_lit_small. lia. }
pose proof (st_ok_pi_region_nth E1 sb_C1 _ 1
  (YP09.mkRegion (Some 8%nat) 0 CALL_SIZE 0 0 [YP09.mkChunk 4 (CVal 4 (SLit 0)); YP09.mkChunk 0 (CVal 4 (SLit 4))])
  HC ltac:(vm_compute; reflexivity)) as HRs.
cbn [ms_mem restrict mkst] in HRs.
pose proof (field_of_region E1 _ 8 c _ 0 CALL_SIZE 0 0 0 4 (SLit 4) 4 HRs U81 ltac:(cbn; tauto) eq_refl
  ltac:(cbn; lia) ltac:(lia)) as VFN.
pose proof (field_of_region E1 _ 8 c _ 0 CALL_SIZE 0 0 4 4 (SLit 0) 0 HRs U81 ltac:(cbn; tauto) eq_refl
  ltac:(cbn; lia) ltac:(lia)) as VNA.
change (N.to_nat 4) with 4%nat in VFN, VNA.
(* the reader the walk carries: the memory at 0x8ade8 inside the slot, the join's outside it *)
set (rd1 := s6_rd (rdW Wc memc) (rdW Wc mem1) c).
assert (AFN : aval_mem rd1 (c + CALL_OFF_FN) 4 REC_CONNECT).
{ intros i Hi. unfold rd1. rewrite s6_rd_in by (unfold CALL_OFF_FN, CALL_SIZE; lia).
  exact (scn_aval_of_val_mem SEGS _ _ _ _ _ VFN i Hi). }
assert (ANA : aval_mem rd1 (c + CALL_OFF_NARGS) 4 0).
{ intros i Hi. unfold rd1. rewrite s6_rd_in by (unfold CALL_OFF_NARGS, CALL_SIZE; lia).
  exact (scn_aval_of_val_mem SEGS _ _ _ _ _ VNA i Hi). }
pose proof (HREC rd1 (fun a Ha => s6_rd_out (rdW Wc memc) (rdW Wc mem1) c a Ha) AFN ANA) as HREP1.
assert (HK1 : forall a, sb_recb (ablocks B lyc Sc) O1 a -> rdW Wc mem1 a = rd1 a).
{ intros a Ha. unfold rd1.
  destruct (Z.le_gt_cases c a) as [Ha1 | Ha1]; [destruct (Z.lt_ge_cases a (c + CALL_SIZE)) as [Ha2 | Ha2]|].
  - rewrite s6_rd_in by lia. reflexivity.
  - rewrite s6_rd_out by lia. apply KEEP; [exact (sb_recb_rng B LAWS lyc Sc Wc mem1 md1 O1 a HAR1 Ha) | lia].
  - rewrite s6_rd_out by lia. apply KEEP; [exact (sb_recb_rng B LAWS lyc Sc Wc mem1 md1 O1 a HAR1 Ha) | lia]. }
(* the block bookkeeping: record() freed only recorder blocks *)
assert (HBK : sb_bk B ly S O (ablocks B lyc Sc) O1).
{ split; [|split].
  - intros pn Hpn. left. exact (HO1O pn Hpn).
  - intros pn Hpn. destruct (in_dec sb_pdec pn O) as [HinO | HnO].
    + right. exact (HOO1 pn Hpn HinO).
    + left. split; [exact (HcS pn Hpn) | exact HnO].
  - exact HSc. }
assert (HINV : sb_inv B MT ly S W mem md (spZ regs) R O Wc mem1 md1 lyc Sc k O1 [] rd1
  (rec_spill_frees R * mo_free MT)
  (LIVE_XSTRDUP (sarg verb) + LIVE_ARG_LINE line + LIVE_XSTRDUP (sarg port_a) + LIVE_XSTRDUP (sarg port_b) +
   LIVE_ANSWER t) 0).
{ split; [exact HJ1|]. split; [exact Hfrsc|].
  split; [unfold LIVE_SUP_CONNECT in Hlive; lia|]. split; [lia|]. split; [exact MLEc|].
  split; [exact HREP1|]. split; [exact HK1 | exact HBK]. }
(* the caller's strings at 0x8ade8: the walk's journal keeps every block it does not name *)
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW Wc mem1))
by exact (sb_arod B RRO RPG SUP_CONNECT_STK (spZ regs) O ly S W mem md [] lyc Sc Wc mem1 md1 k HAR HOin HOpos HJ1 HROD).
assert (KBL : forall q m, In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> In (q, m) (ablocks B lyc Sc))
by (intros q m Hq Hno; exact (HSc (q, m) Hq Hno)).
assert (KBLK : forall q m a, In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> q <= a < q + m ->
  rdW Wc mem1 a = rdW W mem a).
{ intros q m a Hq Hno Ha.
  exact (s6_blk_keep B LAWS SUP_CONNECT_STK (spZ regs) O ly S W mem md [] lyc Sc Wc mem1 md1 k q m a HAR HOin HJ1
    Hq Hno (KBL q m Hq Hno) Ha). }
assert (HSV1 : astr_argA B lyc Sc (rdW Wc mem1) (in_roP SEGS RLO RHI) [] pv verb)
by exact (s6_argA_move B ly S lyc Sc W Wc mem mem1 O pv verb HSV HROD HROD1 KBLK KBL).
assert (HSL1 : sb_sstr (ablocks B lyc Sc) (rdW Wc mem1) pl (Some line))
by exact (s6_sarg_move B LAWS ly S lyc Sc W mem md (rdW Wc mem1) O pl (Some line) HAR HSL KBLK KBL).
assert (HSA1 : sb_sstr (ablocks B lyc Sc) (rdW Wc mem1) pa port_a)
by exact (s6_sarg_move B LAWS ly S lyc Sc W mem md (rdW Wc mem1) O pa port_a HAR HSA KBLK KBL).
assert (HSB1 : sb_sstr (ablocks B lyc Sc) (rdW Wc mem1) pb port_b)
by exact (s6_sarg_move B LAWS ly S lyc Sc W mem md (rdW Wc mem1) O pb port_b HAR HSB KBLK KBL).
exact (SB1 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1
  E1 Wc regs1 mem1 md1 lyc Sc O1 rd1 (conj HPRE HMID) HC HENV E42 HINV HSV1 HSL1 HSA1 HSB1).
Qed.

Lemma scn_seg_b : SB1_stmt B MT -> SCN_B_stmt B MT.
Proof.
intros SB1 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1 t
  HPRE HMID.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HPRE0 & HFRM & Hfr8 & HROD & HRO & H10 & Hpv64 & H11 & Hpl64 & H12 & Hpa64 & H13 & Hpb64 &
  HSV & HSVT & HSL & HSA & HSB & HREP0 & Hev & Hlive & HMOK).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HMID as (HJc & Hk & Hslot & Hpos & HRJ & HFR & HREC & HO1O & HO1c & HOO1 & HcS & HSc & Hfrsc & Hbbc & MLEc).
pose proof HRJ as (Rsp & R8 & R22 & R21 & R20 & R19 & R9 & R3 & R4 & Rhi).
destruct (scn_slot_facts c Hslot) as (Hc8 & Hcr & Hcin).
assert (Hcr' : 0x5e3740 <= c < 0x5e3c18) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcr; lia).
pose proof (proj1 HJc) as HARc.
(* the seed at the join 0x8adac *)
pose proof (s6_seed B PROG_WRITABLE ly regs regsc lyc Sc Wc memc mdc c Hstk HARc Hslot HRJ HFR) as HS.
remember (Eimg (Ereg regsc (scn_extra_m regs))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite HE. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 80) by (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp).
assert (E8 : ew E 8 = w64 c) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (U8 : bv_unsigned (ew E 8) = c) by (rewrite E8; apply unsigned_lit_small; lia).
assert (E22 : ew E 22 = Z_to_bv 64 SCN_SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E21 : ew E 21 = w64 pv) by (rewrite (EE 21%nat 21%bv eq_refl), R21; exact H10).
pose proof (sb_shok B HB LAWS lyc Sc Wc memc mdc E c HARc Hslot U8 E22) as SHOK.
(* 0x8adac .. 0x8addc: c->fn := REC_CONNECT, c->nargs := 0 (the slot's shadow entry removes both checks) *)
paj_run_tok RUN HS HJc SHOK scn_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (sb_awr_slot B HB cif_prog_img); [reflexivity | exact U8 | exact Hslot | cbn; lia | cbn; unfold CALL_SIZE; lia |].
  apply awr_ok_nil. }
s7_set_md mdv1. s7_name_ms HS ms1.
pose proof (kept_of_frame (segs:=SEGS) E _ (w_H Wc) memc (ms_mem ms1) (fun a => c <= a < c + CALL_SIZE) HFr
  ltac:(intros b wlo whi a' Hin Hrr; cbv beta; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U8, ?U2 in Hrr;
          unfold CALL_SIZE; lia|]);
        destruct Hin)) as KEEP1.
clear HF HFr HG.
(* the slot read-only: the two arms of the null check write nothing *)
pose proof (sb_ro_state E _ _ HS) as HSr. clear HS. rename HSr into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
  let v := eval vm_compute in ssx in change ssx with v in HS end.
assert (HU21 : U E (SOff 21 0) = pv) by (apply (U_atom E 21 pv); [exact E21 | exact Hpv64]).
assert (HU0 : U E (SLit 0) = 0) by reflexivity.
assert (HENV : forall regs2 : bvmap 5 word, sb_env (havoc E 41 (map (getr regs2) [10; 21]%bv)) regsc regs).
{ intros regs2. split; [apply img_env_havoc; [exact HEI | cbv; lia]|].
  intros n Hn. rewrite YN3v.ew_havoc_old by lia. rewrite HE. reflexivity. }
(* 0x8addc: bnez s5 *)
psrr_branch_tok RUN BR HS SHOK scn_Bspan.
- (* the verb is a string: straight to 0x8ade8 *)
  assert (Hpv : pv <> 0).
  { rewrite branch_ne_U, HU21, HU0 in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
  paj_run_to_tok RUNTO HS HJc SHOK scn_Bspan SB_M1.
  { awr_ok_tac. }
  s7_set_md mdv2. s7_name_ms HS ms2.
  pose proof (kept_of_frame (segs:=SEGS) E _ (w_H Wc) (ms_mem ms1) (ms_mem ms2) (fun _ => False) HFr
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KEEP2.
  clear HF HFr HG.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> rdW Wc (ms_mem ms2) a = rdW Wc memc a).
  { intros a Ha Hn. rewrite (KEEP2 a Ha ltac:(cbv beta; tauto)). exact (KEEP1 a Ha Hn). }
  prreg HS (21%bv : bv 5) Q21.
  assert (R21' : getr (ms_regs ms2) 21 = Z_to_bv 64 (if pv =? 0 then 0x22480 else pv)).
  { rewrite Q21, E21. rewrite (proj2 (Z.eqb_neq pv 0) Hpv). reflexivity. }
  pmkst HS.
  pose proof (st_ok_pi_restrict_mkst (w_H Wc) _ _ _ HS eq_refl) as Hms2. cbn [ss_pc] in Hms2.
  pose proof (sb_canon_ok Wc _ _ _ 41%nat [10; 21]%bv HS eq_refl ltac:(cbv; lia) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HC.
  rewrite Hms2 in HC.
  lazymatch type of HC with st_ok_pi _ _ _ ?ssx _ =>
    assert (HEQ : ssx = sb_C1) by (vm_compute; reflexivity); rewrite HEQ in HC; clear HEQ end.
  assert (E42 : ew (havoc E 41 (map (getr (ms_regs ms2)) [10; 21]%bv)) 42 =
    Z_to_bv 64 (if pv =? 0 then 0x22480 else pv))
  by (unfold havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth map]; exact R21').
  exact (s7_close SB1 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1
    (havoc E 41 (map (getr (ms_regs ms2)) [10; 21]%bv)) (ms_regs ms2) (ms_mem ms2) mdv2 HPRE HMID HC
    (HENV (ms_regs ms2)) E42 HJc KEEP).
- (* the verb is NULL: s5 := "(null)" (0x22480), then 0x8ade8 *)
  assert (Hpv : pv = 0).
  { rewrite branch_ne_U, HU21, HU0 in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
  paj_run_to_tok RUNTO HS HJc SHOK scn_Bspan SB_M1.
  { awr_ok_tac. }
  s7_set_md mdv2. s7_name_ms HS ms2.
  pose proof (kept_of_frame (segs:=SEGS) E _ (w_H Wc) (ms_mem ms1) (ms_mem ms2) (fun _ => False) HFr
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KEEP2.
  clear HF HFr HG.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> rdW Wc (ms_mem ms2) a = rdW Wc memc a).
  { intros a Ha Hn. rewrite (KEEP2 a Ha ltac:(cbv beta; tauto)). exact (KEEP1 a Ha Hn). }
  prreg HS (21%bv : bv 5) Q21.
  assert (R21' : getr (ms_regs ms2) 21 = Z_to_bv 64 (if pv =? 0 then 0x22480 else pv)).
  { rewrite Q21. rewrite (proj2 (Z.eqb_eq pv 0) Hpv). apply bv_eq.
    rewrite (HEI 293%nat ltac:(unfold A_TEXT, A_LIM; lia)).
    change (VAL 293%nat) with (VAL (A_OBJ 52)). rewrite (scn_obj52 VOBJS).
    rewrite unsigned_lit_small by lia. reflexivity. }
  pmkst HS.
  pose proof (st_ok_pi_restrict_mkst (w_H Wc) _ _ _ HS eq_refl) as Hms2. cbn [ss_pc] in Hms2.
  pose proof (sb_canon_ok Wc _ _ _ 41%nat [10; 21]%bv HS eq_refl ltac:(cbv; lia) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HC.
  rewrite Hms2 in HC.
  lazymatch type of HC with st_ok_pi _ _ _ ?ssx _ =>
    assert (HEQ : ssx = sb_C1) by (vm_compute; reflexivity); rewrite HEQ in HC; clear HEQ end.
  assert (E42 : ew (havoc E 41 (map (getr (ms_regs ms2)) [10; 21]%bv)) 42 =
    Z_to_bv 64 (if pv =? 0 then 0x22480 else pv))
  by (unfold havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth map]; exact R21').
  exact (s7_close SB1 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1
    (havoc E 41 (map (getr (ms_regs ms2)) [10; 21]%bv)) (ms_regs ms2) (ms_mem ms2) mdv2 HPRE HMID HC
    (HENV (ms_regs ms2)) E42 HJc KEEP).
Qed.

End e.
End f.
End d.
