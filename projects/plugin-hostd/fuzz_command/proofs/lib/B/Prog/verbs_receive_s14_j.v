(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the join 0x8d4cc (vr_hd of lib/B/Prog/verbs_receive_iface.v) assembled after a
   recorder callee of the arms S14-S16 of the walk of verbs_receive on the ASan+UBSan build of plugin-hostd/
   fuzz_command: the journal, the meter, the frame, the saved and spilled registers, the recorder's blocks and the
   line and copy blocks carried through the callee. The B twin of the A walk's verbs_receive_s14_j.v (join 0x8dc94):
   B's registers at the call are s3 = tok = F+32, s2 = q, s6 = F and s11 = shadow(F)+4, all callee-saved, which is
   the list vr_rl_hd gives at 0x8d4cc without a0. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route SlotWords.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_s14_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation NoDup := List.NoDup.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis MTL : ameter_laws MT.
Hypothesis PROGU : vr_prog_unowned B.

(* the join 0x8d4cc at any program counter (the return of the callee, before the jump to 0x8d4cc) *)
Definition vr_hdx (e : vrE) (pc : Z) : world SEGS -> config -> Prop := fun Wc cf =>
exists tq O1 pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc pc) regsc memc mdc /\
vr_hd_ntok 0x8d4cc (length (Verbs.toks (e_D e))) /\
4096 <= tq /\ astr_atR (rdW Wc memc) tq (vr_x (e_R e) (e_D e)) /\
vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  (vr_rl_hd e F q c 0x8d4cc tq) (vr_R1 (e_R e) (e_D e)) O1 (vr_qv e)
  k (vr_k1 (e_R e) (e_D e)) nm VR_NM_HD lyc Sc Wc regsc memc mdc /\
vr_line B e q Wc memc /\ vr_copy B e F c tp Wc memc.
Lemma vr_hdx_hd : forall e W cf, vr_hdx e 0x8d4cc W cf -> vr_hd B MT e 0x8d4cc W cf.
Proof. intros e W cf H. exact H. Qed.

Lemma vr_spill_call : forall O STK1 lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 e l,
AR SEGS B lyc Sc W memc mdc -> (forall pn, In pn O -> In pn (ablocks B lyc Sc)) ->
ajournal SEGS B STK1 (vr_s1 e) (vr_cfp O) lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
vr_s1 e + 80 <= 2 ^ 64 -> Forall (fun ov => 0 <= fst ov <= 72) l ->
vr_spill e W memc l -> vr_spill e W2 mem2 l.
Proof.
intros O STK1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 e l HARc HOc HJc Hb Hl H. unfold vr_spill in *.
rewrite Forall_forall in *. intros ov Hov. specialize (H ov Hov). specialize (Hl ov Hov).
apply (aval_mem_agree _ _ _ _ _ H). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
apply (call_kept_hi B PROGU O STK1 (vr_s1 e) lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 HARc HOc HJc). lia.
Qed.

(* the meter after a recorder callee: the walk's meter before it and the callee's mo_le with at most m mallocs of
   VERBS_RECEIVE_REQ bytes and f frees, each at most the callee's EV1 events (the one place the arms S14-S17 step the
   meter across a call; the interface's vri_meter_step) *)
Lemma vr14_meter_call : forall e Sc S2 k nm EV1 XM1 m f,
vr_meter MT e Sc k nm -> mo_le MT Sc S2 XM1 ->
0 <= m <= EV1 -> 0 <= f <= EV1 ->
XM1 <= m * mo_malloc MT VERBS_RECEIVE_REQ + f * mo_free MT ->
vr_meter MT e S2 (k + EV1) (nm + m).
Proof.
intros e Sc S2 k nm EV1 XM1 m f Hmet HMLE Hm Hf HXM.
eapply vri_meter_step; [exact MTL | exact Hmet | exact HMLE | exact HXM | exact Hm | exact Hf].
Qed.

Lemma vr_hdx_of_call : forall e (W : world SEGS) pos F q c tp lyc Sc regsc memc mdc k nm r
  memc' mdc' regsc' STK1 EV1 XM1 m f ly2 S2 (W2 : world SEGS) regs2 mem2 md2 R' t tq O' ret,
vr_ent B MT e ->
(2 <= length (Verbs.toks (e_D e)))%nat ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) r (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
rd_same (rdW W memc) (rdW W memc') ->
AR SEGS B lyc Sc W memc' mdc' ->
vr_rv regsc' (vr_base B e ++ [(19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)]) ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] ly2 S2 W2 mem2 md2 (k + EV1) ->
ajournal SEGS B STK1 (vr_s1 e) (vr_cfp (e_O e)) lyc Sc W memc' mdc' [] ly2 S2 W2 mem2 md2 EV1 ->
aregs_preserved regsc' regs2 ->
getr regs2 10 = w64 tq -> 4096 <= tq ->
rec_repA B ly2 S2 (rdW W2 mem2) R' O' ->
(forall pn, In pn O' -> In pn (e_O e) \/ ~ In pn (ablocks B lyc Sc)) ->
In (tq, Z.of_nat (length t) + 1) (ablocks B ly2 S2) ->
(forall pn, In pn (ablocks B lyc Sc) -> ~ In pn (e_O e) -> pn <> (tq, Z.of_nat (length t) + 1)) -> ~ In tq (map fst O') ->
astr_atR (rdW W2 mem2) tq t ->
(forall pn, In pn (ablocks B lyc Sc) -> ~ In pn (e_O e) -> In pn (ablocks B ly2 S2)) ->
(forall pn, In pn (ablocks B ly2 S2) -> (In pn (ablocks B lyc Sc) /\ ~ In pn (e_O e)) \/ In pn O' \/ pn = (tq, Z.of_nat (length t) + 1)) ->
mo_le MT Sc S2 XM1 ->
0 <= m <= EV1 -> 0 <= f <= EV1 -> m <= 25 ->
XM1 <= m * mo_malloc MT VERBS_RECEIVE_REQ + f * mo_free MT ->
vr_h (e_R e) (e_D e) = (R', t, false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV1 ->
vr_hdx e ret W2 (cfg_at SEGS (vr_pc ret) regs2 mem2 md2).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm r memc' mdc' regsc' STK1 EV1 XM1 m f ly2 S2 W2 regs2 mem2 md2 R' t tq O' ret
He Hlen Hcore Hline Hcopy Hs HARc Hrvc HJ2 HJc HP H10 Htq HREC' HO'1 Hq1 Hq2 Hq3 Hqs HO'2 HO'3 HMLE Hm Hf Hm25 HXM Hh Hk1.
destruct Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsav & Hspl & _ & Hrec & HdO & Hperm & Hquit).
assert (ER1 : vr_R1 (e_R e) (e_D e) = R') by (unfold vr_R1; rewrite Hh; reflexivity).
assert (EX : vr_x (e_R e) (e_D e) = t) by (unfold vr_x; rewrite Hh; reflexivity).
assert (EQV : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite Hh; reflexivity).
pose proof He as (HPRE & _ & _ & _ & _ & _ & _ & Hn & HnD & Hdb & HdbO & _ & _ & HREC0 & _ & _ & _ & _ & _ & Hperm0 & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HS0 & Hceil0 & Hslo0 & Hshi0 & H470 & _).
pose proof asan_consts as (C1 & _).
fold (vr_sp0 e) in Hal16, HS0, Hceil0, Hslo0, Hshi0, H470.
assert (Hs1 : vr_sp0 e - 223 <= vr_s1 e <= vr_sp0 e - 192)
  by (unfold vr_s1; pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)); lia).
pose proof (proj1 HJ) as HAR1.
assert (HOc : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hpn. }
pose proof (ablocks_nodup B _ _ _ _ _ HAR1) as HND1.
assert (HdisjO : forall x, In x (e_O e) -> ~ In x ([vr_lb e q; vr_cb e c] ++ e_rest e))
  by (intros x Hx; exact (NoDup_perm_disj _ _ _ x HND1 Hperm Hx)).
assert (HinSc : forall x, In x ([vr_lb e q; vr_cb e c] ++ e_rest e) -> In x (ablocks B lyc Sc))
  by (intros x Hx; apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; exact Hx).
assert (HnotO : forall x, In x ([vr_lb e q; vr_cb e c] ++ e_rest e) -> ~ In x (e_O e))
  by (intros x Hx HxO; exact (HdisjO x HxO Hx)).
assert (Hlb1 : In (vr_lb e q) (ablocks B lyc Sc)) by (apply HinSc; left; reflexivity).
assert (Hcb1 : In (vr_cb e c) (ablocks B lyc Sc)) by (apply HinSc; right; left; reflexivity).
assert (HlbO : ~ In (vr_lb e q) (e_O e)) by (apply HnotO; left; reflexivity).
assert (HcbO : ~ In (vr_cb e c) (e_O e)) by (apply HnotO; right; left; reflexivity).
assert (Hlb2 : In (vr_lb e q) (ablocks B ly2 S2)) by exact (HO'2 _ Hlb1 HlbO).
assert (Hcb2 : In (vr_cb e c) (ablocks B ly2 S2)) by exact (HO'2 _ Hcb1 HcbO).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
(* the recorder's blocks after the call: the live blocks less the text, the line, the copy and the rest *)
set (K := (tq, Z.of_nat (length t) + 1) :: vr_lb e q :: vr_cb e c :: e_rest e).
set (O1 := zz_minus (ablocks B ly2 S2) K).
pose proof (proj1 HJ2) as HAR2.
pose proof (ablocks_nodup B _ _ _ _ _ HAR2) as HND2.
assert (HNDK : NoDup K).
{ constructor; [intros Hin; exact (Hq2 _ (HinSc _ Hin) (HnotO _ Hin) eq_refl) | exact (NoDup_perm_app_r _ _ _ HND1 Hperm)]. }
assert (HK2 : forall x, In x K -> In x (ablocks B ly2 S2)).
{ intros x [<- | Hx]; [exact Hq1|]. exact (HO'2 x (HinSc x Hx) (HnotO x Hx)). }
pose proof (perm_zz_minus _ _ HND2 HNDK HK2) as HPm.
assert (HO1 : forall pn, In pn O1 <-> In pn O').
{ intros pn. unfold O1. rewrite in_zz_minus. split.
  { intros [H1 H2]. destruct (HO'3 pn H1) as [[H3 H4] | [H3 | H3]]; [|exact H3|].
    { exfalso. apply H2. right. apply (Permutation_in _ Hperm) in H3. apply in_app_or in H3 as [H3|H3]; [contradiction | exact H3]. }
    { exfalso. apply H2. left. symmetry. exact H3. } }
  { intros H. split; [exact (rec_repA_in_blocks B _ _ _ _ _ _ HREC' H)|].
    intros [E | Hin].
    { apply Hq3. apply in_map_iff. exists pn. split; [rewrite <- E; reflexivity | exact H]. }
    { destruct (HO'1 pn H) as [HpO | HpS]; [exact (HdisjO pn HpO Hin) | exact (HpS (HinSc pn Hin))]. } } }
assert (Hdbr : In (e_data e, Z.max (e_n e) 1) (e_rest e)).
{ apply (Permutation_in _ Hperm0) in Hdb. apply in_app_or in Hdb as [Hdb|Hdb]; [contradiction | exact Hdb]. }
exists tq, O1, pos, F, q, c, tp, ly2, S2, regs2, mem2, md2, (k + EV1), (nm + m).
split; [reflexivity|].
split; [change (vr_hd_ntok 0x8d4cc (length (Verbs.toks (e_D e)))) with (2 <= length (Verbs.toks (e_D e)))%nat; exact Hlen|].
split; [exact Htq|]. split; [rewrite EX; exact Hqs|].
rewrite ER1, EQV, EX.
split; [|split].
{ split; [exact HJ2|]. split; [rewrite Hk1; lia|].
  split; [exact (vr14_meter_call e Sc S2 k nm EV1 XM1 m f Hmet HMLE Hm Hf HXM)|].
  split; [unfold VR_NM_HD, VR_NM_PRE in *; lia|].
  split; [exact (call_frame B PROGU (e_O e) STK1 (vr_s1 e) lyc Sc W memc' mdc' ly2 S2 W2 mem2 md2 EV1 HARc HOc HJc pos F vr_sh2 Hfin
      (vr_frame_same _ _ _ _ _ _ _ Hs Hfr))|].
  split.
  { change (vr_rl_hd e F q c 0x8d4cc tq)
      with [(10, tq); (19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)].
    assert (HR2 : vr_rv regs2 (vr_base B e ++ [(19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)])).
    { apply (vr_rv_preserved regsc' regs2 _ HP); [|exact Hrvc]. unfold vr_base. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. }
    unfold vr_rv in HR2 |- *. apply Forall_app in HR2 as [HB2 HL2]. apply Forall_app. split; [exact HB2|].
    constructor; [exact H10 | exact HL2]. }
  split.
  { intros j r0 Hj. assert (Hjl : (j < 13)%nat) by (change 13%nat with (length vr_saved_regs); apply nth_error_Some; rewrite Hj; discriminate).
    pose proof (aval_mem_same _ _ _ _ _ Hs (Hsav j r0 Hj)) as Hv.
    apply (aval_mem_agree _ _ _ _ _ Hv). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
    apply (call_kept_hi B PROGU (e_O e) STK1 (vr_s1 e) lyc Sc W memc' mdc' ly2 S2 W2 mem2 md2 EV1 HARc HOc HJc). lia. }
  split.
  { apply (vr_spill_call (e_O e) STK1 lyc Sc W memc' mdc' ly2 S2 W2 mem2 md2 EV1 e _ HARc HOc HJc); [lia | |].
    { unfold vr_sl3. repeat constructor; cbn [fst]; lia. }
    { exact (vr_spill_same _ _ _ _ _ Hs Hspl). } }
  split; [exact (vr_env_of_journal B MT RRO RPG RECC ROA e _ _ _ _ _ _ _ He HJ2)|].
  split; [exact (rec_repA_iff B _ _ _ _ O1 O' HO1 HREC')|].
  split; [intros H; apply in_zz_minus in H as [_ H]; apply H; right; right; right; exact Hdbr|].
  split; [exact HPm|].
  apply (call_kept_quit B PROGU (e_O e) STK1 (vr_s1 e) lyc Sc W memc' mdc' ly2 S2 W2 mem2 md2 EV1 HARc HOc HJc).
  exact (aval_mem_same _ _ _ _ _ Hs Hquit). }
{ destruct Hline as [Hfl Hstr]. split; [exact Hfl|].
  apply (call_astr B PROGU (e_O e) STK1 (vr_s1 e) lyc Sc W memc' mdc' ly2 S2 W2 mem2 md2 EV1 HARc HOc HJc q (vr_l (e_n e) (e_D e) + 1));
  [exact Hlb1 | exact HlbO | exact Hlb2 | lia | | exact (astr_atR_same _ _ _ _ Hs Hstr)].
  unfold vr_l. rewrite <- HnD, SlotWords.sw_strnlen_upto0. pose proof (SlotWords.sw_line_le (e_D e)). lia. }
{ destruct Hcopy as [Hfc Hat]. split; [exact Hfc|].
  pose proof (atoks_atA_same _ _ _ _ _ _ _ Hs Hat) as (Hal8 & Hlen' & Hw & Hstrs).
  destruct Hfr as (HF & _).
  split; [exact Hal8|]. split; [exact Hlen'|]. split.
  { intros i p Hp. assert (Hi : (i < length tp)%nat) by (apply nth_error_Some; rewrite Hp; discriminate).
    assert (Htk : (length (Verbs.toks (e_D e)) <= 64)%nat) by (unfold Verbs.toks; apply firstn_le_length).
    apply (aval_mem_agree _ _ _ _ _ (Hw i p Hp)). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
    apply (call_kept_frame B PROGU (e_O e) STK1 (vr_s1 e) lyc Sc W memc' mdc' ly2 S2 W2 mem2 md2 EV1 HARc HOc HJc 4 pos); [exact Hfin|].
    left. unfold frame_rng, in_zr. cbn [fst snd]. change (fs_frame_bytes 4) with 1024. rewrite <- HF. lia. }
  { intros i p w Hp Hw'. destruct (Hstrs i p w Hp Hw') as (A1 & A2 & A3 & A4).
    split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
    apply (call_astr B PROGU (e_O e) STK1 (vr_s1 e) lyc Sc W memc' mdc' ly2 S2 W2 mem2 md2 EV1 HARc HOc HJc c
      (Z.of_nat (length (Verbs.line (e_D e))) + 1)); [exact Hcb1 | exact HcbO | exact Hcb2 | exact A3 | exact A4 | exact A1]. } }
Qed.

End e.
End f.
End d.
