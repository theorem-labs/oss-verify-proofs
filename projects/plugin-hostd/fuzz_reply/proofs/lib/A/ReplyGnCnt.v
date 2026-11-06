(* The gone arm's two count rules (lib/A/W_LLVMFuzzerTestOneInput_gone_base.v Section g, after GN_LS_rig), at the
   instance gn_pk := ReplyLScnt.pk_gone, RINV := fr_RINV, and the callee peaks top_x passes, gn_rig_pk := gn_rig_pk_x
   (W_contract_x.v rig_pk at rig_tr), gn_cnl_pk := gn_cnl_pk_x (W_contract_x.v cnl_pk of the slot's two lists).
   proves no function (kind: invariant lemma).
   - The texts are gone_base's own (W8's C1 + C2 text, 2ca82cccb7b, landed with the TOP-step head 14fbe276057):
     gn_cnl_ok with cnl_post's exact capacity law last, GN_CNT_rig / GN_CNT_step over the peak parameters, C2 a
     premise; roomp / cnt_ok_pk are lib/A/W_journal_x.v's.
   - gcnt_rig / gcnt_step: GN_CNT_rig / GN_CNT_step PROVED at pk_gone.
   - The accounting behind gcnt_step, for any count predicate P: the generic part is lib/A/ReplyCntAcc.v (za / tz /
     ws, the model's pieces, check_no_loss's model change acc_cnl_src, check_shape_ends' acc_cshe_src, each callee
     piece's exact net acc_sl_run .. acc_lines, the drain's acc_drain, acc_drain_canon, acc_geik / acc_gei_perm, and
     acc_ws_len / acc_hpkh / acc_texts_lines / acc_za_out); here (Sections rig, loop, mrig) relay_instance_gone's
     model change is at most its trace's net plus g_out's two ends (acc_rig_run), the model after it
     (acc_model_rig), the table-order loop calls each slot at most once and moves the count by at most that slot's
     check_no_loss peak (acc_loop), and those peaks sum to pk_gone's gn_cnl sum (acc_Gs_sum); net_le_peak stays here
     (it reads ReplyLScntRP.lsc_net_le_peak).
   - rp_cnt_gone_cnl_of_step / rp_cnt_gone_later_of_step: ReplyLScntRP.v's gone rows from GN_CNT_step's conclusion
     (its pure-model inequality at the call's model) and the walk's gn_tie. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeakW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyTrPeakCnl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLScnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyLScntRP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCntAcc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_instance_gone_b_lem.
From stdpp Require list_basics.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


Section gc.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the official callee peaks the _x arm passes (W_contract_x.v rig_pk at relay_instance_gone's trace, cnl_pk of the
   slot's two lists) *)
Definition gn_rig_pk_x (cx : lfcx) (m : lmod) (hs : list (hsrc * nat)) : (Z -> bool) -> nat :=
  W_contract_x.rig_pk (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs).
Definition gn_cnl_pk_x (h : hsrc) : (Z -> bool) -> nat := W_contract_x.cnl_pk (hs_expected h) (hs_held h).

(* ================================================================== GN_CNT_rig *)
Lemma gcnt_rig : W_LLVMFuzzerTestOneInput_gone_base.GN_CNT_rig pk_gone gn_rig_pk_x.
Proof.
  intros cx m hs P. unfold gn_rig_pk_x, W_contract_x.rig_pk, pk_gone.
  match goal with |- (Z.to_nat ?a + 3 <= Z.to_nat ?b + _ + 3)%nat =>
    replace a with b by reflexivity end.
  lia.
Qed.
End gc.

(* net_le_peak stays here (the rest of the count accounting is lib/A/ReplyCntAcc.v): it reads
   ReplyLScntRP.lsc_net_le_peak *)
Section acc.
Variable P : Z -> bool.
Local Abbreviation net := (ReplyTrPeakW.tr_net_w (fun n => zb (P n))).
Lemma net_le_peak : forall X (tr : list (RelayRunT.rev X)), net tr <= tr_peakP P tr.
Proof. intros X tr. exact (ReplyLScntRP.lsc_net_le_peak X P tr). Qed.
End acc.


(* ================================================================== relay_instance_gone: per entry, the model change is
   at most the net of that entry's requests (its drain and its key run), up to the g_out chain's two ends *)
Section rig.
Variable P : Z -> bool.
Local Abbreviation net := (ReplyTrPeakW.tr_net_w (fun n => zb (P n))).
Local Abbreviation tz := (tz P).
Local Abbreviation za := (za P).
Local Abbreviation ws := (ws P).

Lemma acc_gei_ws : forall pre H, ws (fst (gei pre H)) + ws (snd (gei pre H)) = ws H.
Proof.
  intros pre H. unfold gei. rewrite <- ws_app. symmetry. apply acc_ws_perm. apply acc_gei_perm.
Qed.
Lemma acc_geik_ws : forall pre K,
  ws (drain_b_c.keys_texts (fst (geik pre K))) = ws (fst (gei pre (drain_b_c.keys_texts K))) /\
  ws (drain_b_c.keys_texts (snd (geik pre K))) = ws (snd (gei pre (drain_b_c.keys_texts K))).
Proof.
  intros pre K. unfold geik, gei, drain_b_c.keys_texts. rewrite length_map.
  destruct (acc_geik (length K) pre 0 K) as (E1 & E2). rewrite E1, E2. split; reflexivity.
Qed.
(* the per-entry facts the rule's premises give an open entry of the table and its source (gn_pairs, RINV, REQ1-REQ3) *)
Definition rig_pf (p : rentry * (hsrc * nat)) : Prop :=
  let e := fst p in let h := fst (snd p) in
  re_eof e = 0 ->
  (re_skip e = 0 \/ re_skip e = 1) /\ re_skip e = hs_overlong h /\ (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) /\
  Z.of_nat (length (re_U e)) <= 6000 /\ ~ In (Z_to_bv 8 0) (re_U e) /\ (re_cap e = 0 \/ 8192 <= re_cap e) /\
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) /\
  Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h)) /\
  hl_recs (hs_expected h) = [].
(* the held array of an entry: none and no key, or at least 8 bytes (aentry_ok, W_rep.v:131-132) *)
Definition rig_hk (e : rentry) : Prop := (re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 <= re_kh e).
(* one entry's model change: its table entry, and its source when it was drained *)
Definition adelta (p : rentry * (hsrc * nat)) (q : rentry * hsrc) : Z :=
  za (aentry_blks (fst q)) - za (aentry_blks (fst p)) +
  (if re_eof (fst p) =? 0 then za (asrc_blks (snd q)) - za (asrc_blks (fst (snd p))) else 0).

(* one table entry of relay_instance_gone: its model change, plus the g_out chain's start, is at most the net of its
   drain (when open) and its key run, plus the chain's end *)
Lemma acc_rig_entry : forall pre mx c (O : list byte) cap e h jj e' h' e1 (LB : list byte) lv no capT nm j o,
  (if re_eof e =? 0 then dr_rel c mx (Z.of_nat (length O)) cap e h e1 h' LB else e1 = e /\ h' = h) ->
  e' = entry_keys e1 (snd (geik pre (re_keys e1))) ->
  rig_pf (e, (h, jj)) -> rig_hk e -> rig_hk e' -> 0 <= capT ->
  let s := relay_remove_b_c.after_drain lv mx no capT e h in
  let a0 := drain_b_c.drain_start nm o e h in
  let td := if re_eof e =? 0 then drain_b_c.drain_tr lv mx no capT e h j a0 else [] in
  let a := relay_remove_b_c.after_drain_adr lv mx no capT e h j a0 in
  let gk := relay_instance_gone_b_c.geia pre (combine (drain_b_c.ds_H s) (drain_b_c.da_keys a)) in
  let xks := map (fun x => (Z.of_nat (length (fst x)), snd x)) (fst gk) in
  let k := gestures_end_b_c.keys_end_run lv mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) xks (j + RelayRunF.nretF td)
             (drain_b_c.da_out a) in
  adelta (e, (h, jj)) (e', h') + tz (fst (snd k)) - tz capT <= net (td ++ fst k) /\ 0 <= fst (snd k).
Proof.
  intros pre mx c O cap e h jj e' h' e1 LB lv no capT nm j o Hd Ee' Hpf Hk Hk' Hc.
  intros s a0 td a gk xks k.
  assert (LK : length (drain_b_c.da_keys a) = length (drain_b_c.ds_H s)).
  { unfold a, a0, s. apply RelayCap.rc_after_drain_len. }
  assert (EX : fold_right Z.add 0 (map (fun xk => zb (P (fst xk + 1))) xks) = ws (fst (gei pre (drain_b_c.ds_H s)))).
  { unfold xks. rewrite <- (RelayCap.rc_geia pre (drain_b_c.ds_H s) (drain_b_c.da_keys a) LK). fold gk.
    generalize (fst gk). induction l as [|x l IHl]; [reflexivity|]. cbn [map fold_right fst]. rewrite ws_cons, IHl.
    reflexivity. }
  pose proof (acc_gei_ws pre (drain_b_c.ds_H s)) as GW.
  unfold adelta. cbn [fst snd]. rewrite net_app. subst e'.
  assert (ZE' : za (aentry_blks (entry_keys e1 (snd (geik pre (re_keys e1))))) =
                tz (re_cap e1) + tz (drain_b_c.ent_ka e1) + ws (snd (gei pre (drain_b_c.keys_texts (re_keys e1))))).
  { pose proof (acc_hpkh P _ Hk') as HH. rewrite za_aentry, HH.
    unfold entry_keys, drain_b_c.ent_ka. cbn [re_cap re_hp re_kh re_keys].
    destruct (acc_geik_ws pre (re_keys e1)) as (_ & G2). rewrite G2. reflexivity. }
  assert (ZE : za (aentry_blks e) = tz (re_cap e) + tz (drain_b_c.ent_ka e) + ws (drain_b_c.keys_texts (re_keys e))).
  { rewrite za_aentry, (acc_hpkh P e Hk). reflexivity. }
  rewrite ZE', ZE.
  destruct (Z.eq_dec (re_eof e) 0) as [E0|E0].
  - rewrite (proj2 (Z.eqb_eq _ _) E0) in Hd |- *.
    cbn in Hpf. destruct (Hpf E0) as (SK & SO & SW & UL & UZ & UC & PD & PF & EX0).
    cbn [fst snd] in SK, SO, SW, UL, UZ, UC, PD, PF, EX0.
    destruct (relay_instance_gone_b_lem.rig_dinit no capT e h SK SO SW UL UZ UC PD PF) as [IV ER].
    assert (FU : (length (relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no capT e h)) +
                  (if drain_b_c.ds_eintr (drain_b_c.drain_init no capT e h) then 2 else 1)
                  <= S (S (length (pending_stream h))))%nat).
    { rewrite ER. unfold bzs. rewrite length_map. destruct (drain_b_c.ds_eintr _); lia. }
    destruct (acc_drain P _ lv mx _ j a0 IV ltac:(cbn; lia) FU) as [D1 D2].
    assert (ES : s = fst (snd (drain_b_c.drain_run (S (S (length (pending_stream h)))) lv mx
                      (drain_b_c.drain_init no capT e h) j a0))).
    { unfold s, relay_remove_b_c.after_drain. rewrite (proj2 (Z.eqb_eq _ _) E0).
      unfold drain_b_c.drain_fin, drain_b_c.drain_go. apply acc_fin_state. }
    assert (ET : td = fst (drain_b_c.drain_run (S (S (length (pending_stream h)))) lv mx
                      (drain_b_c.drain_init no capT e h) j a0)).
    { unfold td. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
    rewrite <- ES, <- ET, ER in D1. rewrite <- ES in D2.
    change (drain_b_c.ds_ref (drain_b_c.drain_init no capT e h)) with (hs_state h) in D1.
    destruct (acc_ker P xks lv mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) (j + RelayRunF.nretF td) (drain_b_c.da_out a)
                D2) as (K1 & K2).
    fold k in K1, K2. rewrite EX in K1.
    (* the model's drain state and the trace's agree on every field but g_nout / g_capout *)
    pose proof (acc_fin_canon (dr_live c h) lv mx mx (Z.of_nat (length O)) no cap capT e h) as CAN.
    assert (FS : drain_b_c.drain_fin lv mx no capT e h = s).
    { unfold s, relay_remove_b_c.after_drain. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
    rewrite FS in CAN.
    pose proof (f_equal drain_b_c.ds_cap CAN) as C1. pose proof (f_equal drain_b_c.ds_ka CAN) as C2.
    pose proof (f_equal drain_b_c.ds_H CAN) as C3. pose proof (f_equal drain_b_c.ds_ecap CAN) as C4.
    unfold acc_canon in C1, C2, C3, C4. cbn [drain_b_c.ds_cap drain_b_c.ds_ka drain_b_c.ds_H drain_b_c.ds_ecap] in C1, C2, C3, C4.
    unfold dr_rel in Hd. cbv zeta in Hd.
    destruct Hd as (_ & _ & _ & Ecap & _ & _ & EH & Eka & _ & _ & Eec & _ & _ & _ & _ & Epr & _ & _ & Epc & Epa & _ &
                    Eexp & _ & Ehd & _).
    unfold dr_fin in Ecap, EH, Eka, Eec. rewrite C1 in Ecap. rewrite C3 in EH. rewrite C2 in Eka. rewrite C4 in Eec.
    rewrite Ecap, Eka, EH.
    rewrite !za_asrc, !za_alist, Epc, Eec, Ehd.
    rewrite (acc_texts_lines P h h' EX0 Eexp).
    assert (TP : texts (hs_pending h') = []) by (unfold texts; rewrite Epr; reflexivity). rewrite TP, ws_nil.
    assert (TE : texts (hs_expected h) = []) by (unfold texts; rewrite EX0; reflexivity). rewrite TE, ws_nil.
    unfold dphi in D1. cbn [drain_b_c.drain_init drain_b_c.ds_cap drain_b_c.ds_ka drain_b_c.ds_H drain_b_c.ds_ecap
      drain_b_c.ds_ocap drain_b_c.ds_pend] in D1.
    change (map (fun r : Z * list byte => bzs (snd r)) (hl_recs (hs_pending h))) with (texts (hs_pending h)) in D1.
    unfold dr_lines. unfold AREC. split; [lia | exact K2].
  - rewrite (proj2 (Z.eqb_neq _ _) E0) in Hd |- *. destruct Hd as (-> & ->).
    assert (ES : s = drain_b_c.drain_init no capT e h).
    { unfold s, relay_remove_b_c.after_drain. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
    assert (ET : td = []) by (unfold td; rewrite (proj2 (Z.eqb_neq _ _) E0); reflexivity).
    assert (HOs : 0 <= drain_b_c.ds_ocap s) by (rewrite ES; cbn; exact Hc).
    destruct (acc_ker P xks lv mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) (j + RelayRunF.nretF td) (drain_b_c.da_out a)
                HOs) as (K1 & K2).
    fold k in K1, K2. rewrite EX in K1. rewrite ET, net_nil.
    rewrite ES in K1, GW. cbn [drain_b_c.drain_init drain_b_c.ds_H drain_b_c.ds_ocap] in K1, GW.
    split; [lia | exact K2].
Qed.

(* the whole table *)
Lemma acc_rig_run : forall pre mx ps qs c O cap c2 O2 cap2 lv no capT nm j o,
  rig_rel pre mx c O cap ps qs c2 O2 cap2 ->
  Forall rig_pf ps -> Forall (fun p => rig_hk (fst p)) ps -> Forall (fun q => rig_hk (fst q)) qs -> 0 <= capT ->
  fold_right Z.add 0 (map (fun pq => adelta (fst pq) (snd pq)) (combine ps qs)) +
    tz (snd (fst (fst (relay_instance_gone_b_c.gone_run lv mx no capT pre ps nm j o)))) - tz capT
    <= net (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no capT pre ps nm j o)))).
Proof.
  intros pre mx ps. induction ps as [|[e [h jj]] ps IH]; intros qs c O cap c2 O2 cap2 lv no capT nm j o HR HF HK HQ Hc.
  - destruct qs; [|cbn in HR; contradiction]. cbn. lia.
  - destruct qs as [|[e' h'] qs]; [cbn in HR; contradiction|].
    cbn [rig_rel] in HR. destruct HR as (e1 & ev & LB & HR). cbv zeta in HR. destruct HR as (Hd & Ee' & Hrest).
    inversion HF as [|? ? Hpf HF']; subst. inversion HK as [|? ? Hk HK']; subst.
    inversion HQ as [|? ? Hq HQ']; subst.
    pose proof (acc_rig_entry pre mx c O cap e h jj (entry_keys e1 (snd (geik pre (re_keys e1)))) h' e1 LB lv no capT
                  nm j o Hd eq_refl Hpf Hk Hq Hc) as HE.
    cbv zeta in HE. destruct HE as (HE1 & HE2).
    rewrite relay_instance_gone_b_lem.rig_gone_run_cons. cbv zeta. cbn [fst snd combine map fold_right].
    match goal with |- context [relay_instance_gone_b_c.gone_run lv mx ?n ?cc pre ps nm ?jj ?oo] =>
      destruct (sl_sends _ _ _ _ _) as [[c3 O3] cap3] eqn:ESL in Hrest;
      pose proof (IH qs c3 O3 cap3 c2 O2 cap2 lv n cc nm jj oo Hrest HF' HK' HQ' HE2) as IH';
      destruct (relay_instance_gone_b_c.gone_run lv mx n cc pre ps nm jj oo) as [[[tr' c'] ss'] [o' das']] end.
    cbn [fst snd] in IH' |- *. rewrite net_app in HE1 |- *. rewrite net_app. lia.
Qed.
End rig.

(* ================================================================== sums over lists and indices *)
Local Abbreviation zs := (fold_right Z.add 0).
Lemma acc_zs_app : forall l1 l2, zs (l1 ++ l2) = zs l1 + zs l2.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma acc_zs_ext : forall {A : Type} (f g : A -> Z) l, (forall x, In x l -> f x = g x) -> zs (map f l) = zs (map g l).
Proof.
  intros A f g l. induction l as [|x l IH]; intros H; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. exact (H y (or_intror Hy)).
Qed.
Lemma acc_zs_le : forall {A : Type} (f g : A -> Z) l, (forall x, In x l -> f x <= g x) -> zs (map f l) <= zs (map g l).
Proof.
  intros A f g l. induction l as [|x l IH]; intros H; cbn; [lia|].
  pose proof (H x (or_introl eq_refl)). pose proof (IH (fun y Hy => H y (or_intror Hy))). lia.
Qed.
Lemma acc_zs_sub : forall {A : Type} (f g : A -> Z) l, zs (map (fun x => f x - g x) l) = zs (map f l) - zs (map g l).
Proof. intros A f g l. induction l as [|x l IH]; cbn; [lia|]. rewrite IH. lia. Qed.
(* a sum over a pairing, against the sums over its two sides *)
Lemma acc_zs_combine_l : forall {A B : Type} (f : A -> Z) (l1 : list A) (l2 : list B), length l1 = length l2 ->
  zs (map (fun x => f (fst x)) (combine l1 l2)) = zs (map f l1).
Proof.
  intros A B f l1. induction l1 as [|a l1 IH]; intros [|b l2] E; cbn in *; try lia. rewrite IH by lia. reflexivity.
Qed.
Lemma acc_zs_combine_r : forall {A B : Type} (f : B -> Z) (l1 : list A) (l2 : list B), length l1 = length l2 ->
  zs (map (fun x => f (snd x)) (combine l1 l2)) = zs (map f l2).
Proof.
  intros A B f l1. induction l1 as [|a l1 IH]; intros [|b l2] E; cbn in *; try lia. rewrite IH by lia. reflexivity.
Qed.
(* an index statement gives a statement of each pair *)
Lemma acc_forall_combine : forall {A B : Type} (Q : A -> B -> Prop) (l1 : list A) (l2 : list B) d1 d2,
  length l1 = length l2 -> (forall i, (i < length l1)%nat -> Q (nth i l1 d1) (nth i l2 d2)) ->
  forall x, In x (combine l1 l2) -> Q (fst x) (snd x).
Proof.
  intros A B Q l1. induction l1 as [|a l1 IH]; intros [|b l2] d1 d2 E H x Hx; cbn in *; try contradiction; try lia.
  destruct Hx as [<-|Hx]; [exact (H 0%nat ltac:(lia))|].
  apply (IH l2 d1 d2 ltac:(lia)); [|exact Hx]. intros i Hi. exact (H (S i) ltac:(lia)).
Qed.
(* a sum over 0 .. N-1 of a function zero off a duplicate-free list S of indices below N is its sum over S *)
Lemma acc_zs_support : forall (g : nat -> Z) N (S : list nat), List.NoDup S -> (forall j, In j S -> (j < N)%nat) ->
  (forall j, (j < N)%nat -> ~ In j S -> g j = 0) -> zs (map g (seq 0 N)) = zs (map g S).
Proof.
  intros g N. induction N as [|N IH]; intros S ND HS H0.
  - destruct S as [|j S]; [reflexivity|]. specialize (HS j (or_introl eq_refl)). lia.
  - rewrite seq_S, map_app, acc_zs_app. cbn [map fold_right]. rewrite Nat.add_0_l.
    destruct (in_dec Nat.eq_dec N S) as [Hin|Hin].
    + destruct (in_split N S Hin) as (S1 & S2 & ES). subst S.
      assert (ND' : List.NoDup (S1 ++ S2)) by exact (NoDup_remove_1 _ _ _ ND).
      pose proof (NoDup_remove_2 _ _ _ ND) as NN.
      rewrite (IH (S1 ++ S2) ND').
      * rewrite !map_app, !acc_zs_app. cbn [map fold_right]. lia.
      * intros j Hj. assert (j <> N) by (intros ->; exact (NN Hj)).
        assert (j < S N)%nat by (apply HS; apply in_app_or in Hj as [Hj|Hj]; apply in_or_app; [left|right; right]; exact Hj).
        lia.
      * intros j Hj Hn. apply H0; [lia|]. intros Hj'. apply in_app_or in Hj' as [Hj'|[Hj'|Hj']]; [| lia |];
          apply Hn; apply in_or_app; [left|right]; exact Hj'.
    + rewrite (H0 N ltac:(lia) Hin), (IH S ND).
      * lia.
      * intros j Hj. assert (j <> N) by (intros ->; exact (Hin Hj)). specialize (HS j Hj). lia.
      * intros j Hj Hn. apply H0; [lia | exact Hn].
Qed.
(* ... and over a duplicate-free list of indices below N, of a function not negative, at most its sum over 0 .. N-1 *)
Lemma acc_zs_incl : forall (g : nat -> Z) N (S : list nat), List.NoDup S -> (forall j, In j S -> (j < N)%nat) ->
  (forall j, 0 <= g j) -> zs (map g S) <= zs (map g (seq 0 N)).
Proof.
  intros g N S ND HS Hg.
  set (g' := fun j => if in_dec Nat.eq_dec j S then g j else 0).
  assert (E : zs (map g S) = zs (map g' S)).
  { apply acc_zs_ext. intros x Hx. unfold g'. destruct (in_dec Nat.eq_dec x S); [reflexivity|contradiction]. }
  rewrite E, <- (acc_zs_support g' N S ND HS).
  - apply acc_zs_le. intros x _. unfold g'. destruct (in_dec Nat.eq_dec x S); [lia|]. apply Hg.
  - intros j _ Hn. unfold g'. destruct (in_dec Nat.eq_dec j S); [contradiction|reflexivity].
Qed.

(* ================================================================== relay_instance_gone's relation, entry by entry *)
(* what rig_rel says of a drained entry's source, at its index: the fd, the expected list the drain appended to, the
   held list it kept *)
Lemma acc_rig_rel_nth : forall pre mx ps qs c O cap c2 O2 cap2,
  rig_rel pre mx c O cap ps qs c2 O2 cap2 ->
  length qs = length ps /\
  forall i, (i < length ps)%nat -> re_eof (fst (nth i ps (gn_e0, gn_hj0))) = 0 ->
    let h := fst (snd (nth i ps (gn_e0, gn_hj0))) in let h' := snd (nth i qs gn_q0) in
    hs_fd h' = hs_fd h /\
    map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
    hs_held h' = hs_held h.
Proof.
  intros pre mx ps. induction ps as [|[e [h jj]] ps IH]; intros qs c O cap c2 O2 cap2 HR.
  - destruct qs; [|cbn in HR; contradiction]. split; [reflexivity|]. intros i Hi. cbn in Hi. lia.
  - destruct qs as [|[e' h'] qs]; [cbn in HR; contradiction|].
    cbn [rig_rel] in HR. destruct HR as (e1 & ev & LB & HR). cbv zeta in HR. destruct HR as (Hd & Ee' & Hrest).
    destruct (sl_sends _ _ _ _ _) as [[c3 O3] cap3] in Hrest.
    destruct (IH qs _ _ _ _ _ _ Hrest) as (L & HI).
    split; [cbn; lia|]. intros [|i] Hi Ho; cbn [nth fst snd] in Ho |- *.
    + rewrite (proj2 (Z.eqb_eq _ _) Ho) in Hd. unfold dr_rel in Hd. cbv zeta in Hd.
      destruct Hd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Efd & _ & _ & _ & _ & _ & _ & _ & _ & Eexp & _ &
                      Ehd & _). split; [exact Efd|]. split; [exact Eexp | exact Ehd].
    + apply HI; [cbn in Hi; lia | exact Ho].
Qed.

(* ================================================================== the relational invariant's slot facts *)
Section rinvs.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma acc_forall2_in_r : forall {A B : Type} (R : A -> B -> Prop) l1 l2 y, Forall2 R l1 l2 -> In y l2 ->
  exists x, In x l1 /\ R x y.
Proof.
  intros A B R l1 l2 y H. induction H as [|x y' l1 l2 Hxy _ IH]; intros Hy; [destruct Hy|].
  destruct Hy as [<-|Hy]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH Hy) as (x' & Hx' & Hr). exists x'. split; [right; exact Hx' | exact Hr].
Qed.
(* every open slot is an entry's source: nothing expected, distinct held texts *)
Lemma acc_rinv_slot : forall cx t m j h, fr_RINV cx t m -> nth j (lm_hs m) None = Some h ->
  hl_recs (hs_expected h) = [] /\ NoDup (texts (hs_held h)).
Proof.
  intros cx t m j h (_ & (HL & _ & _ & _ & hj & HF2 & _ & HO & _) & _) Hj.
  assert (Hj4 : (j < 4)%nat).
  { destruct (Nat.lt_ge_cases j (length (lm_hs m))) as [X|X]; [lia|]. rewrite nth_overflow in Hj by exact X.
    discriminate. }
  destruct (SlotInv.slot_open hj j) eqn:So; [|rewrite (HO j Hj4 So) in Hj; discriminate].
  unfold SlotInv.slot_open in So. apply existsb_exists in So as (j' & Hin & Ej). apply Nat.eqb_eq in Ej. subst j'.
  apply in_map_iff in Hin as (p & Ep & Hp).
  destruct (acc_forall2_in_r _ _ _ _ HF2 Hp) as (e & _ & Hok).
  destruct Hok as (_ & Hn & _ & _ & _ & ND & E0 & _). rewrite Ep, Hj in Hn. injection Hn as Eh. subst h.
  split; [exact E0 | exact ND].
Qed.
End rinvs.

(* ================================================================== the table-order loop *)
Section loop.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable P : Z -> bool.
Local Abbreviation za := (za P).
Local Abbreviation net := (ReplyTrPeakW.tr_net_w (fun n => zb (P n))).

Lemma acc_setn_len : forall k (x : option hsrc) l, length (gn_setn k x l) = length l.
Proof. induction k as [|k IH]; intros x [|y l]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma acc_setn_nth : forall k (x : option hsrc) l j, (k < length l)%nat ->
  nth j (gn_setn k x l) None = if Nat.eqb j k then x else nth j l None.
Proof.
  induction k as [|k IH]; intros x [|y l] j Hk; cbn in Hk; try lia.
  - destruct j; reflexivity.
  - destruct j as [|j]; cbn [gn_setn nth Nat.eqb]; [reflexivity|]. apply IH. lia.
Qed.
Lemma acc_za_setn : forall k x (l : list (option hsrc)), (k < length l)%nat ->
  zs (map (fun o => za (slot_blks o)) (gn_setn k (Some x) l)) =
  zs (map (fun o => za (slot_blks o)) l) - za (slot_blks (nth k l None)) + za (asrc_blks x).
Proof.
  induction k as [|k IH]; intros x [|y l] Hk; cbn in Hk; try lia; cbn [gn_setn map fold_right nth].
  - cbn [slot_blks]. lia.
  - rewrite IH by lia. lia.
Qed.
Lemma acc_za_set : forall mc k x, (k < length (lm_hs mc))%nat ->
  za (model_blks (gn_set mc k x)) = za (model_blks mc) - za (slot_blks (nth k (lm_hs mc) None)) + za (asrc_blks x).
Proof.
  intros mc k x Hk. rewrite !za_model. unfold gn_set. cbn [lm_G lm_es lm_hs lm_cap lm_out].
  rewrite (acc_za_setn k x _ Hk). lia.
Qed.
(* the check_no_loss peak each slot of the loop model m1 carries *)
Definition Gs (m1 : lmod) (j : nat) : Z :=
  match nth j (lm_hs m1) None with
  | Some h => tr_peakP P (W_contract_x.cnl_tr (hs_expected h) (hs_held h))
  | None => 0
  end.
Lemma Gs_nonneg : forall m1 j, 0 <= Gs m1 j.
Proof. intros m1 j. unfold Gs. destruct (nth j (lm_hs m1) None); [apply tr_peakP_nonneg | lia]. Qed.
(* one check_no_loss and check_shape_ends on slot k: the model's count moves by at most the slot's peak *)
Lemma acc_call : forall mc k h h' h'' E' H' Pf gone A0 ob ds c,
  (k < length (lm_hs mc))%nat -> nth k (lm_hs mc) None = Some h -> List.NoDup (texts (hs_held h)) ->
  gn_cnl_ok h h' E' H' -> gn_cshe_ok Pf gone A0 ob h' h'' ds c ->
  za (model_blks (gn_set mc k h'')) <= za (model_blks mc) + tr_peakP P (W_contract_x.cnl_tr (hs_expected h) (hs_held h)) /\
  za (model_blks (gn_set mc k h')) <= za (model_blks mc) + tr_peakP P (W_contract_x.cnl_tr (hs_expected h) (hs_held h)).
Proof.
  intros mc k h h' h'' E' H' Pf gone A0 ob ds c Hk Hh ND HC HS.
  pose proof (acc_cnl_src P h h' E' H' HC ND) as E1.
  pose proof (acc_cshe_src P _ _ _ _ _ _ _ _ HS) as E2.
  pose proof (net_le_peak P _ (W_contract_x.cnl_tr (hs_expected h) (hs_held h))) as E3.
  rewrite !acc_za_set by exact Hk. rewrite Hh. cbn [slot_blks]. split; lia.
Qed.
(* a call's slot was not called before: its fd is entry i's, and a slot called for entry i' < i has entry i''s fd *)
Definition loop_inv (m1 mc : lmod) (i k : nat) (S : list nat) : Prop :=
  List.NoDup S /\ (forall j, In j S -> (j < 4)%nat) /\
  (forall j, ~ In j S -> nth j (lm_hs mc) None = nth j (lm_hs m1) None) /\
  (forall j, In j S -> exists i' h1, ((i' < i)%nat \/ (i' = i /\ (j < k)%nat)) /\ (i' < length (lm_es m1))%nat /\
     nth j (lm_hs m1) None = Some h1 /\ hs_fd h1 = re_fd (nth i' (lm_es m1) gn_e0)) /\
  (forall j hc, nth j (lm_hs mc) None = Some hc -> exists h1, nth j (lm_hs m1) None = Some h1 /\ hs_fd hc = hs_fd h1) /\
  length (lm_hs mc) = 4%nat /\
  za (model_blks mc) <= za (model_blks m1) + zs (map (Gs m1) S).
Lemma acc_fresh : forall m1 mc i k S h, List.NoDup (map re_fd (lm_es m1)) -> loop_inv m1 mc i k S ->
  (i < length (lm_es m1))%nat -> nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  ~ In k S /\ nth k (lm_hs m1) None = Some h.
Proof.
  intros m1 mc i k S h ND (_ & _ & HU & HO & HF & _) Hi Hh Hfd.
  assert (NI : ~ In k S).
  { intros Hin. destruct (HO k Hin) as (i' & h1 & Hord & Hi' & E1 & F1).
    destruct (HF k h Hh) as (h2 & E2 & F2). rewrite E1 in E2. injection E2 as <-.
    assert (EF : nth i' (map re_fd (lm_es m1)) (re_fd gn_e0) = nth i (map re_fd (lm_es m1)) (re_fd gn_e0)).
    { rewrite !map_nth. congruence. }
    apply (proj1 (NoDup_nth (map re_fd (lm_es m1)) (re_fd gn_e0)) ND i' i) in EF;
      [|rewrite length_map; lia|rewrite length_map; lia].
    lia. }
  split; [exact NI|]. rewrite <- (HU k NI). exact Hh.
Qed.
Lemma acc_loop : forall Pf m1, List.NoDup (map re_fd (lm_es m1)) ->
  (forall j h1, nth j (lm_hs m1) None = Some h1 -> List.NoDup (texts (hs_held h1))) ->
  length (lm_hs m1) = 4%nat ->
  forall mc A i k, gn_run Pf m1 mc A i k -> exists S, loop_inv m1 mc i k S.
Proof.
  intros Pf m1 ND NDH L4 mc A i k R.
  induction R as [|mc A i k R IH Hk Hs|mc A i k h h' h'' E' H' ds c R IH Hk Hi Hh Hfd HC HS|mc A i R IH].
  - exists []. unfold loop_inv. split; [constructor|]. split; [intros j []|]. split; [intros j _; reflexivity|].
    split; [intros j []|]. split; [intros j hc Hj; exists hc; split; [exact Hj | reflexivity]|].
    split; [exact L4|]. cbn. lia.
  - destruct IH as (S & ND1 & S4 & HU & HO & HF & HL & HZ). exists S. unfold loop_inv.
    split; [exact ND1|]. split; [exact S4|]. split; [exact HU|].
    split; [intros j Hj; destruct (HO j Hj) as (i' & h1 & Hord & X); exists i', h1; split; [lia | exact X]|].
    split; [exact HF|]. split; [exact HL | exact HZ].
  - destruct IH as (S & ND1 & S4 & HU & HO & HF & HL & HZ).
    destruct (acc_fresh m1 mc i k S h ND (conj ND1 (conj S4 (conj HU (conj HO (conj HF (conj HL HZ))))))
                Hi Hh Hfd) as (NI & Hh1).
    assert (Hk' : (k < length (lm_hs mc))%nat) by lia.
    destruct (acc_call mc k h h' h'' E' H' _ _ _ _ ds c Hk' Hh (NDH k h Hh1) HC HS) as (C1 & _).
    exists (k :: S). unfold loop_inv. unfold gn_set at 1 2 3. cbn [lm_hs].
    split; [constructor; [exact NI | exact ND1]|].
    split; [intros j [<-|Hj]; [exact Hk | exact (S4 j Hj)]|].
    split.
    { intros j Hj. rewrite (acc_setn_nth k _ _ j Hk'). destruct (Nat.eqb_spec j k) as [->|N]; [exfalso; apply Hj; left; reflexivity|].
      apply HU. intros X. apply Hj. right. exact X. }
    split.
    { intros j [<-|Hj].
      - exists i, h. split; [right; split; [reflexivity|lia]|]. split; [exact Hi|]. split; [exact Hh1 | exact Hfd].
      - destruct (HO j Hj) as (i' & h1 & Hord & X). exists i', h1. split; [lia | exact X]. }
    split.
    { intros j hc Hj. rewrite (acc_setn_nth k _ _ j Hk') in Hj. destruct (Nat.eqb_spec j k) as [->|N].
      - injection Hj as <-. exists h. split; [exact Hh1|].
        destruct HC as (-> & _). destruct HS as (H2 & -> & _). reflexivity.
      - exact (HF j hc Hj). }
    split; [rewrite acc_setn_len; exact HL|].
    cbn [map fold_right]. unfold Gs at 1. rewrite Hh1. lia.
  - destruct IH as (S & ND1 & S4 & HU & HO & HF & HL & HZ). exists S. unfold loop_inv.
    split; [exact ND1|]. split; [exact S4|]. split; [exact HU|].
    split; [intros j Hj; destruct (HO j Hj) as (i' & h1 & Hord & X); exists i', h1; split; [lia | exact X]|].
    split; [exact HF|]. split; [exact HL | exact HZ].
Qed.
End loop.

(* ================================================================== the model relay_instance_gone leaves *)
Section mrig.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable P : Z -> bool.
Local Abbreviation za := (za P).
Local Abbreviation tz := (tz P).

Lemma acc_adelta_sum : forall ps qs, length ps = length qs ->
  zs (map (fun pq => adelta P (fst pq) (snd pq)) (combine ps qs)) =
  zs (map (fun q => za (aentry_blks (fst q))) qs) - zs (map (fun p => za (aentry_blks (fst p))) ps) +
  zs (map (fun pq => if re_eof (fst (fst pq)) =? 0 then za (asrc_blks (snd (snd pq))) - za (asrc_blks (fst (snd (fst pq))))
                     else 0) (combine ps qs)).
Proof.
  induction ps as [|p ps IH]; intros [|q qs] E; cbn in E; try lia; [reflexivity|].
  cbn [combine map fold_right fst snd]. rewrite IH by lia. unfold adelta. cbn [fst snd]. lia.
Qed.
Lemma acc_zs_nat : forall {A : Type} (f : A -> nat) l, zs (map (fun x => Z.of_nat (f x)) l) = Z.of_nat (fold_right Nat.add 0%nat (map f l)).
Proof. intros A f l. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. lia. Qed.

(* each drained entry: its slot held its source before, holds the drained source after, with the fd, the expected
   texts the drain appended and the held list kept *)
Lemma acc_rig_slot_facts : forall cx m hs qs c2 O2 cap2 out2 m1,
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  forall pq, In pq (combine (combine (lm_es m) hs) qs) -> re_eof (fst (fst pq)) = 0 ->
    (snd (snd (fst pq)) < 4)%nat /\
    nth (snd (snd (fst pq))) (lm_hs m) None = Some (fst (snd (fst pq))) /\
    nth (snd (snd (fst pq))) (lm_hs m1) None = Some (snd (snd pq)) /\
    hs_fd (snd (snd pq)) = hs_fd (fst (snd (fst pq))) /\
    map snd (hl_recs (hs_expected (snd (snd pq)))) =
      map snd (hl_recs (hs_expected (fst (snd (fst pq))))) ++ map (map (Z_to_bv 8)) (dr_lines (fst (snd (fst pq)))) /\
    hs_held (snd (snd pq)) = hs_held (fst (snd (fst pq))).
Proof.
  intros cx m hs qs c2 O2 cap2 out2 m1 (HLh & HFp & _) HAR (HRR & HLq & _).
  destruct HAR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdr).
  destruct (acc_rig_rel_nth _ _ _ _ _ _ _ _ _ _ HRR) as (Lq & HI).
  assert (Lc : length (combine (lm_es m) hs) = length (lm_es m)) by (rewrite length_combine; lia).
  intros pq Hpq. revert Hpq.
  apply (acc_forall_combine (fun p q => re_eof (fst p) = 0 ->
    (snd (snd p) < 4)%nat /\ nth (snd (snd p)) (lm_hs m) None = Some (fst (snd p)) /\
    nth (snd (snd p)) (lm_hs m1) None = Some (snd q) /\ hs_fd (snd q) = hs_fd (fst (snd p)) /\
    map snd (hl_recs (hs_expected (snd q))) =
      map snd (hl_recs (hs_expected (fst (snd p)))) ++ map (map (Z_to_bv 8)) (dr_lines (fst (snd p))) /\
    hs_held (snd q) = hs_held (fst (snd p))) (combine (lm_es m) hs) qs (gn_e0, gn_hj0) gn_q0 ltac:(lia)).
  intros i Hi Ho. rewrite Lc in Hi.
  assert (Hin : In (nth i (combine (lm_es m) hs) (gn_e0, gn_hj0)) (combine (lm_es m) hs)) by (apply nth_In; lia).
  rewrite Forall_forall in HFp. destruct (HFp _ Hin Ho) as (S4 & Hn & _).
  destruct (HI i ltac:(lia) Ho) as (F1 & F2 & F3). cbv zeta in F1, F2, F3.
  rewrite combine_nth in Ho, S4, Hn, F1, F2, F3 |- * by lia. cbn [fst snd] in *.
  split; [exact S4|]. split; [exact Hn|]. split; [exact (Hdr i Hi Ho)|]. split; [exact F1|]. split; [exact F2 | exact F3].
Qed.
Lemma acc_rig_slots_lt : forall m hs, gn_pairs m hs -> forall j, In j (rig_slots (combine (lm_es m) hs)) -> (j < 4)%nat.
Proof.
  intros m hs (_ & HFp & _) j Hj. unfold rig_slots in Hj. apply in_concat in Hj as (l & Hl & Hj).
  apply in_map_iff in Hl as (p & <- & Hp). destruct (re_eof (fst p) =? 0) eqn:Eo; [|destruct Hj].
  destruct Hj as [<-|[]]. rewrite Forall_forall in HFp. apply Z.eqb_eq in Eo. exact (proj1 (HFp p Hp Eo)).
Qed.
(* an index of rig_slots is a drained entry's slot *)
Lemma acc_rig_slots_in : forall ps (qs : list (rentry * hsrc)) j, length ps = length qs ->
  In j (rig_slots ps) -> exists pq, In pq (combine ps qs) /\ re_eof (fst (fst pq)) = 0 /\ snd (snd (fst pq)) = j.
Proof.
  intros ps qs j L Hj. unfold rig_slots in Hj. apply in_concat in Hj as (l & Hl & Hj).
  apply in_map_iff in Hl as (p & <- & Hp). destruct (re_eof (fst p) =? 0) eqn:Eo; [|destruct Hj].
  destruct Hj as [<-|[]]. apply In_nth with (d := (gn_e0, gn_hj0)) in Hp as (i & Hi & Ep).
  exists (p, nth i qs gn_q0). split; [|split; [apply Z.eqb_eq; exact Eo | reflexivity]].
  rewrite <- Ep. rewrite <- combine_nth by exact L. apply nth_In. rewrite length_combine. lia.
Qed.

(* the model's count after relay_instance_gone: the entries' and drained sources' changes, and g_out's *)
Lemma acc_model_rig : forall cx t m hs qs c2 O2 cap2 out2 m1,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  za (model_blks m1) = za (model_blks m) +
    zs (map (fun pq => adelta P (fst pq) (snd pq)) (combine (combine (lm_es m) hs) qs)) + tz cap2 - tz (lm_cap m).
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 HRI HPA HAR HRO.
  pose proof HRI as (_ & (HL0 & _) & _).
  pose proof HPA as (HLh & HFp & HNd).
  pose proof HRO as (HRR & HLq & _).
  pose proof (acc_rig_slot_facts cx m hs qs c2 O2 cap2 out2 m1 HPA HAR HRO) as SF.
  pose proof HAR as (_ & EG & Ees & _ & _ & _ & Ecap & Eout & _ & _ & HL1 & Hun & _).
  assert (Lps : length (combine (lm_es m) hs) = length (lm_es m)) by (rewrite length_combine; lia).
  rewrite !za_model, Ees, Ecap, !acc_za_out.
  rewrite (acc_adelta_sum (combine (lm_es m) hs) qs ltac:(lia)).
  assert (EA : zs (map (fun p => za (aentry_blks (fst p))) (combine (lm_es m) hs)) =
               zs (map (fun e => za (aentry_blks e)) (lm_es m)))
    by exact (acc_zs_combine_l (fun e => za (aentry_blks e)) (lm_es m) hs ltac:(lia)).
  assert (EQ : zs (map (fun e => za (aentry_blks e)) (map fst qs)) = zs (map (fun q => za (aentry_blks (fst q))) qs))
    by (rewrite map_map; reflexivity).
  rewrite EA, EQ.
  set (sf := fun o : option hsrc => za (slot_blks o)).
  set (g := fun j => sf (nth j (lm_hs m1) None) - sf (nth j (lm_hs m) None)).
  assert (E1a : zs (map (fun j => sf (nth j (lm_hs m1) None)) (seq 0 4)) = zs (map sf (lm_hs m1)))
    by (rewrite <- HL1; apply lsc_seq_sum).
  assert (E1b : zs (map (fun j => sf (nth j (lm_hs m) None)) (seq 0 4)) = zs (map sf (lm_hs m)))
    by (rewrite <- HL0; apply lsc_seq_sum).
  assert (E1 : zs (map sf (lm_hs m1)) - zs (map sf (lm_hs m)) = zs (map g (seq 0 4))).
  { rewrite <- E1a, <- E1b. symmetry.
    exact (acc_zs_sub (fun j => sf (nth j (lm_hs m1) None)) (fun j => sf (nth j (lm_hs m) None)) (seq 0 4)). }
  assert (ND : List.NoDup (rig_slots (combine (lm_es m) hs))) by (apply NoDup_ListNoDup; exact HNd).
  assert (E2 : zs (map g (seq 0 4)) = zs (map g (rig_slots (combine (lm_es m) hs)))).
  { apply (acc_zs_support g 4 _ ND (acc_rig_slots_lt m hs HPA)). intros j Hj Hn. unfold g. rewrite (Hun j Hj Hn). lia. }
  assert (E3 : zs (map g (rig_slots (combine (lm_es m) hs))) =
               zs (map (fun p => if re_eof (fst p) =? 0 then g (snd (snd p)) else 0) (combine (lm_es m) hs)))
    by exact (eq_sym (lsc_slots_sum g (combine (lm_es m) hs))).
  assert (E4 : zs (map (fun p => if re_eof (fst p) =? 0 then g (snd (snd p)) else 0) (combine (lm_es m) hs)) =
    zs (map (fun pq => if re_eof (fst (fst pq)) =? 0 then g (snd (snd (fst pq))) else 0) (combine (combine (lm_es m) hs) qs)))
    by exact (eq_sym (acc_zs_combine_l (fun p => if re_eof (fst p) =? 0 then g (snd (snd p)) else 0)
                        (combine (lm_es m) hs) qs ltac:(lia))).
  assert (E5 : zs (map (fun pq => if re_eof (fst (fst pq)) =? 0 then g (snd (snd (fst pq))) else 0)
                     (combine (combine (lm_es m) hs) qs)) =
    zs (map (fun pq => if re_eof (fst (fst pq)) =? 0 then za (asrc_blks (snd (snd pq))) - za (asrc_blks (fst (snd (fst pq))))
                       else 0) (combine (combine (lm_es m) hs) qs))).
  { apply acc_zs_ext. intros pq Hpq. destruct (re_eof (fst (fst pq)) =? 0) eqn:Eo; [|reflexivity].
    apply Z.eqb_eq in Eo. destruct (SF pq Hpq Eo) as (_ & E0 & E1' & _). unfold g, sf. rewrite E0, E1'. reflexivity. }
  rewrite E2, E3, E4, E5 in E1. unfold sf in *. lia.
Qed.

(* the loop model's check_no_loss peaks, summed over the four slots, are the gn_cnl sum of pk_gone *)
Lemma acc_Gs_sum : forall cx t m hs qs c2 O2 cap2 out2 m1,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  zs (map (Gs P m1) (seq 0 4)) = Z.of_nat (fold_right Nat.add 0%nat (map (gn_cnl P) (combine (lm_es m) hs))).
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 HRI HPA HAR HRO.
  pose proof HPA as (HLh & HFp & HNd). pose proof HRO as (HRR & HLq & _).
  pose proof (acc_rig_slot_facts cx m hs qs c2 O2 cap2 out2 m1 HPA HAR HRO) as SF.
  pose proof HAR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL1 & Hun & _).
  assert (Lps : length (combine (lm_es m) hs) = length (lm_es m)) by (rewrite length_combine; lia).
  assert (ND : List.NoDup (rig_slots (combine (lm_es m) hs))) by (apply NoDup_ListNoDup; exact HNd).
  assert (E2 : zs (map (Gs P m1) (seq 0 4)) = zs (map (Gs P m1) (rig_slots (combine (lm_es m) hs)))).
  { apply (acc_zs_support (Gs P m1) 4 _ ND (acc_rig_slots_lt m hs HPA)). intros j Hj Hn. unfold Gs.
    rewrite (Hun j Hj Hn). destruct (nth j (lm_hs m) None) as [h0|] eqn:Eh; [|reflexivity].
    destruct (acc_rinv_slot cx t m _ _ HRI Eh) as (X0 & _). unfold W_contract_x.cnl_tr. rewrite X0. reflexivity. }
  assert (E3 : zs (map (Gs P m1) (rig_slots (combine (lm_es m) hs))) =
               zs (map (fun p => if re_eof (fst p) =? 0 then Gs P m1 (snd (snd p)) else 0) (combine (lm_es m) hs)))
    by exact (eq_sym (lsc_slots_sum (Gs P m1) (combine (lm_es m) hs))).
  assert (E4 : zs (map (fun p => if re_eof (fst p) =? 0 then Gs P m1 (snd (snd p)) else 0) (combine (lm_es m) hs)) =
    zs (map (fun pq => if re_eof (fst (fst pq)) =? 0 then Gs P m1 (snd (snd (fst pq))) else 0)
          (combine (combine (lm_es m) hs) qs)))
    by exact (eq_sym (acc_zs_combine_l (fun p => if re_eof (fst p) =? 0 then Gs P m1 (snd (snd p)) else 0)
                        (combine (lm_es m) hs) qs ltac:(lia))).
  assert (E5 : Z.of_nat (fold_right Nat.add 0%nat (map (gn_cnl P) (combine (lm_es m) hs))) =
    zs (map (fun pq => Z.of_nat (gn_cnl P (fst pq))) (combine (combine (lm_es m) hs) qs))).
  { rewrite <- acc_zs_nat.
    exact (eq_sym (acc_zs_combine_l (fun p => Z.of_nat (gn_cnl P p)) (combine (lm_es m) hs) qs ltac:(lia))). }
  rewrite E2, E3, E4, E5. apply acc_zs_ext. intros pq Hpq. destruct (re_eof (fst (fst pq)) =? 0) eqn:Eo.
  - apply Z.eqb_eq in Eo. destruct (SF pq Hpq Eo) as (_ & E0 & E1 & _ & Ex & Eh).
    unfold Gs. rewrite E1.
    destruct (acc_rinv_slot cx t m _ _ HRI E0) as (X0 & _).
    rewrite <- (ReplyLScntRP.lsc_gn_cnl_open (fst pq) (snd (snd pq)) P Eo X0 Ex Eh).
    rewrite Z2Nat.id by apply tr_peakP_nonneg. reflexivity.
  - unfold gn_cnl. rewrite Eo. reflexivity.
Qed.

(* every source in the loop model holds distinct texts *)
Lemma acc_m1_held : forall cx t m hs qs c2 O2 cap2 out2 m1,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  forall j h1, nth j (lm_hs m1) None = Some h1 -> List.NoDup (texts (hs_held h1)).
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 HRI HPA HAR HRO j h1 Hj.
  pose proof HPA as (HLh & _ & _). pose proof HRO as (_ & HLq & _).
  pose proof (acc_rig_slot_facts cx m hs qs c2 O2 cap2 out2 m1 HPA HAR HRO) as SF.
  pose proof HAR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL1 & Hun & _).
  assert (Hj4 : (j < 4)%nat).
  { destruct (Nat.lt_ge_cases j 4) as [X|X]; [exact X|]. rewrite nth_overflow in Hj by lia. discriminate. }
  destruct (in_dec Nat.eq_dec j (rig_slots (combine (lm_es m) hs))) as [Hin|Hin].
  - destruct (acc_rig_slots_in (combine (lm_es m) hs) qs j ltac:(rewrite length_combine; lia) Hin)
      as (pq & Hpq & Eo & Ej).
    destruct (SF pq Hpq Eo) as (_ & E0 & E1 & _ & _ & Eh). rewrite Ej in E0, E1. rewrite E1 in Hj.
    injection Hj as <-. rewrite Eh. apply NoDup_ListNoDup. exact (proj2 (acc_rinv_slot cx t m _ _ HRI E0)).
  - rewrite (Hun j Hj4 Hin) in Hj. apply NoDup_ListNoDup. exact (proj2 (acc_rinv_slot cx t m _ _ HRI Hj)).
Qed.
End mrig.

(* ################################################################## the C1 + C2 text proved at pk_gone *)
Section final.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma gcnt_step : W_LLVMFuzzerTestOneInput_gone_base.GN_CNT_step fr_RINV pk_gone gn_cnl_pk_x.
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 mc A i k h P HRI HOP R1 R2 R3 R4 R5 HPA HAR HRO HC2 RUN Hi Hk Hh Hfd R6.
  pose proof HRI as (_ & (HL0 & _ & _ & HEOK & _) & _).
  pose proof HPA as (HLh & HFp & HNd). pose proof HRO as (HRR & HLq & _ & HNdq).
  pose proof HAR as (_ & _ & Ees & _ & _ & _ & _ & _ & _ & _ & HL1 & _ & _).
  set (ps := combine (lm_es m) hs) in *.
  assert (Lps : length ps = length (lm_es m)) by (unfold ps; rewrite length_combine; lia).
  (* relay_instance_gone: the model's change is at most its trace's net, up to g_out's two ends *)
  assert (FPF : Forall rig_pf ps).
  { apply Forall_forall. intros p Hp. unfold rig_pf. intros Eo.
    pose proof (in_combine_l _ _ _ _ (eq_ind _ (fun x => In x _) Hp _ (surjective_pairing p))) as He.
    rewrite Forall_forall in HFp, R1, R3, HEOK.
    destruct (HFp p Hp Eo) as (_ & Hn & _ & Hsk & HW & _).
    destruct (R1 _ He) as (UZ & _). destruct (R3 _ He) as (UL & UC & _). destruct (HEOK _ He) as (_ & _ & _ & _ & SK).
    assert (Hin : In (Some (fst (snd p))) (lm_hs m)) by (rewrite <- Hn; apply nth_In;
      destruct (Nat.lt_ge_cases (snd (snd p)) (length (lm_hs m))) as [X|X]; [exact X|];
      rewrite nth_overflow in Hn by exact X; discriminate).
    rewrite Forall_forall in R4. destruct (R4 _ Hin) as (PD & PF).
    destruct (acc_rinv_slot cx t m _ _ HRI Hn) as (X0 & _).
    unfold APARTIAL in UL.
    split; [exact SK|]. split; [exact Hsk|]. split; [exact HW|]. split; [exact UL|]. split; [exact UZ|].
    split; [lia|]. split; [exact PD|]. split; [exact PF | exact X0]. }
  assert (FHK : Forall (fun p => rig_hk (fst p)) ps).
  { apply Forall_forall. intros p Hp.
    pose proof (in_combine_l _ _ _ _ (eq_ind _ (fun x => In x _) Hp _ (surjective_pairing p))) as He.
    rewrite Forall_forall in R3. destruct (R3 _ He) as (_ & _ & [X|(X1 & _ & X3)]); [left; exact X|right; split; assumption]. }
  assert (FHQ : Forall (fun q => rig_hk (fst q)) qs).
  { apply Forall_forall. intros q Hq. rewrite Forall_forall in HC2.
    destruct (HC2 (fst q) (in_map fst qs q Hq)) as [X|(X1 & _ & X3)]; [left; exact X|right; split; assumption]. }
  set (lv := sl_live (lm_c m) 1).
  set (a0 := drain_b_c.da_out drain_b_c.dadr0).
  pose proof (acc_rig_run P (relay_instance_gone_b_c.instance_prefix (gn_id cx m)) (lm_mx m) ps qs (lm_c m) (lm_O m)
                (lm_cap m) c2 O2 cap2 lv (Z.of_nat (length (lm_O m))) (lm_cap m) (fun _ => a0) 0 a0 HRR FPF FHK FHQ R2)
    as RG.
  set (capT := snd (fst (fst (relay_instance_gone_b_c.gone_run lv (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                 (relay_instance_gone_b_c.instance_prefix (gn_id cx m)) ps (fun _ => a0) 0 a0)))) in RG.
  assert (ERT : fst (fst (fst (relay_instance_gone_b_c.gone_run lv (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                 (relay_instance_gone_b_c.instance_prefix (gn_id cx m)) ps (fun _ => a0) 0 a0))) =
                rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs)
    by reflexivity.
  rewrite ERT in RG.
  pose proof (net_le_peak P _ (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs))
    as NP.
  pose proof (acc_model_rig P cx t m hs qs c2 O2 cap2 out2 m1 HRI HPA HAR HRO) as MR.
  pose proof (tz_range P cap2). pose proof (tz_range P capT).
  (* the loop *)
  assert (NDF : List.NoDup (map re_fd (lm_es m1))) by (rewrite Ees; apply NoDup_ListNoDup; exact HNdq).
  destruct (acc_loop P _ m1 NDF (acc_m1_held cx t m hs qs c2 O2 cap2 out2 m1 HRI HPA HAR HRO) HL1 mc A i k RUN)
    as (S & INV).
  destruct (acc_fresh P m1 mc i k S h NDF INV Hi Hh Hfd) as (NI & Hh1).
  pose proof INV as (NDS & S4 & _ & _ & _ & HLc & HZ).
  assert (GK : Gs P m1 k = tr_peakP P (W_contract_x.cnl_tr (hs_expected h) (hs_held h))) by (unfold Gs; rewrite Hh1; reflexivity).
  assert (SUM : zs (map (Gs P m1) (k :: S)) <= zs (map (Gs P m1) (seq 0 4))).
  { apply acc_zs_incl; [constructor; [exact NI | exact NDS] | | apply Gs_nonneg].
    intros j [<-|Hj]; [exact Hk | exact (S4 j Hj)]. }
  rewrite (acc_Gs_sum P cx t m hs qs c2 O2 cap2 out2 m1 HRI HPA HAR HRO) in SUM. cbn [map fold_right] in SUM.
  assert (EPK : Z.of_nat (pk_gone cx m hs P) =
    tr_peakP P (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) +
    Z.of_nat (fold_right Nat.add 0%nat (map (gn_cnl P) (combine (lm_es m) hs))) + 3).
  { unfold pk_gone. rewrite !Nat2Z.inj_add, Z2Nat.id by apply tr_peakP_nonneg. reflexivity. }
  pose proof (tr_peakP_nonneg _ P (W_contract_x.cnl_tr (hs_expected h) (hs_held h))) as PK0.
  assert (Hk' : (k < length (lm_hs mc))%nat) by lia.
  split.
  - apply Nat2Z.inj_le. rewrite !Nat2Z.inj_add, EPK. unfold gn_cnl_pk_x, W_contract_x.cnl_pk.
    rewrite Nat2Z.inj_add, Z2Nat.id by exact PK0.
    change (Z.of_nat (acnt P (model_blks mc))) with (za P (model_blks mc)).
    change (Z.of_nat (acnt P (model_blks m))) with (za P (model_blks m)).
    unfold ps in *. lia.
  - intros h' E' H' HC.
    pose proof (acc_cnl_src P h h' E' H' HC (acc_m1_held cx t m hs qs c2 O2 cap2 out2 m1 HRI HPA HAR HRO k h Hh1))
      as E1.
    pose proof (net_le_peak P _ (W_contract_x.cnl_tr (hs_expected h) (hs_held h))) as E3.
    pose proof (acc_za_set P mc k h' Hk') as E4. rewrite Hh in E4. cbn [slot_blks] in E4.
    apply Nat2Z.inj_le. rewrite !Nat2Z.inj_add, EPK.
    change (Z.of_nat (acnt P (model_blks (gn_set mc k h')))) with (za P (model_blks (gn_set mc k h'))).
    change (Z.of_nat (acnt P (model_blks m))) with (za P (model_blks m)).
    unfold ps in *. cbn [Z.of_nat]. lia.
Qed.
End final.

(* ================================================================== the gone rp_cnt rows from GN_CNT_step's conclusion *)
(* ReplyLScntRP.v's rp_cnt_gone_cnl :397 / rp_cnt_gone_later :418 take, at a loop call (lyx, Sx), the astate growth
   acnt (ablocks Sx) + (the call's own peak) <= acnt (ablocks S) + rig's peak + the gn_cnl sum, 1 (cnl) and 3 (cshe)
   STRONGER than what lsc_rp_mono needs.  These two take instead GN_CNT_step's conclusion (pure model, at the call's
   model mc) and the walk's gn_tie, and give the same cnt_ok_pk; no inequality is proved twice. *)
Section ofstep.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable RP : W_journal_x.roomp.
Hypothesis RP_CNT : W_journal_x.rp_Psec RP = ReplyCnt.Psec /\ W_journal_x.rp_P24 RP = ReplyCnt.P24 /\
  W_journal_x.rp_Lsec RP = ReplyCnt.Lsec /\ W_journal_x.rp_L24 RP = ReplyCnt.L24 /\
  W_journal_x.rp_Pcls RP = ReplyCnt.Pcls /\ W_journal_x.rp_LPRIM RP = ReplyCnt.LPRIM.
Lemma gcnt_tie : forall cx m mc ly S lyx Sx (P : Z -> bool) (X Y : nat),
  (exists rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest)) ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (acnt P (model_blks mc) + X <= acnt P (model_blks m) + Y)%nat ->
  (acnt P (ablocks B lyx Sx) + X <= acnt P (ablocks B ly S) + Y)%nat.
Proof.
  intros cx m mc ly S lyx Sx P X Y (rest & HS) HT HM. pose proof (HT rest HS) as HX.
  rewrite (acnt_perm P _ _ HS), (acnt_perm P _ _ HX), !acnt_app. lia.
Qed.
Lemma rp_cnt_gone_cnl_of_step : forall cx t m ly S hs mc h (lyx : alayout) (Sx : astate),
  ReplyLS3p.fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall k h0, nth k (lm_hs m) None = Some h0 ->
     (hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
     (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) ->
  (exists rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest)) ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (forall P, (ReplyCnt.acnt P (model_blks mc) + W_contract_x.cnl_pk (hs_expected h) (hs_held h) P
     <= ReplyCnt.acnt P (model_blks m) + pk_gone cx m hs P)%nat) ->
  W_journal_x.cnt_ok_pk RP (W_contract_x.cnl_pk (hs_expected h) (hs_held h)) (ablocks B lyx Sx).
Proof.
  intros cx t m ly S hs mc h lyx Sx HLS HRI Hgp Hm Ht HU Hpos Hoff Hsep HT HG.
  apply (ReplyLScntRP.lsc_rp_mono RP RP_CNT (pk_gone cx m hs) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_gone B cx t m ly S hs HLS HRI Hgp Hm Ht HU Hpos Hoff).
  - intros P. exact (gcnt_tie cx m mc ly S lyx Sx P _ _ Hsep HT (HG P)).
Qed.
Lemma rp_cnt_gone_later_of_step : forall cx t m ly S hs mc (lyx : alayout) (Sx : astate),
  ReplyLS3p.fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall k h0, nth k (lm_hs m) None = Some h0 ->
     (hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
     (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) ->
  (exists rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest)) ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (forall P, (ReplyCnt.acnt P (model_blks mc) + W_contract_x.cshe_pk P
     <= ReplyCnt.acnt P (model_blks m) + pk_gone cx m hs P)%nat) ->
  W_journal_x.cnt_ok_pk RP W_contract_x.cshe_pk (ablocks B lyx Sx).
Proof.
  intros cx t m ly S hs mc lyx Sx HLS HRI Hgp Hm Ht HU Hpos Hoff Hsep HT HG.
  apply (ReplyLScntRP.lsc_rp_mono RP RP_CNT (pk_gone cx m hs) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_gone B cx t m ly S hs HLS HRI Hgp Hm Ht HU Hpos Hoff).
  - intros P. exact (gcnt_tie cx m mc ly S lyx Sx P _ _ Hsep HT (HG P)).
Qed.
End ofstep.
