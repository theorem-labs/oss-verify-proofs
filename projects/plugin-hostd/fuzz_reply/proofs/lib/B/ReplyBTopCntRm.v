(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: arm 4 (op_remove) of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput, in
   the form of the cgif walks (lib/A/ACf5.v rt_from segments) over the cut invariants of
   W_LLVMFuzzerTestOneInput_cut.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_remove.v, with its module names changed; 321 of its 391 lines of code are new or changed and 5205 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyCntArms.v, with its module paths and module names changed; 80 of its 293 lines of code are new or changed and 178 lines of the source are left out. *)
(* The remove arm's three count rules on image B, each at the text of lib/B/ReplyBTop.v's Context of the same name
   (RM_CNT_cnl, RM_CNT_cshe, RM_CNT_sr: the Section hypotheses of lib/B/W_LLVMFuzzerTestOneInput_remove_x.v :316 /
   :310 / :315 at the composition's instance), for every rc, fx:
   - btcnt_RM_CNT_cnl: check_no_loss's count premise at the state relay_remove leaves;
   - btcnt_RM_CNT_cshe: check_shape_ends' count premise at the state check_no_loss leaves;
   - btcnt_RM_CNT_sr: source_reset's count premise at the state check_shape_ends leaves.
   proves no function (kind: invariant lemma).
   The proof is image A's lib/A/ReplyCntArms.v cnt_rm_rr / cnt_rm_cnl_src / cnt_rm_cnl_pk / cnt_rm_cnl /
   cnt_rm_after_cnl / cnt_rm_cshe / cnt_rm_sr with its helpers rmc_zs_perm / rmc_zs_set / rmc_peak_app /
   rmc_za_mk, over B's twins: the accounting lib/B/ReplyB3CntAcc.v (A's ReplyCntAcc.v), lsc_net_le_peak /
   lsc_cnl_W8 / lsc_cnl_W8_empty of lib/B/ReplyB3LScntRP.v (A's ReplyLScntRP.v), rrp_find of
   lib/B/ReplyLSBDrainPre.v (A's rmc_find).  The model texts A's proof reads (W_contract.v dr_rel / rr_tr / dr_fin /
   dr_tr / dr_live / dr_lines, _remove.v rm_rr_ok / rm_cnl_ok / rm_cshe_ok / rm_mfacts / rm_mk / rm_at, _remove_x.v
   rm_pk / rm_cnl_pk / rm3_pre, W_contract_x.v cnl_tr / cnl_pk / cshe_pk / sr_pk) are B's word for word.
   A's two family arguments are read off fr_RINV here: RI_rm_rr_pair's fact (the removed entry's skip and partial
   line against the source) and the held texts' NoDup are clauses of fr_pair_ok (lib/B/ReplyRINVB.v:140) of the
   pair ReplyLSBDrainPre.rm3_pair gives; relay_remove keeps the held list, so the NoDup holds after it. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF ListTr HarnessTr drain_b_c relay_remove_b_c relay_instance_gone_b_lem SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyTrPeakW ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3CntAcc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_remove_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyRINVB ReplyLSBDrainPre ReplyB3LScntRP.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module RX := W_LLVMFuzzerTestOneInput_remove_x.
Module GC := ReplyB3CntAcc.

(* Speed (image A's ReplyCntArms.v:71-75): at Qed the kernel's conversion of lia's certificate should unfold lia's
   checker before these model functions, the arithmetic's atoms; A measured cnt_rm_rr's Qed at 215 s without it,
   1.6 s with it.  Local keeps it out of importers. *)
Local Strategy 1000 [drain_b_c.drain_run dr_fin dr_tr ReplyCnt.tr_peakP GC.tz GC.ws GC.za rr_tr rm_rr_tr].

(* A's ReplyCntAcc.v za_nonneg / ws_nonneg, which B's ReplyB3CntAcc.v does not carry *)
Lemma btcnt_za_nonneg : forall (P : Z -> bool) l, 0 <= GC.za P l.
Proof. intros P l. unfold GC.za. lia. Qed.
Lemma btcnt_ws_nonneg : forall (P : Z -> bool) T, 0 <= GC.ws P T.
Proof.
  intros P T. induction T as [|x T IH]; [cbn; lia|]. rewrite GC.ws_cons.
  first [ pose proof (GC.zb_range (P (Z.of_nat (length x) + 1)))
        | pose proof (GC.zb_range P (P (Z.of_nat (length x) + 1))) ].
  lia.
Qed.

Local Abbreviation zs := (fold_right Z.add 0).

(* A's ReplyCntArms.v rmc_zs_perm / rmc_zs_set / rmc_peak_app *)
Lemma btcnt_zs_perm : forall {A : Type} (f : A -> Z) l l', Permutation l l' -> zs (map f l) = zs (map f l').
Proof.
  intros A f l l' H. induction H as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; cbn [map fold_right]; lia.
Qed.
Lemma btcnt_zs_set : forall {A : Type} (f : A -> Z) n (x d : A) l, (n < length l)%nat ->
  zs (map f (rm_set_nth n x l)) = zs (map f l) - f (nth n l d) + f x.
Proof.
  intros A f n. induction n as [|n IH]; intros x d [|y l] Hn; cbn [length] in Hn; try lia;
    cbn [rm_set_nth map fold_right nth]; [lia|]. rewrite (IH x d l ltac:(lia)). lia.
Qed.
Lemma btcnt_peak_app : forall (X : Type) (P : Z -> bool) (a b : list (RelayRunT.rev X)),
  ReplyCnt.tr_peakP P a <= ReplyCnt.tr_peakP P (a ++ b).
Proof.
  intros X P a b. rewrite !ReplyCnt.tr_peakP_w, ReplyTrPeakW.tr_peak_w_app. lia.
Qed.

Section rm.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* A's rmc_za_mk: the model after relay_remove (and after each later callee of the arm): the found entry removed,
   slot si holding o, g_out (cap, out) *)
Lemma btcnt_za_mk : forall (P : Z -> bool) (cx : @lfcx rc) m si o j0 c O cap out,
  (j0 < length (lm_es m))%nat -> (si < length (lm_hs m))%nat ->
  GC.za P (model_blks (rm_mk cx m si o j0 c O cap out)) =
  GC.za P (model_blks m) - GC.za P (aentry_blks (rm_ent m j0)) - GC.za P (slot_blks (nth si (lm_hs m) None)) +
  GC.za P (slot_blks o) + GC.tz P cap - GC.tz P (lm_cap m).
Proof.
  intros P cx m si o j0 c O cap out Hj Hs. rewrite !GC.za_model. unfold rm_mk. cbn [lm_es lm_hs lm_cap lm_out lm_G].
  rewrite (btcnt_zs_perm (fun e => GC.za P (aentry_blks e)) (lm_es m)
             (rm_ent m j0 :: relay_remove_b_c.remove_at j0 (lm_es m))
             (SlotReads.remove_at_perm (lm_es m) j0 relay_remove_b_c.no_entry Hj)).
  rewrite (btcnt_zs_set (fun o => GC.za P (slot_blks o)) si o None (lm_hs m) Hs).
  rewrite !GC.acc_za_out. cbn [map fold_right]. lia.
Qed.

(* A's cnt_rm_rr: relay_remove's model change is at most its trace's peak plus 1 (g_out's capacity after its key
   run), and what it leaves for check_no_loss: the drained lines when the entry was open, nothing at eof *)
Lemma btcnt_rm_rr : forall (cx : @lfcx rc) t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 (P : Z -> bool),
  ReplyRINVB.fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_mfacts m ->
  RX.rm3_pre (rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  GC.za P (model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2)) <=
    GC.za P (model_blks m) + ReplyCnt.tr_peakP P (rm_rr_tr m h) + 1 /\
  hl_recs (hs_expected h) = [] /\ hs_held h1 = hs_held h /\
  map snd (hl_recs (hs_expected h1)) =
    map snd (hl_recs (hs_expected h)) ++
    (if re_eof (rm_ent m j0) =? 0 then map (map (Z_to_bv 8)) (dr_lines h) else []).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 P HRI Hat Hrr (HBP & _ & HPD) Hpre EX0.
  pose proof Hat as (_ & EO & _ & _ & Hsi & Hn & Hj & Hfd & Hq).
  set (e := rm_ent m j0) in *.
  destruct Hpre as (Hsk & Hfd0 & UC & UL & UZ & Hke & PF).
  assert (Hsl : (si < length (lm_hs m))%nat).
  { destruct (Nat.lt_ge_cases si (length (lm_hs m))) as [X|X]; [exact X|].
    rewrite nth_overflow in Hn by exact X. discriminate. }
  pose proof (HPD si h Hn) as PD.
  rewrite (btcnt_za_mk P cx m si (Some h1) j0 c2 O2 cap2 out2 Hj Hsl). fold e. rewrite Hn. cbn [slot_blks].
  pose proof (GC.tz_range P cap2) as T2. pose proof (GC.tz_range P (lm_cap m)) as T0.
  pose proof (btcnt_za_nonneg P (aentry_blks e)) as ZE.
  pose proof (ReplyCnt.tr_peakP_nonneg _ P (rm_rr_tr m h)) as PK0.
  (* relay_remove's trace: the found entry's drain (when open), then its key run and two frees *)
  assert (FIND : find (fun x => re_fd x =? hs_fd h) (lm_es m) = Some e).
  { exact (ReplyLSBDrainPre.rrp_find (lm_es m) j0 (hs_fd h) Hj Hfd Hq). }
  unfold rm_rr_ok in Hrr. cbv zeta in Hrr. fold e in Hrr. destruct Hrr as (Hd & _).
  destruct (Z.eq_dec (re_eof e) 0) as [E0|E0].
  - rewrite (proj2 (Z.eqb_eq _ _) E0) in Hd |- *. cbv iota in Hd.
    (* RI_rm_rr_pair's fact: fr_pair_ok's eof clause (ReplyRINVB.v:148) of fr_RINV's pair (e, h) *)
    destruct (ReplyLSBDrainPre.rm3_pair cx t m si h j0 HRI Hat) as (HPR & _).
    destruct HPR as (_ & _ & _ & HSW & _).
    destruct (HSW E0) as (SO & SW). cbn [fst] in SO, SW. fold e in SO, SW.
    set (c := lm_c m) in *. set (mx := lm_mx m) in *. set (no := Z.of_nat (length (lm_O m))) in *.
    set (cap := lm_cap m) in *.
    (* g_out's capacity: a block size of the model when nonzero, so nonnegative (rm_mfacts) *)
    assert (Hcap : 0 <= cap).
    { destruct (Z.eq_dec cap 0) as [Z0|Z0]; [lia|].
      apply (HBP (lm_out m, cap)). unfold model_blks. right. apply in_or_app. right. apply in_or_app. right.
      unfold aout_blks. fold cap. rewrite (proj2 (Z.eqb_neq _ _) Z0). left. reflexivity. }
    destruct (relay_instance_gone_b_lem.rig_dinit no cap e h Hsk SO SW ltac:(unfold APARTIAL in UL; lia) UZ
                ltac:(lia) PD PF) as [IV ER].
    assert (FU : (length (relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h)) +
                  (if drain_b_c.ds_eintr (drain_b_c.drain_init no cap e h) then 2 else 1)
                  <= S (S (length (pending_stream h))))%nat).
    { rewrite ER. unfold bzs. rewrite length_map. destruct (drain_b_c.ds_eintr _); lia. }
    destruct (GC.acc_drain P (S (S (length (pending_stream h)))) (dr_live c h) mx _ 0 drain_b_c.dadr0 IV
                ltac:(cbn; lia) FU) as [D1 _].
    assert (EF : fst (snd (drain_b_c.drain_run (S (S (length (pending_stream h)))) (dr_live c h) mx
                   (drain_b_c.drain_init no cap e h) 0 drain_b_c.dadr0)) = dr_fin c mx no cap e h) by reflexivity.
    assert (ET : fst (drain_b_c.drain_run (S (S (length (pending_stream h)))) (dr_live c h) mx
                   (drain_b_c.drain_init no cap e h) 0 drain_b_c.dadr0) = dr_tr c mx no cap e h) by reflexivity.
    rewrite EF, ET, ER in D1.
    change (drain_b_c.ds_ref (drain_b_c.drain_init no cap e h)) with (hs_state h) in D1.
    unfold GC.dphi in D1. cbn [drain_b_c.drain_init drain_b_c.ds_cap drain_b_c.ds_ka drain_b_c.ds_H
      drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend] in D1.
    change (map (fun r : Z * list byte => bzs (snd r)) (hl_recs (hs_pending h))) with (texts (hs_pending h)) in D1.
    set (fin := dr_fin c mx no cap e h) in D1.
    pose proof (GC.tz_range P (drain_b_c.ds_cap fin)). pose proof (GC.tz_range P (drain_b_c.ds_ka fin)).
    pose proof (GC.tz_range P (drain_b_c.ds_ocap fin)). pose proof (btcnt_ws_nonneg P (drain_b_c.ds_H fin)).
    (* the drain is a prefix of relay_remove's trace *)
    assert (FD0 : (hs_fd h <? 0) = false) by (apply Z.ltb_ge; lia).
    assert (PR : ReplyCnt.tr_peakP P (dr_tr c mx no cap e h) <= ReplyCnt.tr_peakP P (rm_rr_tr m h)).
    { unfold rm_rr_tr, rr_tr. fold c mx no cap. rewrite FD0, FIND. cbv beta iota zeta.
      rewrite (proj2 (Z.eqb_eq _ _) E0). cbv iota. apply btcnt_peak_app. }
    pose proof (ReplyB3LScntRP.lsc_net_le_peak _ P (dr_tr c mx no cap e h)) as NP.
    unfold dr_rel in Hd. cbv zeta in Hd. fold fin in Hd.
    destruct Hd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eec & _ & _ & _ & _ & Epr & _ & _ & Epc & _ & _ &
                    Eexp & _ & Ehd & _).
    pose proof (GC.acc_hpkh P e Hke) as HKe.
    pose proof (GC.acc_texts_lines P h h1 EX0 Eexp) as TL.
    split; [|split; [exact EX0 | split; [exact Ehd | exact Eexp]]].
    rewrite !GC.za_asrc, !GC.za_alist, GC.za_aentry, HKe, Ehd, Epc, Eec, TL.
    assert (TP : texts (hs_pending h1) = []) by (unfold texts; rewrite Epr; reflexivity). rewrite TP, GC.ws_nil.
    assert (TE : texts (hs_expected h) = []) by (unfold texts; rewrite EX0; reflexivity). rewrite TE, GC.ws_nil.
    unfold dr_lines in D1 |- *. unfold AREC in D1 |- *.
    lia.
  - rewrite (proj2 (Z.eqb_neq _ _) E0) in Hd |- *. cbv iota in Hd |- *. destruct Hd as (_ & ->).
    split; [lia|]. split; [exact EX0|]. split; [reflexivity|]. rewrite app_nil_r. reflexivity.
Qed.

(* A's cnt_rm_cnl_src: check_no_loss's model change is its trace's net, up to its held vector's capacity
   (rm_cnl_ok bounds it only) *)
Lemma btcnt_rm_cnl_src : forall (P : Z -> bool) (h1 : hsrc) (E' H' : hlist),
  rm_cnl_ok h1 E' H' -> List.NoDup (texts (hs_held h1)) ->
  GC.za P (asrc_blks (set_exp_held h1 E' H')) <=
    GC.za P (asrc_blks h1) + ReplyCnt.tr_peakP P (W_contract_x.cnl_tr (hs_expected h1) (hs_held h1)) + 1.
Proof.
  intros P h1 E' H' (ER & _ & EC & _ & ET & _) ND.
  pose proof (ReplyB3LScntRP.lsc_net_le_peak _ P (W_contract_x.cnl_tr (hs_expected h1) (hs_held h1))) as NP.
  assert (SK : ListTr.sh_keys (ListTr.sh_of (fun _ => RelayRunF.adr0) (hs_held h1)) = texts (hs_held h1)).
  { unfold ListTr.sh_keys, ListTr.sh_of, texts. cbn [ListTr.sh_recs]. rewrite map_map. reflexivity. }
  assert (ND' : List.NoDup (ListTr.sh_keys (ListTr.sh_of (fun _ => RelayRunF.adr0) (hs_held h1))))
    by (rewrite SK; exact ND).
  pose proof (GC.acc_cnl_run P (fun _ => RelayRunF.adr0) (hl_recs (hs_expected h1)) 0 _ ND') as NE.
  change (HarnessTr.check_no_loss_tr 0 (ListTr.sh_of (fun _ => RelayRunF.adr0) (hs_held h1))
            (map (ListTr.shr (fun _ => RelayRunF.adr0)) (hl_recs (hs_expected h1))))
    with (W_contract_x.cnl_tr (hs_expected h1) (hs_held h1)) in NE.
  rewrite SK in NE. cbn [ListTr.sh_cap ListTr.sh_of] in NE.
  change (map (fun r : Z * list byte => bzs (snd r)) (hl_recs (hs_expected h1))) with (texts (hs_expected h1)) in NE.
  match type of NE with _ = GC.tz P ?a + _ - _ - _ - _ => pose proof (GC.tz_range P a) end.
  pose proof (GC.tz_range P (AREC * hl_cap H')).
  rewrite !GC.za_asrc. unfold set_exp_held. cbn [hs_pending hs_expected hs_held].
  rewrite !GC.za_alist, ET, EC.
  assert (TE : texts E' = []) by (unfold texts; rewrite ER; reflexivity). rewrite TE, GC.ws_nil.
  unfold AREC in *. lia.
Qed.

(* A's cnt_rm_cnl_pk: check_no_loss's own peak at the state relay_remove leaves: rm_pk's part (the drained lines),
   0 at eof *)
Lemma btcnt_rm_cnl_pk : forall m h j0 h1 (P : Z -> bool),
  hl_recs (hs_expected h) = [] -> hs_held h1 = hs_held h ->
  map snd (hl_recs (hs_expected h1)) =
    map snd (hl_recs (hs_expected h)) ++
    (if re_eof (rm_ent m j0) =? 0 then map (map (Z_to_bv 8)) (dr_lines h) else []) ->
  Z.to_nat (ReplyCnt.tr_peakP P (W_contract_x.cnl_tr (hs_expected h1) (hs_held h1))) =
  (if (re_eof (rm_ent m j0) =? 0)%Z then RX.rm_cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P
   else 0)%nat.
Proof.
  intros m h j0 h1 P EX0 Ehd Eexp. revert Eexp. destruct (re_eof (rm_ent m j0) =? 0); intros Eexp.
  - exact (ReplyB3LScntRP.lsc_cnl_W8 h h1 P EX0 Eexp Ehd).
  - rewrite app_nil_r, EX0 in Eexp. cbn [map] in Eexp.
    destruct (hl_recs (hs_expected h1)) eqn:E1.
    + exact (ReplyB3LScntRP.lsc_cnl_W8_empty _ _ P E1).
    + exfalso. try rewrite E1 in Eexp. discriminate.
Qed.

(* A's cnt_rm_after_cnl: the model after check_no_loss is 2 under the arm's start count plus rm_pk; the held texts'
   NoDup is fr_pair_ok's clause (ReplyRINVB.v:150) of fr_RINV's pair (rm_ent m j0, h), and relay_remove keeps the
   held list (btcnt_rm_rr) *)
Lemma btcnt_rm_after_cnl : forall (cx : @lfcx rc) t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' (P : Z -> bool),
  ReplyRINVB.fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_mfacts m -> RX.rm3_pre (rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  GC.za P (model_blks (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2)) + 2 <=
    Z.of_nat (ReplyCnt.acnt P (model_blks m)) + Z.of_nat (RX.rm_pk m h j0 P).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' P HRI Hat Hrr Hcnl Hmf Hpre HE0.
  destruct (btcnt_rm_rr cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 P HRI Hat Hrr Hmf Hpre HE0)
    as (D & EX0 & Ehd & Eexp).
  pose proof (btcnt_rm_cnl_pk m h j0 h1 P EX0 Ehd Eexp) as CK.
  destruct (ReplyLSBDrainPre.rm3_pair cx t m si h j0 HRI Hat) as (HPR & _).
  destruct HPR as (_ & _ & _ & _ & _ & ND0 & _).
  assert (ND : List.NoDup (texts (hs_held h1))).
  { rewrite Ehd. first [exact (proj1 (NoDup_ListNoDup _) ND0) | exact ND0]. }
  pose proof (btcnt_rm_cnl_src P h1 E' H' Hcnl ND) as C.
  pose proof Hat as (_ & _ & _ & _ & _ & Hn & Hj & _).
  assert (Hsl : (si < length (lm_hs m))%nat).
  { destruct (Nat.lt_ge_cases si (length (lm_hs m))) as [X|X]; [exact X|].
    rewrite nth_overflow in Hn by exact X. discriminate. }
  rewrite (btcnt_za_mk P cx m si (Some h1) j0 c2 O2 cap2 out2 Hj Hsl) in D.
  rewrite (btcnt_za_mk P cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2 Hj Hsl).
  cbn [slot_blks] in D |- *.
  pose proof (ReplyCnt.tr_peakP_nonneg _ P (rm_rr_tr m h)) as PK0.
  pose proof (ReplyCnt.tr_peakP_nonneg _ P (W_contract_x.cnl_tr (hs_expected h1) (hs_held h1))) as PK1.
  rewrite <- (Z2Nat.id _ PK1) in C. rewrite CK in C.
  unfold RX.rm_pk. rewrite !Nat2Z.inj_add, Z2Nat.id by exact PK0.
  change (Z.of_nat (ReplyCnt.acnt P (model_blks m))) with (GC.za P (model_blks m)).
  destruct (re_eof (rm_ent m j0) =? 0); cbn [Z.of_nat] in C |- *; lia.
Qed.
End rm.

(* ================================================================== the three rows, at ReplyBTop.v's Context texts *)
(* The binders follow the Contexts' order; the types of m, h, e1, h1, LB, c2, O2, E', H', H'' and ds are left to
   the remove arm's definitions, which fix them to the Contexts' (lmod, hsrc, rentry, list byte, ctl, hlist). *)
(* RM_CNT_cnl (_remove_x.v:305): A's cnt_rm_cnl *)
Lemma btcnt_RM_CNT_cnl : forall (rc : YM05.RunCeil) (fx : YK11.FPState)
    (cx : @lfcx rc) (t : Z) m (si : nat) h (j0 : nat) e1 h1 (ev : Z) LB c2 O2 (cap2 out2 : Z) (P : Z -> bool),
  ReplyRINVB.fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_mfacts m ->
  RX.rm3_pre (rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2)) +
     W_contract_x.cnl_pk (hs_expected h1) (hs_held h1) P <= ReplyCnt.acnt P (model_blks m) + RX.rm_pk m h j0 P)%nat.
Proof.
  intros rc fx cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 P HRI Hat Hrr Hmf Hpre HE0.
  destruct (btcnt_rm_rr cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 P HRI Hat Hrr Hmf Hpre HE0)
    as (D & EX0 & Ehd & Eexp).
  pose proof (btcnt_rm_cnl_pk m h j0 h1 P EX0 Ehd Eexp) as CK.
  pose proof (ReplyCnt.tr_peakP_nonneg _ P (rm_rr_tr m h)) as PK0.
  unfold W_contract_x.cnl_pk, RX.rm_pk. cbv beta. rewrite CK.
  apply Nat2Z.inj_le. rewrite !Nat2Z.inj_add, Z2Nat.id by exact PK0.
  change (Z.of_nat (ReplyCnt.acnt P (model_blks m))) with (GC.za P (model_blks m)).
  change (Z.of_nat (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2))))
    with (GC.za P (model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2))).
  destruct (re_eof (rm_ent m j0) =? 0); cbn [Z.of_nat]; lia.
Qed.

(* RM_CNT_cshe (_remove_x.v:310): A's cnt_rm_cshe *)
Lemma btcnt_RM_CNT_cshe : forall (rc : YM05.RunCeil) (fx : YK11.FPState)
    (cx : @lfcx rc) (t : Z) m (si : nat) h (j0 : nat) e1 h1 (ev : Z) LB c2 O2 (cap2 out2 : Z) E' H'
    (P : Z -> bool),
  ReplyRINVB.fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  rm_cnl_ok h1 E' H' -> rm_mfacts m -> RX.rm3_pre (rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2)) +
     W_contract_x.cshe_pk P <= ReplyCnt.acnt P (model_blks m) + RX.rm_pk m h j0 P)%nat.
Proof.
  intros rc fx cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' P HRI Hat Hrr Hcnl Hmf Hpre HE0.
  pose proof (btcnt_rm_after_cnl cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' P HRI Hat Hrr Hcnl Hmf Hpre HE0)
    as A.
  unfold W_contract_x.cshe_pk. cbv beta. apply Nat2Z.inj_le. rewrite !Nat2Z.inj_add.
  change (Z.of_nat (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2))))
    with (GC.za P (model_blks (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2))).
  cbn [Z.of_nat]. lia.
Qed.

(* RM_CNT_sr (_remove_x.v:315): A's cnt_rm_sr; check_shape_ends only drops held records
   (ReplyB3CntAcc.acc_cshe_src) *)
Lemma btcnt_RM_CNT_sr : forall (rc : YM05.RunCeil) (fx : YK11.FPState)
    (cx : @lfcx rc) (t : Z) m (si : nat) h (j0 : nat) e1 h1 (ev : Z) LB c2 O2 (cap2 out2 : Z) E' H' H'' ds
    (cc : Z) (P : Z -> bool),
  ReplyRINVB.fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  rm_cnl_ok h1 E' H' -> rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc -> rm_mfacts m ->
  RX.rm3_pre (rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 c2 O2 cap2 out2)) +
     W_contract_x.sr_pk P <= ReplyCnt.acnt P (model_blks m) + RX.rm_pk m h j0 P)%nat.
Proof.
  intros rc fx cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc P HRI Hat Hrr Hcnl Hcs Hmf Hpre HE0.
  pose proof (btcnt_rm_after_cnl cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' P HRI Hat Hrr Hcnl Hmf Hpre HE0)
    as A.
  assert (CS : GC.za P (asrc_blks (set_held (set_exp_held h1 E' H') H'')) <=
               GC.za P (asrc_blks (set_exp_held h1 E' H'))).
  { destruct Hcs as (EV & EC & ND & C0 & HR).
    apply (GC.acc_cshe_src P [] (lm_gn m) (rm_A1 m h1) O2 (set_exp_held h1 E' H') _ ds cc).
    hnf. exists H''. split; [reflexivity|]. split; [exact EV|]. split; [exact EC|]. split; [exact ND|].
    split; [exact C0 | exact HR]. }
  pose proof Hat as (_ & _ & _ & _ & _ & Hn & Hj & _).
  assert (Hsl : (si < length (lm_hs m))%nat).
  { destruct (Nat.lt_ge_cases si (length (lm_hs m))) as [X|X]; [exact X|].
    rewrite nth_overflow in Hn by exact X. discriminate. }
  rewrite (btcnt_za_mk P cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2 Hj Hsl) in A.
  unfold W_contract_x.sr_pk. cbv beta. apply Nat2Z.inj_le. rewrite !Nat2Z.inj_add.
  change (Z.of_nat (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H''))
    j0 c2 O2 cap2 out2)))) with
    (GC.za P (model_blks (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 c2 O2 cap2 out2))).
  rewrite (btcnt_za_mk P cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 c2 O2 cap2 out2 Hj Hsl).
  cbn [slot_blks] in A |- *. cbn [Z.of_nat]. lia.
Qed.
