(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: arm 4 (op_remove) of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput, in
   the form of the cgif walks (lib/A/ACf5.v rt_from segments) over the cut invariants of
   W_LLVMFuzzerTestOneInput_cut.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_remove.v, with its module names changed; 321 of its 391 lines of code are new or changed and 5205 lines of the source are left out. *)
(* The drain and remove arms' count rules (a Theorem Labs lane's piece A-CNT-arms): pure model rules for any count predicate
   P, in family form - each for every RINV, given the arm Section's own RI hypotheses as arguments - so each arm plugs
   its rule inside its Section by `exact`.  proves no function (kind: invariant lemma).
   - cnt_dr_grow: lib/A/W_LLVMFuzzerTestOneInput_drain_x.v:489-508 DR_CNT_grow (drainarm 80da6149505).  Arguments:
     drain_x's RI_src (:512) and RI_pair (:520).
   - cnt_dr_cnl: drain_x.v:638 DR_CNT_cnl at the top's dr_cnl_pk (ReplyTrPeakCnl.cnl_pk over the drained lines), from
     s5-r1d's ReplyLScntRP.lsc_cnl_W8.
   - cnt_rm_cnl / cnt_rm_cshe / cnt_rm_sr: lib/A/W_LLVMFuzzerTestOneInput_remove_x.v:277-292 RM_CNT_cnl / _cshe / _sr
     (rmexit 250502f7048), with its rm3_pre (:94-101).  Arguments: remove_x's RI_rm_rr_pair (:154), and for cshe / sr
     RI_rm_cnl_pre (:178).  The bound: relay_remove's model change is at most its trace's peak + 1 (cnt_rm_rr; the
     drain is a prefix of rr_tr, the removed entry only drops blocks, g_out's capacity after the key run adds at most
     1), check_no_loss's at most its trace's peak + 1 (cnt_rm_cnl_src; rm_cnl_ok bounds the held vector's capacity
     only), check_shape_ends only drops held records; rm_pk's + 4 covers the two 1s and cnl_pk's + 2.
   The accounting is a Theorem Labs lane's lib/A/ReplyCntAcc.v (moved verbatim from its ReplyGnCnt.v, 1dc17932836),
   cited: acc_drain (a drain's model change is at most its trace's net), za / tz / ws and za_* (the P-counts of the
   blocks), acc_hpkh, acc_texts_lines, acc_za_out, acc_cnl_run, acc_cshe_src; also ReplyLScntRP.lsc_net_le_peak (a
   trace's net is at most its peak) and lsc_cnl_W8 / lsc_cnl_W8_empty (check_no_loss's peak over the drained lines),
   relay_instance_gone_b_lem.rig_dinit (the drain's start state satisfies dr_inv), RelayCap.drain_ocap_dead (a dead
   drain keeps g_capout). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF ListTr drain_b_c relay_remove_b_c RelayCap relay_instance_gone_b_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeakW ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCntAcc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_drain_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyLScntRP ReplyTrPeakCnl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotReads.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module DX := W_LLVMFuzzerTestOneInput_drain_x.
Module RX := W_LLVMFuzzerTestOneInput_remove_x.
Module GC := ReplyCntAcc.

(* Speed: at Qed the kernel's conversion of lia's certificate should unfold lia's checker before these model
   functions, which are the arithmetic's atoms.  Without this line cnt_dr_grow's and cnt_rm_rr's Qeds took 222 s and
   215 s (rocq -time-file on a build machine), with it 1.6 s each.  A numeric level (not opaque) keeps them unfoldable by
   the tactics; Local keeps it out of importers. *)
Local Strategy 1000 [drain_b_c.drain_run dr_fin dr_tr ReplyCnt.tr_peakP GC.tz GC.ws GC.za dr_cap1 rr_tr rm_rr_tr].

Section dr.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ================================================================== DR_CNT_grow (drain_x.v:489), family form *)
Lemma cnt_dr_grow : forall (RINV : lfcx -> Z -> lmod -> Prop),
  (* drain_x.v:512 RI_src *)
  (forall cx t m si h,
    RINV cx t m -> dr_pick cx m si h ->
    hl_recs (hs_expected h) = [] /\ NoDup (texts (hs_held h)) /\ 0 <= hs_fd h < 2 ^ 31) ->
  (* drain_x.v:520 RI_pair *)
  (forall cx t m si h j,
    RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
    re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
    re_skip (nth j (lm_es m) dr_e0) = hs_overlong h /\
    (re_skip (nth j (lm_es m) dr_e0) = 0 -> bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h)) /\
    length (re_pad1 (nth j (lm_es m) dr_e0)) = 4%nat /\ length (re_pad2 (nth j (lm_es m) dr_e0)) = 4%nat) ->
  (* DR_CNT_grow, with W8's two added premises (marked) *)
  forall cx t m si h j e' h' LB out' (P : Z -> bool),
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  (* added: aentry_ok's skip clause, W_rep.v:121 *)
  (re_skip (nth j (lm_es m) dr_e0) = 0 \/ re_skip (nth j (lm_es m) dr_e0) = 1) ->
  DX.msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  DX.dr3_epre (nth j (lm_es m) dr_e0) -> DX.ls3_kh (nth j (lm_es m) dr_e0) ->
  DX.dr3_hpre h -> DX.ls3_hn h -> 0 <= lm_cap m ->
  dr_dfun m si h j e' h' LB ->
  DX.dr3_epost (nth j (lm_es m) dr_e0) e' h ->
  (* added: the held-array clause of the entry drain leaves (aentry_ok e', W_rep.v:131-132) *)
  ((re_hp e' = 0 /\ re_keys e' = []) \/ (re_hp e' <> 0 /\ 8 <= re_kh e')) ->
  DX.dr3_hpost h h' ->
  DX.ls3_dpost m j h e' h' ->
  (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks (dr_cap1 m j h) out') <=
   ReplyCnt.acnt P (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) +
   Z.to_nat (ReplyCnt.tr_peakP P
     (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)))%nat.
Proof.
  intros RINV RIsrc RIpair cx t m si h j e' h' LB out' P HRI Hop Hpk Hj Hfd Heof Hsk Hmsz Ht HU Hpos Hep Hkh Hhp
    Hhn Hcap Hdf Hepo Hk' Hhpo Hdp.
  set (e := nth j (lm_es m) dr_e0) in *.
  destruct (RIsrc cx t m si h HRI Hpk) as (EX0 & _ & _).
  destruct (RIpair cx t m si h j HRI Hpk Hj Hfd Heof) as (SO & SW & _ & _).
  fold e in SO, SW.
  destruct Hep as (UC & UL & UZ & Hkh8 & _).
  destruct Hhp as (PD & PF).
  set (c := lm_c m) in *. set (mx := lm_mx m) in *. set (no := Z.of_nat (length (lm_O m))) in *.
  set (cap := lm_cap m) in *.
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
  unfold GC.dphi in D1. cbn [drain_b_c.drain_init drain_b_c.ds_cap drain_b_c.ds_ka drain_b_c.ds_H drain_b_c.ds_ecap
    drain_b_c.ds_ocap drain_b_c.ds_pend] in D1.
  change (map (fun r : Z * list byte => bzs (snd r)) (hl_recs (hs_pending h))) with (texts (hs_pending h)) in D1.
  (* g_capout after the drain: the run's when its sends are live, else unchanged (a dead run keeps it) *)
  assert (CP1 : GC.tz P (dr_cap1 m j h) = GC.tz P (drain_b_c.ds_ocap (dr_fin c mx no cap e h))).
  { unfold dr_cap1. fold c mx no cap e. destruct (dr_live c h) eqn:EL; [reflexivity|].
    unfold dr_fin. rewrite EL, RelayCap.drain_ocap_dead. reflexivity. }
  (* dr_dfun's and the posts' facts *)
  unfold dr_dfun in Hdf. cbv zeta in Hdf. fold e c mx no cap in Hdf.
  destruct Hdf as (_ & _ & _ & Ecap & _ & _ & EH & Eka & _ & _ & _ & _ & _ & Epr & _ & _ & Eexp & Ehd & _ & _ & _ &
                   Eec & _ & _).
  destruct Hhpo as (_ & Epc & _).
  assert (Hke : (re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 <= re_kh e)).
  { destruct Hkh as [X | (X1 & _)]; [left; exact X | right; split; [exact X1 | exact (Hkh8 X1)]]. }
  pose proof (GC.acc_hpkh P e Hke) as HKe. pose proof (GC.acc_hpkh P e' Hk') as HKe'.
  pose proof (GC.acc_texts_lines P h h' EX0 Eexp) as TL.
  pose proof (ReplyLScntRP.lsc_net_le_peak _ P (dr_tr c mx no cap e h)) as NP.
  pose proof (ReplyCnt.tr_peakP_nonneg _ P (dr_tr c mx no cap e h)) as PK0.
  (* the counts, in Z *)
  apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, Z2Nat.id by exact PK0.
  assert (ZA : forall l, Z.of_nat (ReplyCnt.acnt P l) = GC.za P l) by reflexivity.
  rewrite !ZA, !GC.za_app, !GC.za_aentry, !GC.za_asrc, !GC.za_alist, !GC.acc_za_out, HKe, HKe', CP1.
  rewrite Ecap, EH, Eka, Ehd, Epc, Eec, TL.
  assert (TP : texts (hs_pending h') = []) by (unfold texts; rewrite Epr; reflexivity). rewrite TP, GC.ws_nil.
  assert (TE : texts (hs_expected h) = []) by (unfold texts; rewrite EX0; reflexivity). rewrite TE, GC.ws_nil.
  unfold dr_lines. unfold AREC.
  lia.
Qed.

(* ================================================================== DR_CNT_cnl (drain_x.v:638) at the top's instance
   dr_cnl_pk := fun h P => ReplyTrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P: check_no_loss's
   peak after the drain is s5-r1d's ReplyLScntRP.lsc_cnl_W8.  Plug at the top: exact ReplyCntArms.cnt_dr_cnl. *)
Lemma cnt_dr_cnl : forall (h h'' : hsrc) (P : Z -> bool),
  hl_recs (hs_expected h) = [] ->
  map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  (Z.to_nat (ReplyCnt.tr_peakP P (W_contract_x.cnl_tr (hs_expected h'') (hs_held h''))) <=
   ReplyTrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P)%nat.
Proof.
  intros h h'' P E0 Ex Eh. exact (Nat.eq_le_incl _ _ (ReplyLScntRP.lsc_cnl_W8 h h'' P E0 Ex Eh)).
Qed.
End dr.

(* ================================================================== the remove arm: RM_CNT_cnl / _cshe / _sr *)
(* rm3_pre is remove_x.v:94-101's (RiRestate, 250502f7048), cited as RX.rm3_pre: the found entry's aentry_ok clauses
   (W_rep.v:121, :123, :124, :125, :131-132) and the slot's pending records (:91) *)

Local Abbreviation zs := (fold_right Z.add 0).

Lemma rmc_zs_perm : forall {A : Type} (f : A -> Z) l l', Permutation l l' -> zs (map f l) = zs (map f l').
Proof.
  intros A f l l' H. induction H as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; cbn [map fold_right]; lia.
Qed.
Lemma rmc_zs_set : forall {A : Type} (f : A -> Z) n (x d : A) l, (n < length l)%nat ->
  zs (map f (rm_set_nth n x l)) = zs (map f l) - f (nth n l d) + f x.
Proof.
  intros A f n. induction n as [|n IH]; intros x d [|y l] Hn; cbn [length] in Hn; try lia;
    cbn [rm_set_nth map fold_right nth]; [lia|]. rewrite (IH x d l ltac:(lia)). lia.
Qed.
(* the first entry of fd: relay_remove's find *)
Lemma rmc_find : forall FD (es : list rentry) j0 d, (j0 < length es)%nat -> re_fd (nth j0 es d) = FD ->
  (forall q, (q < j0)%nat -> re_fd (nth q es d) <> FD) -> find (fun e => re_fd e =? FD) es = Some (nth j0 es d).
Proof.
  intros FD es. induction es as [|x es IH]; intros j0 d Hj Hf Hq; cbn [length] in Hj; [lia|].
  cbn [find]. destruct j0 as [|j0].
  - cbn [nth] in Hf. rewrite (proj2 (Z.eqb_eq _ _) Hf). reflexivity.
  - assert (Hx : re_fd x <> FD) by exact (Hq 0%nat ltac:(lia)).
    rewrite (proj2 (Z.eqb_neq _ _) Hx). cbn [nth] in Hf |- *. apply (IH j0 d); [lia | exact Hf |].
    intros q Hq'. exact (Hq (S q) ltac:(lia)).
Qed.
Lemma rmc_peak_app : forall (X : Type) (P : Z -> bool) (a b : list (RelayRunT.rev X)),
  ReplyCnt.tr_peakP P a <= ReplyCnt.tr_peakP P (a ++ b).
Proof.
  intros X P a b. rewrite !ReplyCnt.tr_peakP_w, ReplyTrPeakW.tr_peak_w_app. lia.
Qed.
(* the model after relay_remove (and after each later callee of the arm): the found entry removed, slot si
   holding o, g_out (cap, out) *)
Lemma rmc_za_mk {rc : YM05.RunCeil} : forall (P : Z -> bool) cx m si o j0 c O cap out,
  (j0 < length (lm_es m))%nat -> (si < length (lm_hs m))%nat ->
  GC.za P (model_blks (rm_mk cx m si o j0 c O cap out)) =
  GC.za P (model_blks m) - GC.za P (aentry_blks (rm_ent m j0)) - GC.za P (slot_blks (nth si (lm_hs m) None)) +
  GC.za P (slot_blks o) + GC.tz P cap - GC.tz P (lm_cap m).
Proof.
  intros P cx m si o j0 c O cap out Hj Hs. rewrite !GC.za_model. unfold rm_mk. cbn [lm_es lm_hs lm_cap lm_out lm_G].
  rewrite (rmc_zs_perm (fun e => GC.za P (aentry_blks e)) (lm_es m)
             (rm_ent m j0 :: relay_remove_b_c.remove_at j0 (lm_es m))
             (SlotReads.remove_at_perm (lm_es m) j0 relay_remove_b_c.no_entry Hj)).
  rewrite (rmc_zs_set (fun o => GC.za P (slot_blks o)) si o None (lm_hs m) Hs).
  rewrite !GC.acc_za_out. cbn [map fold_right]. lia.
Qed.

Section rm.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* remove_x.v:154 RI_rm_rr_pair *)
Hypothesis RIpair : forall cx t m si h j0,
  RINV cx t m -> rm_at cx m si h j0 -> re_eof (rm_ent m j0) = 0 ->
  re_skip (rm_ent m j0) = hs_overlong h /\ (re_skip (rm_ent m j0) = 0 -> bzs (re_U (rm_ent m j0)) = bzs (hs_W h)).
(* RI_rm_src's fact (remove_x.v:159) is each RM_CNT_* text's premise `hl_recs (hs_expected h) = []` *)

(* relay_remove's model change is at most its trace's peak plus 1 (g_out's capacity after its key run), and what
   it leaves for check_no_loss: the drained lines when the entry was open, nothing at eof *)
Lemma cnt_rm_rr : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 (P : Z -> bool),
  RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_mfacts m ->
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
  rewrite (rmc_za_mk P cx m si (Some h1) j0 c2 O2 cap2 out2 Hj Hsl). fold e. rewrite Hn. cbn [slot_blks].
  pose proof (GC.tz_range P cap2) as T2. pose proof (GC.tz_range P (lm_cap m)) as T0.
  pose proof (GC.za_nonneg P (aentry_blks e)) as ZE.
  pose proof (ReplyCnt.tr_peakP_nonneg _ P (rm_rr_tr m h)) as PK0.
  (* relay_remove's trace: the found entry's drain (when open), then its key run and two frees *)
  assert (FIND : find (fun x => re_fd x =? hs_fd h) (lm_es m) = Some e).
  { exact (rmc_find (hs_fd h) (lm_es m) j0 relay_remove_b_c.no_entry Hj Hfd Hq). }
  unfold rm_rr_ok in Hrr. cbv zeta in Hrr. fold e in Hrr. destruct Hrr as (Hd & _).
  destruct (Z.eq_dec (re_eof e) 0) as [E0|E0].
  - rewrite (proj2 (Z.eqb_eq _ _) E0) in Hd |- *. cbv iota in Hd.
    destruct (RIpair cx t m si h j0 HRI Hat E0) as (SO & SW). fold e in SO, SW.
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
    pose proof (GC.tz_range P (drain_b_c.ds_ocap fin)). pose proof (GC.ws_nonneg P (drain_b_c.ds_H fin)).
    (* the drain is a prefix of relay_remove's trace *)
    assert (FD0 : (hs_fd h <? 0) = false) by (apply Z.ltb_ge; lia).
    assert (PR : ReplyCnt.tr_peakP P (dr_tr c mx no cap e h) <= ReplyCnt.tr_peakP P (rm_rr_tr m h)).
    { unfold rm_rr_tr, rr_tr. fold c mx no cap. rewrite FD0, FIND. cbv beta iota zeta.
      rewrite (proj2 (Z.eqb_eq _ _) E0). cbv iota. apply rmc_peak_app. }
    pose proof (ReplyLScntRP.lsc_net_le_peak _ P (dr_tr c mx no cap e h)) as NP.
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

(* check_no_loss's model change: its trace's net, up to its held vector's capacity (rm_cnl_ok bounds it only) *)
Lemma cnt_rm_cnl_src : forall (P : Z -> bool) (h1 : hsrc) (E' H' : hlist),
  rm_cnl_ok h1 E' H' -> List.NoDup (texts (hs_held h1)) ->
  GC.za P (asrc_blks (set_exp_held h1 E' H')) <=
    GC.za P (asrc_blks h1) + ReplyCnt.tr_peakP P (W_contract_x.cnl_tr (hs_expected h1) (hs_held h1)) + 1.
Proof.
  intros P h1 E' H' (ER & _ & EC & _ & ET & _) ND.
  pose proof (ReplyLScntRP.lsc_net_le_peak _ P (W_contract_x.cnl_tr (hs_expected h1) (hs_held h1))) as NP.
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

(* check_no_loss's own peak at the state relay_remove leaves: rm_pk's part (the drained lines), 0 at eof *)
Lemma cnt_rm_cnl_pk : forall m h j0 h1 (P : Z -> bool),
  hl_recs (hs_expected h) = [] -> hs_held h1 = hs_held h ->
  map snd (hl_recs (hs_expected h1)) =
    map snd (hl_recs (hs_expected h)) ++
    (if re_eof (rm_ent m j0) =? 0 then map (map (Z_to_bv 8)) (dr_lines h) else []) ->
  Z.to_nat (ReplyCnt.tr_peakP P (W_contract_x.cnl_tr (hs_expected h1) (hs_held h1))) =
  (if (re_eof (rm_ent m j0) =? 0)%Z then RX.rm_cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P
   else 0)%nat.
Proof.
  intros m h j0 h1 P EX0 Ehd Eexp. revert Eexp. destruct (re_eof (rm_ent m j0) =? 0); intros Eexp.
  - exact (ReplyLScntRP.lsc_cnl_W8 h h1 P EX0 Eexp Ehd).
  - rewrite app_nil_r, EX0 in Eexp. cbn [map] in Eexp.
    destruct (hl_recs (hs_expected h1)) eqn:E1.
    + exact (ReplyLScntRP.lsc_cnl_W8_empty _ _ P E1).
    + exfalso. try rewrite E1 in Eexp. discriminate.
Qed.

(* check_no_loss's count premise at the state relay_remove leaves (RM_CNT_cnl, remove_x.v:253) *)
Lemma cnt_rm_cnl : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 (P : Z -> bool),
  RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_mfacts m ->
  RX.rm3_pre (rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2)) +
     W_contract_x.cnl_pk (hs_expected h1) (hs_held h1) P <= ReplyCnt.acnt P (model_blks m) + RX.rm_pk m h j0 P)%nat.
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 P HRI Hat Hrr Hmf Hpre HE0.
  destruct (cnt_rm_rr cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 P HRI Hat Hrr Hmf Hpre HE0)
    as (D & EX0 & Ehd & Eexp).
  pose proof (cnt_rm_cnl_pk m h j0 h1 P EX0 Ehd Eexp) as CK.
  pose proof (ReplyCnt.tr_peakP_nonneg _ P (rm_rr_tr m h)) as PK0.
  unfold W_contract_x.cnl_pk, RX.rm_pk. cbv beta. rewrite CK.
  apply Nat2Z.inj_le. rewrite !Nat2Z.inj_add, Z2Nat.id by exact PK0.
  change (Z.of_nat (ReplyCnt.acnt P (model_blks m))) with (GC.za P (model_blks m)).
  change (Z.of_nat (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2))))
    with (GC.za P (model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2))).
  destruct (re_eof (rm_ent m j0) =? 0); cbn [Z.of_nat]; lia.
Qed.

(* check_shape_ends' count premise at the state check_no_loss leaves (RM_CNT_cshe, remove_x.v:258);
   remove_x.v:178 RI_rm_cnl_pre gives the held texts' NoDup *)
Hypothesis RIcnlpre : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Forall (fun e => Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e)) (lm_es m) ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  AREC * capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).

Lemma cnt_rm_after_cnl : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' (P : Z -> bool),
  RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_mfacts m -> RX.rm3_pre (rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  GC.za P (model_blks (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2)) + 2 <=
    Z.of_nat (ReplyCnt.acnt P (model_blks m)) + Z.of_nat (RX.rm_pk m h j0 P).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' P HRI Hat Hrr Hcnl Hmf Hpre HE0.
  destruct (cnt_rm_rr cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 P HRI Hat Hrr Hmf Hpre HE0)
    as (D & EX0 & Ehd & Eexp).
  pose proof (cnt_rm_cnl_pk m h j0 h1 P EX0 Ehd Eexp) as CK.
  pose proof Hmf as (_ & HK & _).
  destruct (RIcnlpre cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr HK) as (ND & _).
  pose proof (cnt_rm_cnl_src P h1 E' H' Hcnl (proj1 (NoDup_ListNoDup _) ND)) as C.
  pose proof Hat as (_ & _ & _ & _ & _ & Hn & Hj & _).
  assert (Hsl : (si < length (lm_hs m))%nat).
  { destruct (Nat.lt_ge_cases si (length (lm_hs m))) as [X|X]; [exact X|].
    rewrite nth_overflow in Hn by exact X. discriminate. }
  rewrite (rmc_za_mk P cx m si (Some h1) j0 c2 O2 cap2 out2 Hj Hsl) in D.
  rewrite (rmc_za_mk P cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2 Hj Hsl).
  cbn [slot_blks] in D |- *.
  pose proof (ReplyCnt.tr_peakP_nonneg _ P (rm_rr_tr m h)) as PK0.
  pose proof (ReplyCnt.tr_peakP_nonneg _ P (W_contract_x.cnl_tr (hs_expected h1) (hs_held h1))) as PK1.
  rewrite <- (Z2Nat.id _ PK1) in C. rewrite CK in C.
  unfold RX.rm_pk. rewrite !Nat2Z.inj_add, Z2Nat.id by exact PK0.
  change (Z.of_nat (ReplyCnt.acnt P (model_blks m))) with (GC.za P (model_blks m)).
  destruct (re_eof (rm_ent m j0) =? 0); cbn [Z.of_nat] in C |- *; lia.
Qed.

Lemma cnt_rm_cshe : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' (P : Z -> bool),
  RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_mfacts m -> RX.rm3_pre (rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2)) +
     W_contract_x.cshe_pk P <= ReplyCnt.acnt P (model_blks m) + RX.rm_pk m h j0 P)%nat.
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' P HRI Hat Hrr Hcnl Hmf Hpre HE0.
  pose proof (cnt_rm_after_cnl cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' P HRI Hat Hrr Hcnl Hmf Hpre HE0)
    as A.
  unfold W_contract_x.cshe_pk. cbv beta. apply Nat2Z.inj_le. rewrite !Nat2Z.inj_add.
  change (Z.of_nat (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2))))
    with (GC.za P (model_blks (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2))).
  cbn [Z.of_nat]. lia.
Qed.

(* source_reset's count premise at the state check_shape_ends leaves (RM_CNT_sr, remove_x.v:263):
   check_shape_ends only drops held records *)
Lemma cnt_rm_sr : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc (P : Z -> bool),
  RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc -> rm_mfacts m ->
  RX.rm3_pre (rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 c2 O2 cap2 out2)) +
     W_contract_x.sr_pk P <= ReplyCnt.acnt P (model_blks m) + RX.rm_pk m h j0 P)%nat.
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc P HRI Hat Hrr Hcnl Hcs Hmf Hpre HE0.
  pose proof (cnt_rm_after_cnl cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' P HRI Hat Hrr Hcnl Hmf Hpre HE0)
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
  rewrite (rmc_za_mk P cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2 Hj Hsl) in A.
  unfold W_contract_x.sr_pk. cbv beta. apply Nat2Z.inj_le. rewrite !Nat2Z.inj_add.
  change (Z.of_nat (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H''))
    j0 c2 O2 cap2 out2)))) with
    (GC.za P (model_blks (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 c2 O2 cap2 out2))).
  rewrite (rmc_za_mk P cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 c2 O2 cap2 out2 Hj Hsl).
  cbn [slot_blks] in A |- *. cbn [Z.of_nat]. lia.
Qed.
End rm.
