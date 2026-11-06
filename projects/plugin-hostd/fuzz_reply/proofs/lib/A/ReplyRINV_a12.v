(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, group RI-b of a Theorem Labs lane's TOPX owner table: the model rules of
   W_LLVMFuzzerTestOneInput_top_x.v (integ bb9dae5d905) RI_exit_slots, RI_exit_ends, RI_rm_rr_pair, RI_rm_cnl_pre,
   RI_rm_cshe_pre, RI_rm_csd at RINV := fr_RINV, against their `_obl` texts in ReplyRINV.v (atop 5ab58d26200).  Each
   `_obl` is top_x's text with RINV := fr_RINV; the model functions it names are the same constants (_exit.v's) or
   byte-equal copies (ReplyRINV.v's copies of _remove.v's rm_at / rm_ent / rm_rr_ok / rm_cnl_ok / rm_cshe_ok / rm_A1
   and of W_contract.v's capb as rm_capb).
   Proved at those texts: RI_exit_slots_holds, RI_rm_rr_pair_holds.
   False for fr_RINV as it is defined, at the texts top_x had before the restatement: RI_exit_ends, RI_rm_cnl_pre,
   RI_rm_cshe_pre, RI_rm_csd (copied as RI_*_unrestated).  For each, the `_false` lemma proves the negation of that
   text from a state that meets fr_RINV and the rule's premises and not its conclusion:
   - RI_exit_ends: fr_RINV does not say lm_gn m is 0 or 1 (fr_gone only says what 0 and 1 imply; agone_at, W_rep.v:193,
     says it in amodel_at), and it does not say that the held texts have no NUL byte.  State: one open slot 0 holding
     h, held list [(0, "a")], one relay entry of fd 100 whose one key has the text "a", lm_gn m = 2, the controller
     CTL 3 0 0 0 0.  relay_finish's output lx_rf_O m is "a" ++ " end\0" (6 bytes); at gone = 2 lx_ends_c1 keeps the
     offset, so lx_ends_run gives Some 0, not Some 6.  A second state, at lm_gn m = 0: the key text and the held
     text are the one byte NUL; the output starts with NUL, so check_shape_ends' first line is empty and
     CheckRep.ends_run gives None.  (RI_exit_ends_obl_false, RI_exit_ends_obl_false_nul)
   - RI_rm_cnl_pre: fr_RINV does not bound the held count below 2 ^ 22 (ReplyRINV.v:254-256 says the same for the
     drain step).  State: lm_gn m = 0, one open slot 0 holding h, its entry at eof (re_eof = 1, so rm_rr_ok gives
     h1 = h), 2 ^ 22 held records with distinct 3-byte texts and one key for each; the cost is keys_total =
     8 * 2 ^ 22 = 2 ^ 25 <= lm_k m < c_n cx < 2 ^ 26.  Then hl_n (hs_held h1) + count_begin (texts (hs_expected h1))
     = 2 ^ 22, not < 2 ^ 22.  (RI_rm_cnl_pre_obl_false)
   - RI_rm_cshe_pre: fr_RINV does not say that the held texts have no NUL byte.  State: lm_gn m = 0, the controller
     CTL 3 0 0 0 0, one open slot 0 holding h with held list [(0, [NUL])], its entry at eof with one key of text
     [NUL].  O2 = [NUL] ++ " end\0"; rm_A1 m h1 = 0; CheckRep.ends_run's first line is empty, so it gives None.
     (RI_rm_cshe_pre_obl_false)
   - RI_rm_csd: fr_RINV does not say lm_gn m is 0 or 1.  State: lm_gn m = 2, the controller CTL 3 0 0 0 0, one open
     slot 0 holding h with held list [(0, "a")], its entry at eof with one key of text "a".  O2 = "a" ++ " end\0" (6
     bytes); rm_cshe_ok's first branch (gone <> 0) holds with cc = 0, and rm_A1 m h1 = 0 at gone <> 0, so
     rm_A1 m h1 + cc = 0, not 6.  (RI_rm_csd_obl_false)
   With the premises the arms hold (a Theorem Labs lane's ruling: give the rules the arm's premise, fr_RINV unchanged), the
   four rows hold: fr_exit_ends (lm_gn m is 0 or 1, agone_at; the keys' texts have no NUL byte, aentry_ok),
   fr_rm_cnl_pre_core (every key text of the removed entry is >= 14 bytes, rm_mfacts conjunct 2: 19 bytes a key and
   21 a begin line inside the row's cost < 2 ^ 26 give the 2 ^ 22 bound), fr_rm_cshe_pre_core (lm_gn m = 0; the
   new keys have no NUL byte) and fr_rm_csd_core (lm_gn m is 0 or 1; no NUL premise: a run of the check that succeeds
   has read only NUL-free texts).  RI_exit_ends_holds, RI_rm_cnl_pre_holds, RI_rm_cshe_pre_holds and RI_rm_csd_holds
   state them at the restated top_x texts (a working branch 3f40808c334).  lines_nul_free and
   upds_nul_free (RelayModel terms) say the drained lines and the keys they add have no NUL byte. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
RelayRunT drain_b_c gestures_end_b_c relay_remove_b_c relay_instance_gone_b_c SlotInv SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_drain W_LLVMFuzzerTestOneInput_event W_LLVMFuzzerTestOneInput_exit
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
Import ListNotations.
(* ReplyRINV.v Requires W_LLVMFuzzerTestOneInput_remove.v (it cites the remove arm's model names), whose library chain
   leaves lia's division flag off; this file's proofs were written with it on (a12_ks_nodup's lia reads the bytes'
   mod / div), so it is set here for this file only *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section rinv_a12.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the cost bound reaches every row: a row's cost is at most the table's (the rows' costs are >= 0) *)
Lemma fr_a12_sum_nonneg : forall (l : list (rentry * (hsrc * nat))),
  0 <= fold_right Z.add 0 (map (fun q => fr_pair_cost (fst q) (snd q)) l).
Proof.
  induction l as [|q l IH]; cbn [map fold_right]; [lia|].
  pose proof (fr_pair_cost_nonneg (fst q) (snd q)). lia.
Qed.
Lemma fr_a12_sum_ge : forall (l : list (rentry * (hsrc * nat))) q, In q l ->
  fr_pair_cost (fst q) (snd q) <= fold_right Z.add 0 (map (fun q => fr_pair_cost (fst q) (snd q)) l).
Proof.
  induction l as [|q0 l IH]; intros q Hq; [destruct Hq|]. cbn [map fold_right].
  pose proof (fr_a12_sum_nonneg l) as Hl. pose proof (fr_pair_cost_nonneg (fst q0) (snd q0)) as H0.
  destruct Hq as [<- | Hq]; [lia|]. specialize (IH q Hq). lia.
Qed.
Lemma fr_a12_cost_ge : forall es hj e p, In (e, p) (combine es hj) -> fr_pair_cost e p <= fr_cost es hj.
Proof. intros es hj e p Hin. unfold fr_cost. exact (fr_a12_sum_ge (combine es hj) (e, p) Hin). Qed.
(* a held key costs at least 5 (gesture_end's " end\0") *)
Lemma fr_a12_keys_len : forall ks, 5 * Z.of_nat (length ks) <= gestures_end_b_c.keys_total ks.
Proof.
  unfold gestures_end_b_c.keys_total. induction ks as [|k ks IH]; cbn [fold_right length]; lia.
Qed.
(* the held list is no longer than the keys: its texts are distinct and each is a key's *)
Lemma fr_a12_held_keys : forall ks (H : hlist), NoDup (texts H) -> same_set (drain_b_c.keys_texts ks) (texts H) ->
  hl_n H <= Z.of_nat (length ks).
Proof.
  intros ks H Hnd Hss. first [apply NoDup_ListNoDup in Hnd | idtac].
  assert (Hinc : incl (texts H) (drain_b_c.keys_texts ks)) by (intros y Hy; exact (proj2 (Hss y) Hy)).
  pose proof (NoDup_incl_length Hnd Hinc) as Hle.
  unfold texts, drain_b_c.keys_texts in Hle. rewrite !length_map in Hle. unfold hl_n. lia.
Qed.

(* _exit.v:765 RI_exit_slots: an open slot's held list is an entry's (fr_pair_ok: distinct texts, one key for each),
   and the keys' cost (5 bytes or more each) is in the input cost, below c_n cx < 2 ^ 26 *)
Lemma RI_exit_slots_holds : RI_exit_slots_obl.
Proof.
  intros cx t m (_ & HR & Hn & _) j Hj.
  destruct HR as (_ & _ & _ & _ & hj & HF & _ & Hcl & _ & Hcn).
  destruct (nth j (lm_hs m) None) as [h|] eqn:Eh; cbn [lx_ends_slot_ok]; [|exact I].
  destruct (fr_pair_of_open m t hj j h HF Hcl Hj Eh) as (e & p & Hin & HRp & _ & Hfst).
  destruct HRp as (_ & _ & _ & _ & Hss & Hnd & _). rewrite Hfst in Hss, Hnd.
  split; [first [exact Hnd | exact (proj1 (NoDup_ListNoDup _) Hnd) | exact (proj2 (NoDup_ListNoDup _) Hnd)]|].
  pose proof (fr_a12_held_keys (re_keys e) (hs_held h) Hnd Hss) as Hle.
  pose proof (fr_a12_keys_len (re_keys e)) as Hk.
  pose proof (fr_a12_cost_ge (lm_es m) hj e p Hin) as Hc.
  unfold fr_pair_cost in Hc. destruct (re_skip e =? 0); lia.
Qed.

(* remove-s2 _remove.v:1949 RI_rm_rr_pair: the entry j0 of h's fd is paired with a source of that fd, which is h
   (two open slots have distinct fds, RI_fds_holds); fr_pair_ok's open-entry clause is the conclusion *)
Lemma RI_rm_rr_pair_holds : RI_rm_rr_pair_obl.
Proof.
  intros cx t m si h j0 HRI Hat Heof.
  pose proof HRI as (_ & HR & _ & _).
  destruct HR as (_ & _ & _ & _ & hj & HF & _ & _ & _).
  destruct Hat as (_ & _ & _ & _ & Hsi & Hh & Hj & Hfd & _).
  pose proof (fr_F2_nth _ _ _ _ _ HF j0 relay_remove_b_c.no_entry relay_instance_gone_b_c.no_hj Hj) as HRp.
  change (nth j0 (lm_es m) relay_remove_b_c.no_entry) with (rm_ent m j0) in HRp.
  set (p := nth j0 hj relay_instance_gone_b_c.no_hj) in HRp.
  destruct HRp as (Hs4 & Hsn & Hpfd & Hpr & _).
  assert (Es : snd p = si).
  { destruct (Nat.eq_dec (snd p) si) as [E | Ne]; [exact E|]. exfalso.
    apply (RI_fds_holds cx t m (snd p) si (fst p) h HRI Hs4 Hsi Ne Hsn Hh). rewrite Hpfd, Hfd. reflexivity. }
  rewrite Es, Hh in Hsn. injection Hsn as Eh.
  rewrite Eh. exact (Hpr Heof).
Qed.

(* ================================================================== the four rows fr_RINV does not meet
   Each `_false` lemma is the negation of the row's `_obl`, from any call context cx0 (its layout, state, world,
   registers, memory and model are kept; the input is replaced).  The states are the ones of the header: one open
   slot 0 with source a12_src H (fd 100, held list H), one relay entry a12_ent ks (fd 100, at eof, keys ks), and the
   controller CTL 3 0 0 0 0. *)
Definition a12_cx (cx0 : lfcx) (n : Z) (pl : list byte) : lfcx :=
  LFCX (c_ly cx0) (c_S cx0) (c_W cx0) (c_regs cx0) (c_mem cx0) (c_md cx0) 0 n pl 0.
Definition a12_pad : list byte := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition a12_E0 : hlist := HL 0 0 [] [].
Definition a12_src (H : hlist) : hsrc := HS 100 1 0 0 a12_E0 0 0 [] 0 0 [] a12_E0 H.
Definition a12_ent (ks : list (Z * list byte * list byte)) : rentry :=
  RE 100 1 1 a12_pad 0 0 0 0 0 a12_pad ks [] [].
Definition a12_m (k : Z) (H : hlist) (ks : list (Z * list byte * list byte)) (gn : Z) : lmod :=
  LM k [Some (a12_src H); None; None; None] 0 [a12_ent ks] (CTL 3 0 0 0 0) [] 0 0 0 gn 1.

(* fr_RINV holds at the state when the keys and the held texts agree and the keys' cost is in the input *)
Lemma a12_RINV : forall cx0 n pl k H ks gn,
  NoDup (drain_b_c.keys_texts ks) -> same_set (drain_b_c.keys_texts ks) (texts H) -> NoDup (texts H) ->
  hl_cap H < 2 ^ 24 -> gestures_end_b_c.keys_total ks <= k -> k <= n -> n < 2 ^ 26 -> gn <> 1 ->
  fr_RINV (a12_cx cx0 n pl) 0 (a12_m k H ks gn).
Proof.
  intros cx0 n pl k H ks gn Hnk Hss Hnd Hcap Hk Hkn Hn Hgn.
  split; [|split; [|split]].
  - unfold fr_count, nopen, OPS_MAX, a12_m. cbn [lm_nfd lm_hs List.filter length Z.of_nat]. lia.
  - unfold fr_relay, a12_m. cbn [lm_hs lm_es lm_nfd lm_k length].
    split; [reflexivity|].
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split; [constructor; [cbn; lia | constructor]|].
    split.
    { constructor; [|constructor]. unfold fr_entry_ok, a12_ent, a12_pad.
      cbn [re_eof re_pad1 re_pad2 re_keys re_skip length].
      split; [right; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hnk | right; reflexivity]. }
    exists [(a12_src H, 0%nat)].
    split.
    { constructor; [|constructor]. unfold fr_pair_ok, a12_src, a12_ent.
      cbn [fst snd nth lm_hs re_eof re_fd hs_fd re_keys hs_held hs_expected hs_off hl_recs hl_cap].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros E; discriminate E|].
      split; [exact Hss|]. split; [exact Hnd|]. split; [reflexivity|].
      split; [left; reflexivity|]. split; [exact Hcap|].
      split; [unfold pending_stream, a12_E0; cbn [hs_pending hl_recs length Z.of_nat]; unfold SlotInv.WRITE_MAX; lia
             | lia]. }
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split.
    { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *; first [discriminate Ho | reflexivity | lia]. }
    unfold fr_cost, fr_pair_cost, a12_ent, a12_src, pending_stream, a12_E0.
    cbn -[gestures_end_b_c.keys_total]. lia.
  - exact Hn.
  - unfold fr_gone, a12_m. cbn [lm_gn lm_c ct_cl ct_br ct_dd].
    split; intros E; [repeat split | exfalso; exact (Hgn E)].
Qed.
Lemma a12_pick : forall h kb, pick [Some h; None; None; None] kb = Some 0%nat.
Proof. intros h kb. unfold pick. cbn -[Z.modulo]. rewrite Z.mod_1_r. reflexivity. Qed.
(* the remove arm's operation at the state: op 4 at the cursor k, slot 0, entry 0 *)
Lemma a12_rm_at : forall cx0 n pl k H ks gn, 0 <= k -> k + 1 < n -> in_byte (a12_cx cx0 n pl) k mod 10 = 4 ->
  rm_at (a12_cx cx0 n pl) (a12_m k H ks gn) 0 (a12_src H) 0.
Proof.
  intros cx0 n pl k H ks gn Hk Hkn Hb. unfold rm_at, a12_m. cbn [lm_k lm_O lm_hs lm_es length].
  split; [unfold a12_cx; cbn [c_n]; lia|].
  split; [reflexivity|]. split; [exact Hb|]. split; [apply a12_pick|].
  split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
  intros q Hq. lia.
Qed.
(* relay_remove at an entry at eof: the entry and the source are kept, the keys' ends are sent *)
Lemma a12_rr_ok : forall k H ks gn c2 O2 cap2,
  sl_sends 0 (CTL 3 0 0 0 0) [] 0 (ge_bytes ks) = (c2, O2, cap2) ->
  rm_rr_ok (a12_m k H ks gn) (a12_src H) 0 (a12_ent ks) (a12_src H) 0 [] c2 O2 cap2.
Proof. intros k H ks gn c2 O2 cap2 Er. unfold rm_rr_ok. split; [split; reflexivity | exact Er]. Qed.
(* check_no_loss with nothing expected keeps the held list *)
Lemma a12_cnl_ok : forall H, NoDup (texts H) -> rm_cnl_ok (a12_src H) a12_E0 H.
Proof.
  intros H Hnd. unfold rm_cnl_ok, a12_src, a12_E0. cbn [hl_recs hl_v hl_cap hs_expected hs_held].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hnd|].
  split; [reflexivity | lia].
Qed.

(* the small states: one held text x, one key of text x, cost 6 = |x| + 5; the input 10 bytes of 4 *)
Definition a12_pl : list byte := repeat (Z_to_bv 8 4) 10.
Definition a12_H1 (x : list byte) : hlist := HL 0 8 [(0, x)] [].
Definition a12_ks1 (x : list byte) : list (Z * list byte * list byte) := [(0, x, [])].
Definition a12_a : list byte := [Z_to_bv 8 97].   (* "a" *)
Definition a12_nul : list byte := [Z_to_bv 8 0].  (* one NUL byte *)
Lemma a12_RINV1 : forall cx0 x gn, length x = 1%nat -> gn <> 1 ->
  fr_RINV (a12_cx cx0 10 a12_pl) 0 (a12_m 6 (a12_H1 x) (a12_ks1 x) gn).
Proof.
  intros cx0 x gn Hx Hgn. apply a12_RINV; try lia.
  - apply NoDup_ListNoDup. repeat constructor. intros [].
  - intros y. split; intros Hy; exact Hy.
  - apply NoDup_ListNoDup. repeat constructor. intros [].
  - cbn. lia.
  - unfold gestures_end_b_c.keys_total, a12_ks1, gestures_end_b_c.key_text. cbn [fold_right fst snd].
    rewrite Hx. cbn. lia.
Qed.
Lemma a12_rm_at1 : forall cx0 x gn, rm_at (a12_cx cx0 10 a12_pl) (a12_m 6 (a12_H1 x) (a12_ks1 x) gn) 0 (a12_src (a12_H1 x)) 0.
Proof. intros cx0 x gn. apply a12_rm_at; [lia | lia | reflexivity]. Qed.
Lemma a12_nd1 : forall x, NoDup (texts (a12_H1 x)).
Proof. intros x. apply NoDup_ListNoDup. repeat constructor. intros []. Qed.

(* the four rules as top_x stated them before the restatement (integ bb9dae5d905, = ReplyRINV.v's `_obl` at atop
   5ab58d26200), at RINV := fr_RINV; the `_false` lemmas refute these texts *)
Definition RI_exit_ends_unrestated : Prop := forall cx t m, fr_RINV cx t m -> (0 < length (lm_es m))%nat ->
  lx_ends_run (lm_gn m) (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).
Definition RI_rm_cnl_pre_unrestated : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  AREC * rm_capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).
Definition RI_rm_cshe_pre_unrestated : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 ->
  rm_A1 m h1 <= Z.of_nat (length O2) /\
  ends_run [] (hl_recs H') (skipn (Z.to_nat (rm_A1 m h1)) O2) (want_of [] (hl_recs H')) <> None.
Definition RI_rm_csd_unrestated : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  rm_A1 m h1 + cc = Z.of_nat (length O2).

(* RI_exit_ends at lm_gn m = 2 (not 0 or 1): relay_finish sends "a end\0" and the check at gone <> 0 keeps
   the offset 0 *)
Lemma RI_exit_ends_obl_false : lfcx -> ~ RI_exit_ends_unrestated.
Proof.
  intros cx0 Hobl.
  pose proof (Hobl _ _ _ (a12_RINV1 cx0 a12_a 2 eq_refl ltac:(lia)) ltac:(cbn; lia)) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.
(* RI_exit_ends at lm_gn m = 0 with a held text of one NUL byte: the check's first line is empty *)
Lemma RI_exit_ends_obl_false_nul : lfcx -> ~ RI_exit_ends_unrestated.
Proof.
  intros cx0 Hobl.
  pose proof (Hobl _ _ _ (a12_RINV1 cx0 a12_nul 0 eq_refl ltac:(lia)) ltac:(cbn; lia)) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.
(* the stream relay_remove leaves: the ends of the keys ks1 x, sent to the live controller *)
Definition a12_r (x : list byte) : ctl * list byte * Z := sl_sends 0 (CTL 3 0 0 0 0) [] 0 (ge_bytes (a12_ks1 x)).
(* RI_rm_cshe_pre at lm_gn m = 0 with a held text of one NUL byte *)
Lemma RI_rm_cshe_pre_obl_false : lfcx -> ~ RI_rm_cshe_pre_unrestated.
Proof.
  intros cx0 Hobl.
  pose proof (Hobl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (a12_RINV1 cx0 a12_nul 0 eq_refl ltac:(lia)) (a12_rm_at1 cx0 a12_nul 0)
    (a12_rr_ok 6 (a12_H1 a12_nul) (a12_ks1 a12_nul) 0 (fst (fst (a12_r a12_nul))) (snd (fst (a12_r a12_nul)))
       (snd (a12_r a12_nul)) eq_refl)
    (a12_cnl_ok (a12_H1 a12_nul) (a12_nd1 a12_nul)) eq_refl) as (_ & Hne).
  apply Hne. vm_compute. reflexivity.
Qed.
(* RI_rm_csd at lm_gn m = 2: rm_cshe_ok's gone branch with cc = 0, rm_A1 = 0, and 6 bytes sent *)
Lemma RI_rm_csd_obl_false : lfcx -> ~ RI_rm_csd_unrestated.
Proof.
  intros cx0 Hobl.
  assert (Hcs : rm_cshe_ok (a12_m 6 (a12_H1 a12_a) (a12_ks1 a12_a) 2)
    (set_exp_held (a12_src (a12_H1 a12_a)) a12_E0 (a12_H1 a12_a)) (snd (fst (a12_r a12_a)))
    (rm_A1 (a12_m 6 (a12_H1 a12_a) (a12_ks1 a12_a) 2) (a12_src (a12_H1 a12_a)))
    (HL 0 8 [] []) [(0, a12_a)] 0).
  { unfold rm_cshe_ok. cbn [hl_v hl_cap hs_held set_exp_held a12_src a12_H1 a12_m lm_gn hl_recs].
    split; [reflexivity|]. split; [reflexivity|].
    split; [apply NoDup_ListNoDup; constructor|]. split; [lia|].
    left. split; [lia|]. split; [reflexivity|]. split; reflexivity. }
  pose proof (Hobl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (a12_RINV1 cx0 a12_a 2 eq_refl ltac:(lia)) (a12_rm_at1 cx0 a12_a 2)
    (a12_rr_ok 6 (a12_H1 a12_a) (a12_ks1 a12_a) 2 (fst (fst (a12_r a12_a))) (snd (fst (a12_r a12_a)))
       (snd (a12_r a12_a)) eq_refl)
    (a12_cnl_ok (a12_H1 a12_a) (a12_nd1 a12_a)) Hcs) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

(* RI_rm_cnl_pre: 2 ^ 22 held records with distinct 3-byte texts, one key for each; the cost 8 * 2 ^ 22 = 2 ^ 25 is
   below the cursor 2 ^ 25 and the input length 2 ^ 25 + 2 < 2 ^ 26.  The lists are never computed: every fact about
   them is a lemma over map / seq. *)
Definition a12_NB : nat := Z.to_nat (2 ^ 22).
Definition a12_t (n : nat) : list byte :=
  [Z_to_bv 8 (Z.of_nat n mod 256); Z_to_bv 8 (Z.of_nat n / 256 mod 256); Z_to_bv 8 (Z.of_nat n / 65536)].
Definition a12_ks : list (Z * list byte * list byte) := map (fun n => (0, a12_t n, [])) (seq 0 a12_NB).
Definition a12_bH : hlist := HL 0 (2 ^ 22) (map (fun n => (0, a12_t n)) (seq 0 a12_NB)) [].
Definition a12_bpl : list byte := repeat (Z_to_bv 8 0) (Z.to_nat (2 ^ 25)) ++ [Z_to_bv 8 4; Z_to_bv 8 4].
Lemma a12_nodup_map_in : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup l -> List.NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd. revert Hinj. induction Hnd as [|a l Ha Hnd IH]; intros Hinj; cbn [map]; constructor.
  - intros Hin. apply in_map_iff in Hin as (b & Hb & Hbl). apply Ha.
    rewrite (Hinj b a (or_intror Hbl) (or_introl eq_refl) Hb) in Hbl. exact Hbl.
  - apply IH. intros x y Hx Hy Exy. apply Hinj; [right; exact Hx | right; exact Hy | exact Exy].
Qed.
Lemma a12_texts : drain_b_c.keys_texts a12_ks = texts a12_bH.
Proof.
  unfold drain_b_c.keys_texts, texts, a12_ks, a12_bH. cbn [hl_recs]. rewrite !map_map.
  apply map_ext. intros n. reflexivity.
Qed.
Lemma a12_ks_nodup : NoDup (drain_b_c.keys_texts a12_ks).
Proof.
  apply NoDup_ListNoDup. unfold drain_b_c.keys_texts, a12_ks. rewrite map_map.
  apply a12_nodup_map_in; [|apply seq_NoDup].
  intros x y Hx Hy E. apply in_seq in Hx as [_ Hx]. apply in_seq in Hy as [_ Hy].
  change (x < a12_NB)%nat in Hx. change (y < a12_NB)%nat in Hy. unfold a12_NB in Hx, Hy.
  apply Nat2Z.inj_lt in Hx, Hy. rewrite Z2Nat.id in Hx, Hy by lia.
  unfold gestures_end_b_c.key_text, a12_t, bzs in E. cbn [fst snd map] in E.
  injection E as E1 E2 E3.
  rewrite !SlotReads.bz_lit in E1, E2, E3 by first [apply Z.mod_pos_bound; lia | split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia].
  apply Nat2Z.inj. lia.
Qed.
Lemma a12_ks_total : gestures_end_b_c.keys_total a12_ks = 2 ^ 25.
Proof.
  assert (Hm : forall l, gestures_end_b_c.keys_total (map (fun n => (0, a12_t n, @nil byte)) l) = 8 * Z.of_nat (length l)).
  { unfold gestures_end_b_c.keys_total. induction l as [|a l IH]; [reflexivity|].
    cbn [map fold_right length]. rewrite IH. unfold gestures_end_b_c.key_text. cbn [fst snd a12_t length]. lia. }
  unfold a12_ks. rewrite Hm, length_seq. unfold a12_NB. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma a12_bH_n : hl_n a12_bH = 2 ^ 22.
Proof.
  unfold hl_n, a12_bH. cbn [hl_recs]. rewrite length_map, length_seq. unfold a12_NB. rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma a12_bpl_at : forall cx0, in_byte (a12_cx cx0 (2 ^ 25 + 2) a12_bpl) (2 ^ 25) mod 10 = 4.
Proof.
  intros cx0. unfold in_byte, a12_cx. cbn [c_pl]. unfold a12_bpl.
  rewrite app_nth2 by (rewrite repeat_length; apply Nat.le_refl).
  rewrite repeat_length, Nat.sub_diag. reflexivity.
Qed.
Lemma RI_rm_cnl_pre_obl_false : lfcx -> ~ RI_rm_cnl_pre_unrestated.
Proof.
  intros cx0 Hobl.
  assert (HRI : fr_RINV (a12_cx cx0 (2 ^ 25 + 2) a12_bpl) 0 (a12_m (2 ^ 25) a12_bH a12_ks 0)).
  { apply a12_RINV.
    - exact a12_ks_nodup.
    - rewrite a12_texts. intros y. split; intros Hy; exact Hy.
    - rewrite <- a12_texts. exact a12_ks_nodup.
    - change (hl_cap a12_bH) with (2 ^ 22). lia.
    - rewrite a12_ks_total. lia.
    - lia.
    - lia.
    - lia. }
  destruct (sl_sends 0 (CTL 3 0 0 0 0) [] 0 (ge_bytes a12_ks)) as [[c2 O2] cap2] eqn:Er.
  destruct (Hobl _ _ _ _ _ _ _ _ _ _ _ _ _ HRI
    (a12_rm_at cx0 (2 ^ 25 + 2) a12_bpl (2 ^ 25) a12_bH a12_ks 0 ltac:(lia) ltac:(lia) (a12_bpl_at cx0))
    (a12_rr_ok (2 ^ 25) a12_bH a12_ks 0 c2 O2 cap2 Er)) as (_ & _ & Hb & _).
  change (hl_n a12_bH + Z.of_nat (count_begin (texts a12_E0)) < 2 ^ 22) in Hb.
  rewrite a12_bH_n in Hb. change (count_begin (texts a12_E0)) with 0%nat in Hb. lia.
Qed.

(* ================================================================== RI_exit_ends with the arm's premises
   (lm_gn m is 0 or 1; the held keys' texts have no NUL byte).  At gone = 0 the controller is live, so relay_finish
   sends every entry's keys_out in table order, and the shutdown check consumes each entry's part at its slot (the
   slot of its fd, which has the same texts); at gone = 1 nothing is sent and the check keeps the offset 0. *)
Definition fr_live3 (c : ctl) : Prop := ct_cl c = 3 /\ ct_br c = 0 /\ ct_dd c = 0.
Definition fr_dead (c : ctl) : Prop := ct_cl c = -1 \/ ct_br c = 1 \/ ct_dd c = 1.
Lemma fr_sl_live3 : forall c len, fr_live3 c -> sl_live c len = negb (len =? 0).
Proof.
  intros [cl br dd ei ev] len (E1 & E2 & E3). cbn [ct_cl ct_br ct_dd] in *. subst cl br dd.
  unfold sl_live, send_line_c.send_live, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  destruct (len =? 0); reflexivity.
Qed.
Lemma fr_sl_ctl3 : forall c len, fr_live3 c -> fr_live3 (sl_ctl c len).
Proof.
  intros [cl br dd ei ev] len (E1 & E2 & E3). cbn [ct_cl ct_br ct_dd] in *. subst cl br dd.
  unfold sl_ctl, fr_live3. cbn [ct_cl ct_br ct_dd].
  destruct (send_line_c.send_off 3 0 len); (repeat split); reflexivity.
Qed.
Lemma fr_sl_O3 : forall c O x, fr_live3 c -> sl_O c O x = O ++ x.
Proof.
  intros c O x H. unfold sl_O. rewrite (fr_sl_live3 c _ H).
  destruct x as [|b x]; [cbn; rewrite app_nil_r; reflexivity | reflexivity].
Qed.
Lemma fr_ge_O3 : forall c O x, fr_live3 c -> ge_O c O x = O ++ x ++ END5.
Proof.
  intros c O x H. unfold ge_O. rewrite (fr_sl_O3 c O x H), (fr_sl_O3 _ _ END5 (fr_sl_ctl3 c _ H)).
  rewrite app_assoc. reflexivity.
Qed.
Lemma fr_gse_run3 : forall xs c O mx no cap, fr_live3 c ->
  gse_O (gse_run c O mx no cap xs) = O ++ concat (map (fun x => x ++ END5) xs) /\
  fr_live3 (gse_c (gse_run c O mx no cap xs)).
Proof.
  induction xs as [|x xs IH]; intros c O mx no cap H.
  - cbn [gse_run gse_O gse_c fst snd map concat]. rewrite app_nil_r. split; [reflexivity | exact H].
  - cbn [gse_run map concat].
    destruct (IH (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
      (ge_cap c mx no cap (Z.of_nat (length x))) (fr_sl_ctl3 _ 5 (fr_sl_ctl3 c _ H))) as (E & L).
    split; [|exact L]. rewrite E, (fr_ge_O3 c O x H). rewrite <- !app_assoc. reflexivity.
Qed.
Lemma fr_rf_run3 : forall es c O mx no cap, fr_live3 c ->
  gse_O (lx_rf_run c O mx no cap es) = O ++ concat (map (fun e => gestures_end_b_c.keys_out (re_keys e)) es).
Proof.
  induction es as [|e es IH]; intros c O mx no cap H.
  - cbn [lx_rf_run gse_O fst snd map concat]. rewrite app_nil_r. reflexivity.
  - cbn [lx_rf_run map concat].
    destruct (fr_gse_run3 (gse_keys e) c O mx no cap H) as (E & L).
    rewrite IH by exact L. rewrite E. rewrite <- app_assoc. f_equal. f_equal.
    unfold gse_keys, gestures_end_b_c.keys_out. rewrite map_map. reflexivity.
Qed.
Lemma fr_sl_dead : forall c len, fr_dead c -> sl_live c len = false /\ fr_dead (sl_ctl c len).
Proof.
  intros [cl br dd ei ev] len Hd. unfold fr_dead in *. cbn [ct_cl ct_br ct_dd] in Hd.
  unfold sl_live, sl_ctl, send_line_c.send_live, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  destruct Hd as [-> | [-> | ->]].
  - split; [reflexivity | left; reflexivity].
  - destruct (cl <? 0); (split; [reflexivity | right; left; reflexivity]).
  - destruct ((cl <? 0) || (br =? 1) || (len =? 0)); (split; [reflexivity | right; right; reflexivity]).
Qed.
Lemma fr_ge_dead : forall c O x, fr_dead c -> ge_O c O x = O /\ fr_dead (ge_ctl c (Z.of_nat (length x))).
Proof.
  intros c O x H. unfold ge_O, ge_ctl, sl_O.
  destruct (fr_sl_dead c (Z.of_nat (length x)) H) as (L1 & D1).
  destruct (fr_sl_dead _ 5 D1) as (_ & D2).
  destruct (fr_sl_dead _ (Z.of_nat (length END5)) D1) as (L2 & _).
  rewrite L1, L2. split; [reflexivity | exact D2].
Qed.
Lemma fr_gse_dead : forall xs c O mx no cap, fr_dead c ->
  gse_O (gse_run c O mx no cap xs) = O /\ fr_dead (gse_c (gse_run c O mx no cap xs)).
Proof.
  induction xs as [|x xs IH]; intros c O mx no cap H; cbn [gse_run].
  - split; [reflexivity | exact H].
  - destruct (fr_ge_dead c O x H) as (E & D). rewrite E. apply IH. exact D.
Qed.
Lemma fr_rf_dead : forall es c O mx no cap, fr_dead c -> gse_O (lx_rf_run c O mx no cap es) = O.
Proof.
  induction es as [|e es IH]; intros c O mx no cap H; cbn [lx_rf_run]; [reflexivity|].
  destruct (fr_gse_dead (gse_keys e) c O mx no cap H) as (E & D). rewrite IH by exact D. exact E.
Qed.
(* the check at gone <> 0 only drops the records of prefix "" and keeps the offset *)
Lemma fr_scan_gone : forall gone ob oi A sl, gone <> 0 -> exists sl', lx_ends_scan gone ob oi A sl = Some (sl', A).
Proof.
  intros gone ob oi A sl Hg. apply Z.eqb_neq in Hg.
  induction sl as [|o sl IH]; [exists []; reflexivity|].
  destruct IH as (sl' & E). destruct o as [[fd recs]|]; cbn [lx_ends_scan].
  - destruct (fd =? oi).
    + unfold lx_ends_c1. rewrite Hg. cbv beta iota zeta. rewrite E. eexists. reflexivity.
    + cbv beta iota zeta. rewrite E. eexists. reflexivity.
  - rewrite E. eexists. reflexivity.
Qed.
Lemma fr_outer_gone : forall gone ob ord n i A sl, gone <> 0 ->
  exists sl', lx_ends_outer gone ob ord n i A sl = Some (sl', A).
Proof.
  intros gone ob ord n. induction n as [|n IH]; intros i A sl Hg; cbn [lx_ends_outer].
  - exists sl. reflexivity.
  - destruct (fr_scan_gone gone ob (ord i) A sl Hg) as (sl' & E). rewrite E.
    destruct (IH (i + 1) A sl' Hg) as (sl'' & E'). exists sl''. exact E'.
Qed.
(* the scan at gone = 0 when exactly one slot s0 has the entry's fd oi *)
Lemma fr_scan_none : forall ob oi A (sl : list lx_ends_rslot),
  (forall s fd recs, nth s sl None = Some (fd, recs) -> fd <> oi) ->
  lx_ends_scan 0 ob oi A sl = Some (sl, A).
Proof.
  intros ob oi A sl. induction sl as [|o sl IH]; intros Hn; [reflexivity|].
  assert (Hn' : forall s fd recs, nth s sl None = Some (fd, recs) -> fd <> oi)
    by (intros s fd recs E; exact (Hn (S s) fd recs E)).
  destruct o as [[fd recs]|]; cbn [lx_ends_scan].
  - assert (Hf : fd <> oi) by exact (Hn 0%nat fd recs eq_refl). apply Z.eqb_neq in Hf. rewrite Hf.
    rewrite (IH Hn'). reflexivity.
  - rewrite (IH Hn'). reflexivity.
Qed.
Lemma fr_scan_one : forall ob oi recs0 recs0' A A' (sl : list lx_ends_rslot) s0,
  nth s0 sl None = Some (oi, recs0) ->
  (forall s fd recs, s <> s0 -> nth s sl None = Some (fd, recs) -> fd <> oi) ->
  lx_ends_c1 0 ob recs0 A = Some (recs0', A') ->
  lx_ends_scan 0 ob oi A sl = Some (rm_set_nth s0 (Some (oi, recs0')) sl, A').
Proof.
  intros ob oi recs0 recs0' A A' sl. induction sl as [|o sl IH]; intros s0 H0 Hn Hc;
    [destruct s0; discriminate H0|].
  destruct s0 as [|s0].
  - cbn [nth] in H0. subst o.
    assert (Hn0 : forall s fd recs, nth s sl None = Some (fd, recs) -> fd <> oi)
      by (intros s fd recs E; exact (Hn (S s) fd recs ltac:(lia) E)).
    cbn [lx_ends_scan rm_set_nth]. rewrite Z.eqb_refl, Hc. cbv beta iota zeta.
    rewrite (fr_scan_none ob oi A' sl Hn0). reflexivity.
  - cbn [nth] in H0.
    assert (Hn' : forall s fd recs, s <> s0 -> nth s sl None = Some (fd, recs) -> fd <> oi)
      by (intros s fd recs Hs E; exact (Hn (S s) fd recs ltac:(lia) E)).
    destruct o as [[fd recs]|]; cbn [lx_ends_scan rm_set_nth].
    + assert (Hf : fd <> oi) by exact (Hn 0%nat fd recs ltac:(lia) eq_refl). apply Z.eqb_neq in Hf. rewrite Hf.
      rewrite (IH s0 H0 Hn' Hc). reflexivity.
    + rewrite (IH s0 H0 Hn' Hc). reflexivity.
Qed.
Lemma fr_firstn_S : forall (T : Type) (l : list T) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  intros T l. induction l as [|x l IH]; intros [|i] d Hi; cbn [length] in Hi; try lia; [reflexivity|].
  cbn [firstn nth app]. rewrite (IH i d) by lia. reflexivity.
Qed.
Lemma fr_skipn_S : forall (T : Type) (l : list T) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof.
  intros T l. induction l as [|x l IH]; intros [|i] d Hi; cbn [length] in Hi; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.
Lemma fr_skipn_concat : forall (T U : Type) (f : T -> list U) (l : list T) i,
  skipn (length (concat (map f (firstn i l)))) (concat (map f l)) = concat (map f (skipn i l)).
Proof.
  intros T U f l. induction l as [|x l IH]; intros [|i]; cbn [firstn skipn map concat]; try reflexivity.
  rewrite length_app, skipn_app, skipn_all2 by lia.
  replace (length (f x) + length (concat (map f (firstn i l))) - length (f x))%nat
    with (length (concat (map f (firstn i l)))) by lia.
  cbn [app]. apply IH.
Qed.
(* the slot list during the check: closed slots stay None, an open slot keeps its fd, and an open slot whose fd no
   entry before i has keeps its held records *)
Definition fr_xinv (es : list rentry) (hs : list (option hsrc)) (i : nat) (sl : list lx_ends_rslot) : Prop :=
  length sl = length hs /\
  forall s, (nth s hs None = None -> nth s sl None = None) /\
    (forall h, nth s hs None = Some h -> exists recs, nth s sl None = Some (hs_fd h, recs) /\
       ((forall k, (k < i)%nat -> re_fd (nth k es lxo_e0) <> hs_fd h) -> recs = hl_recs (hs_held h))).
Lemma fr_xinv0 : forall es hs, fr_xinv es hs 0 (map lx_ends_slot0 hs).
Proof.
  intros es hs. split; [apply length_map|]. intros s.
  change (nth s (map lx_ends_slot0 hs) None) with (nth s (map lx_ends_slot0 hs) (lx_ends_slot0 None)).
  rewrite map_nth. split.
  - intros E. rewrite E. reflexivity.
  - intros h E. exists (hl_recs (hs_held h)). rewrite E. split; [reflexivity | intros _; reflexivity].
Qed.
Lemma fr_exit_ends_live : forall cx t m, fr_RINV cx t m -> fr_live3 (lm_c m) ->
  Forall (fun e => Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) (re_keys e)) (lm_es m) ->
  lx_ends_run 0 (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).
Proof.
  intros cx t m HRI Hlive Hnul.
  pose proof HRI as (_ & HR & _ & _).
  destruct HR as (Hlen & Hnd & _ & Hent & hj & HF & HNDs & Hcl & _).
  apply NoDup_ListNoDup in Hnd. rewrite Forall_forall in Hent, Hnul.
  assert (HO : lx_rf_O m = concat (map (fun e => gestures_end_b_c.keys_out (re_keys e)) (lm_es m)))
    by (unfold lx_rf_O; rewrite (fr_rf_run3 _ _ _ _ _ _ Hlive); reflexivity).
  assert (Hn4 : (length (lm_es m) <= 4)%nat).
  { rewrite (Forall2_length HF). apply NoDup_ListNoDup in HNDs.
    assert (Hinc : incl (map snd hj) [0; 1; 2; 3]%nat).
    { intros y Hy. apply in_map_iff in Hy as (p & <- & Hp).
      destruct (fr_Forall2_r _ _ _ _ _ HF p Hp) as (e & _ & (Hs4 & _)). clear - Hs4.
      revert Hs4. generalize (snd p) as q. intros q Hq.
      destruct q as [|[|[|[|q]]]]; cbn; first [tauto | lia]. }
    pose proof (NoDup_incl_length HNDs Hinc) as X. rewrite length_map in X. exact X. }
  assert (Hno : Z.to_nat (lx_norder m) = length (lm_es m)) by (unfold lx_norder; lia).
  (* the loop over order[0 .. norder) *)
  assert (Hout : forall n i zi A sl, (i + n = length (lm_es m))%nat -> zi = Z.of_nat i ->
      fr_xinv (lm_es m) (lm_hs m) i sl ->
      A = Z.of_nat (length (concat (map (fun e => gestures_end_b_c.keys_out (re_keys e)) (firstn i (lm_es m))))) ->
      exists sl', lx_ends_outer 0 (lx_rf_O m) (lx_ord m) n zi A sl = Some (sl', Z.of_nat (length (lx_rf_O m)))).
  { induction n as [|n IH]; intros i zi A sl Hin Hzi Hinv HA.
    - exists sl. cbn [lx_ends_outer]. rewrite HA, HO. replace i with (length (lm_es m)) by lia.
      rewrite firstn_all. reflexivity.
    - assert (Hi : (i < length (lm_es m))%nat) by lia.
      set (e := nth i (lm_es m) lxo_e0).
      pose proof (fr_F2_nth _ _ _ _ _ HF i lxo_e0 relay_instance_gone_b_c.no_hj Hi) as HRp. fold e in HRp.
      set (p := nth i hj relay_instance_gone_b_c.no_hj) in HRp.
      destruct HRp as (Hs4 & Hsn & Hpfd & _ & Hss & Hndh & _).
      destruct Hinv as (Hsl & Hinv).
      destruct (proj2 (Hinv (snd p)) (fst p) Hsn) as (recs0 & Hr0 & Hun).
      assert (Hunp : forall k, (k < i)%nat -> re_fd (nth k (lm_es m) lxo_e0) <> hs_fd (fst p)).
      { intros k Hk E. rewrite Hpfd in E.
        assert (k = i); [|lia].
        apply (proj1 (NoDup_nth (map re_fd (lm_es m)) (re_fd lxo_e0)) Hnd k i); rewrite ?length_map; try lia.
        rewrite !map_nth. exact E. }
      specialize (Hun Hunp). subst recs0.
      assert (Hoi : lx_ord m zi = re_fd e) by (unfold lx_ord; rewrite Hzi, Nat2Z.id; reflexivity).
      (* the entry's part of the output: its keys' ends, at the offset A *)
      assert (He : In e (lm_es m)) by (apply nth_In; exact Hi).
      assert (Hk : exists rs' ds, ends_run [] (hl_recs (hs_held (fst p)))
          (gestures_end_b_c.keys_out (re_keys e) ++
           concat (map (fun e => gestures_end_b_c.keys_out (re_keys e)) (skipn (S i) (lm_es m))))
          (length (hl_recs (hs_held (fst p)))) =
        Some (rs', ds, Z.of_nat (length (gestures_end_b_c.keys_out (re_keys e))))).
      { apply SlotReads.ends_run_keys.
        - destruct (Hent e He) as (_ & _ & _ & X & _). first [exact X | exact (proj1 (NoDup_ListNoDup _) X)
            | exact (proj2 (NoDup_ListNoDup _) X)].
        - first [exact Hndh | exact (proj1 (NoDup_ListNoDup _) Hndh) | exact (proj2 (NoDup_ListNoDup _) Hndh)].
        - exact Hss.
        - exact (Hnul e He). }
      destruct Hk as (rs' & ds & Hrun).
      assert (Hc1 : lx_ends_c1 0 (lx_rf_O m) (hl_recs (hs_held (fst p))) A =
          Some (rs', A + Z.of_nat (length (gestures_end_b_c.keys_out (re_keys e))))).
      { unfold lx_ends_c1. cbn [Z.eqb]. rewrite HA, Nat2Z.id, HO, fr_skipn_concat, (fr_skipn_S _ _ i lxo_e0 Hi).
        cbn [map concat]. fold e. rewrite SlotReads.want_of_nil, Hrun. reflexivity. }
      assert (Hr0' : nth (snd p) sl None = Some (re_fd e, hl_recs (hs_held (fst p)))) by (rewrite Hr0, Hpfd; reflexivity).
      assert (Hsc := fr_scan_one (lx_rf_O m) (re_fd e) (hl_recs (hs_held (fst p))) rs' A
        (A + Z.of_nat (length (gestures_end_b_c.keys_out (re_keys e)))) sl (snd p) Hr0').
      assert (Hsc' : lx_ends_scan 0 (lx_rf_O m) (re_fd e) A sl =
          Some (rm_set_nth (snd p) (Some (re_fd e, rs')) sl, A + Z.of_nat (length (gestures_end_b_c.keys_out (re_keys e))))).
      { apply Hsc; [|exact Hc1]. intros s fd recs Hs E.
        destruct (nth s (lm_hs m) None) as [h|] eqn:Eh.
        - destruct (proj2 (Hinv s) h Eh) as (recs1 & Er & _). rewrite E in Er. injection Er as -> _.
          assert (Hs4' : (s < 4)%nat).
          { destruct (Nat.lt_ge_cases s 4) as [X | X]; [exact X|]. rewrite nth_overflow in Eh by lia. discriminate Eh. }
          intros Ef. apply (RI_fds_holds cx t m s (snd p) h (fst p) HRI Hs4' Hs4 Hs Eh Hsn). rewrite Ef, Hpfd. reflexivity.
        - rewrite (proj1 (Hinv s) Eh) in E. discriminate E. }
      cbn [lx_ends_outer]. rewrite Hoi, Hsc'. cbv beta iota zeta.
      apply (IH (S i) (zi + 1)); [lia | lia | |].
      + split; [rewrite fr_rm_set_nth_length; exact Hsl|]. intros s.
        destruct (Nat.eq_dec s (snd p)) as [-> | Ns].
        * split; [intros E; rewrite Hsn in E; discriminate E|].
          intros h E. rewrite Hsn in E. injection E as <-. exists rs'. split.
          -- assert (Hsp : (snd p < length sl)%nat) by (rewrite Hsl, Hlen; exact Hs4).
             rewrite Hpfd. exact (fr_rm_set_nth_same _ (snd p) (Some (re_fd e, rs')) sl None Hsp).
          -- intros Hk. exfalso. apply (Hk i ltac:(lia)). fold e. exact (eq_sym Hpfd).
        * rewrite (fr_rm_set_nth_other lx_ends_rslot (snd p) s) by (intros X; apply Ns; symmetry; exact X).
          split; [exact (proj1 (Hinv s))|]. intros h E.
          destruct (proj2 (Hinv s) h E) as (recs1 & Er & Hu). exists recs1. split; [exact Er|].
          intros Hk. apply Hu. intros k Hk'. apply Hk. lia.
      + rewrite HA, (fr_firstn_S _ _ i lxo_e0 Hi), map_app, concat_app, length_app. cbn [map concat].
        rewrite app_nil_r. fold e. lia. }
  unfold lx_ends_run. rewrite Hno.
  destruct (Hout (length (lm_es m)) 0%nat 0 0 (map lx_ends_slot0 (lm_hs m)) eq_refl eq_refl (fr_xinv0 _ _) eq_refl)
    as (sl' & E).
  rewrite E. reflexivity.
Qed.
Lemma fr_exit_ends : forall cx t m, fr_RINV cx t m -> (lm_gn m = 0 \/ lm_gn m = 1) ->
  Forall (fun e => Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) (re_keys e)) (lm_es m) ->
  lx_ends_run (lm_gn m) (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).
Proof.
  intros cx t m HRI Hg Hnul. pose proof HRI as (_ & _ & _ & (G0 & G1)).
  destruct Hg as [E | E]; rewrite E.
  - exact (fr_exit_ends_live cx t m HRI (G0 E) Hnul).
  - assert (HO : lx_rf_O m = []) by (unfold lx_rf_O; apply fr_rf_dead; exact (G1 E)).
    rewrite HO. unfold lx_ends_run.
    destruct (fr_outer_gone 1 [] (lx_ord m) (Z.to_nat (lx_norder m)) 0 0 (map lx_ends_slot0 (lm_hs m)) ltac:(lia))
      as (sl' & E'). rewrite E'. reflexivity.
Qed.

(* ================================================================== the remove arm with the arm's premises
   What relay_remove leaves (rm_rr_ok): the held list is h's, the new keys are the held texts updated by the drained
   lines Ls (none when the entry was at eof), the expected list is Ls, and the stream is the expected stream then
   the new keys' ends when the controller is live, nothing when it is gone. *)
Lemma fr_skipn_len : forall (T : Type) (x y : list T), skipn (length x) (x ++ y) = y.
Proof. intros T x y. induction x as [|a x IH]; [reflexivity|]. cbn [length skipn app]. exact IH. Qed.
Lemma fr_ge_out : forall ks, concat (ge_bytes ks) = gestures_end_b_c.keys_out ks.
Proof.
  unfold ge_bytes, gestures_end_b_c.keys_out. induction ks as [|k ks IH]; [reflexivity|].
  cbn [map concat]. rewrite concat_app, IH. cbn [concat]. rewrite app_nil_r. reflexivity.
Qed.
Lemma fr_sends3 : forall Bs mx c O cap, fr_live3 c -> snd (fst (sl_sends mx c O cap Bs)) = O ++ concat Bs.
Proof.
  induction Bs as [|Bl r IH]; intros mx c O cap H; cbn [sl_sends].
  - cbn. rewrite app_nil_r. reflexivity.
  - rewrite IH by (apply fr_sl_ctl3; exact H). rewrite (fr_sl_O3 c O Bl H). cbn [concat]. rewrite app_assoc.
    reflexivity.
Qed.
Lemma fr_sends_dead : forall Bs mx c O cap, fr_dead c -> snd (fst (sl_sends mx c O cap Bs)) = O.
Proof.
  induction Bs as [|Bl r IH]; intros mx c O cap H; cbn [sl_sends]; [reflexivity|].
  destruct (fr_sl_dead c (Z.of_nat (length Bl)) H) as (L & D). rewrite IH by exact D. unfold sl_O. rewrite L.
  reflexivity.
Qed.
Lemma fr_sends_len : forall Bs mx c O cap,
  (length (snd (fst (sl_sends mx c O cap Bs))) <= length O + length (concat Bs))%nat.
Proof.
  induction Bs as [|Bl r IH]; intros mx c O cap; cbn [sl_sends].
  - cbn. lia.
  - etransitivity; [apply IH|]. unfold sl_O. cbn [concat]. rewrite length_app.
    destruct (sl_live c (Z.of_nat (length Bl))); [rewrite length_app|]; lia.
Qed.
Lemma fr_dr_ctl3 : forall c h ev, fr_live3 c -> fr_live3 (dr_ctl c h ev).
Proof.
  intros [cl br dd ei ev0] h ev (E1 & E2 & E3). cbn [ct_cl ct_br ct_dd] in *. subst cl br dd.
  unfold dr_ctl, fr_live3. cbn [ct_cl ct_br ct_dd].
  destruct (send_line_c.send_off 3 0 (dr_tot h)); (repeat split); reflexivity.
Qed.
Lemma fr_dr_ctl_dead : forall c h ev, fr_dead c -> fr_dead (dr_ctl c h ev).
Proof.
  intros [cl br dd ei ev0] h ev Hd. unfold fr_dead in *. cbn [ct_cl ct_br ct_dd] in Hd.
  unfold dr_ctl, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  destruct Hd as [-> | [-> | ->]].
  - left; reflexivity.
  - destruct (cl <? 0); right; left; reflexivity.
  - right; right; reflexivity.
Qed.
(* keys_total is SlotPass2Aux's sum over the key texts *)
Lemma fr_kt_ksum : forall ks, gestures_end_b_c.keys_total ks = SlotPass2Aux.p2_ksum (drain_b_c.keys_texts ks).
Proof.
  unfold gestures_end_b_c.keys_total, SlotPass2Aux.p2_ksum, drain_b_c.keys_texts.
  induction ks as [|k ks IH]; [reflexivity|]. cbn [map fold_right]. rewrite IH. unfold bzs. rewrite length_map.
  reflexivity.
Qed.
Lemma fr_lines_zr : forall h, Forall SlotReads.zrange (dr_lines h).
Proof.
  intros h. unfold dr_lines. apply (SlotReads.lines_range (bzs (pending_stream h)) (hs_state h));
    [unfold hs_state; cbn [ls_w] | ]; apply SlotReads.zrange_bzs.
Qed.
(* the entry j0 and the operation's source h are one row of the table *)
Lemma fr_rm_pair : forall cx t m si h j0, fr_RINV cx t m -> rm_at cx m si h j0 ->
  fr_pair_ok m t (rm_ent m j0) (h, si) /\ fr_pair_cost (rm_ent m j0) (h, si) < 2 ^ 26 /\
  fr_entry_ok (rm_ent m j0).
Proof.
  intros cx t m si h j0 HRI Hat. pose proof HRI as (_ & HR & Hn & _).
  destruct HR as (_ & _ & _ & Hent & hj & HF & _ & _ & _ & Hcn).
  pose proof Hat as (_ & _ & _ & _ & Hsi & Hh & Hj & Hfd & _).
  pose proof (fr_F2_nth _ _ _ _ _ HF j0 relay_remove_b_c.no_entry relay_instance_gone_b_c.no_hj Hj) as HRp.
  change (nth j0 (lm_es m) relay_remove_b_c.no_entry) with (rm_ent m j0) in HRp.
  assert (Hin : In (rm_ent m j0, nth j0 hj relay_instance_gone_b_c.no_hj) (combine (lm_es m) hj)).
  { unfold rm_ent. rewrite <- combine_nth by exact (Forall2_length HF). apply nth_In.
    rewrite length_combine, <- (Forall2_length HF). lia. }
  revert HRp Hin. destruct (nth j0 hj relay_instance_gone_b_c.no_hj) as [h' s'] eqn:Ep. intros HRp Hin.
  pose proof HRp as (Hs4 & Hsn & Hpfd & _). cbn [fst snd] in Hs4, Hsn, Hpfd.
  assert (Es : s' = si).
  { destruct (Nat.eq_dec s' si) as [E | Ne]; [exact E|]. exfalso.
    apply (RI_fds_holds cx t m s' si h' h HRI Hs4 Hsi Ne Hsn Hh). rewrite Hpfd, Hfd. reflexivity. }
  subst s'. rewrite Hh in Hsn. injection Hsn as <-.
  split; [exact HRp|]. split.
  - pose proof (fr_a12_cost_ge (lm_es m) hj _ _ Hin). lia.
  - rewrite Forall_forall in Hent. apply Hent. eapply in_combine_l. exact Hin.
Qed.
Lemma fr_rm_facts : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  exists Ls,
    hs_held h1 = hs_held h /\
    NoDup (drain_b_c.keys_texts (re_keys e1)) /\
    same_set (drain_b_c.keys_texts (re_keys e1)) (upds (texts (hs_held h)) Ls) /\
    texts (hs_expected h1) = Ls /\
    map snd (hl_recs (hs_expected h1)) = map (map (Z_to_bv 8)) Ls /\ Forall SlotReads.zrange Ls /\
    Z.of_nat (length (with_nul Ls)) <=
      (if re_skip (rm_ent m j0) =? 0 then Z.of_nat (length (re_U (rm_ent m j0))) else 0) +
      Z.of_nat (length (pending_stream h)) /\
    gestures_end_b_c.keys_total (re_keys e1) <=
      gestures_end_b_c.keys_total (re_keys (rm_ent m j0)) + Z.of_nat (length (with_nul Ls)) /\
    (fr_live3 (lm_c m) -> O2 = bstream (hs_expected h1) ++ gestures_end_b_c.keys_out (re_keys e1)) /\
    (fr_dead (lm_c m) -> O2 = []) /\
    (length O2 <= length (with_nul Ls) + length (gestures_end_b_c.keys_out (re_keys e1)))%nat /\
    (Ls = [] \/ (re_eof (rm_ent m j0) = 0 /\ Ls = dr_lines h)).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr.
  destruct (fr_rm_pair cx t m si h j0 HRI Hat) as (HP & _ & HE).
  pose proof HP as (_ & _ & _ & Heof & Hss & Hndh & Hexp & _). cbn [fst snd] in Heof, Hss, Hndh, Hexp.
  pose proof HE as (Hef & _ & _ & Hndk & Hsk).
  pose proof Hat as (_ & HO & _).
  unfold rm_rr_ok in Hrr. cbv beta zeta in Hrr. rewrite HO in Hrr.
  destruct (Z.eqb_spec (re_eof (rm_ent m j0)) 0) as [E0 | E1].
  - (* the entry was open: drain ran *)
    try rewrite (proj2 (Z.eqb_eq _ _) E0) in Hrr. cbn [andb] in Hrr. destruct Hrr as (Hdr & Hsd).
    destruct Hdr as (_ & _ & _ & _ & _ & _ & _ & _ & Dnd & Dss & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      Dexp & _ & Dheld & _ & _ & DLB).
    rewrite Hexp in Dexp. cbn [map app] in Dexp.
    pose proof (fr_lines_zr h) as Hzr.
    assert (HT : texts (hs_expected h1) = dr_lines h).
    { unfold texts. rewrite <- (map_map snd bzs), Dexp. apply fr_bzs_lines. exact Hzr. }
    assert (HB : bstream (hs_expected h1) = LB).
    { apply SlotReads.bzs_inj. rewrite (SlotReads.bstream_bzs _ _ Dexp Hzr). symmetry. exact DLB. }
    assert (HLB : length LB = length (with_nul (dr_lines h))).
    { rewrite <- (length_map bz LB). change (map bz LB) with (bzs LB). rewrite DLB. reflexivity. }
    pose proof (f_equal (fun r => snd (fst r)) Hsd) as HO2. cbn [fst snd] in HO2.
    exists (dr_lines h). split; [exact Dheld|]. split; [exact Dnd|]. split.
    { eapply SlotReads.same_set_trans; [exact Dss|]. apply SlotReads.upds_same_set. exact Hss. }
    split; [exact HT|]. split; [exact Dexp|]. split; [exact Hzr|].
    split.
    { pose proof (Heof E0) as (S1 & S2).
      assert (Ho : hs_overlong h = 0 \/ hs_overlong h = 1) by (rewrite <- S1; exact Hsk).
      exact (SlotReads.reads_bound (fr_ru (rm_ent m j0)) h S1 S2 Ho eq_refl). }
    split.
    { rewrite !fr_kt_ksum. etransitivity.
      - apply SlotPass2Aux.p2_ksum_incl; [first [exact Dnd | apply NoDup_ListNoDup; exact Dnd]|].
        intros y Hy. exact (proj1 (Dss y) Hy).
      - apply SlotPass2Aux.p2_ksum_upds. }
    split.
    { intros Hl. rewrite <- HO2. rewrite (fr_sends3 _ _ _ _ _ (fr_dr_ctl3 _ h ev Hl)), fr_ge_out.
      f_equal. rewrite HB. unfold dr_live. rewrite (fr_sl_live3 _ _ Hl). unfold dr_tot.
      destruct (Z.of_nat (length (with_nul (dr_lines h))) =? 0) eqn:Et; cbn [negb]; [|reflexivity].
      apply Z.eqb_eq in Et. destruct LB as [|b LB]; [reflexivity|]. cbn [length] in HLB. lia. }
    split.
    { intros Hd. rewrite <- HO2. rewrite (fr_sends_dead _ _ _ _ _ (fr_dr_ctl_dead _ h ev Hd)).
      unfold dr_live. rewrite (proj1 (fr_sl_dead _ (dr_tot h) Hd)). reflexivity. }
    split; [|right; split; [exact E0 | reflexivity]].
    rewrite <- HO2. etransitivity; [apply fr_sends_len|]. rewrite fr_ge_out.
    destruct (dr_live (lm_c m) h); cbn [app length]; lia.
  - (* the entry was at eof: nothing drained *)
    try rewrite (proj2 (Z.eqb_neq _ _) E1) in Hrr. cbn [andb] in Hrr. destruct Hrr as ((-> & ->) & Hsd).
    pose proof (f_equal (fun r => snd (fst r)) Hsd) as HO2. cbn [fst snd] in HO2.
    assert (HT : texts (hs_expected h) = []) by (unfold texts; rewrite Hexp; reflexivity).
    assert (HW0 : Z.of_nat (length (with_nul [])) = 0) by reflexivity.
    exists []. split; [reflexivity|]. split; [exact Hndk|]. split; [exact Hss|].
    split; [exact HT|]. split; [rewrite Hexp; reflexivity|]. split; [constructor|].
    split; [rewrite HW0; pose proof (Zle_0_nat (length (pending_stream h)));
            pose proof (Zle_0_nat (length (re_U (rm_ent m j0)))); destruct (re_skip (rm_ent m j0) =? 0); lia|].
    split; [rewrite HW0; lia|].
    split.
    { intros Hl. rewrite <- HO2. rewrite (fr_sends3 _ _ _ _ _ Hl), fr_ge_out. unfold bstream. rewrite Hexp.
      reflexivity. }
    split; [intros Hd; rewrite <- HO2; exact (fr_sends_dead _ _ _ _ _ Hd)|].
    split; [|left; reflexivity].
    rewrite <- HO2. etransitivity; [apply fr_sends_len|]. rewrite fr_ge_out. cbn [length with_nul map concat]. lia.
Qed.

(* the relay's lines have no NUL byte when the partial line it carries has none (or is dropped: ls_k = true), and
   the held-key texts the lines add (gesture's key, a prefix of a line) have none either; stated over RelayModel's
   plain terms *)
Lemma lines_nul_free : forall (d : list Z) (st : lstate), (ls_k st = false -> ~ In 0 (ls_w st)) ->
  Forall (fun l => ~ In 0 l) (lines st d).
Proof.
  induction d as [|b d IH]; intros st Hst; [rewrite lines_nil; constructor|].
  rewrite lines_cons.
  destruct (Z.eq_dec b 0) as [-> | Hb].
  - rewrite step_zero. cbn [fst snd].
    assert (H0 : Forall (fun l => ~ In 0 l) (lines (LS [] false) d)) by (apply IH; intros _ []).
    destruct (ls_k st) eqn:Hk; [exact H0|]. constructor; [exact (Hst eq_refl) | exact H0].
  - destruct (ls_k st) eqn:Hk.
    + rewrite (step_nz_k st b Hb Hk). cbn [fst snd]. apply IH. rewrite Hk. intros Hf; discriminate Hf.
    + destruct (Nat.eq_dec (length (ls_w st)) LINE_LIMIT) as [He | He].
      * rewrite (step_nz_full st b Hb Hk He). cbn [fst snd]. apply IH. cbn [ls_k]. intros Hf; discriminate Hf.
      * rewrite (step_nz_add st b Hb Hk He). cbn [fst snd]. apply IH. cbn [ls_k ls_w]. intros _ Hin.
        apply in_app_or in Hin as [Hin | [E | []]]; [exact (Hst eq_refl Hin) | exact (Hb E)].
Qed.
Lemma fr_gesture_sub : forall l k x, gesture l = Some (k, x) -> forall z, In z x -> In z l.
Proof.
  intros l k x Hg z Hz. unfold gesture in Hg. cbv zeta in Hg.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l));
    [|discriminate Hg].
  destruct (last_space_from 0 l) as [j|]; [|discriminate Hg].
  destruct (Nat.ltb 13 j); [|discriminate Hg].
  rewrite <- (firstn_skipn j l). apply in_or_app. left.
  destruct (list_eqb (skipn (S j) l) W_BEGIN); [injection Hg as _ <-; exact Hz|].
  destruct (list_eqb (skipn (S j) l) W_END); [injection Hg as _ <-; exact Hz | discriminate Hg].
Qed.
Lemma upds_nul_free : forall (Ls G : list (list Z)), Forall (fun x => ~ In 0 x) G ->
  Forall (fun l => ~ In 0 l) Ls -> Forall (fun x => ~ In 0 x) (upds G Ls).
Proof.
  unfold upds. induction Ls as [|l Ls IH]; intros G HG HL; cbn [fold_left]; [exact HG|].
  apply Forall_cons_iff in HL as [Hl HL']. apply IH; [|exact HL'].
  unfold upd. destruct (gesture l) as [[[|] x]|] eqn:Eg.
  - destruct (existsb (list_eqb x) G); cbv beta iota; [exact HG|].
    apply Forall_app. split; [exact HG|]. constructor; [|constructor].
    intros Hx. exact (Hl (fr_gesture_sub l _ x Eg 0 Hx)).
  - apply Forall_forall. intros y Hy. apply filter_In in Hy as [Hy _]. rewrite Forall_forall in HG. exact (HG y Hy).
  - exact HG.
Qed.
Lemma fr_nz_bzs : forall x, ~ In (Z_to_bv 8 0) x -> ~ In 0 (bzs x).
Proof.
  intros x Hx Hin. unfold bzs in Hin. apply in_map_iff in Hin as (b & Eb & Hb). apply Hx.
  replace (Z_to_bv 8 0) with b; [exact Hb|]. apply SlotReads.bz_inj. rewrite Eb. reflexivity.
Qed.
Lemma fr_nz_bzs' : forall x, ~ In 0 (bzs x) -> ~ In (Z_to_bv 8 0) x.
Proof.
  intros x Hx Hin. apply Hx. unfold bzs. replace 0 with (bz (Z_to_bv 8 0)) by reflexivity. apply in_map. exact Hin.
Qed.
(* the keys relay_remove leaves on the removed entry have no NUL byte when its unfinished line and its keys have
   none: the drained lines are NUL-free (the unfinished line is the source's partial line while it is read,
   fr_pair_ok), so every key they add is *)
Lemma fr_rm_keys_nz : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  ~ In (Z_to_bv 8 0) (re_U (rm_ent m j0)) ->
  Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) (re_keys (rm_ent m j0)) ->
  Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) (re_keys e1).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr HU HK.
  destruct (fr_rm_pair cx t m si h j0 HRI Hat) as (HP & _ & HE).
  pose proof HP as (_ & _ & _ & Heof & Hss & _). cbn [fst snd] in Heof, Hss.
  pose proof HE as (_ & _ & _ & _ & Hsk).
  destruct (fr_rm_facts cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr)
    as (Ls & _ & _ & Hss1 & _ & _ & _ & _ & _ & _ & _ & _ & HLs).
  assert (HG : Forall (fun x => ~ In 0 x) (texts (hs_held h))).
  { apply Forall_forall. intros y Hy. apply (proj2 (Hss y)) in Hy.
    unfold drain_b_c.keys_texts in Hy. apply in_map_iff in Hy as (k & <- & Hk).
    rewrite Forall_forall in HK. apply fr_nz_bzs. exact (HK k Hk). }
  assert (HL : Forall (fun l => ~ In 0 l) Ls).
  { destruct HLs as [-> | (E0 & ->)]; [constructor|].
    unfold dr_lines. apply lines_nul_free. unfold hs_state. cbn [ls_k ls_w]. intros Hk.
    destruct (Heof E0) as (S1 & S2).
    assert (Hs0 : re_skip (rm_ent m j0) = 0).
    { destruct Hsk as [E | E]; [exact E|]. exfalso. rewrite S1 in E. rewrite E in Hk. discriminate Hk. }
    rewrite <- (S2 Hs0). apply fr_nz_bzs. exact HU. }
  pose proof (upds_nul_free Ls (texts (hs_held h)) HG HL) as HU2. rewrite Forall_forall in HU2.
  apply Forall_forall. intros k Hk. apply fr_nz_bzs'. apply HU2. apply (proj1 (Hss1 _)).
  unfold drain_b_c.keys_texts. apply (in_map (fun k => bzs (gestures_end_b_c.key_text k))). exact Hk.
Qed.

(* RI_rm_cnl_pre with K14 (every key text >= 14 bytes, rm_mfacts conjunct 2): the plain proof's p4_cnl_bound route
   (19 * keys <= keys_total, 21 * count_begin <= the drained bytes, both within the row's cost < 2 ^ 26) *)
Lemma fr_rm_cnl_pre_core : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (rm_ent m j0)) ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  AREC * rm_capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr K14.
  destruct (fr_rm_pair cx t m si h j0 HRI Hat) as (HP & HC & _).
  pose proof HP as (_ & _ & _ & _ & Hss & Hndh & _ & _ & Hcap & _). cbn [fst snd] in Hss, Hndh, Hcap.
  destruct (fr_rm_facts cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr)
    as (Ls & Hheld & _ & _ & HT & Hexp & _ & Hwn & Hkt & Hlive & _ & Hlen & _).
  pose proof (fr_a12_held_keys _ _ Hndh Hss) as HHK.
  pose proof (SlotReads.keys_total_count _ K14) as K19.
  pose proof (SlotReads.count_begin_bytes Ls) as CB.
  pose proof (SlotReads.lines_count Ls) as LC.
  pose proof (SlotReads.keys_out_length (re_keys e1)) as KO.
  unfold fr_pair_cost in HC. cbn [fst] in HC.
  assert (Hnexp : hl_n (hs_expected h1) = Z.of_nat (length Ls)).
  { unfold hl_n. rewrite <- (length_map snd), Hexp, length_map. reflexivity. }
  assert (Hb : hl_n (hs_held h) + Z.of_nat (count_begin Ls) < 2 ^ 22).
  { pose proof (Zle_0_nat (length (pending_stream h))). pose proof (Zle_0_nat (length (re_U (rm_ent m j0)))).
    destruct (re_skip (rm_ent m j0) =? 0); lia. }
  rewrite Hheld, HT. split; [exact Hndh|]. split.
  { rewrite Hnexp. pose proof (Zle_0_nat (length (pending_stream h))).
    pose proof (Zle_0_nat (length (re_U (rm_ent m j0)))). destruct (re_skip (rm_ent m j0) =? 0); lia. }
  split; [exact Hb|]. split.
  { unfold rm_capb, AREC. rewrite HT. lia. }
  split.
  { pose proof (Zle_0_nat (length (pending_stream h))). pose proof (Zle_0_nat (length (re_U (rm_ent m j0)))).
    pose proof (fr_keys_total_nonneg (re_keys (rm_ent m j0))).
    assert (Z.of_nat (length O2) <= Z.of_nat (length (with_nul Ls)) + gestures_end_b_c.keys_total (re_keys e1)) by lia.
    destruct (re_skip (rm_ent m j0) =? 0); lia. }
  intros Hg. pose proof HRI as (_ & _ & _ & (G0 & _)).
  exists (gestures_end_b_c.keys_out (re_keys e1)). exact (Hlive (G0 Hg)).
Qed.

(* the shutdown check's run never reads a NUL byte: every record it matched (all of them, at want = length) has a
   NUL-free text *)
Lemma fr_split_nul_nz : forall d l d', split_nul d = Some (l, d') -> ~ In (Z_to_bv 8 0) l.
Proof.
  induction d as [|b d IH]; intros l d' Hs; cbn [split_nul] in Hs; [discriminate Hs|].
  revert Hs. destruct (Z.eqb_spec (bv_unsigned b) 0) as [_ | Hb]; intros Hs.
  - injection Hs as <- _. intros [].
  - revert Hs. destruct (split_nul d) as [[l0 r]|] eqn:E; intros Hs; [|discriminate Hs]. injection Hs as <- <-.
    intros [Eb | Hin].
    + apply Hb. rewrite Eb. reflexivity.
    + exact (IH l0 r eq_refl Hin).
Qed.
Lemma fr_find_text_some : forall y rs i, find_text y rs = Some i ->
  (i < length rs)%nat /\ bzs (snd (nth i rs (0, []))) = bzs y.
Proof.
  intros y rs. induction rs as [|r rs IH]; intros i Hf; cbn [find_text] in Hf; [discriminate Hf|].
  revert Hf. destruct (list_eqb (bzs (snd r)) (bzs y)) eqn:E; intros Hf.
  - injection Hf as <-.
    assert (X : bzs (snd r) = bzs y).
    { revert E. unfold list_eqb. destruct (list_eq_dec Z.eq_dec (bzs (snd r)) (bzs y)) as [X|_]; intros E;
        [exact X | discriminate E]. }
    cbn [nth length]. split; [lia | exact X].
  - revert Hf. destruct (find_text y rs) as [i0|] eqn:Ef; cbn [option_map]; intros Hf; [|discriminate Hf].
    injection Hf as <-. destruct (IH i0 eq_refl) as (Hi & Ht). cbn [length nth]. split; [lia | exact Ht].
Qed.
Lemma fr_ends_nz : forall w rs d x, ends_run [] rs d w = Some x -> w = length rs ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) rs.
Proof.
  induction w as [|w IH]; intros rs d x Hr Hw.
  - destruct rs; [constructor | discriminate Hw].
  - cbn [ends_run] in Hr. revert Hr.
    destruct (split_nul d) as [[l d']|] eqn:Es; [|intros Hr; discriminate Hr]. cbv beta iota zeta.
    destruct (Nat.leb 4 (length l) && list_eqb (bzs (skipn (length l - 4)%nat l)) (bzs END4) && prefixb [] l);
      [|intros Hr; discriminate Hr]. cbv beta iota zeta.
    destruct (find_text (firstn (length l - 4)%nat l) rs) as [i|] eqn:Ef; [|intros Hr; discriminate Hr].
    cbv beta iota zeta.
    destruct (ends_run [] (drop_nth i rs) d' w) as [y|] eqn:Er; [|intros Hr; discriminate Hr]. intros _.
    destruct (fr_find_text_some _ _ _ Ef) as (Hi & Ht).
    assert (Hd : Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (drop_nth i rs)).
    { apply (IH _ _ _ Er). unfold drop_nth. rewrite length_app, length_firstn, length_skipn. lia. }
    assert (Hn : ~ In (Z_to_bv 8 0) (snd (nth i rs (0, [])))).
    { apply SlotReads.bzs_inj in Ht. rewrite Ht. intros Hin. apply (fr_split_nul_nz _ _ _ Es).
      rewrite <- (firstn_skipn (length l - 4)%nat l). apply in_or_app. left. exact Hin. }
    rewrite (fr_split_nth _ rs i (0, []) Hi). unfold drop_nth in Hd. apply Forall_app in Hd as [H1 H2].
    apply Forall_app. split; [exact H1|]. constructor; [exact Hn | exact H2].
Qed.
(* the key texts are NUL-free when the held list they match is *)
Lemma fr_keys_nz : forall ks (rs : list (Z * list byte)), Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) rs ->
  (forall y, In y (drain_b_c.keys_texts ks) -> In y (map (fun r => bzs (snd r)) rs)) ->
  Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) ks.
Proof.
  intros ks rs HR HS. apply Forall_forall. intros k Hk HZ.
  assert (Hy : In (bzs (gestures_end_b_c.key_text k)) (drain_b_c.keys_texts ks))
    by (unfold drain_b_c.keys_texts; apply (in_map (fun k => bzs (gestures_end_b_c.key_text k))); exact Hk).
  apply HS in Hy. apply in_map_iff in Hy as (r & Er & Hr).
  apply SlotReads.bzs_inj in Er. rewrite Forall_forall in HR. apply (HR r Hr). rewrite Er. exact HZ.
Qed.
(* the check over the remove arm's stream at gone = 0: skipn rm_A1 O2 is the new keys' ends *)
Lemma fr_rm_ends : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 ->
  rm_A1 m h1 <= Z.of_nat (length O2) /\
  skipn (Z.to_nat (rm_A1 m h1)) O2 = gestures_end_b_c.keys_out (re_keys e1) /\
  NoDup (drain_b_c.keys_texts (re_keys e1)) /\ same_set (drain_b_c.keys_texts (re_keys e1)) (texts H') /\
  Z.of_nat (length O2) = rm_A1 m h1 + Z.of_nat (length (gestures_end_b_c.keys_out (re_keys e1))).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg.
  destruct (fr_rm_facts cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr)
    as (Ls & Hheld & Hndk & Hss & HT & _ & _ & _ & _ & Hlive & _ & _).
  pose proof HRI as (_ & _ & _ & (G0 & _)). specialize (Hlive (G0 Hg)).
  destruct Hcnl as (_ & _ & _ & _ & HTH & _).
  assert (HA : rm_A1 m h1 = Z.of_nat (length (bstream (hs_expected h1)))) by (unfold rm_A1; rewrite Hg; reflexivity).
  rewrite HA, Hlive, Nat2Z.id, fr_skipn_len, length_app, Nat2Z.inj_add.
  split; [lia|]. split; [reflexivity|]. split; [exact Hndk|]. split; [|reflexivity].
  rewrite HTH, Hheld, HT. exact Hss.
Qed.
Lemma fr_rm_cshe_pre_core : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 -> Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) (re_keys e1) ->
  rm_A1 m h1 <= Z.of_nat (length O2) /\
  ends_run [] (hl_recs H') (skipn (Z.to_nat (rm_A1 m h1)) O2) (want_of [] (hl_recs H')) <> None.
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg Hnz.
  pose proof Hcnl as (_ & _ & _ & HndH & _).
  destruct (fr_rm_ends cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg) as (Hle & Hsk & Hndk & Hss & _).
  split; [exact Hle|]. rewrite Hsk, SlotReads.want_of_nil, <- (app_nil_r (gestures_end_b_c.keys_out (re_keys e1))).
  destruct (SlotReads.ends_run_keys (re_keys e1) (hl_recs H') [])
    as (rs' & ds & E).
  all: try first [exact Hndk | exact (proj1 (NoDup_ListNoDup _) Hndk) | exact (proj2 (NoDup_ListNoDup _) Hndk)
                 | exact HndH | exact (proj1 (NoDup_ListNoDup _) HndH) | exact (proj2 (NoDup_ListNoDup _) HndH)
                 | exact Hss | exact Hnz].
  rewrite E. discriminate.
Qed.
Lemma fr_rm_csd_core : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  (lm_gn m = 0 \/ lm_gn m = 1) ->
  rm_A1 m h1 + cc = Z.of_nat (length O2).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc HRI Hat Hrr Hcnl Hcs Hg.
  pose proof HRI as (_ & _ & _ & (G0 & G1)).
  destruct Hcs as (_ & _ & _ & _ & [(Hg1 & _ & _ & Hcc) | (Hg0 & Hrun)]).
  - (* gone: nothing was sent *)
    assert (E1 : lm_gn m = 1) by lia.
    destruct (fr_rm_facts cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr)
      as (Ls & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdead & _).
    rewrite (Hdead (G1 E1)), Hcc. unfold rm_A1. rewrite E1. reflexivity.
  - (* live: the check consumed the new keys' ends *)
    cbn [hs_held set_exp_held] in Hrun.
    pose proof Hcnl as (_ & _ & _ & HndH & _).
    destruct (fr_rm_ends cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg0)
      as (_ & Hsk & Hndk & Hss & Hlen).
    rewrite Hsk, SlotReads.want_of_nil in Hrun.
    assert (Hnz : Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H')) by exact (fr_ends_nz _ _ _ _ Hrun eq_refl).
    rewrite <- (app_nil_r (gestures_end_b_c.keys_out (re_keys e1))) in Hrun.
    destruct (SlotReads.ends_run_keys (re_keys e1) (hl_recs H') [])
      as (rs' & ds' & E).
    all: try first [exact Hndk | exact (proj1 (NoDup_ListNoDup _) Hndk) | exact (proj2 (NoDup_ListNoDup _) Hndk)
                   | exact HndH | exact (proj1 (NoDup_ListNoDup _) HndH) | exact (proj2 (NoDup_ListNoDup _) HndH)
                   | exact Hss | exact (fr_keys_nz _ _ Hnz (fun y Hy => proj1 (Hss y) Hy))].
    rewrite E in Hrun. injection Hrun as _ _ <-. lia.
Qed.

(* ================================================================== the four rows at their restated texts
   (a working branch 3f40808c334, W_LLVMFuzzerTestOneInput_top_x.v RI_exit_ends / RI_rm_cnl_pre /
   RI_rm_cshe_pre / RI_rm_csd), at RINV := fr_RINV, with ReplyRINV.v's copies of _remove.v's model functions *)
Lemma fr_a12_F2_l : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall x, In x l1 -> exists y, In y l2 /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists y; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (y' & Hy' & HR). exists y'. split; [right; exact Hy' | exact HR].
Qed.
Lemma RI_exit_ends_holds : forall cx t m, fr_RINV cx t m -> (0 < length (lm_es m))%nat ->
  0 <= lm_gn m <= 1 ->
  (forall i h, nth i (lm_hs m) None = Some h -> Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))) ->
  lx_ends_run (lm_gn m) (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).
Proof.
  intros cx t m HRI _ Hg Hnul. apply (fr_exit_ends cx t m HRI); [lia|].
  pose proof HRI as (_ & HR & _ & _). destruct HR as (_ & _ & _ & _ & hj & HF & _ & _ & _).
  apply Forall_forall. intros e He.
  destruct (fr_a12_F2_l _ _ _ _ _ HF e He) as (p & _ & HRp).
  destruct HRp as (_ & Hsn & _ & _ & Hss & _).
  exact (fr_keys_nz (re_keys e) (hl_recs (hs_held (fst p))) (Hnul _ _ Hsn) (fun y Hy => proj1 (Hss y) Hy)).
Qed.
Lemma RI_rm_cnl_pre_holds : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Forall (fun e => Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e)) (lm_es m) ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  AREC * rm_capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr HK.
  apply (fr_rm_cnl_pre_core cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr).
  rewrite Forall_forall in HK. apply HK. pose proof Hat as (_ & _ & _ & _ & _ & _ & Hj & _).
  unfold rm_ent. apply nth_In. exact Hj.
Qed.
Lemma RI_rm_cshe_pre_holds : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H') ->
  rm_A1 m h1 <= Z.of_nat (length O2) /\
  ends_run [] (hl_recs H') (skipn (Z.to_nat (rm_A1 m h1)) O2) (want_of [] (hl_recs H')) <> None.
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg Hnz.
  apply (fr_rm_cshe_pre_core cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg).
  destruct (fr_rm_ends cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg) as (_ & _ & _ & Hss & _).
  exact (fr_keys_nz _ _ Hnz (fun y Hy => proj1 (Hss y) Hy)).
Qed.
Lemma RI_rm_csd_holds : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  0 <= lm_gn m <= 1 ->
  rm_A1 m h1 + cc = Z.of_nat (length O2).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc HRI Hat Hrr Hcnl Hcs Hg.
  exact (fr_rm_csd_core cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc HRI Hat Hrr Hcnl Hcs ltac:(lia)).
Qed.

(* ================================================================== the six `_holds`' premises are satisfiable
   (VERIFY rule 10): from any call context, a state that meets every premise of the row *)
Definition a12_ent0 : rentry := RE 100 0 0 a12_pad 0 0 0 0 0 a12_pad (a12_ks1 a12_a) [] [].
Definition a12_m0 : lmod :=
  LM 6 [Some (a12_src (a12_H1 a12_a)); None; None; None] 0 [a12_ent0] (CTL 3 0 0 0 0) [] 0 0 0 0 1.
(* the open entry's state: fr_pair_ok's eof clause is met (skip 0 = overlong 0, the unfinished line [] = hs_W []) *)
Lemma a12_RINV0 : forall cx0, fr_RINV (a12_cx cx0 10 a12_pl) 0 a12_m0.
Proof.
  intros cx0. split; [|split; [|split]].
  - unfold fr_count, nopen, OPS_MAX, a12_m0. cbn [lm_nfd lm_hs List.filter length Z.of_nat]. lia.
  - unfold fr_relay, a12_m0. cbn [lm_hs lm_es lm_nfd lm_k length].
    split; [reflexivity|].
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split; [constructor; [cbn; lia | constructor]|].
    split.
    { constructor; [|constructor]. unfold fr_entry_ok, a12_ent0, a12_pad.
      cbn [re_eof re_pad1 re_pad2 re_keys re_skip length].
      split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros [] | left; reflexivity]. }
    exists [(a12_src (a12_H1 a12_a), 0%nat)].
    split.
    { constructor; [|constructor]. unfold fr_pair_ok, a12_src, a12_ent0.
      cbn [fst snd nth lm_hs re_eof re_fd hs_fd re_keys hs_held hs_expected hs_off hl_recs hl_cap].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; split; [reflexivity | intros _; reflexivity]|].
      split; [intros y; split; intros Hy; exact Hy|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split; [reflexivity|]. split; [left; reflexivity|]. split; [cbn; lia|].
      split; [unfold pending_stream, a12_E0; cbn [hs_pending hl_recs length Z.of_nat]; unfold SlotInv.WRITE_MAX; lia
             | lia]. }
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split.
    { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *; first [discriminate Ho | reflexivity | lia]. }
    unfold fr_cost, fr_pair_cost, a12_ent0, a12_src, pending_stream, a12_E0, a12_ks1, a12_a,
      gestures_end_b_c.keys_total, gestures_end_b_c.key_text.
    cbn. lia.
  - unfold a12_cx. cbn [c_n]. lia.
  - unfold fr_gone, a12_m0. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. split; intros E; [repeat split | discriminate E].
Qed.
Lemma a12_rm_at0 : forall cx0, rm_at (a12_cx cx0 10 a12_pl) a12_m0 0 (a12_src (a12_H1 a12_a)) 0.
Proof.
  intros cx0. unfold rm_at, a12_m0. cbn [lm_k lm_O lm_hs lm_es length].
  split; [unfold a12_cx; cbn [c_n]; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply a12_pick|].
  split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. intros q Hq. lia.
Qed.
Lemma a12_a_nz : ~ In (Z_to_bv 8 0) a12_a.
Proof. intros [X | []]. apply (f_equal bv_unsigned) in X. vm_compute in X. discriminate X. Qed.
Definition a12_k14 : list byte := repeat (Z_to_bv 8 97) 14.
Definition a12_pl30 : list byte := repeat (Z_to_bv 8 4) 30.
Definition a12_r14 : ctl * list byte * Z := sl_sends 0 (CTL 3 0 0 0 0) [] 0 (ge_bytes (a12_ks1 a12_k14)).
Lemma RI_exit_slots_sat : lfcx -> exists cx t m, fr_RINV cx t m.
Proof. intros cx0. exists (a12_cx cx0 10 a12_pl), 0, a12_m0. apply a12_RINV0. Qed.
Lemma RI_rm_rr_pair_sat : lfcx -> exists cx t m si h j0,
  fr_RINV cx t m /\ rm_at cx m si h j0 /\ re_eof (rm_ent m j0) = 0.
Proof.
  intros cx0. exists (a12_cx cx0 10 a12_pl), 0, a12_m0, 0%nat, (a12_src (a12_H1 a12_a)), 0%nat.
  split; [apply a12_RINV0|]. split; [apply a12_rm_at0 | reflexivity].
Qed.
Lemma RI_exit_ends_sat : lfcx -> exists cx t m, fr_RINV cx t m /\ (0 < length (lm_es m))%nat /\ 0 <= lm_gn m <= 1 /\
  (forall i h, nth i (lm_hs m) None = Some h -> Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))).
Proof.
  intros cx0. exists (a12_cx cx0 10 a12_pl), 0, (a12_m 6 (a12_H1 a12_a) (a12_ks1 a12_a) 0).
  split; [apply a12_RINV1; [reflexivity | lia]|]. split; [cbn; lia|]. split; [cbn; lia|].
  intros i h E. destruct i as [|[|[|[|i]]]]; cbn [a12_m lm_hs nth] in E;
    [| discriminate E | discriminate E | discriminate E | destruct i; discriminate E].
  injection E as <-. constructor; [exact a12_a_nz | constructor].
Qed.
Lemma RI_rm_cnl_pre_sat : lfcx -> exists cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m /\ rm_at cx m si h j0 /\ rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 /\
  Forall (fun e => Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e)) (lm_es m).
Proof.
  intros cx0. exists (a12_cx cx0 30 a12_pl30), 0, (a12_m 19 (a12_H1 a12_k14) (a12_ks1 a12_k14) 0), 0%nat,
    (a12_src (a12_H1 a12_k14)), 0%nat, (a12_ent (a12_ks1 a12_k14)), (a12_src (a12_H1 a12_k14)), 0, [],
    (fst (fst a12_r14)), (snd (fst a12_r14)), (snd a12_r14).
  split.
  { apply a12_RINV; try lia.
    - apply NoDup_ListNoDup. repeat constructor. intros [].
    - intros y. split; intros Hy; exact Hy.
    - apply NoDup_ListNoDup. repeat constructor. intros [].
    - cbn. lia.
    - unfold gestures_end_b_c.keys_total, a12_ks1, a12_k14, gestures_end_b_c.key_text. cbn. lia. }
  split; [apply a12_rm_at; [lia | lia | reflexivity]|].
  split; [apply a12_rr_ok; reflexivity|].
  constructor; [|constructor]. constructor; [|constructor]. cbn. lia.
Qed.
Lemma RI_rm_cshe_pre_sat : lfcx -> exists cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  fr_RINV cx t m /\ rm_at cx m si h j0 /\ rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 /\ rm_cnl_ok h1 E' H' /\
  lm_gn m = 0 /\ Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H').
Proof.
  intros cx0. exists (a12_cx cx0 10 a12_pl), 0, (a12_m 6 (a12_H1 a12_a) (a12_ks1 a12_a) 0), 0%nat,
    (a12_src (a12_H1 a12_a)), 0%nat, (a12_ent (a12_ks1 a12_a)), (a12_src (a12_H1 a12_a)), 0, [],
    (fst (fst (a12_r a12_a))), (snd (fst (a12_r a12_a))), (snd (a12_r a12_a)), a12_E0, (a12_H1 a12_a).
  split; [apply a12_RINV1; [reflexivity | lia]|]. split; [apply a12_rm_at1|].
  split; [apply a12_rr_ok; reflexivity|]. split; [apply a12_cnl_ok, a12_nd1|]. split; [reflexivity|].
  constructor; [exact a12_a_nz | constructor].
Qed.
Lemma RI_rm_csd_sat : lfcx -> exists cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  fr_RINV cx t m /\ rm_at cx m si h j0 /\ rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 /\ rm_cnl_ok h1 E' H' /\
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc /\ 0 <= lm_gn m <= 1.
Proof.
  intros cx0. exists (a12_cx cx0 10 a12_pl), 0, (a12_m 6 (a12_H1 a12_a) (a12_ks1 a12_a) 0), 0%nat,
    (a12_src (a12_H1 a12_a)), 0%nat, (a12_ent (a12_ks1 a12_a)), (a12_src (a12_H1 a12_a)), 0, [],
    (fst (fst (a12_r a12_a))), (snd (fst (a12_r a12_a))), (snd (a12_r a12_a)), a12_E0, (a12_H1 a12_a),
    (HL 0 8 [] []), [(0, a12_a)], 6.
  split; [apply a12_RINV1; [reflexivity | lia]|]. split; [apply a12_rm_at1|].
  split; [apply a12_rr_ok; reflexivity|]. split; [apply a12_cnl_ok, a12_nd1|].
  split; [|cbn; lia].
  unfold rm_cshe_ok. split; [reflexivity|]. split; [reflexivity|]. split; [apply NoDup_ListNoDup; constructor|].
  split; [lia|]. right. split; [reflexivity|]. vm_compute. reflexivity.
Qed.

End rinv_a12.
