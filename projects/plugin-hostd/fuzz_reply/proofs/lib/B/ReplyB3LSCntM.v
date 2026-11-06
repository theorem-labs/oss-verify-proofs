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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyB3Base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3LSCntL.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3 ReplyLSCntL ReplyB3LS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).

Lemma cnt_sec_le_len : forall l, cnt_sec l <= Z.of_nat (length l).
Proof.
  induction l as [|[a n] l IH]; [reflexivity|]. rewrite cnt_sec_cons. cbn [length].
  destruct (Psec n); lia.
Qed.
Lemma cnt_sec_small : forall l, Forall (fun b => 0 <= snd b < 64513) l -> cnt_sec l = 0.
Proof.
  induction l as [|[a n] l IH]; intros H; [reflexivity|]. inversion H as [|? ? Hb Hl]; subst.
  rewrite cnt_sec_cons, (IH Hl). cbn [snd] in Hb. rewrite (is_sec_iff n ltac:(lia)).
  destruct (Z.leb_spec 64513 n); lia.
Qed.
Lemma cnt_sec_concat : forall (A : Type) (f : A -> list (Z * Z)) (g : A -> Z) l,
  (forall x, In x l -> cnt_sec (f x) <= g x) -> cnt_sec (concat (map f l)) <= zsum (map g l).
Proof.
  intros A f g l. induction l as [|x l IH]; intros H; [reflexivity|].
  cbn [map concat fold_right]. rewrite cnt_sec_app.
  pose proof (H x (or_introl eq_refl)). pose proof (IH (fun y Hy => H y (or_intror Hy))). lia.
Qed.
Lemma zsum_const : forall (A : Type) (c : Z) (l : list A), zsum (map (fun _ => c) l) = c * Z.of_nat (length l).
Proof. intros A c l. induction l as [|x l IH]; cbn [map fold_right length]; [lia|]. rewrite IH. lia. Qed.

Lemma cnt_sec_alist_lines : forall l, texts_ok l -> cnt_sec (alist_blks l) <= 1.
Proof.
  intros l Hl. unfold alist_blks. rewrite cnt_sec_app.
  assert (V : cnt_sec (if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]) <= 1).
  { destruct (hl_cap l =? 0); [rewrite cnt_sec_nil; lia|]. rewrite cnt_sec_cons, cnt_sec_nil; destruct (Psec _); lia. }
  rewrite (cnt_sec_small (map _ (hl_recs l))); [lia|]. apply Forall_map. eapply Forall_impl; [|exact Hl].
  intros r Hr. cbn [snd]. unfold APARTIAL in Hr. lia.
Qed.
Lemma cnt_sec_alist : forall l, cnt_sec (alist_blks l) <= 1 + hl_n l.
Proof.
  intros l. unfold alist_blks, hl_n. rewrite cnt_sec_app.
  assert (V : cnt_sec (if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]) <= 1).
  { destruct (hl_cap l =? 0); [rewrite cnt_sec_nil; lia|]. rewrite cnt_sec_cons, cnt_sec_nil; destruct (Psec _); lia. }
  pose proof (cnt_sec_le_len (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l))) as T.
  rewrite length_map in T. lia.
Qed.
Lemma cnt_sec_entry : forall e, 0 <= re_cap e <= 16384 ->
  Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e) ->
  cnt_sec (aentry_blks e) <= 1.
Proof.
  intros e Hc Hk. unfold aentry_blks. rewrite !cnt_sec_app.
  assert (B1 : cnt_sec (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) = 0).
  { destruct (re_cap e =? 0); [reflexivity|]. apply cnt_sec_small. constructor; [cbn; lia | constructor]. }
  assert (B2 : cnt_sec (if re_hp e =? 0 then [] else [(re_hp e, re_kh e)]) <= 1).
  { destruct (re_hp e =? 0); [rewrite cnt_sec_nil; lia|]. rewrite cnt_sec_cons, cnt_sec_nil; destruct (Psec _); lia. }
  rewrite (cnt_sec_small (map _ (re_keys e))); [lia|]. apply Forall_map. eapply Forall_impl; [|exact Hk].
  intros k Hk'. cbn [snd]. unfold APARTIAL in Hk'. lia.
Qed.
Lemma cnt_sec_slot : forall o, match o with Some h => texts_ok (hs_expected h) /\ texts_ok (hs_held h) | None => True end ->
  cnt_sec (slot_blks o) <= 3 + slot_npend o.
Proof.
  intros [h|] Ho; cbn [slot_blks slot_npend]; [|rewrite cnt_sec_nil; lia]. destruct Ho as (He & Hh).
  unfold asrc_blks. rewrite cnt_sec_cons, !cnt_sec_app.
  assert (Ea : Psec APARTIAL = false) by (rewrite is_sec_iff by (unfold APARTIAL; lia); reflexivity). rewrite Ea.
  pose proof (cnt_sec_alist (hs_pending h)). pose proof (cnt_sec_alist_lines _ He). pose proof (cnt_sec_alist_lines _ Hh).
  lia.
Qed.

Lemma zsum_3_npend : forall hs, zsum (map (fun o => 3 + slot_npend o) hs) = 3 * Z.of_nat (length hs) + zsum (map slot_npend hs).
Proof. induction hs as [|o hs IH]; cbn [map fold_right length]; [lia|]. rewrite IH. lia. Qed.

Lemma cnt_sec_model : forall m, msz_ok (lm_es m) (lm_hs m) ->
  cnt_sec (model_blks m) <= npend m + Z.of_nat (length (lm_es m)) + 3 * Z.of_nat (length (lm_hs m)) + 1.
Proof.
  intros m (He & Hh). unfold model_blks. rewrite cnt_sec_cons, !cnt_sec_app.
  assert (Ea : Psec ATABLE = false) by (rewrite is_sec_iff by (unfold ATABLE; lia); reflexivity). rewrite Ea.
  assert (CE : cnt_sec (concat (map aentry_blks (lm_es m))) <= zsum (map (fun _ => 1) (lm_es m))).
  { apply cnt_sec_concat. intros e Hin. rewrite Forall_forall in He. destruct (He e Hin) as (Hc & Hk).
    exact (cnt_sec_entry e Hc Hk). }
  assert (CS : cnt_sec (concat (map slot_blks (lm_hs m))) <= zsum (map (fun o => 3 + slot_npend o) (lm_hs m))).
  { apply cnt_sec_concat. intros o Hin. rewrite Forall_forall in Hh. exact (cnt_sec_slot o (Hh o Hin)). }
  assert (Z1 : zsum (map (fun o => 3 + slot_npend o) (lm_hs m)) = 3 * Z.of_nat (length (lm_hs m)) + npend m)
    by (unfold npend; apply zsum_3_npend).
  rewrite zsum_const in CE.
  assert (CO : cnt_sec (aout_blks (lm_cap m) (lm_out m)) <= 1).
  { unfold aout_blks. destruct (lm_cap m =? 0); [rewrite cnt_sec_nil; lia|].
    rewrite cnt_sec_cons, cnt_sec_nil; destruct (Psec (lm_cap m)); lia. }
  lia.
Qed.

Section cut.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CALL_ROOM_B : Z.
Lemma cnt_sec_input : forall (cx : lfcx (rc := rc)), cnt_sec (input_blks cx) <= 1.
Proof.
  intros cx. unfold input_blks. destruct (c_n cx =? 0); [rewrite cnt_sec_nil; lia|].
  rewrite cnt_sec_cons, cnt_sec_nil. destruct (Psec (c_n cx)); lia.
Qed.
Lemma fr_LS3c_sec_cut : forall cx t m ly S, fr_LS3c B CALL_ROOM_B cx t m ly S -> msz_ok (lm_es m) (lm_hs m) ->
  cnt_sec (ablocks B ly S) <= t + Z.of_nat (length (lm_es m)) + 3 * Z.of_nat (length (lm_hs m)) + 2 + SEC0.
Proof.
  intros cx t m ly S (_ & (C1 & _ & C3)) Hm.
  change (cnt_sec (ablocks B ly S) - cnt_sec (model_blks m) - cnt_sec (input_blks cx) <= SEC0) in C1.
  pose proof (cnt_sec_model m Hm). pose proof (cnt_sec_input cx). lia.
Qed.
End cut.
