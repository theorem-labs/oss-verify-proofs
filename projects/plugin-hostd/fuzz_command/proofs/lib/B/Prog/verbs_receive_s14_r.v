(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run-side helpers of the arms S14 QCLEAR, S15 POLICY and S16 LV2 of the walk
   of verbs_receive on the ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v): the
   symbolic regions the arms seed, the registers a run keeps, the spill word at a route state, the UBSan trap branch
   refuted from the frame's bounds, and the event, meter and live-byte budgets of the three recorder callees at the
   entry recorder (no call recorded yet). The B twin of the A walk's verbs_receive_s14_r.v
   (a working branch): B keeps tok in the spill slot s1+40 and reloads it into s3 before each
   arm (A kept it in s6), and B's recorder callees call record() and arg_s() (xmalloc) where A inlined record() and
   called xstrdup, so the budgets unfold B's constants. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c record_c arg_s_c hand_back_c answer_c
sup_quarantine_clear_c sup_policy_set_c sup_lv2_worker_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the regions the arms seed: the spill slot s1+40 (tok = F+32, atom 32), and the words of tok[] at tok+8 / tok+16,
   based at atom 32 (B's `ld s3,40(s1)` gives s3 that atom, and the arms read tok[1], tok[2] through s3) *)
Definition v14_spill_r : YP09.region :=
YP09.mkRegion (Some 9%nat) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 32 0))].
Definition v14_tok1_r (a : nat) : YP09.region :=
YP09.mkRegion (Some 32%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff a 0))].
Definition v14_tok2_r (a b : nat) : YP09.region :=
YP09.mkRegion (Some 32%nat) 8 24 0 0 [YP09.mkChunk 8 (CVal 8 (SOff a 0)); YP09.mkChunk 16 (CVal 8 (SOff b 0))].

(* the text of a recorder stub is at most 28 bytes (the plain proof's verbs_receive_br.v stub_text_len) *)
Lemma v14_stub_len : forall R fn As v ch, -2^31 <= r_code R < 2^31 ->
(length (snd (rec_stub R fn As (shape_of v) ch)) <= 28)%nat.
Proof.
intros R fn As v ch HC. unfold rec_stub. rewrite rec_answer_text.
assert (E : r_code (rec_record R fn As) = r_code R) by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
destruct (r_refuse (rec_record R fn As) =? 0).
- exact (proj1 (proj2 (shape_of_facts v))).
- rewrite E. pose proof (resp_length (r_code R) HC). lia.
Qed.
Lemma v14_spill0 : forall R, r_calls R = [] -> rec_spill_frees R = 0.
Proof. intros R H. unfold rec_spill_frees. rewrite H. reflexivity. Qed.

(* the UBSan check before a load through tok (0x8d4f8, 0x8d52c/0x8d534, 0x8d57c/0x8d584: `bltu a0,s3,0x8d938` with
   a0 = -9 or -17 and s3 = tok = F+32, atom 32): taken only if tok + 8 (+ 16) wraps, which the frame's bounds
   (frames_bounds: F + 1024 <= alloc_ceiling < 2^47) refute *)
Ltac v14_trap Hc E32 :=
rewrite branch_ltu_U in Hc; rewrite (U_atom _ 32 _ E32) in Hc by lia;
lazymatch type of Hc with
| context [U ?E' (SLit ?z)] => let v := eval vm_compute in (U E' (SLit z)) in change (U E' (SLit z)) with v in Hc
end;
apply Z.ltb_lt in Hc; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma v14_val_mem_of_aval : forall H mem a n v, aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte SEGS H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma v14_kept_regs : forall E ss ms (regs0 : bvmap 5 word) extra (zs : list Z),
st_ok SEGS E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (map (Z_to_bv 5) zs) = true ->
forall r, In r zs -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss ms regs0 extra zs HS HA Hl r Hr.
apply (regs_kept_of_st_ok SEGS E ss ms regs0 extra (map (Z_to_bv 5) zs) HS HA Hl). apply in_map. exact Hr.
Qed.
Lemma v14_env_agree : forall (regs : bvmap 5 word) extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Lemma v14_code_range : forall ly S rd R O, rec_repA B ly S rd R O -> -2^31 <= r_code R < 2^31.
Proof. intros ly S rd R O (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HC & _) & _) & _). exact HC. Qed.

Lemma v14_rv_get : forall (regs : bvmap 5 word) l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. unfold vr_rv in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.
Lemma v14_rv_intro : forall (regs : bvmap 5 word) l, (forall r v, In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v) -> vr_rv regs l.
Proof. intros regs l H. unfold vr_rv. apply Forall_forall. intros [r v] Hin. exact (H r v Hin). Qed.
(* the registers at a state after a run: vr_base kept, and each listed register either kept from the route state's
   list or of a known value *)
Lemma v14_rv_keep : forall e (regs regsc : bvmap 5 word) rl rl',
vr_rv regsc (vr_base B e ++ rl) ->
(forall r, In r [2; 3; 4; 8; 9] -> getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
(forall r v, In (r, v) rl' ->
  (In (r, v) rl /\ getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) \/ getr regs (Z_to_bv 5 r) = w64 v) ->
vr_rv regs (vr_base B e ++ rl').
Proof.
intros e regs regsc rl rl' Hrv Hb Hl. apply v14_rv_intro. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
- assert (Hr : In r [2; 3; 4; 8; 9]).
  { unfold vr_base in Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _; cbn; tauto. }
  rewrite (Hb r Hr). apply (v14_rv_get regsc _ _ _ Hrv). apply in_or_app; left; exact Hin.
- destruct (Hl r v Hin) as [[H1 H2] | H]; [|exact H].
  rewrite H2. apply (v14_rv_get regsc _ _ _ Hrv). apply in_or_app; right; exact H1.
Qed.

(* the spill word the arms reload: s1+40 holds tok = F+32 (B's map) *)
Lemma v14_spill_at : forall e (W : world SEGS) m F q c, vr_spill e W m (vr_sl3 F q c) ->
aval_mem (rdW W m) (vr_s1 e + 40) 8 (F + 32).
Proof.
intros e W m F q c H. unfold vr_spill in H. rewrite Forall_forall in H.
exact (H (40, F + 32) ltac:(cbn; tauto)).
Qed.

(* the budgets of the three recorder callees at a recorder with no call recorded: events, meter (mallocs of at most
   VERBS_RECEIVE_REQ bytes and one free) and live bytes. B: record()'s spill arm (0 here), arg_s's xmalloc of each
   argument, answer's hand_back (one free and two xmallocs of the text) *)
Ltac v14_bunfold Hc :=
unfold EV_SUP_QUARANTINE_CLEAR, XM_SUP_QUARANTINE_CLEAR, LIVE_SUP_QUARANTINE_CLEAR,
  EV_SUP_POLICY_SET, XM_SUP_POLICY_SET, LIVE_SUP_POLICY_SET,
  EV_SUP_LV2_WORKER_SET, XM_SUP_LV2_WORKER_SET, LIVE_SUP_LV2_WORKER_SET,
  EV_RECORD, XM_RECORD, EV_ARG_S, XM_ARG_S, LIVE_ARG_S, EV_ANSWER, XM_ANSWER, LIVE_ANSWER,
  EV_HAND_BACK, XM_HAND_BACK, LIVE_HAND_BACK, EV_XMALLOC, XM_XMALLOC, LIVE_XMALLOC;
rewrite (v14_spill0 _ Hc); cbn [sarg].
Ltac v14_bfinish :=
assert (HREQ : VERBS_RECEIVE_REQ = 8194) by reflexivity;
pose proof (mo_free_nonneg MT MTL);
split; [lia|]; split; [lia | lia].

Lemma v14_qclear_budget : forall R a, r_calls R = [] -> -2^31 <= r_code R < 2^31 -> Z.of_nat (length a) <= 8192 ->
EV_SUP_QUARANTINE_CLEAR R = 4 /\
XM_SUP_QUARANTINE_CLEAR MT R (Some a) <= 3 * mo_malloc MT VERBS_RECEIVE_REQ + 1 * mo_free MT /\
LIVE_SUP_QUARANTINE_CLEAR R (Some a) <= 29 * VERBS_RECEIVE_REQ.
Proof.
intros R a Hc Hcode Ha. v14_bunfold Hc.
set (t := snd (sup_quarantine_clear_m R (Some a))).
assert (Ht : (length t <= 28)%nat) by (unfold t, sup_quarantine_clear_m, daemon_shape; apply v14_stub_len; exact Hcode).
pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length a) + 1) 1) VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M1.
pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length t) + 1) 1) VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
v14_bfinish.
Qed.

Lemma v14_policy_budget : forall R a b, r_calls R = [] -> -2^31 <= r_code R < 2^31 ->
Z.of_nat (length a) <= 8192 -> Z.of_nat (length b) <= 8192 ->
EV_SUP_POLICY_SET R = 5 /\
XM_SUP_POLICY_SET MT R (Some a) (Some b) <= 4 * mo_malloc MT VERBS_RECEIVE_REQ + 1 * mo_free MT /\
LIVE_SUP_POLICY_SET R (Some a) (Some b) <= 29 * VERBS_RECEIVE_REQ.
Proof.
intros R a b Hc Hcode Ha Hb. v14_bunfold Hc.
set (t := snd (sup_policy_set_m R (Some a) (Some b))).
assert (Ht : (length t <= 28)%nat) by (unfold t, sup_policy_set_m, daemon_shape; apply v14_stub_len; exact Hcode).
pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length a) + 1) 1) VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M1.
pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length b) + 1) 1) VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M1'.
pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length t) + 1) 1) VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
v14_bfinish.
Qed.

Lemma v14_lv2_budget : forall R a b, r_calls R = [] -> -2^31 <= r_code R < 2^31 ->
Z.of_nat (length a) <= 8192 -> Z.of_nat (length b) <= 8192 ->
EV_SUP_LV2_WORKER_SET R = 5 /\
XM_SUP_LV2_WORKER_SET MT R (Some a) (Some b) <= 4 * mo_malloc MT VERBS_RECEIVE_REQ + 1 * mo_free MT /\
LIVE_SUP_LV2_WORKER_SET R (Some a) (Some b) <= 29 * VERBS_RECEIVE_REQ.
Proof.
intros R a b Hc Hcode Ha Hb. v14_bunfold Hc.
set (t := snd (sup_lv2_worker_set_m R (Some a) (Some b))).
assert (Ht : (length t <= 28)%nat) by (unfold t, sup_lv2_worker_set_m, daemon_shape; apply v14_stub_len; exact Hcode).
pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length a) + 1) 1) VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M1.
pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length b) + 1) 1) VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M1'.
pose proof (mo_malloc_mono MT MTL (Z.max (Z.of_nat (length t) + 1) 1) VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as M2.
v14_bfinish.
Qed.

End e.
End f.
End d.
