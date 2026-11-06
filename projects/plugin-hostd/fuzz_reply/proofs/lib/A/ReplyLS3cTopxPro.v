(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_pro_x.v, with its module names changed; 94 of its 149 lines of code are new or changed and 3014 lines of the source are left out. *)
(* top_x's LS_pro (W_LLVMFuzzerTestOneInput_top_x.v:342 at integ bb9dae5d905) at W8Entry-2's decision (a)
   (a Theorem Labs lane 04:21Z): inside its `exists T0 rest0` it also takes the cut's own count bound
   `ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out` and HFH0
   `fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out`, both of which SEG_PRO
   supplies from the pre.  Until LatchX's commit fixes the word order, the two facts sit after the entry split's
   Permutation and before relay_add's two cases.  proves no function (kind: invariant lemma).
   - The bridge: every primary request's class is in 1 .. 30 (in_cls_range, for ANY size: needed0 >= 8 and a primary
     request has needed0 <= 2^16, and class_id maps 1 .. 2^16 into 1 .. 30, checked by computation), so the classes
     xcnt_ok leaves out count nothing, and xcnt_ok -> xcnt_pre (ReplyLS3c.v:255) with no block fact.
   - topx_LS_pro_xok_px: top_x's LS_pro text (W_LLVMFuzzerTestOneInput_top_x.v:413-425 at the TOP head 3d17f490d56,
     this file's former TX_LS_pro_xok, which top_x adopted) at LSx := txp_LSx B OM (= fr_LS3cp /\ fr_OUT /\ fr_ENT),
     TfibB := B, MT a Variable (KF-COUNT), fr_live_pre := ACfn_cf.fr_live_pre; ReplyLSI.v lsi_LS_pro adds fr_CAP and
     fr_SEC. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf CfParamsReply W_LLVMFuzzerTestOneInput_exit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3 ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3cTopx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3o ReplyLS3e ReplyLS3p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyLS3cTopxGone8.
(* lf_base_x: lib/A/W_LLVMFuzzerTestOneInput_cut_x.v's; fr_hblks: W_LLVMFuzzerTestOneInput_cut.v's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut_x.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== every primary class is in 1 .. 30 *)
(* class_id on 1 .. 2^16, checked by computation *)
Fixpoint cls_chk (s : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S f => (1 <=? PresetRoom.class_id s) && (PresetRoom.class_id s <=? 30) && cls_chk (s + 1) f
  end.
Lemma cls_chk_ok : cls_chk 1 65536 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cls_chk_sound : forall f s m, cls_chk s f = true -> s <= m < s + Z.of_nat f ->
  1 <= PresetRoom.class_id m <= 30.
Proof.
  induction f as [|f IH]; intros s m H Hm; [lia|].
  cbn [cls_chk] in H. apply andb_true_iff in H as (H1 & H2). apply andb_true_iff in H1 as (H1 & H3).
  destruct (Z.eq_dec m s) as [->|Hne]; [apply Z.leb_le in H1; apply Z.leb_le in H3; lia|].
  apply (IH (s + 1) m H2). lia.
Qed.
Lemma needed0_ge8 : forall n, 8 <= PresetRoom.needed0 n.
Proof.
  intros n. unfold PresetRoom.needed0, PresetRoom.rounded_size, PresetRoom.rz_size, PresetRoom.rup.
  assert (0 <= Z.shiftl 16 (PresetRoom.rz_log n)) by (rewrite Z.shiftl_nonneg; lia).
  assert (Z.max n 8 <= (Z.max n 8 + 8 - 1) / 8 * 8).
  { pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
    lia. }
  lia.
Qed.
Lemma in_cls_range : forall c n, PresetRoom.in_cls c n = true -> 1 <= c <= 30.
Proof.
  intros c n H. unfold PresetRoom.in_cls, PresetRoom.cls in H.
  destruct (PresetRoom.is_primary n) eqn:Ep; [|discriminate]. apply Z.eqb_eq in H. subst c.
  unfold PresetRoom.is_primary in Ep. apply Z.leb_le in Ep. unfold PresetRoom.K_MAX_SIZE in Ep.
  pose proof (needed0_ge8 n).
  apply (cls_chk_sound 65536 1 _ cls_chk_ok). change (Z.of_nat 65536) with 65536. lia.
Qed.
(* a class outside 1 .. 30 counts no block *)
Lemma cnt_cls_out : forall c l, ~ (1 <= c <= 30) -> cnt_cls c l = 0.
Proof.
  intros c l Hc. rewrite cnt_cls_ccnt. unfold PresetRoom.ccnt.
  induction (map snd l) as [|n r IH]; [reflexivity|]. cbn [List.filter].
  destruct (PresetRoom.in_cls c n) eqn:E; [apply in_cls_range in E; lia | exact IH].
Qed.

Section br.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the bridge: the cut's xcnt_ok (ReplyCnt.v:127, classes 1 .. 30) gives fr_LS3c_pro's xcnt_pre (every class) *)
Lemma xok_pre : forall cx T0 cap out,
  ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out -> xcnt_pre B cx T0 cap out.
Proof.
  intros cx T0 cap out (X1 & X2). split; [exact X1|].
  intros c. destruct (Z_le_dec 1 c) as [L1|L1]; [destruct (Z_le_dec c 30) as [L2|L2]|].
  - exact (X2 c (conj L1 L2)).
  - rewrite (cnt_cls_out c (ablocks B (c_ly cx) (c_S cx)) ltac:(lia)).
    pose proof (cnt_cls_nonneg c (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out)).
    unfold CLS0. lia.
  - rewrite (cnt_cls_out c (ablocks B (c_ly cx) (c_S cx)) ltac:(lia)).
    pose proof (cnt_cls_nonneg c (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out)).
    unfold CLS0. lia.
Qed.
(* aout_at's capacity clause (W_rep.v:187-188) *)
Lemma aout_cap_nonneg : forall RG ly S W mem c O mx no cap out,
  aout_at B RG ly S W mem c O mx no cap out -> 0 <= cap.
Proof.
  intros RG ly S W mem c O mx no cap out H. unfold aout_at in H.
  repeat match type of H with _ /\ ?R => destruct H as [_ H] end.
  destruct H as [(Hc & _) | (Hc & _)]; lia.
Qed.
End br.


(* ================================================================== the plugs *)
Section plug.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the meter (KF-COUNT): a Variable, implicit (read off lf_base_x / mo_le); the rule does not read it *)
Context {MT : ameter_ops}.

(* LSx := fr_LS3cp /\ fr_OUT /\ fr_ENT *)
Definition txp_LSx (OM : Z) : lfcx -> Z -> lmod -> alayout -> astate -> Prop :=
  fun cx t m ly S => fr_LS3cp B cx t m ly S /\ fr_OUT OM cx t m ly S /\ fr_ENT B cx m ly S.
(* top_x's LS_pro at LSx := txp_LSx B OM: fr_LS3c by fr_LS3c_pro's text over lf_base_x (ReplyLS3cTopx.v
   topx3c_LS_pro_xcnt) with xcnt_ok -> xcnt_pre (xok_pre); fr_POT at the first head (no key, no mass:
   ReplyLS3p.pt_pro_zero); fr_OUT's twin ReplyLS3o.fr_OUT_pro (its 0 <= cap from the aout_at premise); fr_ENT's
   ReplyLS3e.fr_ENT_pro (from HFH0) *)
Lemma topx_LS_pro_xok_px : forall OM, OUT_MAX4 <= OM -> forall XM_LIB RLO RHI LIBROOM NP G ARX,
  forall cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x B MT XM_LIB RLO RHI ACfn_cf.fr_live_pre LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT S2 S (oa_cost MT) ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  txp_LSx OM cx 0 (pro_m q T' pj c O cap out) ly S.
Proof.
  intros OM HOM XM_LIB RLO RHI LIBROOM NP G ARX cx Hp q T' pj c O cap out S2 pos ly S HB Hout Hc1 Hc2 Hc3 Hc4 Hb2
    Hf2 Hn2 Hbb2 Hmo (T0 & rest0 & HE0 & Hx & HFH0 & Hcase).
  assert (H3c : fr_LS3c B cx 0 (pro_m q T' pj c O cap out) ly S).
  { exact (topx3c_LS_pro_xcnt B XM_LIB RLO RHI LIBROOM NP G ARX cx Hp q T' pj c O cap out S2 pos ly S HB Hout
      Hc1 Hc2 Hc3 Hc4 Hb2 Hf2 Hn2 Hbb2 Hmo
      (ex_intro _ T0 (ex_intro _ rest0 (conj HE0 (conj (xok_pre B cx T0 cap out Hx) Hcase))))). }
  destruct Hout as (c0 & mx0 & Hout).
  pose proof (aout_cap_nonneg B _ _ _ _ _ _ _ _ _ _ _ Hout) as Hcap0.
  unfold txp_LSx, fr_LS3cp. refine (conj (conj H3c _) (conj _ _)).
  - intros k. destruct (pt_pro_zero q T' pj c O cap out k) as (E1 & E2).
    change (pro_m q T' pj c O cap out) with (ls_pro_m q T' pj c O cap out). rewrite E1, E2. lia.
  - exact (fr_OUT_pro B OM HOM cx q T' pj c O cap out ly S Hcap0
      (ex_intro _ T0 (ex_intro _ rest0 (conj HE0 Hcase)))).
  - exact (fr_ENT_pro B cx q T' pj c O cap out ly S T0 rest0 HE0 Hcase HFH0).
Qed.
End plug.
