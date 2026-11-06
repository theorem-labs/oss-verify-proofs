(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyLS.v, with its module names changed; 201 of its 283 lines of code are new or changed and 512 lines of the source are left out. *)
(* top_x's LS rules at LS v3: the Section hypotheses LS_* of fr_contract_top_x (a working branch bb9dae5d905,
   lib/A/W_LLVMFuzzerTestOneInput_top_x.v), each stated in top_x's text at LSx := fr_LS3c B (Section topx3c) or
   LSx := fr_LS3 B (Section topx3), RINV := fr_RINV, MT a Variable (KF-COUNT), TfibB := B, for the rows that had no
   lemma at that text and are provable from what exists.  proves no function (kind: invariant lemma).
   The meter: MT is each Section's implicit Context (read off the rules' mo_le / lf_base_x arguments).  No lemma here
   reads it: the rows' mo_ok conjuncts (and the rows that are only a mo_ok) are ReplyLSI.v's, proved there from its
   fr_SEC, so the lemmas here state the rows' other conjuncts.
   Names: top_x's W_LLVMFuzzerTestOneInput_remove.rm_at / rm_mk / rm_rr_ok / ... are ReplyRINV.v's copies
   (definition texts identical to bb9dae5d905's _remove.v); the meters rm_rr_cost / rm_cnl_cost / rm_cshe_cost are
   _remove.v's own; pro_m is ReplyRINV.v's copy (= bb9dae5d905 _pro.v's); lf_base_x and
   fr_lib_pre_cf_x are lib/A/W_LLVMFuzzerTestOneInput_cut_x.v's and fr_hblks is _cut.v's.  WR_MMAX (top_x's write
   rules) and CfParamsReply.fr_MMAX are equal by computation (topx_WR_MMAX_pin).  fr_live_pre is the driver's
   (ACfn_cf.fr_live_pre) where a rule needs it. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf CfParamsReply W_LLVMFuzzerTestOneInput_exit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3 ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyLS3cArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* top_x's write rules name WR_MMAX (this tree: 2^30 - 2^20; bb9dae5d905: CfParamsReply.fr_MMAX), its other rules
   CfParamsReply.fr_MMAX: one value (ReplyATop.v atop_WR_MMAX_pin on a working branch 5ab58d26200) *)
Example topx_WR_MMAX_pin : WR_MMAX = CfParamsReply.fr_MMAX.
Proof. reflexivity. Qed.

(* ReplyLS3.v's perm_lia (local to its Section) *)
Local Ltac topx_perm_lia :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *); lia.

(* ================================================================== LSx := fr_LS3 B *)
Section topx3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Context {MT : ameter_ops}.
Local Notation LSx := (fr_LS3 B).
Local Notation RINV := fr_RINV.
Local Notation TfibB := B.

(* top_x :216 LS_add_room's room conjunct (ReplyLS3.v fr_LS3_add_room :240) *)
Lemma topx3_LS_add_room : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX.
Proof. intros cx t m ly S H _ _. exact (fr_LS3_add_room B cx t m ly S H). Qed.
(* top_x :219 LS_add_open (fr_LS3_add_open :252 drops the RINV, ad_at_op and mo_le premises) *)
Lemma topx3_LS_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  mo_le MT S S' (oa_cost MT) -> Permutation (ablocks TfibB ly' S') ((q, APARTIAL) :: ablocks TfibB ly S) ->
  LSx cx (t + 1) (ad_open m i q pj ev) ly' S'.
Proof.
  intros cx t m i q pj ev ly S ly' S' H _ _ Hf _ HP. exact (fr_LS3_add_open B cx t m i q pj ev ly S ly' S' H Hf HP).
Qed.
(* top_x :223 LS_add_none (fr_LS3_add_none :245 drops the RINV, ad_at_op and oa_first premises) *)
Lemma topx3_LS_add_none : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None ->
  LSx cx (t + 1) (ad_none m) ly S.
Proof. intros cx t m ly S H _ _ _. exact (fr_LS3_add_none B cx t m ly S H). Qed.
(* top_x :239 LS_write_room's two room conjuncts (fr_LS3_write_room :294) *)
Lemma topx3_LS_write_room : forall cx t m si h ly S,
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < WR_MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX.
Proof. intros cx t m si h ly S H Hp Hn. exact (fr_LS3_write_room B cx t m si h ly S H Hp Hn). Qed.
(* top_x :246 LS_write_push (fr_LS3_write_push :315 drops the mo_le premise; its binder ev is last) *)
Lemma topx3_LS_write_push : forall cx t m si h (l' : hlist) d ev ly S ly' S',
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks TfibB ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks TfibB ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le MT S S' (lp_cost MT (hs_pending h) (wr_n cx m)) ->
  LSx cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros cx t m si h l' d ev ly S ly' S' H Hp Hn Hr Hc Hv HP _.
  exact (fr_LS3_write_push B cx t m si h l' d ly S ly' S' ev H Hp Hn Hr Hc Hv HP).
Qed.

(* the two facts of lf_base_x the prologue's rules read: the input's size and the driver's room *)
Lemma topx_lf_base_x_facts : forall MT0 XM_LIB RLO RHI LIBROOM NP G_fr ARx cx Hp,
  lf_base_x B MT0 XM_LIB RLO RHI ACfn_cf.fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  0 <= c_n cx < 2 ^ 26 /\ blocks_bytes (c_S cx) + ACfn_cf.CALL_ROOM <= LIVE_MAX.
Proof.
  intros MT0 XM_LIB RLO RHI LIBROOM NP G_fr ARx cx Hp (_ & Hpre).
  destruct Hpre as (_ & _ & _ & _ & Hd & _ & _ & _ & Hlive & _). unfold ACfn_cf.fr_live_pre in Hlive.
  split; [destruct Hd as [(Hd & _) | (Hd & _)]; lia | exact Hlive].
Qed.
(* top_x :328 LS_pro_oa's room conjunct (the row names no LS): at the driver's fr_live_pre *)
Lemma topx_LS_pro_oa : forall XM_LIB RLO RHI LIBROOM NP G ARX cx Hp (S2 : astate) pos,
  lf_base_x TfibB MT XM_LIB RLO RHI ACfn_cf.fr_live_pre LIBROOM NP G ARX cx Hp ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX.
Proof.
  intros XM_LIB RLO RHI LIBROOM NP G ARX cx Hp S2 pos HB _ _ _ Hbb.
  destruct (topx_lf_base_x_facts _ _ _ _ _ _ _ _ cx Hp HB) as (_ & Hlive).
  assert (E1 : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
  assert (E2 : LIVE_MAX = 17179869184) by reflexivity.
  rewrite Hbb. rewrite E1, E2 in *. unfold APARTIAL, ATABLE. lia.
Qed.
(* top_x :342 LS_pro at LSx := fr_LS3 B: fr_LS3_pro's proof (ReplyLS3.v:413) over lf_base_x's two facts; the premises
   it does not read (aout_at, the controller, S2, mo_le) are top_x's *)
Lemma topx3_LS_pro : forall XM_LIB RLO RHI LIBROOM NP G ARX cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x TfibB MT XM_LIB RLO RHI ACfn_cf.fr_live_pre LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at TfibB fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT S2 S (oa_cost MT) ->
  (exists T0 rest0, Permutation (ablocks TfibB (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks TfibB ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks TfibB ly S) ((q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))))) ->
  LSx cx 0 (pro_m q T' pj c O cap out) ly S.
Proof.
  intros XM_LIB RLO RHI LIBROOM NP G ARX cx Hp q T' pj c O cap out S2 pos ly S HB _ _ _ _ _ _ _ _ _ _
    (T0 & rest0 & HE0 & Hcase).
  destruct (topx_lf_base_x_facts _ _ _ _ _ _ _ _ cx Hp HB) as (Hc & Hlive).
  assert (Hmb : model_blks (pro_m q T' pj c O cap out) = (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out)
    by reflexivity.
  assert (Ep : pend_bytes (pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Eh : held_bytes (pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Ev : vslack (pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Ec : ECRED (pro_m q T' pj c O cap out) = E_ENT + K0) by reflexivity.
  assert (En : npend (pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Eo : nopen (lm_hs (pro_m q T' pj c O cap out)) = 1) by reflexivity.
  assert (Ek : kk cx (pro_m q T' pj c O cap out) = 0) by (unfold kk; cbn [pro_m lm_k]; lia).
  assert (Eb0 : blocks_bytes (c_S cx) = bsum (ablocks B (c_ly cx) (c_S cx))) by apply blocks_bytes_bsum.
  destruct Hcase as [(HT0 & HP) | (HT0 & HT' & HP)].
  - subst T0. rewrite Z.eqb_refl in HE0. cbv beta iota in HE0.
    exists rest0, (bsum (aout_blks cap out)).
    split; [rewrite Hmb; topx_perm_lia |].
    split; [rewrite Eb0, (bsum_perm _ _ HE0), !bsum_app, ?bsum_nil; lia |].
    split; [exact Hlive | split; [exact Hc | split; [reflexivity | split]]].
    + rewrite En, Ek. lia.
    + unfold PHI3, PHI. rewrite Hmb, Ep, Eh, Ev, Ec, Eo, Ek. rewrite !bsum_cons. cbn [snd].
      unfold W_OPEN, MB_K, MB_C, W_P, W_H, APARTIAL, ATABLE, E_ENT, K0. lia.
  - subst T'. rewrite (proj2 (Z.eqb_neq _ _) HT0) in HE0. cbv beta iota in HE0.
    exists rest0, (ATABLE + bsum (aout_blks cap out)).
    split; [rewrite Hmb; topx_perm_lia |].
    split; [rewrite Eb0, (bsum_perm _ _ HE0), !bsum_app, bsum_cons, ?bsum_nil; cbn [snd]; lia |].
    split; [exact Hlive | split; [exact Hc | split; [reflexivity | split]]].
    + rewrite En, Ek. lia.
    + unfold PHI3, PHI. rewrite Hmb, Ep, Eh, Ev, Ec, Eo, Ek. rewrite !bsum_cons. cbn [snd].
      unfold W_OPEN, MB_K, MB_C, W_P, W_H, APARTIAL, ATABLE, E_ENT, K0. lia.
Qed.
End topx3.

(* ================================================================== LSx := fr_LS3c B *)
Section topx3c.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Context {MT : ameter_ops}.
Local Notation LSx := (fr_LS3c B).
Local Notation RINV := fr_RINV.
Local Notation TfibB := B.

(* top_x :216 LS_add_room's room conjunct *)
Lemma topx3c_LS_add_room : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX.
Proof. intros cx t m ly S H. exact (topx3_LS_add_room B cx t m ly S (proj1 H)). Qed.
(* top_x :219 LS_add_open (ReplyLS3c.v fr_LS3c_add_open :147 drops the RINV, ad_at_op and mo_le premises) *)
Lemma topx3c_LS_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  mo_le MT S S' (oa_cost MT) -> Permutation (ablocks TfibB ly' S') ((q, APARTIAL) :: ablocks TfibB ly S) ->
  LSx cx (t + 1) (ad_open m i q pj ev) ly' S'.
Proof.
  intros cx t m i q pj ev ly S ly' S' H _ _ Hf _ HP. exact (fr_LS3c_add_open B cx t m i q pj ev ly S ly' S' H Hf HP).
Qed.
(* top_x :223 LS_add_none (fr_LS3c_add_none :142 drops three premises) *)
Lemma topx3c_LS_add_none : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None ->
  LSx cx (t + 1) (ad_none m) ly S.
Proof. intros cx t m ly S H _ _ _. exact (fr_LS3c_add_none B cx t m ly S H). Qed.
(* top_x :239 LS_write_room's two room conjuncts *)
Lemma topx3c_LS_write_room : forall cx t m si h ly S,
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < WR_MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX.
Proof. intros cx t m si h ly S H. exact (topx3_LS_write_room B cx t m si h ly S (proj1 H)). Qed.
(* top_x :246 LS_write_push (fr_LS3c_write_push :189 drops the mo_le premise; its binder ev is last) *)
Lemma topx3c_LS_write_push : forall cx t m si h (l' : hlist) d ev ly S ly' S',
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks TfibB ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks TfibB ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le MT S S' (lp_cost MT (hs_pending h) (wr_n cx m)) ->
  LSx cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros cx t m si h l' d ev ly S ly' S' H Hp Hn Hr Hc Hv HP _.
  exact (fr_LS3c_write_push B cx t m si h l' d ly S ly' S' ev H Hp Hn Hr Hc Hv HP).
Qed.
(* top_x :279 LS_event_malloc's two room conjuncts (ReplyLS3Arms.v fr_LS3_event_malloc :1206) *)
Lemma topx3c_LS_event_malloc : forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  re_len e < CfParamsReply.fr_MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX.
Proof. intros cx t m ly S e H. exact (fr_LS3_event_malloc B cx t m ly S e (proj1 H)). Qed.
(* top_x :282 LS_event_relay's two room conjuncts (fr_LS3_event_relay_r :1249, at ameter_triv: its mo_le is True) *)
Lemma topx3c_LS_event_relay : forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  sl_maxr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < CfParamsReply.fr_MMAX /\
  blocks_bytes S1 + sl_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX.
Proof.
  intros cx t m ly S S1 e ly1 q H HRI He _.
  exact (fr_LS3_event_relay_r B cx t m ly S S1 e ly1 q (proj1 H) HRI He I).
Qed.
(* top_x :420 LS_drain_skip (fr_LS3_drain_skip :760 and fr_CNT's keep rule: dr_skip moves only the cursor) *)
Lemma topx3c_LS_drain_skip : forall cx t m ly S,
  LSx cx t m ly S -> LSx cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
Proof.
  intros cx t m ly S (H1 & H2). split; [exact (fr_LS3_drain_skip B cx t m ly S H1)|].
  apply (fr_CNT_k_only B cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H2.
Qed.
(* top_x LS_exit_budget, LS_event_free, LS_rm_cshe_pre and LS_rm_sr_pre are each a mo_ok only: ReplyLSI.v's *)
(* top_x :523 LS_rm_step (ReplyLS3cArms.v fr_LS3c_rm_step_p :61, the same text) *)
Lemma topx3c_LS_rm_step : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSx cx t m ly0 S0 ->
  mo_le MT S0 S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h +
                 W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT (hs_expected h1) (hs_held h1) +
                 W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S)
       (input_blks cx ++ model_blks (rm_mk cx m si None j0
          (rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k)))
    (re_keys (rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  LSx cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 H _.
  exact (fr_LS3c_rm_step_p B cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 H I).
Qed.
(* top_x :342 LS_pro at LSx := fr_LS3c B was NOT provable at bb9dae5d905's text: fr_CNT at the first head needs the
   count of the entry's live blocks other than the input, the kept table and g_out (xcnt_pre, ReplyLS3c.v:260), and
   neither bb9dae5d905's lf_base_x (_cut_x.v:79-103, before the XCNT clause) nor any other premise of top_x's LS_pro
   bounded it.  The bridge: top_x's text with xcnt_pre in the entry split, as fr_LS3c_pro (ReplyLS3c.v:260) states
   it, over lf_base_x *)
Lemma topx3c_LS_pro_xcnt : forall XM_LIB RLO RHI LIBROOM NP G ARX cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x TfibB MT XM_LIB RLO RHI ACfn_cf.fr_live_pre LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at TfibB fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT S2 S (oa_cost MT) ->
  (exists T0 rest0, Permutation (ablocks TfibB (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     xcnt_pre B cx T0 cap out /\
     ((T0 = 0 /\ Permutation (ablocks TfibB ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks TfibB ly S) ((q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))))) ->
  LSx cx 0 (pro_m q T' pj c O cap out) ly S.
Proof.
  intros XM_LIB RLO RHI LIBROOM NP G ARX cx Hp q T' pj c O cap out S2 pos ly S HB Hout Hc1 Hc2 Hc3 Hc4 Hb2 Hf2 Hn2 Hbb2
    Hmo (T0 & rest0 & HE0 & (X1 & X2) & Hcase).
  split.
  { exact (topx3_LS_pro B XM_LIB RLO RHI LIBROOM NP G ARX cx Hp q T' pj c O cap out S2 pos ly S HB Hout Hc1 Hc2 Hc3 Hc4
      Hb2 Hf2 Hn2 Hbb2 Hmo (ex_intro _ T0 (ex_intro _ rest0 (conj HE0 Hcase)))). }
  assert (Hmb : model_blks (pro_m q T' pj c O cap out) = (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out)
    by reflexivity.
  assert (En : npend (pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (HP : Permutation (ablocks B ly S) (input_blks cx ++ model_blks (pro_m q T' pj c O cap out) ++ rest0)).
  { rewrite Hmb. destruct Hcase as [(HT0 & HP) | (HT0 & HT' & HP)].
    - subst T0. rewrite Z.eqb_refl in HE0. cbv beta iota in HE0. topx_perm_lia.
    - subst T'. rewrite (proj2 (Z.eqb_neq _ _) HT0) in HE0. cbv beta iota in HE0. topx_perm_lia. }
  unfold fr_CNT. rewrite (cnt_sec_perm _ _ HP), !cnt_sec_app.
  rewrite (cnt_sec_perm _ _ HE0), !cnt_sec_app in X1.
  split; [lia | split; [| rewrite En; lia]].
  intros c0. specialize (X2 c0). rewrite (cnt_cls_perm _ _ _ HP), !cnt_cls_app.
  rewrite (cnt_cls_perm _ _ _ HE0), !cnt_cls_app in X2. lia.
Qed.
End topx3c.
