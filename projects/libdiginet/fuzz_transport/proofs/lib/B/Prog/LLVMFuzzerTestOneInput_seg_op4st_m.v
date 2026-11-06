(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 2309 of its 2385 lines of code are new or changed and 689 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/LLVMFuzzerTestOneInput_seg_op4st.v, with its module paths and module names changed; 170 of its 519 lines of code are new or changed and 2036 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4st_m: the model and world lemmas of segment OP4ST of the image-B walk of
   LLVMFuzzerTestOneInput (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), op 4 (op_submit, tagged mode) after the CMDW cut.
   This file names no machine state and runs no code. It holds:
   1. the model's worlds of the segment (TOps.v op_submit_m :258-273): o4_cmdw (g_cmd[s] filled), o4_b6 (the replace
      or the append when want = SPEC_OK, else B5), o4_b7 (g_ncmd + 1), and o4_b6_skip (want <> SPEC_OK keeps B5);
   2. the running view of the stores at image B's world table TMAP_B (lib/B/Prog/TWorldB.v), over TWorldG.v's
      tw_write / tw_fill / tw_kept: o4x_mix P rdF rd0 is the final view rdF on the bytes P marks (written so far) and
      the entry's view rd0 elsewhere; o4x_tw_start, o4x_tw_step (a store of m bytes of v), o4x_tw_fill (a span
      written with a byte list), o4x_tw_end, the tactic o4x_unP that splits a P x = false into its ranges, and
      o4x_inN; and G (lib/B/TransportGB.v G_HARNESS_B): o4_inG_row, o4_tw_in_G and the ranges of g_cmd, g_q, g_nq,
      g_ncmd (o4_inG_cmd, o4_inG_q, o4_inG_nq, o4_inG_ncmd);
   3. the world lemmas: the world relation tw_at TMAP_B after the segment's stores (o4_w_cmd: g_cmd[s]'s st, key,
      display, len and bytes; o4_w_ncmd: g_ncmd + 1 alone; o4_w_rep: the replace; o4_w_app: the append) and
      o4_cmdw_keep (o4_cmdw keeps g_nq and g_ncmd), with their helpers o4w_*;
   4. the model lemmas: the cursor, tag, key and display facts (o4m_oc_ok, o4m_kd_ok, o4m_tag, o4_tag_facts,
      o4m_lor32, o4_kd_facts), the ranges of at and want (o4m_find_range, o4_at_range, o4_want_cases), the tail of
      op_submit (o4m_settle_tail, o4m_tail), and o4_model: from the CMDW cut's equations, LoopOk.v op_ok at
      LinksProof.v links_holds fixes the replace / append bounds, settle keeps B7, and the operation's equation at
      timg_B ends at B7 with the cursor tg_c at every stream. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb TSess0 TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

(* ------------------------------------------------------------------ *)
(* 1. The model's worlds of the segment (TOps.v op_submit_m :258-273)  *)
(* ------------------------------------------------------------------ *)

(* g_cmd[s] filled when want = SPEC_OK (:260-263): st, key, display, len, the first len bytes of cb. *)
Definition o4_cmdw (B5 : list byte) (s key disp len : Z) (cb : list byte) : list byte :=
  TW.set_Cmd_bytes
    (TW.set_Cmd_len (TW.set_Cmd_display (TW.set_Cmd_key (TW.set_Cmd_st B5 s TC.PENDING) s key) s disp) s len)
    s (firstn (Z.to_nat len) cb).
(* B6 (:258-272): the replace (at >= 0) or the append (at < 0) from Bw when want = SPEC_OK, else B5. *)
Definition o4_b6 (B5 Bw : list byte) (want at_ s : Z) : list byte :=
  if want =? DSpec.SPEC_OK then
    if 0 <=? at_ then TW.set_Q_at (TW.set_Cmd_st Bw (TW.Q_at Bw at_) TC.REPLACED) at_ s
    else TW.set_g_nq (TW.set_Q_at Bw (TW.g_nq Bw) s) ((TW.g_nq Bw + 1) mod 2 ^ 32)
  else B5.
(* B7 (:273): g_ncmd + 1. *)
Definition o4_b7 (B6 : list byte) : list byte := TW.set_g_ncmd B6 ((TW.g_ncmd B6 + 1) mod 2 ^ 32).

(* want <> SPEC_OK keeps B5. *)
Lemma o4_b6_skip : forall B5 Bw want at_ s, want <> 0 -> o4_b6 B5 Bw want at_ s = B5.
Proof. intros B5 Bw want at_ s H. unfold o4_b6, DSpec.SPEC_OK. rewrite (proj2 (Z.eqb_neq want 0) H). reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 2. The running view of the stores, and G                            *)
(* ------------------------------------------------------------------ *)

(* A view that is rdF on the bytes P marks and rd0 elsewhere: the written bytes so far, the entry's on the others. *)
Definition o4x_in (lo n x : Z) : bool := (lo <=? x) && (x <? lo + n).
Definition o4x_mix (P : Z -> bool) (rdF rd0 : Z -> option Z) : Z -> option Z :=
  fun x => if P x then rdF x else rd0 x.

Lemma o4x_in_true : forall lo n x, lo <= x < lo + n -> o4x_in lo n x = true.
Proof. intros lo n x H. unfold o4x_in. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma o4x_in_false' : forall lo n x, ~ (lo <= x < lo + n) -> o4x_in lo n x = false.
Proof.
intros lo n x H. unfold o4x_in. destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + n)); cbn [andb];
  first [reflexivity | exfalso; lia].
Qed.
Lemma o4x_in_false : forall lo n x, o4x_in lo n x = false -> ~ (lo <= x < lo + n).
Proof. intros lo n x H Hx. rewrite (o4x_in_true lo n x Hx) in H. discriminate H. Qed.

Lemma o4x_tw_start : forall rdF rd0 Bw, tw_at TMAP_B rd0 Bw -> tw_at TMAP_B (o4x_mix (fun _ => false) rdF rd0) Bw.
Proof. intros rdF rd0 Bw H. apply (tw_kept TMAP_B rd0 _ Bw H). intros x _. reflexivity. Qed.

(* One store of m bytes of v at the world offset ko = o + k of the row (o, b, n). *)
Lemma o4x_tw_step : forall rdF rd0 P Bw o b n k ko (m : nat) v,
  tw_at TMAP_B (o4x_mix P rdF rd0) Bw -> In (o, b, n) TMAP_B -> ko = o + k -> 0 <= k -> k + Z.of_nat m <= n ->
  (forall j, (j < m)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  tw_at TMAP_B (o4x_mix (fun x => P x || o4x_in (b + k) (Z.of_nat m) x) rdF rd0) (TW.upd Bw ko (TW.put m v)).
Proof.
intros rdF rd0 P Bw o b n k ko m v H Hin Hko Hk Hkm HV. subst ko.
apply (tw_write TMAP_B (o4x_mix P rdF rd0) (o4x_mix (fun x => P x || o4x_in (b + k) (Z.of_nat m) x) rdF rd0)
  Bw o b n k m v TMAP_B_ok H Hin Hk Hkm).
- intros j Hj. unfold o4x_mix. cbv beta.
  rewrite (o4x_in_true (b + k) (Z.of_nat m) (b + k + Z.of_nat j)) by lia. rewrite orb_true_r. exact (HV j Hj).
- intros x Hx Hn. unfold o4x_mix. cbv beta.
  rewrite (o4x_in_false' (b + k) (Z.of_nat m) x Hn). rewrite orb_false_r. reflexivity.
Qed.

(* A span at the world offset ko = o + k of the row (o, b, n) written with the bytes src (a memcpy / memset). *)
Lemma o4x_tw_fill : forall rdF rd0 P Bw o b n k ko (src : list byte),
  tw_at TMAP_B (o4x_mix P rdF rd0) Bw -> In (o, b, n) TMAP_B -> ko = o + k -> 0 <= k ->
  k + Z.of_nat (length src) <= n ->
  (forall i, 0 <= i < Z.of_nat (length src) ->
     rdF (b + k + i) = Some (bv_unsigned (nth (Z.to_nat i) src (Z_to_bv 8 0)))) ->
  tw_at TMAP_B (o4x_mix (fun x => P x || o4x_in (b + k) (Z.of_nat (length src)) x) rdF rd0) (TW.upd Bw ko src).
Proof.
intros rdF rd0 P Bw o b n k ko src H Hin Hko Hk Hkn HV. subst ko.
apply (tw_fill TMAP_B (o4x_mix P rdF rd0)
  (o4x_mix (fun x => P x || o4x_in (b + k) (Z.of_nat (length src)) x) rdF rd0) Bw o b n k src
  TMAP_B_ok H Hin Hk Hkn).
- intros i Hi. unfold o4x_mix. cbv beta.
  rewrite (o4x_in_true (b + k) (Z.of_nat (length src)) (b + k + i)) by lia. rewrite orb_true_r. exact (HV i Hi).
- intros x Hx Hn. unfold o4x_mix. cbv beta.
  rewrite (o4x_in_false' (b + k) (Z.of_nat (length src)) x Hn). rewrite orb_false_r. reflexivity.
Qed.

Lemma o4x_tw_end : forall rdF rd0 P Bw, tw_at TMAP_B (o4x_mix P rdF rd0) Bw ->
  (forall x, tw_in TMAP_B x -> P x = false -> rdF x = rd0 x) -> tw_at TMAP_B rdF Bw.
Proof.
intros rdF rd0 P Bw H Hk. apply (tw_kept TMAP_B (o4x_mix P rdF rd0) rdF Bw H).
intros x Hx. unfold o4x_mix. destruct (P x) eqn:E; [reflexivity | exact (Hk x Hx E)].
Qed.

Ltac o4x_unP HP :=
  cbv beta in HP;
  repeat match type of HP with
  | orb _ _ = false =>
      let Hq := fresh "Hq" in apply orb_false_iff in HP; destruct HP as [HP Hq]; apply o4x_in_false in Hq
  end.

(* A byte of a range of n bytes is the range's byte j. *)
Lemma o4x_inN : forall b a n, b <= a < b + Z.of_nat n -> exists j, (j < n)%nat /\ a = b + Z.of_nat j.
Proof. intros b a n H. exists (Z.to_nat (a - b)). split; lia. Qed.

(* A payload byte of a row of TMAP_B is a byte of G. *)
Lemma o4_inG_row : forall o b n a, In (o, b, n) TMAP_B -> b <= a < b + n -> inG TG.G_HARNESS_B a.
Proof.
intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_B_in_G o b n Hin) | change (b <= a < b + n); exact Ha].
Qed.

(* A payload byte of the world table is a byte of G. *)
Lemma o4_tw_in_G : forall x, tw_in TMAP_B x -> inG TG.G_HARNESS_B x.
Proof. intros x (o & b & n & Hin & Hx). exact (o4_inG_row o b n x Hin Hx). Qed.

(* The payloads of g_cmd, g_q, g_nq and g_ncmd are bytes of G. *)
Lemma o4_inG_cmd : forall a, TB_g_cmd <= a < TB_g_cmd + 40960 -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. assert (SC : TW.SZ_g_cmd = 40960) by reflexivity.
apply (o4_inG_row _ _ _ a TMAP_B_g_cmd). rewrite SC. exact Ha.
Qed.

Lemma o4_inG_q : forall a, TB_g_q <= a < TB_g_q + 4096 -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. assert (SQ : TW.SZ_g_q = 4096) by reflexivity.
apply (o4_inG_row _ _ _ a TMAP_B_g_q). rewrite SQ. exact Ha.
Qed.

Lemma o4_inG_nq : forall a, TB_g_nq <= a < TB_g_nq + 4 -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. assert (SNQ : TW.SZ_g_nq = 4) by reflexivity.
apply (o4_inG_row _ _ _ a TMAP_B_g_nq). rewrite SNQ. exact Ha.
Qed.

Lemma o4_inG_ncmd : forall a, TB_g_ncmd <= a < TB_g_ncmd + 4 -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. assert (SN : TW.SZ_g_ncmd = 4) by reflexivity.
apply (o4_inG_row _ _ _ a TMAP_B_g_ncmd). rewrite SN. exact Ha.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The world lemmas: helpers                                       *)
(* ------------------------------------------------------------------ *)

Lemma o4w_nth_firstn : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros l n. revert l. induction n as [|n IH]; intros l i d Hi; [lia|].
destruct l as [|x l]; [destruct i; reflexivity|]. destruct i as [|i]; [reflexivity|].
cbn [firstn nth]. apply IH. lia.
Qed.

Lemma o4w_le4_mod : forall v j, YO0f.le_byte (v mod 2 ^ 32) 4 j = YO0f.le_byte v 4 j.
Proof.
intros v j. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma o4w_len : forall (B v : list byte) k, length B = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= TW.W_LEN -> length (TW.upd B k v) = Z.to_nat TW.W_LEN.
Proof. intros B v k HL Hk Hv. rewrite TWL.length_upd; [exact HL | exact Hk | rewrite HL; lia]. Qed.

Lemma o4w_u_out : forall (B v : list byte) k k' m, length B = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= TW.W_LEN -> 0 <= k' -> (k' + Z.of_nat m <= k \/ k + Z.of_nat (length v) <= k') ->
  TW.u_at (TW.upd B k v) k' m = TW.u_at B k' m.
Proof.
intros B v k k' m HL Hk Hv Hk' Hd. apply TWL.u_at_upd_out; [exact Hk | exact Hk' | exact Hd | rewrite HL; lia].
Qed.

(* The length of a world after stores inside it. *)
Ltac o4w_lenW HL :=
  lazymatch goal with
  | |- length (TW.upd _ _ _) = _ => apply o4w_len; [o4w_lenW HL | lia | rewrite ?TWL.length_put; lia]
  | |- _ => exact HL
  end.

(* u_at of a world after stores outside the read span. *)
Ltac o4w_uout HL :=
  repeat (rewrite o4w_u_out;
    [| o4w_lenW HL | lia | rewrite ?TWL.length_put; lia | lia
     | first [left; rewrite ?TWL.length_put; lia | right; rewrite ?TWL.length_put; lia]]).

(* ------------------------------------------------------------------ *)
(* 3. The world lemmas                                                 *)
(* ------------------------------------------------------------------ *)

(* g_cmd[s]'s st, key, display (4 bytes each), len (1 byte) and the first len bytes of cb at s + 12. *)
Lemma o4_w_cmd : forall (B5 : list byte) (rd0 rdF : Z -> option Z) (s key disp len : Z) (cb : list byte),
  tw_at TMAP_B rd0 B5 -> 0 <= s < 1024 -> 0 <= len <= 24 -> length cb = 24%nat ->
  (forall j, (j < 4)%nat -> rdF (TB_g_cmd + 40 * s + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_g_cmd + 40 * s + 4 + Z.of_nat j) = Some (YO0f.le_byte key 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_g_cmd + 40 * s + 8 + Z.of_nat j) = Some (YO0f.le_byte disp 4 j)) ->
  rdF (TB_g_cmd + 40 * s + 36) = Some (YO0f.le_byte len 1 0) ->
  (forall i, 0 <= i < len ->
     rdF (TB_g_cmd + 40 * s + 12 + i) = Some (bv_unsigned (nth (Z.to_nat i) cb (Z_to_bv 8 0)))) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_g_cmd + 40 * s <= x < TB_g_cmd + 40 * s + 12 + len) ->
     x <> TB_g_cmd + 40 * s + 36 -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (o4_cmdw B5 s key disp len cb).
Proof.
intros B5 rd0 rdF s key disp len cb Htw Hs Hlen Hcb Vst Vkey Vdisp Vlen Vcb Hk.
assert (SC : TW.SZ_g_cmd = 40960) by reflexivity.
assert (HLs : length (firstn (Z.to_nat len) cb) = Z.to_nat len) by (apply firstn_length_le; lia).
assert (HP : TC.PENDING = 1) by reflexivity.
unfold o4_cmdw, TW.set_Cmd_bytes, TW.set_Cmd_len, TW.set_Cmd_display, TW.set_Cmd_key, TW.set_Cmd_st,
  TW.A_Cmd_bytes, TW.A_Cmd_len, TW.A_Cmd_display, TW.A_Cmd_key, TW.A_Cmd_st.
rewrite HP.
pose proof (o4x_tw_start rdF rd0 B5 Htw) as H0.
pose proof (o4x_tw_step rdF rd0 _ _ TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (40 * s) (TW.OFF_g_cmd + 40 * s + 0) 4 1
  H0 TMAP_B_g_cmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Vst) as H1.
pose proof (o4x_tw_step rdF rd0 _ _ TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (40 * s + 4) (TW.OFF_g_cmd + 40 * s + 4) 4
  key H1 TMAP_B_g_cmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; replace (TB_g_cmd + (40 * s + 4) + Z.of_nat j) with (TB_g_cmd + 40 * s + 4 + Z.of_nat j)
          by lia; exact (Vkey j Hj))) as H2.
pose proof (o4x_tw_step rdF rd0 _ _ TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (40 * s + 8) (TW.OFF_g_cmd + 40 * s + 8) 4
  disp H2 TMAP_B_g_cmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; replace (TB_g_cmd + (40 * s + 8) + Z.of_nat j) with (TB_g_cmd + 40 * s + 8 + Z.of_nat j)
          by lia; exact (Vdisp j Hj))) as H3.
pose proof (o4x_tw_step rdF rd0 _ _ TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (40 * s + 36) (TW.OFF_g_cmd + 40 * s + 36) 1
  len H3 TMAP_B_g_cmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; assert (Hj0 : j = 0%nat) by lia; subst j;
        replace (TB_g_cmd + (40 * s + 36) + Z.of_nat 0) with (TB_g_cmd + 40 * s + 36) by lia; exact Vlen)) as H4.
pose proof (o4x_tw_fill rdF rd0 _ _ TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (40 * s + 12) (TW.OFF_g_cmd + 40 * s + 12)
  (firstn (Z.to_nat len) cb) H4 TMAP_B_g_cmd ltac:(lia) ltac:(lia) ltac:(rewrite HLs; lia)
  ltac:(rewrite HLs; intros i Hi; rewrite o4w_nth_firstn by lia;
        replace (TB_g_cmd + (40 * s + 12) + i) with (TB_g_cmd + 40 * s + 12 + i) by lia; apply Vcb; lia)) as H5.
rewrite HLs in H5. rewrite Z2Nat.id in H5 by lia.
apply (o4x_tw_end rdF rd0 _ _ H5).
intros x Hx HP5. o4x_unP HP5. apply Hk; [exact Hx | lia | lia].
Qed.

(* g_ncmd + 1 alone (want <> SPEC_OK). *)
Lemma o4_w_ncmd : forall (B6 : list byte) (rd0 rdF : Z -> option Z),
  tw_at TMAP_B rd0 B6 ->
  (forall j, (j < 4)%nat -> rdF (TB_g_ncmd + Z.of_nat j) = Some (YO0f.le_byte (TW.g_ncmd B6 + 1) 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_g_ncmd <= x < TB_g_ncmd + 4) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (o4_b7 B6).
Proof.
intros B6 rd0 rdF Htw Vn Hk.
assert (SN : TW.SZ_g_ncmd = 4) by reflexivity.
unfold o4_b7, TW.set_g_ncmd.
pose proof (o4x_tw_start rdF rd0 B6 Htw) as H0.
pose proof (o4x_tw_step rdF rd0 _ _ TW.OFF_g_ncmd TB_g_ncmd TW.SZ_g_ncmd 0 TW.OFF_g_ncmd 4
  ((TW.g_ncmd B6 + 1) mod 2 ^ 32) H0 TMAP_B_g_ncmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; rewrite o4w_le4_mod;
        replace (TB_g_ncmd + 0 + Z.of_nat j) with (TB_g_ncmd + Z.of_nat j) by lia; exact (Vn j Hj))) as H1.
apply (o4x_tw_end rdF rd0 _ _ H1).
intros x Hx HP. o4x_unP HP. apply Hk; [exact Hx | lia].
Qed.

(* The replace: g_cmd[q].st = 3 (q = g_q[at]), g_q[at] = s, then g_ncmd + 1. *)
Lemma o4_w_rep : forall (Bw : list byte) (rd0 rdF : Z -> option Z) (at_ s : Z),
  tw_at TMAP_B rd0 Bw -> 0 <= at_ < 1024 -> 0 <= TW.Q_at Bw at_ < 1024 ->
  (forall j, (j < 4)%nat ->
     rdF (TB_g_cmd + 40 * TW.Q_at Bw at_ + Z.of_nat j) = Some (YO0f.le_byte 3 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_g_q + 4 * at_ + Z.of_nat j) = Some (YO0f.le_byte s 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_g_ncmd + Z.of_nat j) = Some (YO0f.le_byte (TW.g_ncmd Bw + 1) 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_g_cmd + 40 * TW.Q_at Bw at_ <= x < TB_g_cmd + 40 * TW.Q_at Bw at_ + 4) ->
     ~ (TB_g_q + 4 * at_ <= x < TB_g_q + 4 * at_ + 4) -> ~ (TB_g_ncmd <= x < TB_g_ncmd + 4) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (o4_b7 (TW.set_Q_at (TW.set_Cmd_st Bw (TW.Q_at Bw at_) TC.REPLACED) at_ s)).
Proof.
intros Bw rd0 rdF at_ s Htw Hat Hq Vst Vq Vn Hk.
pose proof (tw_len TMAP_B rd0 Bw Htw) as HL.
assert (EW : TW.W_LEN = 65616) by reflexivity. assert (EC : TW.OFF_g_cmd = 19912) by reflexivity.
assert (EQ : TW.OFF_g_q = 60872) by reflexivity. assert (EM : TW.OFF_g_ncmd = 64984) by reflexivity.
assert (SC : TW.SZ_g_cmd = 40960) by reflexivity. assert (SQ : TW.SZ_g_q = 4096) by reflexivity.
assert (SN : TW.SZ_g_ncmd = 4) by reflexivity.
assert (HR : TC.REPLACED = 3) by reflexivity.
assert (EN6 : TW.g_ncmd (TW.set_Q_at (TW.set_Cmd_st Bw (TW.Q_at Bw at_) TC.REPLACED) at_ s) = TW.g_ncmd Bw).
{ unfold TW.g_ncmd, TW.set_Q_at, TW.set_Cmd_st, TW.A_Cmd_st. o4w_uout HL. reflexivity. }
unfold o4_b7. rewrite EN6. rewrite HR.
unfold TW.set_g_ncmd, TW.set_Q_at, TW.set_Cmd_st, TW.A_Cmd_st.
pose proof (o4x_tw_start rdF rd0 Bw Htw) as H0.
pose proof (o4x_tw_step rdF rd0 _ _ TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (40 * TW.Q_at Bw at_)
  (TW.OFF_g_cmd + 40 * TW.Q_at Bw at_ + 0) 4 3 H0 TMAP_B_g_cmd ltac:(lia) ltac:(lia)
  ltac:(cbn [Z.of_nat]; lia) Vst) as H1.
pose proof (o4x_tw_step rdF rd0 _ _ TW.OFF_g_q TB_g_q TW.SZ_g_q (4 * at_) (TW.OFF_g_q + 4 * at_) 4 s H1
  TMAP_B_g_q ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Vq) as H2.
pose proof (o4x_tw_step rdF rd0 _ _ TW.OFF_g_ncmd TB_g_ncmd TW.SZ_g_ncmd 0 TW.OFF_g_ncmd 4
  ((TW.g_ncmd Bw + 1) mod 2 ^ 32) H2 TMAP_B_g_ncmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; rewrite o4w_le4_mod;
        replace (TB_g_ncmd + 0 + Z.of_nat j) with (TB_g_ncmd + Z.of_nat j) by lia; exact (Vn j Hj))) as H3.
apply (o4x_tw_end rdF rd0 _ _ H3).
intros x Hx HP. o4x_unP HP. apply Hk; [exact Hx | lia | lia | lia].
Qed.

(* The append: g_nq + 1, g_q[old g_nq] = s, then g_ncmd + 1. *)
Lemma o4_w_app : forall (Bw : list byte) (rd0 rdF : Z -> option Z) (s : Z),
  tw_at TMAP_B rd0 Bw -> 0 <= TW.g_nq Bw < 1024 ->
  (forall j, (j < 4)%nat -> rdF (TB_g_nq + Z.of_nat j) = Some (YO0f.le_byte (TW.g_nq Bw + 1) 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_g_q + 4 * TW.g_nq Bw + Z.of_nat j) = Some (YO0f.le_byte s 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_g_ncmd + Z.of_nat j) = Some (YO0f.le_byte (TW.g_ncmd Bw + 1) 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_g_nq <= x < TB_g_nq + 4) ->
     ~ (TB_g_q + 4 * TW.g_nq Bw <= x < TB_g_q + 4 * TW.g_nq Bw + 4) -> ~ (TB_g_ncmd <= x < TB_g_ncmd + 4) ->
     rdF x = rd0 x) ->
  tw_at TMAP_B rdF (o4_b7 (TW.set_g_nq (TW.set_Q_at Bw (TW.g_nq Bw) s) ((TW.g_nq Bw + 1) mod 2 ^ 32))).
Proof.
intros Bw rd0 rdF s Htw Hnq Vnq Vq Vn Hk.
pose proof (tw_len TMAP_B rd0 Bw Htw) as HL.
assert (EW : TW.W_LEN = 65616) by reflexivity. assert (EQ : TW.OFF_g_q = 60872) by reflexivity.
assert (EN : TW.OFF_g_nq = 64980) by reflexivity. assert (EM : TW.OFF_g_ncmd = 64984) by reflexivity.
assert (SQ : TW.SZ_g_q = 4096) by reflexivity. assert (SNQ : TW.SZ_g_nq = 4) by reflexivity.
assert (SN : TW.SZ_g_ncmd = 4) by reflexivity.
assert (EN6 : TW.g_ncmd (TW.set_g_nq (TW.set_Q_at Bw (TW.g_nq Bw) s) ((TW.g_nq Bw + 1) mod 2 ^ 32)) =
  TW.g_ncmd Bw).
{ unfold TW.g_ncmd, TW.set_g_nq, TW.set_Q_at. o4w_uout HL. reflexivity. }
unfold o4_b7. rewrite EN6.
unfold TW.set_g_ncmd, TW.set_g_nq, TW.set_Q_at.
pose proof (o4x_tw_start rdF rd0 Bw Htw) as H0.
pose proof (o4x_tw_step rdF rd0 _ _ TW.OFF_g_q TB_g_q TW.SZ_g_q (4 * TW.g_nq Bw) (TW.OFF_g_q + 4 * TW.g_nq Bw) 4 s
  H0 TMAP_B_g_q ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Vq) as H1.
pose proof (o4x_tw_step rdF rd0 _ _ TW.OFF_g_nq TB_g_nq TW.SZ_g_nq 0 TW.OFF_g_nq 4
  ((TW.g_nq Bw + 1) mod 2 ^ 32) H1 TMAP_B_g_nq ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; rewrite o4w_le4_mod;
        replace (TB_g_nq + 0 + Z.of_nat j) with (TB_g_nq + Z.of_nat j) by lia; exact (Vnq j Hj))) as H2.
pose proof (o4x_tw_step rdF rd0 _ _ TW.OFF_g_ncmd TB_g_ncmd TW.SZ_g_ncmd 0 TW.OFF_g_ncmd 4
  ((TW.g_ncmd Bw + 1) mod 2 ^ 32) H2 TMAP_B_g_ncmd ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
  ltac:(intros j Hj; rewrite o4w_le4_mod;
        replace (TB_g_ncmd + 0 + Z.of_nat j) with (TB_g_ncmd + Z.of_nat j) by lia; exact (Vn j Hj))) as H3.
apply (o4x_tw_end rdF rd0 _ _ H3).
intros x Hx HP. o4x_unP HP. apply Hk; [exact Hx | lia | lia | lia].
Qed.

(* o4_cmdw writes only g_cmd[s]: g_nq and g_ncmd keep their values. *)
Lemma o4_cmdw_keep : forall (B5 : list byte) (s key disp len : Z) (cb : list byte),
  length B5 = Z.to_nat TW.W_LEN -> 0 <= s < 1024 -> 0 <= len <= 24 -> length cb = 24%nat ->
  TW.g_nq (o4_cmdw B5 s key disp len cb) = TW.g_nq B5 /\ TW.g_ncmd (o4_cmdw B5 s key disp len cb) = TW.g_ncmd B5.
Proof.
intros B5 s key disp len cb HL Hs Hlen Hcb.
assert (HLs : length (firstn (Z.to_nat len) cb) = Z.to_nat len) by (apply firstn_length_le; lia).
assert (EW : TW.W_LEN = 65616) by reflexivity. assert (EC : TW.OFF_g_cmd = 19912) by reflexivity.
assert (EN : TW.OFF_g_nq = 64980) by reflexivity. assert (EM : TW.OFF_g_ncmd = 64984) by reflexivity.
unfold o4_cmdw, TW.g_nq, TW.g_ncmd, TW.set_Cmd_bytes, TW.set_Cmd_len, TW.set_Cmd_display, TW.set_Cmd_key,
  TW.set_Cmd_st, TW.A_Cmd_bytes, TW.A_Cmd_len, TW.A_Cmd_display, TW.A_Cmd_key, TW.A_Cmd_st.
o4w_uout HL. split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The model lemmas of the segment                                  *)
(* ------------------------------------------------------------------ *)

(* The cursor after the op byte, and after the key and display bytes, stays in range (QueueFacts.v fuzz_u8_ok). *)
Lemma o4m_oc_ok : forall (D : list byte) (c : TOP.fuzz_in), QF.fuzz_in_ok D c -> QF.fuzz_in_ok D (lc_oc D c).
Proof.
intros D c Hc. destruct (QF.fuzz_u8_ok D c Hc) as (c1 & v & E & Hc1 & _).
unfold lc_oc. rewrite E. exact Hc1.
Qed.

Lemma o4m_kd_ok : forall (D : list byte) (c1 : TOP.fuzz_in),
  QF.fuzz_in_ok D c1 -> QF.fuzz_in_ok D (sv_c (lc_sub_kd D c1)).
Proof.
intros D c1 Hc1. unfold lc_sub_kd.
destruct (QF.fuzz_u8_ok D c1 Hc1) as (c1' & kb & E1 & Hc1' & _). rewrite E1. cbv beta iota zeta.
destruct (QF.fuzz_u8_ok D c1' Hc1') as (c2 & ab & E2 & Hc2 & _). rewrite E2. cbv beta iota zeta.
destruct (QF.fuzz_u8_ok D c2 Hc2) as (c3 & db & E3 & Hc3 & _). rewrite E3. cbv beta iota zeta.
cbn [sv_c]. exact Hc3.
Qed.

(* lc_tag_vals from a cursor in range: len, the 24 bytes of c, the take's length and the cursors around it. *)
Lemma o4m_tag : forall (D B1 : list byte) (c3 : TOP.fuzz_in),
  QF.fuzz_in_ok D c3 ->
  let tv := lc_tag_vals D B1 c3 in
  3 <= tg_len tv <= 24 /\ length (tg_cbytes tv) = 24%nat /\ 0 <= tg_n tv <= tg_len tv - 3 /\
  0 <= TOP.fi_off (tg_c4 tv) /\ 0 <= TOP.fi_n (tg_c4 tv) /\ tg_n tv <= TOP.fi_n (tg_c4 tv) /\
  TOP.fi_off (tg_c tv) = TOP.fi_off (tg_c4 tv) + tg_n tv /\
  TOP.fi_n (tg_c tv) = TOP.fi_n (tg_c4 tv) - tg_n tv.
Proof.
intros D B1 c3 Hc3. cbv zeta. unfold lc_tag_vals.
destruct (QF.fuzz_u8_ok D c3 Hc3) as (c4 & lb & E4 & (H0 & H1 & H2) & Hlb). rewrite E4.
cbv beta iota zeta. unfold TOP.fuzz_take_m. cbv beta iota zeta.
cbn [tg_len tg_cbytes tg_n tg_c4 tg_c TOP.fi_off TOP.fi_n].
pose proof (Z.mod_pos_bound lb 22 ltac:(lia)) as Hm.
destruct (Z.ltb_spec (lb mod 22 + 3 - 3) (TOP.fi_n c4)) as [Hlt|Hge]; cbv beta iota;
  (split; [lia|]);
  (split; [rewrite !length_app, repeat_length, QF.length_sub_D by lia; cbn [length]; lia|]);
  repeat split; lia.
Qed.

(* The bytes and the cursor of the tagged mode. *)
Lemma o4_tag_facts : forall (D B1 : list byte) (c0 : TOP.fuzz_in),
  QF.fuzz_in_ok D c0 ->
  let tv := lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D c0))) in
  3 <= tg_len tv <= 24 /\ length (tg_cbytes tv) = 24%nat /\ 0 <= tg_n tv <= tg_len tv - 3 /\
  0 <= TOP.fi_off (tg_c4 tv) /\ 0 <= TOP.fi_n (tg_c4 tv) /\ tg_n tv <= TOP.fi_n (tg_c4 tv) /\
  TOP.fi_off (tg_c tv) = TOP.fi_off (tg_c4 tv) + tg_n tv /\
  TOP.fi_n (tg_c tv) = TOP.fi_n (tg_c4 tv) - tg_n tv.
Proof.
intros D B1 c0 Hc0.
exact (o4m_tag D B1 _ (o4m_kd_ok D _ (o4m_oc_ok D c0 Hc0))).
Qed.

(* Z.lor of two u32 values is a u32. *)
Lemma o4m_lor32 : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> 0 <= Z.lor x y < 2 ^ 32.
Proof.
intros x y Hx Hy.
assert (H0 : 0 <= Z.lor x y) by (apply Z.lor_nonneg; lia).
split; [exact H0|].
destruct (Z.eq_dec (Z.lor x y) 0) as [E|E]; [rewrite E; lia|].
apply (proj2 (Z.log2_lt_pow2 (Z.lor x y) 32 ltac:(lia))).
rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
- destruct (Z.eq_dec x 0) as [E0|E0].
  + rewrite E0. change (Z.log2 0) with 0. lia.
  + apply (proj1 (Z.log2_lt_pow2 x 32 ltac:(lia))). lia.
- destruct (Z.eq_dec y 0) as [E0|E0].
  + rewrite E0. change (Z.log2 0) with 0. lia.
  + apply (proj1 (Z.log2_lt_pow2 y 32 ltac:(lia))). lia.
Qed.

(* The key and display bytes. *)
Lemma o4_kd_facts : forall (D : list byte) (c1 : TOP.fuzz_in),
  0 <= sv_key (lc_sub_kd D c1) < 2 ^ 32 /\ (sv_display (lc_sub_kd D c1) = 0 \/ sv_display (lc_sub_kd D c1) = 1).
Proof.
intros D c1. unfold lc_sub_kd.
destruct (TOP.fuzz_u8_m D c1) as [c1' kb].
destruct (TOP.fuzz_u8_m D c1') as [c2 ab].
destruct (TOP.fuzz_u8_m D c2) as [c3 db].
cbv zeta. cbn [sv_key sv_display].
split.
- unfold DSpec.KEY. apply o4m_lor32.
  + pose proof (Z.mod_pos_bound kb 9 ltac:(lia)). lia.
  + change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound ab (2 ^ 16) ltac:(lia)). lia.
- assert (E : Z.land db 1 = db mod 2).
  { change (Z.land db 1) with (Z.land db (Z.ones 1)). rewrite Z.land_ones by lia. reflexivity. }
  rewrite E. pose proof (Z.mod_pos_bound db 2 ltac:(lia)) as Hm.
  destruct (Z.eq_dec (db mod 2) 0) as [E0|E0]; [left; exact E0|right; lia].
Qed.

(* submit_find_at answers -1 or an index below CMDS_MAX. *)
Lemma o4m_find_range : forall (fuel : nat) (B : list byte) (key i r : Z),
  0 <= i -> TOP.submit_find_at fuel B key i = Some r -> r = -1 \/ 0 <= r < TC.CMDS_MAX.
Proof.
induction fuel as [|f IH]; intros B key i r Hi H; cbn [TOP.submit_find_at] in H; [discriminate H|].
destruct (i <? TW.g_nq B).
- destruct (TC.CMDS_MAX <=? i) eqn:E1; [discriminate H|].
  destruct (TC.CMDS_MAX <=? TW.Q_at B i); [discriminate H|].
  destruct (TW.Cmd_key B (TW.Q_at B i) =? key); cbv beta iota in H.
  + right. apply Z.leb_gt in E1. injection H as E. subst r. lia.
  + exact (IH B key (i + 1) r ltac:(lia) H).
- left. cbv beta iota in H. injection H as E. subst r. reflexivity.
Qed.

(* at is -1 or an index below CMDS_MAX. *)
Lemma o4_at_range : forall (tv : ltg) (key at_ : Z), lc_at tv key = Some at_ -> at_ = -1 \/ 0 <= at_ < TC.CMDS_MAX.
Proof.
intros tv key at_ H. unfold lc_at in H.
destruct (negb (TC.h_coalescable_m key =? 0)); cbv beta iota in H.
- exact (o4m_find_range _ _ _ 0 at_ (Z.le_refl 0) H).
- left. injection H as E. subst at_. reflexivity.
Qed.

(* want is one of three codes. *)
Lemma o4_want_cases : forall (tv : ltg) (at_ : Z),
  lc_want tv at_ = DSpec.SPEC_OK \/ lc_want tv at_ = DSpec.SPEC_E_REFUSED \/ lc_want tv at_ = DSpec.SPEC_E_SPACE.
Proof.
intros tv at_. unfold lc_want.
destruct (lc_sys tv); [right; left; reflexivity|].
destruct ((at_ <? 0) && (TW.g_nq (tg_B2 tv) =? TC.QUEUE_MAX)); [right; right; reflexivity|left; reflexivity].
Qed.

(* The end of op_submit's tagged mode (TOps.v :274-275) under op 4's match (:311-312): a Some answer is settle's
   Some at B7, which keeps B7 (LLVMFuzzerTestOneInput_st.v lc_settle_world). *)
Lemma o4m_settle_tail : forall (Y : list byte) (cn : TOP.fuzz_in) (k : nat) (B' : list byte) (c' : TOP.fuzz_in)
    (k' : nat),
  match
    match TC.settle_m Y 0 with
    | None => None
    | Some (B8, _) => Some (B8, cn)
    end
  with
  | Some (B1, c2) => Some (B1, (c2, k))
  | None => None
  end = Some (B', (c', k')) ->
  TC.settle_m Y 0 = Some (Y, tt) /\ B' = Y /\ c' = cn /\ k' = k.
Proof.
intros Y cn k B' c' k' E.
destruct (TC.settle_m Y 0) as [[B8 u]|] eqn:Es; [|discriminate E].
pose proof (lc_settle_world Y B8 0 u Es) as EB. subst B8. destruct u.
cbv beta iota in E.
destruct (lc_some3 _ Y B' cn c' k k' eq_refl E) as (E1 & E2 & E3).
split; [first [exact Es | reflexivity]|].
split; [symmetry; exact E1|]. split; [symmetry; exact E2|]. symmetry; exact E3.
Qed.

(* The stores of g_cmd[serial] and of the queue (TOps.v :258-272), g_ncmd + 1 and settle (:273-275): a Some answer
   fixes the replace / append bounds, the world B7 and the cursor. *)
Lemma o4m_tail : forall (B5 : list byte) (s key disp len : Z) (cb : list byte) (want at_ : Z)
    (cn : TOP.fuzz_in) (k : nat) (B' : list byte) (c' : TOP.fuzz_in) (k' : nat),
  match
    match
      (if want =? DSpec.SPEC_OK then
         if 0 <=? at_ then
           if TC.CMDS_MAX <=? TW.Q_at (o4_cmdw B5 s key disp len cb) at_ then None
           else Some (TW.set_Q_at (TW.set_Cmd_st (o4_cmdw B5 s key disp len cb)
                                     (TW.Q_at (o4_cmdw B5 s key disp len cb) at_) TC.REPLACED) at_ s)
         else
           if TC.CMDS_MAX <=? TW.g_nq (o4_cmdw B5 s key disp len cb) then None
           else Some (TW.set_g_nq (TW.set_Q_at (o4_cmdw B5 s key disp len cb)
                                     (TW.g_nq (o4_cmdw B5 s key disp len cb)) s)
                        ((TW.g_nq (o4_cmdw B5 s key disp len cb) + 1) mod 2 ^ 32))
       else Some B5)
    with
    | None => None
    | Some B6 =>
        match TC.settle_m (TW.set_g_ncmd B6 ((TW.g_ncmd B6 + 1) mod 2 ^ 32)) 0 with
        | None => None
        | Some (B8, _) => Some (B8, cn)
        end
    end
  with
  | Some (B1, c2) => Some (B1, (c2, k))
  | None => None
  end = Some (B', (c', k')) ->
  (want = DSpec.SPEC_OK -> 0 <= at_ -> TW.Q_at (o4_cmdw B5 s key disp len cb) at_ < TC.CMDS_MAX) /\
  (want = DSpec.SPEC_OK -> at_ < 0 -> TW.g_nq (o4_cmdw B5 s key disp len cb) < TC.CMDS_MAX) /\
  TC.settle_m (o4_b7 (o4_b6 B5 (o4_cmdw B5 s key disp len cb) want at_ s)) 0 =
    Some (o4_b7 (o4_b6 B5 (o4_cmdw B5 s key disp len cb) want at_ s), tt) /\
  B' = o4_b7 (o4_b6 B5 (o4_cmdw B5 s key disp len cb) want at_ s) /\ c' = cn /\ k' = k.
Proof.
intros B5 s key disp len cb want at_ cn k B' c' k' E.
set (Bw := o4_cmdw B5 s key disp len cb) in *.
unfold o4_b6. revert E.
destruct (want =? DSpec.SPEC_OK) eqn:Ew.
- apply Z.eqb_eq in Ew.
  destruct (0 <=? at_) eqn:Ea.
  + apply Z.leb_le in Ea.
    destruct (TC.CMDS_MAX <=? TW.Q_at Bw at_) eqn:Eq; cbv beta iota; intros E; [discriminate E|].
    apply Z.leb_gt in Eq.
    destruct (o4m_settle_tail _ cn k B' c' k' E) as (Es & EB & EC & EK).
    split; [intros _ _; exact Eq|]. split; [intros _ Hn; lia|].
    split; [exact Es|]. split; [exact EB|]. exact (conj EC EK).
  + apply Z.leb_gt in Ea.
    destruct (TC.CMDS_MAX <=? TW.g_nq Bw) eqn:Eq; cbv beta iota; intros E; [discriminate E|].
    apply Z.leb_gt in Eq.
    destruct (o4m_settle_tail _ cn k B' c' k' E) as (Es & EB & EC & EK).
    split; [intros _ Hp; lia|]. split; [intros _ _; exact Eq|].
    split; [exact Es|]. split; [exact EB|]. exact (conj EC EK).
- apply Z.eqb_neq in Ew. cbv beta iota. intros E.
  destruct (o4m_settle_tail _ cn k B' c' k' E) as (Es & EB & EC & EK).
  split; [intros Hw; exfalso; exact (Ew Hw)|]. split; [intros Hw; exfalso; exact (Ew Hw)|].
  split; [exact Es|]. split; [exact EB|]. exact (conj EC EK).
Qed.

(* The segment's model: from the CMDW cut's equations and the operation's simulation facts, the model's Some
   (LoopOk.op_ok) fixes the replace / append bounds, settle keeps B7, and the operation's equation at every
   stream ends at B7 with the cursor tg_c. *)
Lemma o4_model : forall (D B0 B1 B3 B4 B5 : list byte) (c0 : TOP.fuzz_in) (k0 : nat) (ops at_ rc : Z),
  AG.agree timg_B ops B0 -> 0 <= ops < TC.OPS_MAX -> QF.fuzz_in_ok D c0 -> TOP.fi_n c0 <> 0 ->
  lc_opc D c0 = 4 ->
  TC.op_begin_m B0 = Some (B1, tt) -> TW.g_raw B1 = 0 ->
  let kd := lc_sub_kd D (lc_oc D c0) in
  let tv := lc_tag_vals D B1 (sv_c kd) in
  let cs := TOP.cmd_struct (tg_cbytes tv) (tg_len tv) (sv_display kd) (sv_key kd) in
  let want := lc_want tv at_ in
  let Bw := o4_cmdw B5 (tg_serial tv) (sv_key kd) (sv_display kd) (tg_len tv) (tg_cbytes tv) in
  let B7 := o4_b7 (o4_b6 B5 Bw want at_ (tg_serial tv)) in
  0 <= tg_serial tv < TC.CMDS_MAX ->
  lc_at tv (sv_key kd) = Some at_ ->
  TS0.diginet_session_submit_m (tg_B2 tv) cs = Some (B3, rc) ->
  TC.check_refusal_submit_m B3 cs rc (TW.S_queued B0) = Some (B4, tt) ->
  (if lc_sys tv then B5 = B4 else TC.check_latest_submit_m B4 rc want = Some (B5, tt)) ->
  (want = DSpec.SPEC_OK -> 0 <= at_ -> 0 <= TW.Q_at Bw at_ < TC.CMDS_MAX) /\
  (want = DSpec.SPEC_OK -> at_ < 0 -> 0 <= TW.g_nq Bw < TC.CMDS_MAX) /\
  TC.settle_m B7 0 = Some (B7, tt) /\
  (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_B B0 A D c0 k0 = Some (B7, (tg_c tv, k0))).
Proof.
intros D B0 B1 B3 B4 B5 c0 k0 ops at_ rc HA Hops Hc Hn Ho HOB HR.
cbv zeta. intros Hser Hat Hsub Href Hlat.
destruct (LOK.op_ok LP.links_holds timg_B ops B0 (fun _ => 1) D c0 k0 HA Hops Hc Hn
            ltac:(cbv beta; lia) ltac:(cbv beta; lia)) as (B' & c' & k' & E0 & _ & _).
assert (Hany : forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_B B0 A D c0 k0 =
                         TOP.LLVMFuzzerTestOneInput_op_m timg_B B0 (fun _ => 1) D c0 k0).
{ intros A. rewrite (lc_op4_eq timg_B B0 A D c0 k0 Ho), (lc_op4_eq timg_B B0 (fun _ => 1) D c0 k0 Ho).
  reflexivity. }
pose proof E0 as E'.
rewrite (lc_op4_eq timg_B B0 (fun _ => 1) D c0 k0 Ho) in E'.
rewrite (lc_submit_tag_eq B0 B1 D (lc_oc D c0) HOB HR) in E'.
cbv zeta in E'.
set (kd := lc_sub_kd D (lc_oc D c0)) in *.
set (tv := lc_tag_vals D B1 (sv_c kd)) in *.
rewrite (proj2 (Z.leb_gt TC.CMDS_MAX (tg_serial tv)) (proj2 Hser)) in E'. cbv beta iota in E'.
rewrite Hat in E'. cbv beta iota in E'.
rewrite Hsub in E'. cbv beta iota in E'.
rewrite Href in E'. cbv beta iota in E'.
assert (H5 : (if lc_sys tv then Some (B4, tt) else TC.check_latest_submit_m B4 rc (lc_want tv at_)) =
             Some (B5, tt)).
{ revert Hlat. destruct (lc_sys tv); intros Hlat; [rewrite Hlat; reflexivity|exact Hlat]. }
rewrite H5 in E'. cbv beta iota in E'.
destruct (o4m_tail B5 (tg_serial tv) (sv_key kd) (sv_display kd) (tg_len tv) (tg_cbytes tv) (lc_want tv at_) at_
            (tg_c tv) k0 B' c' k' E') as (Hq & Hg & Hs & EB & EC & EK).
split; [intros Hw Ha; split; [unfold TW.Q_at; apply QF.u_at_nonneg|exact (Hq Hw Ha)]|].
split; [intros Hw Ha; split; [unfold TW.g_nq; apply QF.u_at_nonneg|exact (Hg Hw Ha)]|].
split; [exact Hs|].
intros A. rewrite (Hany A), E0, EB, EC, EK. reflexivity.
Qed.
