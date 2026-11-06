(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEC.

Definition b2z (b : bool) : Z := if b then 1 else 0.

Definition mode_code (m : pmode) : Z :=
  match m with
  | Mroot => 0 | Maccept => 1 | Marray => 2 | Miarray => 3 | Mtarray => 4 | Mkey => 5 | Mval => 6 | Mtkey => 7 | Mtval => 8 | Mikey => 9 | Mival => 10
  end.
Definition ps_conv (t : UbjRef.pstate) : PM.pstate := PM.PS (mode_code (ps_mode t)) (ps_len t) (ps_type t) (ps_idx t).

Definition stk_conv (stk : list UbjRef.pstate) : list PM.pstate := map ps_conv (rev stk).

Lemma mode_code_range m : 0 <= mode_code m <= 10.
Proof. destruct m; cbn; lia. Qed.
Lemma mode_code_inj m m' : mode_code m = mode_code m' -> m = m'.
Proof. destruct m, m'; cbn; intros H; try reflexivity; discriminate. Qed.
Lemma stk_conv_length stk : length (stk_conv stk) = length stk.
Proof. unfold stk_conv. rewrite length_map, length_rev. reflexivity. Qed.
Lemma stk_conv_cons t r : stk_conv (t :: r) = stk_conv r ++ [ps_conv t].
Proof. unfold stk_conv. cbn [rev]. rewrite map_app. reflexivity. Qed.

Section WithImage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable E : pe_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.

Abbreviation parser_at := (PM.parser_at segs A acc ann).
Abbreviation iss_at := (PM.iss_at segs A acc).
Abbreviation sink_at := (PESK.sink_at segs L acc ann).

Record enc : Type := ENC { en_b : Z; en_k : Z; en_stk : list UbjRef.eitem  ; en_depth : Z }.
Definition ecap (k : Z) : Z := if k =? 0 then 0 else 2 ^ (k - 1).
Definition ESZ : Z := 24.
Definition enc_own (en : enc) : list (Z * Z) := if en_k en =? 0 then [] else [(en_b en, ESZ * ecap (en_k en))].

Definition eitem_at (M : word -> option byte) (a : Z) (e : UbjRef.eitem) : Prop :=
  L5.u32_at segs M a (ei_kind e) /\ L5.u64_at segs M (a + 8) (ei_len e) /\ L5.u64_at segs M (a + 16) (ei_cnt e).

Definition enc_at (M : word -> option byte) (ov fb : Z) (en : enc) : Prop :=
  L5.u64_at segs M ov (pe_vt E) /\ L5.u64_at segs M (ov + 8) (PESK.o_sink E fb) /\ L5.u32_at segs M (ov + 16) UbjRef.MAX_DEPTH
  /\ L5.u64_at segs M (ov + 24) (en_b en)
  /\ L5.u64_at segs M (ov + 32) (en_b en + ESZ * Z.of_nat (length (en_stk en)))
  /\ L5.u64_at segs M (ov + 40) (en_b en + ESZ * ecap (en_k en))
  /\ L5.u32_at segs M (ov + 48) (en_depth en)
  /\ L5.defined M ov 56 /\ acc M ov 56
  /\ 0 <= en_k en <= 12 /\ Z.of_nat (length (en_stk en)) <= ecap (en_k en) /\ 0 <= en_depth en <= UbjRef.MAX_DEPTH + 1
  /\ (en_k en = 0 -> en_b en = 0)
  /\ (0 < en_k en ->
        en_b en mod 8 = 0 /\ L5.defined M (en_b en) (ESZ * ecap (en_k en)) /\ block_range L (en_b en) (ESZ * ecap (en_k en))
        /\ acc M (en_b en) (ESZ * Z.of_nat (length (en_stk en)))
        /\ ann M (en_b en) (ESZ * Z.of_nat (length (en_stk en))) (ESZ * ecap (en_k en)))
  /\ (forall i, (i < length (en_stk en))%nat -> eitem_at M (en_b en + ESZ * Z.of_nat i) (nth i (en_stk en) (EI 0 0 0))).

Definition enc0 : enc := ENC 0 0 [] 0.

Definition pot_estack (k : Z) : credit :=
  (hl_k_per_malloc L * (12 - k), ESZ * (2 ^ 12 - 2 ^ k) + (12 - k) * hl_b_overhead L).

Definition pos_of (p : list Z) (src : PM.srcst) (sm : PM.strm) : Z := blen p - PM.unread src sm.
Definition content_ok (M : word -> option byte) (fb : Z) (p : list Z) (src : PM.srcst) (str : PM.vstr) (sm : PM.strm) : Prop :=
  PM.vs_size str = blen p
  /\ L5.bytes_at segs M (PM.vs_data (PMSP.o_is A fb + 80) str) p
  /\ 0 <= pos_of p src sm
  /\ L5.bytes_at segs M (PM.sr_de src) (UbjRef.slice p (pos_of p src sm) (PM.sr_rem src))
  /\ (PM.sm_st sm = 2 -> PM.sm_g sm = PM.sm_eg sm).

Definition clink (p : list Z) (X : UbjRef.st) (s : PM.pst) (sm : PM.strm) (en : enc) (k : PESK.sink) : Prop :=
  PM.p_more s = b2z (s_more X) /\ PM.p_done s = b2z (s_done X) /\ PM.p_depth s = s_depth X
  /\ PM.p_stk s = stk_conv (s_stk X)
  /\ (s_more X = true -> s_done X = false -> pos_of p (PM.p_src s) sm = s_pos X)
  /\ en_stk en = rev (s_estk X) /\ en_depth en = s_edepth X
  /\ s_lo X <= PESK.sk_z k <= s_hi X
  /\ s_bad X = false.

Definition ec_state (M : word -> option byte) (fb : Z) (e : bool) (cat : Z) : Prop :=
  if e then exists v, 1 <= v <= 64 /\ PMSP.ec_at segs M (PMSP.o_ec A fb) v (pa_errcat_obj A)
  else PMSP.ec_at segs M (PMSP.o_ec A fb) 0 cat.

Definition owned (s : PM.pst) (en : enc) (k : PESK.sink) : list (Z * Z) := PM.parser_own s ++ enc_own en ++ PESK.sink_own k.
Lemma owned_app s en k LBX : PM.parser_own s ++ (enc_own en ++ PESK.sink_own k ++ LBX) = owned s en k ++ LBX.
Proof. unfold owned. rewrite <- !app_assoc. reflexivity. Qed.

Definition crun_pre (P : PESK.sink_policy) (M : word -> option byte) (fb : Z) (p : list Z) (X : UbjRef.st)
           (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : enc) (k : PESK.sink) (e : bool) (cat : Z) : Prop :=
  parser_at M (PMSP.o_p A fb) (PMSP.o_is A fb) s /\ iss_at M (PMSP.o_is A fb) str sm
  /\ enc_at M (PMSP.o_v A fb) fb en /\ L5.u64_at segs M (PMSP.o_p A fb + 384) (PMSP.o_v A fb)
  /\ sink_at P M (PESK.o_sink E fb) k
  /\ PMST.base_ok segs A M /\ PEST.err_ok segs A E M e /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
  /\ content_ok M fb p (PM.p_src s) str sm
  /\ clink p X s sm en k
  /\ ec_state M fb (s_ec X) cat
  /\ (s_ec X = true -> e = true).

Definition W_crun (fb : Z) : list L5.range :=
  PMSP.W_run A fb ++ [(PMSP.o_v A fb, 56); (PESK.o_sink E fb, 24)].

Definition W_enc (fb : Z) : list L5.range :=
  [(PMSP.o_v A fb, 56); (PESK.o_sink E fb, 24); (PMSP.o_ec A fb, 16)] ++ PMSP.err_W A.

Definition credit_add (c d : credit) : credit := (fst c + fst d, snd c + snd d).
Definition pot_all (P : PESK.sink_policy) (s : PM.pst) (en : enc) (k : PESK.sink) : credit :=
  credit_add (PM.pot_parser L s) (credit_add (pot_estack (en_k en)) (PESK.sink_pot P (PESK.sk_c k))).
Definition pot_enc (P : PESK.sink_policy) (en : enc) (k : PESK.sink) : credit :=
  credit_add (pot_estack (en_k en)) (PESK.sink_pot P (PESK.sk_c k)).

End WithImage.

Lemma ecap_nonneg k : 0 <= ecap k.
Proof. unfold ecap. destruct (k =? 0); [lia|]. apply Z.pow_nonneg. lia. Qed.
Lemma ecap_step k : 1 <= k -> ecap (k + 1) = 2 * ecap k.
Proof.
  intros Hk. unfold ecap.
  replace (k + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (k + 1 - 1) with (k - 1 + 1) by lia. rewrite Z.pow_add_r, Z.pow_1_r; lia.
Qed.
Lemma ecap_1 : ecap 1 = 1. Proof. reflexivity. Qed.

End PEC.
