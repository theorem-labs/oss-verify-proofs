(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QzQg.

From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um2h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um2h.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSCw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSCw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTru.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTru. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U3Uw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U3Uw.Mq0.
Import ListNotations.
Import QlEo.Mq0.Exc. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := tt.
End GwI.

Lemma zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. first [GwInst.gw_exact (@QzQg.Mq2.zlength_app) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.zlength_app)]. Qed.
Lemma zlength_nil : zlength (@nil Z) = 0.
Proof. first [GwInst.gw_exact (@QzQg.Mq2.zlength_nil) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.zlength_nil)]. Qed.
Lemma zlength_concat_cons : forall {A} (p : list A) ps, zlength (concat (p :: ps)) = zlength p + zlength (concat ps).
Proof. first [GwInst.gw_exact (@QzQg.Mq2.zlength_concat_cons) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.zlength_concat_cons)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.tail_pieces) (@QSCw.tail_pieces) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_pieces_loop) (@QSCw.printf_pieces_loop) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_pieces) (@QSCw.printf_pieces) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_model) (@QSCw.printf_model) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_loop) (@QSCw.printf_loop) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pad_pieces) (@QSCw.pad_pieces) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.mpad) (@QSCw.mpad) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.int_pieces) (@QSCw.int_pieces) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.dec_digits) (@QSCw.dec_digits) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_tail) (@QSCw.conv_tail) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_pieces) (@QSCw.conv_pieces) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_int) (@QSCw.conv_int) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv) (@QSCw.conv) (Q6nq.gwt_def (@Q8l1.Mq1.SN_CAP) (@UTru.SN_CAP) (Q6nq.gwt_def (@Q8l1.Mq1.OUT_sn) (@UTru.OUT_sn) (Q6nq.gwt_def (@Q8l1.Mq1.OUTFP_sn) (@UTru.OUTFP_sn) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.FMT_d) (@QSCw.FMT_d) Q6nq.gwt_nil))))))))))))))))).
Lemma zlength_concat_app : ltac2:(Q6nq.tyx '(@QzQg.Mq2.zlength_concat_app) [] '(@nil Z) 'gwt_X).
Proof. first [GwInst.gw_exact (@QzQg.Mq2.zlength_concat_app) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.zlength_concat_app)]. Qed.
Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. first [GwInst.gw_exact (@QzQg.Mq2.zlength_nonneg) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.zlength_nonneg)]. Qed.

Lemma mbind_eq : ltac2:(Q6nq.tyx '(@QzQg.Mq2.mbind_eq) [] '(@nil Z) 'gwt_X).
Proof. first [GwInst.gw_exact (@QzQg.Mq2.mbind_eq) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.mbind_eq)]. Qed.

Lemma OUT_sn_eq : forall bs o, zlength o + zlength bs <= SN_CAP -> OUT_sn bs o = QlEo.Mq0.Ret (Ok (tt, o ++ bs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]]); first [GwInst.gw_exact (@QzQg.Mq2.OUT_sn_eq) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.OUT_sn_eq)]. Qed.

Lemma OUTFP_sn_eq : ltac2:(Q6nq.tyx '(@QzQg.Mq2.OUTFP_sn_eq) [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]] '(@nil Z) '(Q6nq.gwt_zc SN_CAP gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]]); first [GwInst.gw_exact (@QzQg.Mq2.OUTFP_sn_eq) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.OUTFP_sn_eq)]. Qed.

Lemma mbind_mbind_eq : ltac2:(Q6nq.tyx '(@QzQg.Mq2.mbind_mbind_eq) [] '(@nil Z) 'gwt_X).
Proof. first [GwInst.gw_exact (@QzQg.Mq2.mbind_mbind_eq) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.mbind_mbind_eq)]. Qed.

Lemma mpad_sn_eq : ltac2:(Q6nq.tyx '(@QzQg.Mq2.mpad_sn_eq) [[@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]; [@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_pad_pieces__3; @gw_eq_pad_pieces__2; @gw_eq_pad_pieces]] '(@nil Z) '(Q6nq.gwt_zc SN_CAP gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]; [@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_pad_pieces__3; @gw_eq_pad_pieces__2; @gw_eq_pad_pieces]]); first [GwInst.gw_exact (@QzQg.Mq2.mpad_sn_eq) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.mpad_sn_eq)]. Qed.

Ltac msn E := first [ rewrite (mbind_mbind_eq _ _ _ _ _ _ E) | rewrite (mbind_eq _ _ _ _ _ E) ]; cbv beta.

Lemma conv_tail_sn : ltac2:(Q6nq.tyx '(@QzQg.Mq2.conv_tail_sn) [[@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]; [@gw_eq_conv_tail__3; @gw_eq_conv_tail__2; @gw_eq_conv_tail]; [@gw_eq_tail_pieces__3; @gw_eq_tail_pieces__2; @gw_eq_tail_pieces]] '(@nil Z) '(Q6nq.gwt_zc SN_CAP gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]; [@gw_eq_conv_tail__3; @gw_eq_conv_tail__2; @gw_eq_conv_tail]; [@gw_eq_tail_pieces__3; @gw_eq_tail_pieces__2; @gw_eq_tail_pieces]]); first [GwInst.gw_exact (@QzQg.Mq2.conv_tail_sn) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.conv_tail_sn)]. Qed.

Lemma conv_int_sn : ltac2:(Q6nq.tyx '(@QzQg.Mq2.conv_int_sn) [[@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_int_pieces__3; @gw_eq_int_pieces__2; @gw_eq_int_pieces]] '(@nil Z) '(Q6nq.gwt_zc SN_CAP gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_int_pieces__3; @gw_eq_int_pieces__2; @gw_eq_int_pieces]]); first [GwInst.gw_exact (@QzQg.Mq2.conv_int_sn) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.conv_int_sn)]. Qed.

Lemma conv_sn : ltac2:(Q6nq.tyx '(@QzQg.Mq2.conv_sn) [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]; [@gw_eq_conv__3; @gw_eq_conv__2; @gw_eq_conv]; [@gw_eq_conv_pieces__3; @gw_eq_conv_pieces__2; @gw_eq_conv_pieces]] '(@nil Z) '(Q6nq.gwt_zc SN_CAP gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]; [@gw_eq_conv__3; @gw_eq_conv__2; @gw_eq_conv]; [@gw_eq_conv_pieces__3; @gw_eq_conv_pieces__2; @gw_eq_conv_pieces]]); first [GwInst.gw_exact (@QzQg.Mq2.conv_sn) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.conv_sn)]. Qed.

Lemma printf_loop_sn : ltac2:(Q6nq.tyx '(@QzQg.Mq2.printf_loop_sn) [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_printf_pieces_loop__3; @gw_eq_printf_pieces_loop__2; @gw_eq_printf_pieces_loop]] '(@nil Z) '(Q6nq.gwt_zc SN_CAP gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_printf_pieces_loop__3; @gw_eq_printf_pieces_loop__2; @gw_eq_printf_pieces_loop]]); first [GwInst.gw_exact (@QzQg.Mq2.printf_loop_sn) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.printf_loop_sn)]. Qed.

Theorem printf_model_sn : ltac2:(Q6nq.tyx '(@QzQg.Mq2.printf_model_sn) [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]; [@gw_eq_printf_model__3; @gw_eq_printf_model__2; @gw_eq_printf_model]; [@gw_eq_printf_pieces__3; @gw_eq_printf_pieces__2; @gw_eq_printf_pieces]] '(@nil Z) '(Q6nq.gwt_zc SN_CAP gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_SN_CAP__3; @gw_eq_SN_CAP__2; @gw_eq_SN_CAP]; [@gw_eq_printf_model__3; @gw_eq_printf_model__2; @gw_eq_printf_model]; [@gw_eq_printf_pieces__3; @gw_eq_printf_pieces__2; @gw_eq_printf_pieces]]); first [GwInst.gw_exact (@QzQg.Mq2.printf_model_sn) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.printf_model_sn)]. Qed.

Lemma dec_digits_step1 : forall x, 1 <= x < 2^64 -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10].
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [GwInst.gw_exact (@QzQg.Mq2.dec_digits_step1) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.dec_digits_step1)]. Qed.

Lemma dec_digits_pos_length : forall x, 1 <= x < 2^64 -> (1 <= length (dec_digits x))%nat.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [GwInst.gw_exact (@QzQg.Mq2.dec_digits_pos_length) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.dec_digits_pos_length)]. Qed.

Lemma dec_digits_len_bound : forall n x, 0 <= x < 10 ^ Z.of_nat n -> x < 2^64 -> (length (dec_digits x) <= n)%nat.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [GwInst.gw_exact (@QzQg.Mq2.dec_digits_len_bound) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.dec_digits_len_bound)]. Qed.

Lemma firstn_S_snoc : forall (l : list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof. first [GwInst.gw_exact (@QzQg.Mq2.firstn_S_snoc) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.firstn_S_snoc)]. Qed.

Lemma zsub_snoc : ltac2:(Q6nq.tyx '(@QzQg.Mq2.zsub_snoc) [] '(@nil Z) 'gwt_X).
Proof. first [GwInst.gw_exact (@QzQg.Mq2.zsub_snoc) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.zsub_snoc)]. Qed.

Lemma zsub_0 : forall l i, zsub l i 0 = [].
Proof. first [GwInst.gw_exact (@QzQg.Mq2.zsub_0) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.zsub_0)]. Qed.

Lemma fmt_u_loop_dec : ltac2:(Q6nq.tyx '(@QzQg.Mq2.fmt_u_loop_dec) [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [GwInst.gw_exact (@QzQg.Mq2.fmt_u_loop_dec) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.fmt_u_loop_dec)]. Qed.

Lemma pow10_20 : 2^64 < 10 ^ Z.of_nat 20.
Proof. first [GwInst.gw_exact (@QzQg.Mq2.pow10_20) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.pow10_20)]. Qed.

Lemma fmt_u_dec : ltac2:(Q6nq.tyx '(@QzQg.Mq2.fmt_u_dec) [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [GwInst.gw_exact (@QzQg.Mq2.fmt_u_dec) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.fmt_u_dec)]. Qed.

Ltac zb1 :=
match goal with
| |- context [?a <=? ?b] => first [replace (a <=? b) with true by (symmetry; apply Z.leb_le; lia) | replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia)]
| |- context [?a <? ?b] => first [replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)]
| |- context [?a =? ?b] => first [replace (a =? b) with true by (symmetry; apply Z.eqb_eq; lia) | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia)]
end; cbn [andb orb negb]; cbv beta iota.

Lemma FL1 : (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = true. Proof. first [GwInst.gw_exact (@QzQg.Mq2.FL1) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.FL1)]. Qed.
Lemma FL2 : (Z.land (Z.lxor 0 ZERO_PAD) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = false. Proof. first [GwInst.gw_exact (@QzQg.Mq2.FL2) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.FL2)]. Qed.
Lemma FL3 : (Z.land (Z.lxor 0 LEFT_ADJ) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = false. Proof. first [GwInst.gw_exact (@QzQg.Mq2.FL3) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.FL3)]. Qed.
Lemma FL4 : (Z.land 0 MARK_POS =? 0) = true. Proof. first [GwInst.gw_exact (@QzQg.Mq2.FL4) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.FL4)]. Qed.
Lemma FL5 : (Z.land 0 PAD_POS =? 0) = true. Proof. first [GwInst.gw_exact (@QzQg.Mq2.FL5) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.FL5)]. Qed.
Ltac fl0 := rewrite ?FL1, ?FL2, ?FL3, ?FL4, ?FL5; cbn [negb orb andb].

Ltac lhs_cbv1 := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces dec_digits] in l in change l with l' end.
Ltac lhs_cbv2 := match goal with |- ?l = _ => let l' := eval cbv -[int_pieces Z.modulo Z.pow Z.ltb INTMAX_MAX Z.opp dec_digits] in l in change l with l' end.

Lemma tail_pieces_d : ltac2:(Q6nq.tyx '(@QzQg.Mq2.tail_pieces_d) [[@gw_eq_tail_pieces__3; @gw_eq_tail_pieces__2; @gw_eq_tail_pieces]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_tail_pieces__3; @gw_eq_tail_pieces__2; @gw_eq_tail_pieces]]); first [GwInst.gw_exact (@QzQg.Mq2.tail_pieces_d) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.tail_pieces_d)]. Qed.

Lemma printf_pieces_d_pos : ltac2:(Q6nq.tyx '(@QzQg.Mq2.printf_pieces_d_pos) [[@gw_eq_FMT_d__3; @gw_eq_FMT_d__2; @gw_eq_FMT_d]; [@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_printf_pieces__3; @gw_eq_printf_pieces__2; @gw_eq_printf_pieces]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_FMT_d__3; @gw_eq_FMT_d__2; @gw_eq_FMT_d]; [@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_printf_pieces__3; @gw_eq_printf_pieces__2; @gw_eq_printf_pieces]]); first [GwInst.gw_exact (@QzQg.Mq2.printf_pieces_d_pos) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.printf_pieces_d_pos)]. Qed.

Lemma printf_pieces_d_neg : ltac2:(Q6nq.tyx '(@QzQg.Mq2.printf_pieces_d_neg) [[@gw_eq_FMT_d__3; @gw_eq_FMT_d__2; @gw_eq_FMT_d]; [@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_printf_pieces__3; @gw_eq_printf_pieces__2; @gw_eq_printf_pieces]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_FMT_d__3; @gw_eq_FMT_d__2; @gw_eq_FMT_d]; [@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_printf_pieces__3; @gw_eq_printf_pieces__2; @gw_eq_printf_pieces]]); first [GwInst.gw_exact (@QzQg.Mq2.printf_pieces_d_neg) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.printf_pieces_d_neg)]. Qed.

Lemma fmt_d_pos : forall x, 1 <= x < 2^31 -> fmt_d x = Some (dec_digits x, zlength (dec_digits x)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [GwInst.gw_exact (@QzQg.Mq2.fmt_d_pos) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.fmt_d_pos)]. Qed.

Lemma fmt_d_neg : forall x, -2^31 <= x < 0 -> fmt_d x = Some (45 :: dec_digits (- x), 1 + zlength (dec_digits (- x))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [GwInst.gw_exact (@QzQg.Mq2.fmt_d_neg) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.fmt_d_neg)]. Qed.

Theorem printf_sn_d : ltac2:(Q6nq.tyx '(@QzQg.Mq2.printf_sn_d) [[@gw_eq_FMT_d__3; @gw_eq_FMT_d__2; @gw_eq_FMT_d]; [@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_printf_model__3; @gw_eq_printf_model__2; @gw_eq_printf_model]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_FMT_d__3; @gw_eq_FMT_d__2; @gw_eq_FMT_d]; [@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_printf_model__3; @gw_eq_printf_model__2; @gw_eq_printf_model]]); first [GwInst.gw_exact (@QzQg.Mq2.printf_sn_d) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq2.printf_sn_d)]. Qed.

Ltac lhs_cbvg1 := match goal with |- ?l = _ => let l' := eval cbv -[fmt_fp f128_of_d conv OUT_sn OUTFP_sn mbind mret] in l in change l with l' end.
Ltac lhs_cbvg2 := match goal with |- ?l = _ => let l' := eval cbv -[fmt_fp f128_of_d OUT_sn OUTFP_sn mbind mret munr Z.ltb Z.leb orb Z.sub Z.add] in l in change l with l' end.

