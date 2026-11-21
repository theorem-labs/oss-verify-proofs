(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Export Z_kit Z_dview Z_drep Z_dkit Z_irep.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface InflateState InflateArms.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).



Lemma bv_swrap32_eqm : forall a b, (a - b) mod 2^32 = 0 -> bv_swrap 32 a = bv_swrap 32 b.
Proof.
  intros a b H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (2 ^ 32) with 4294967296 in H. change (4294967296 / 2) with 2147483648. Z.div_mod_to_equations. lia.
Qed.

Lemma swrap32_sub : forall x k c, c = 18446744073709551616 - k -> - 2^31 <= x - k < 2^31 -> bv_swrap 32 (x + c) = x - k.
Proof.
  intros x k c -> H. rewrite (bv_swrap32_eqm _ (x - k)); [apply bv_swrap32_id; exact H|].
  replace (x + (18446744073709551616 - k) - (x - k)) with (4294967296 * 4294967296) by lia. apply Z.mod_mul. lia.
Qed.

Lemma land_ones64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.


Ltac br_norm K := zify_cond K; rewrite ?unsigned_lit in K by lia; rewrite ?land_ones64 in K by lia.
Ltac br_true := let K := fresh "K" in if_cases K; br_norm K; [clear K | exfalso; lia].
Ltac br_false := let K := fresh "K" in if_cases K; br_norm K; [exfalso; lia | clear K].
Ltac br_cases K := if_cases K; br_norm K.


Ltac open_izs H :=
  let p1 := fresh "zp1" in let p2 := fresh "zp2" in let dt := fresh "zdt" in let p3 := fresh "zp3" in let r := fresh "zresv" in
  destruct H as (p1 & p2 & dt & p3 & r & H); unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE in H; cbn [app] in H.
Ltac open_isA H := unfold isA, isA_cells in H.
Ltac open_isT H := let pad := fresh "padT" in destruct H as (pad & H); unfold isT_cells in H.

Ltac open_IST ST :=
  let GA := fresh "GA" in let GT := fresh "GT" in let Gl := fresh "Gl" in let Gw := fresh "Gw" in let Gc := fresh "Gc" in
  let Gwin := fresh "Gwin" in let ARRS := fresh "ARRS" in let LAY := fresh "LAY" in
  destruct ST as [GA GT Gl Gw Gc Gwin ARRS LAY].

Ltac itr_groups MUf WMf :=
  lazymatch type of MUf with
  | munch ?W ?ma ?mb =>
      repeat match goal with
      | H : izs ma ?L ?c |- _ => apply (izs_munch ma mb L W c) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : isA ma ?L ?s |- _ => apply (isA_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : isT ma ?L ?s |- _ => apply (isT_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : ilens ma ?L ?s |- _ => apply (ilens_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : iwork ma ?L ?s |- _ => apply (iwork_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : icodes ma ?L ?s |- _ => apply (icodes_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : iwin ma ?L ?s |- _ => apply (iwin_munch ma mb L s W) in H;
          [ | exact MUf | exact WMf
            | let NE := fresh "NEw" in intros NE;
              try (match goal with P : is_window_blk s <> None -> _ = true |- _ => let HW := fresh "HASW" in pose proof (P NE) as HW end);
              cbn [disjoint_from]; slia ]
      end
  end.

Lemma rw_cells_read_sub : forall m A cs k c (o n : nat) a,
  rw_cells psegs m A cs -> cell_at cs k = Some c -> cell_wf c -> (o + n <= csize c)%nat -> a = wa (A + Z.of_nat k + Z.of_nat o) ->
  ov_read_bytes psegs m a n = Some (firstn n (skipn o (cbytes c))).
Proof.
  intros m A cs k c o n a [[Hwf Hb] _] Hc Hcw Hon ->.
  destruct (cell_at_split _ _ _ c Hc) as (pre & post & E & Hsz & _). subst cs.
  apply cells_wf_app in Hwf. destruct Hwf as [Wpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  assert (LC : length (cbytes c) = csize c).
  { destruct c; cbn [cbytes csize cell_wf] in *; rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; try reflexivity. exact Hcw. }
  replace (A + Z.of_nat k + Z.of_nat o) with (A + Z.of_nat (k + o)) by lia.
  rewrite (bytes_at_ov_read psegs m A _ (k + o) n Hb).
  2:{ rewrite !length_app, LC, (cells_bytes_length pre Wpre). lia. }
  f_equal. rewrite <- Hsz, <- (cells_bytes_length pre Wpre).
  rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
  replace (length (cells_bytes pre) + o - length (cells_bytes pre))%nat with o by lia.
  rewrite skipn_app, firstn_app. rewrite length_skipn, LC.
  replace (n - (csize c - o))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Ltac rd_sub H kn on nn :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let c := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs kn) in
      lazymatch c with
      | Some ?cc =>
          let k := eval vm_compute in (Z.of_nat kn + Z.of_nat on) in
          let RD := fresh "RD" in
          pose proof (rw_cells_read_sub m A cs kn cc on nn (wa (A + k)) H ltac:(cells_cbv; reflexivity) I ltac:(cbn; lia)
                        ltac:(f_equal; lia)) as RD;
          cbn [cbytes le4 le2 le8 firstn skipn Z_to_le_bytes] in RD
      end
  end.

Lemma bv8_unsigned_wrap : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma le1_zx8_wz : forall v, 0 <= v < 2^64 -> le1 (zx8 (wz v)) = [Z_to_bv 8 (wrap8 v)].
Proof.
  intros v H. unfold le1, zx8, wrap8. rewrite (Z_to_bv_unsigned 64 v), (bv_wrap_small 64 v) by (unfold bv_modulus; cbn; lia).
  assert (R : 0 <= v mod 2^8 < 2^8) by (apply Z.mod_pos_bound; lia).
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  cbn [Z_to_le_bytes]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity.
Qed.

Ltac ired := cbn [w_s w_c w_r is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits iset_wsize iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset iset_extra iset_lencode iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have iset_next iset_lens iset_work iset_codes iset_sane iset_back iset_was iset_self_blk icset_input icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out icset_adler icset_data_type icset_msg irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret wset_s wset_c wset_r].
Ltac inorm := unfold fixedtables; ired.
Ltac ired_in H := cbn [w_s w_c w_r is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits iset_wsize iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset iset_extra iset_lencode iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have iset_next iset_lens iset_work iset_codes iset_sane iset_back iset_was iset_self_blk icset_input icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out icset_adler icset_data_type icset_msg irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret wset_s wset_c wset_r] in H.

Ltac norm_bytes :=
  repeat match goal with
  | |- context [Z_to_bv 8 ?z] =>
      lazymatch z with Z0 => fail | Zpos _ => fail | Zneg _ => fail | _ => idtac end;
      let v := eval vm_compute in (bv_unsigned (Z_to_bv 8 z)) in
      replace (Z_to_bv 8 z) with (Z_to_bv 8 v) by (apply bv_eq; vm_compute; reflexivity)
  end.
Lemma le8_fixed_bits : le8 (wz 21474836489) = le4 (wz 9) ++ le4 (wz 5).
Proof. unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes app]. norm_bytes. reflexivity. Qed.

Lemma land_ones64_neg : forall x, - 2^63 <= x < 0 -> Z.land x 18446744073709551615 = x + 2^64.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 63) with 9223372036854775808 in H. Z.div_mod_to_equations. lia.
Qed.
