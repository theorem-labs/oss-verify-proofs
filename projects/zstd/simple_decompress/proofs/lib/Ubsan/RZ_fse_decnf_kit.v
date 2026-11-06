(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition FDU (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 : word) (m : fmem) (SPV lo DST cap WK wksz SRCI DT : Z)
    (srci : list byte) (tb : list Z) (out : list byte) (m1 : fmem) : Prop :=
  u8arr usegs m1 DST out
  /\ zlen out = cap
  /\ stk usegs m1 WK (WK + wksz)
  /\ bytes_at usegs m1 SRCI srci
  /\ bytes_at usegs m1 (DT + 4) (map (Z_to_bv 8) tb)
  /\ stk usegs m1 lo (SPV + -192)
  /\ (exists (gap : list byte) (msv_slot tlog_slot : word),
        rw_cells usegs m1 (SPV + -192) [CB 8 gap; C4 msv_slot; C4 tlog_slot])
  /\ (exists state_w table_w : word, rw_cells usegs m1 (SPV + -176) [C8 state_w; C8 table_w])
  /\ (exists state_w table_w : word, rw_cells usegs m1 (SPV + -160) [C8 state_w; C8 table_w])
  /\ (exists (bits_w used_w : word) (gap : list byte) (cur_w start_w lim_w : word),
        rw_cells usegs m1 (SPV + -144) [C8 bits_w; C4 used_w; CB 4 gap; C8 cur_w; C8 start_w; C8 lim_w])
  /\ rw_cells usegs m1 (SPV + -104)
       [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0]
  /\ mem_inv usegs m1
  /\ munch [(DST, DST + cap); (WK, WK + wksz); (SPV - 448, SPV)] m m1
  /\ wmono usegs m m1.
Ltac open_fdu I := destruct I as (OUT & OLEN & WKS & SRCB & CELB & STK & (fj0 & fmsv & ftlw & F0) & (f2a & f2b & FS2) & (f1a & f1b & FS1)
                                  & (fbc & fbb & fbpad & fbp & fbs & fbl & FBD) & FSAV & MI & MU & WM).
Ltac close_fdu := unfold FDU; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                  split; [do 3 eexists; eassumption|]; split; [do 2 eexists; eassumption|]; split; [do 2 eexists; eassumption|];
                  split; [do 6 eexists; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

Definition FDCU (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 : word) (m : fmem) (SPV lo DST cap WK wksz SRCI DT : Z)
    (srci : list byte) (tb : list Z) (out : list byte) (st1 st2 : Z) (cont : word) (bc : Z) (pad : list byte) (ptr : Z)
    (m1 : fmem) : Prop :=
  u8arr usegs m1 DST out
  /\ zlen out = cap
  /\ stk usegs m1 WK (WK + wksz)
  /\ bytes_at usegs m1 SRCI srci
  /\ bytes_at usegs m1 (DT + 4) (map (Z_to_bv 8) tb)
  /\ stk usegs m1 lo (SPV + -192)
  /\ (exists (gap : list byte) (msv_slot tlog_slot : word),
        rw_cells usegs m1 (SPV + -192) [CB 8 gap; C4 msv_slot; C4 tlog_slot])
  /\ rw_cells usegs m1 (SPV + -176) [C8 (Z_to_bv 64 st2); C8 (Z_to_bv 64 (DT + 4))]
  /\ rw_cells usegs m1 (SPV + -160) [C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 (DT + 4))]
  /\ rw_cells usegs m1 (SPV + -144) (bitd_cells cont (Z_to_bv 64 bc) pad ptr SRCI)
  /\ rw_cells usegs m1 (SPV + -104)
       [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0]
  /\ mem_inv usegs m1
  /\ munch [(DST, DST + cap); (WK, WK + wksz); (SPV - 448, SPV)] m m1
  /\ wmono usegs m m1.
Ltac open_fdcu I := destruct I as (OUT & OLEN & WKS & SRCB & CELB & STK & (fj0 & fmsv & ftlw & F0) & FS2 & FS1 & FBD & FSAV & MI & MU & WM);
                    unfold bitd_cells in FBD.

Lemma fdcu_fdu : forall s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 m SPV lo DST cap WK wksz SRCI DT srci tb out st1 st2 cont bc pad ptr m1,
  FDCU s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 m SPV lo DST cap WK wksz SRCI DT srci tb out st1 st2 cont bc pad ptr m1 ->
  FDU s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 m SPV lo DST cap WK wksz SRCI DT srci tb out m1.
Proof.
  intros until m1; intros I. open_fdcu I. close_fdu.
Qed.

Lemma fse_cell_ok_0 : forall tl fast tb u, fse_cell_ok tl fast tb u -> fse_cell_ok tl 0 tb u.
Proof.
  unfold fse_cell_ok; cbv zeta. intros tl fast tb u (A & B & C & D).
  split; [exact A|]. split; [intros H; discriminate H|]. split; [exact C | exact D].
Qed.

Lemma sub_mod64 : forall a b, Z_to_bv 64 (a mod 18446744073709551616 - b mod 18446744073709551616) = Z_to_bv 64 (a - b).
Proof. intros. apply Z_to_bv_eqm. change 18446744073709551616 with (2^64). rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity. Qed.
Lemma sub_mod64l : forall a b, Z_to_bv 64 (a mod 18446744073709551616 - b) = Z_to_bv 64 (a - b).
Proof. intros. apply Z_to_bv_eqm. change 18446744073709551616 with (2^64). rewrite Zminus_mod_idemp_l. reflexivity. Qed.
Lemma sub_mod64r : forall a b, Z_to_bv 64 (a - b mod 18446744073709551616) = Z_to_bv 64 (a - b).
Proof. intros. apply Z_to_bv_eqm. change 18446744073709551616 with (2^64). rewrite Zminus_mod_idemp_r. reflexivity. Qed.
Ltac sub_norm := rewrite ?sub_mod64, ?sub_mod64l, ?sub_mod64r.

Definition fc_hi (tb : list Z) (st : Z) : Z := fc_sy tb st + 256 * fc_nb tb st.

Lemma fc_hi_rd : forall m A (tb : list Z) st a, bytes_at usegs m A (map (Z_to_bv 8) tb) ->
  0 <= st -> 4 * st + 4 <= Z.of_nat (length tb) ->
  0 <= Znth (4 * st + 2) tb < 256 -> 0 <= Znth (4 * st + 3) tb < 256 -> a = wa (A + (4 * st + 2)) ->
  ov_read_bytes usegs m a 2 = Some (le2 (Z_to_bv 64 (fc_hi tb st))).
Proof.
  intros m A tb st a tb_cells st_nonneg tb_room sy_byte nb_byte a_at.
  set (k := Z.to_nat (4 * st + 2)).
  assert (sy_slot : nth_error tb k = Some (fc_sy tb st)).
  { unfold fc_sy, Znth. apply nth_error_nth'. unfold k. lia. }
  assert (nb_slot : nth_error tb (S k) = Some (fc_nb tb st)).
  { unfold fc_nb, Znth. replace (Z.to_nat (4 * st + 3)) with (S k) by (unfold k; lia).
    apply nth_error_nth'. unfold k. lia. }
  assert (window : firstn 2 (skipn k tb) = [fc_sy tb st; fc_nb tb st]).
  { rewrite <- (firstn_skipn_step tb k 1 _ sy_slot), <- (firstn_skipn_step tb (S k) 0 _ nb_slot). reflexivity. }
  set (hw := fc_sy tb st + 256 * fc_nb tb st).
  assert (hw_low : hw mod 256 = fc_sy tb st).
  { unfold hw. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. unfold fc_sy. lia. }
  assert (hw_high : hw ≫ 8 = fc_nb tb st).
  { unfold hw. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite Z.mul_comm, Z_div_plus_full by lia. rewrite Z.div_small by (unfold fc_sy; lia). reflexivity. }
  assert (hw_word : bv_unsigned (Z_to_bv 64 hw) = hw) by (apply unsigned_lit; unfold hw, fc_sy, fc_nb; lia).
  rewrite a_at, (bytes_at_read usegs m A _ (4 * st + 2) 2 tb_cells) by (rewrite ?length_map; lia).
  change (Z.to_nat (4 * st + 2)) with k. rewrite skipn_map, firstn_map, window.
  unfold le2, fc_hi. fold hw. rewrite hw_word. cbn [Z_to_le_bytes map].
  rewrite hw_high, (Z_to_bv8_mod hw), hw_low. reflexivity.
Qed.

Ltac ldhi CELB DT tb st :=
  let a := cur_mem_addr in
  let RDc := fresh "RDc" in
  pose proof (fc_hi_rd _ (DT + 4) tb st a CELB ltac:(lia) ltac:(lia) ltac:(unfold fc_sy, fc_nb in *; lia) ltac:(unfold fc_sy, fc_nb in *; lia)
                ltac:(unfold wa; f_equal; lia)) as RDc;
  zstep; rewrite (zx16_u (fc_hi tb st)) by (unfold fc_hi; lia); clear RDc;
  let HI := fresh "HI" in assert (HI : 0 <= fc_hi tb st < 256 + 256 * fc_nb tb st) by (unfold fc_hi; lia).

Lemma fc_hi_nb : forall tb st, 0 <= fc_sy tb st < 256 -> fc_hi tb st * 65536 / 16777216 = fc_nb tb st.
Proof. intros tb st H. symmetry. apply Z.div_unique with (r := fc_sy tb st * 65536); [left; lia | unfold fc_hi; lia]. Qed.
Lemma fc_hi_lor : forall h nx, 0 <= nx < 65536 -> Z.lor (h * 65536) nx = h * 65536 + nx.
Proof.
  intros h nx H. apply (lor_add_disj 16); [lia | change (2^16) with 65536; lia |].
  change (2^16) with 65536. apply Z.mod_mul. lia.
Qed.
Lemma fc_hi_land : forall h nx, 0 <= nx < 65536 -> Z.land (h * 65536 + nx) 65535 = nx.
Proof.
  intros h nx H. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2^16) with 65536.
  rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma fc_hi_shr : forall h nx, 0 <= nx < 65536 -> (h * 65536 + nx) / 65536 = h.
Proof. intros h nx H. symmetry. apply Z.div_unique with (r := nx); [left; lia | lia]. Qed.
Lemma lxor_range : forall a b, 0 <= a < 18446744073709551616 -> 0 <= b < 18446744073709551616 -> 0 <= Z.lxor a b < 18446744073709551616.
Proof.
  intros a b. change 18446744073709551616 with (2 ^ 64). exact (Z_lxor_range a b).
Qed.
Lemma lxor_ltb1 : forall a b, 0 <= a -> 0 <= b -> a <> b -> (Z.lxor a b <? 1) = false.
Proof.
  intros a b a_nn b_nn a_ne_b.
  assert (x_nz : Z.lxor a b <> 0) by (rewrite Z.lxor_eq_0_iff; exact a_ne_b).
  assert (x_nn : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; tauto).
  apply Z.ltb_ge. lia.
Qed.

Ltac znorm_step :=
  match goal with
  | |- context [?x ≪ ?k] =>
      is_Zlit_zb k;
      let p := eval vm_compute in (2 ^ k) in
      replace (x ≪ k) with (x * p) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity)
  | |- context [?x ≫ ?k] =>
      is_Zlit_zb k;
      let p := eval vm_compute in (2 ^ k) in
      replace (x ≫ k) with (x / p) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity)
  | |- context [fc_hi ?tb ?st * 65536 / 16777216] => rewrite (fc_hi_nb tb st) by lia
  | |- context [Z.lor (?h * 65536) ?nx] => rewrite (fc_hi_lor h nx) by lia
  | |- context [Z.land (?h * 65536 + ?nx) 65535] => rewrite (fc_hi_land h nx) by lia
  | |- context [(?h * 65536 + ?nx) / 65536] => rewrite (fc_hi_shr h nx) by lia
  | |- context [Z.lxor ?a ?b <? 1] => rewrite (lxor_ltb1 a b) by lia
  | |- context [Z.lxor ?a ?b mod 18446744073709551616] =>
      rewrite (Z.mod_small (Z.lxor a b) 18446744073709551616) by (apply lxor_range; lia)
  | |- context [Z.lxor ?a ?b] =>
      assert_fails (idtac; match constr:(Z.lxor a b) with context [?y] => is_var y end);
      let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
  | |- context [?a mod ?b] =>
      assert_fails (idtac; match constr:(a mod b) with context [?y] => is_var y end);
      let v := eval vm_compute in (a mod b) in change (a mod b) with v
  | |- context [?e mod 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
  | |- context [bv_swrap 32 ?e] => rewrite (swrap32_small e) by lia
  | |- context [Z.land ?x ?c] =>
      is_Zlit_zb c;
      let n := eval vm_compute in (Z.log2 (c + 1)) in
      let p := eval vm_compute in (2 ^ n) in
      let q := eval vm_compute in (c + 1) in
      constr_eq p q;
      replace (Z.land x c) with (x mod p) by (change c with (Z.ones n); rewrite Z.land_ones by lia; reflexivity)
  | |- context [?e / ?c] => is_Zlit_zb c; rewrite (Z.div_small e c) by lia
  | |- context [?a <? ?b] =>
      first [ rewrite (proj2 (Z.ltb_ge a b)) by lia | rewrite (proj2 (Z.ltb_lt a b)) by lia ]
  | |- context [Z.b2z false] => change (Z.b2z false) with 0
  | |- context [Z.b2z true] => change (Z.b2z true) with 1
  end.
Ltac znorm := repeat znorm_step.
Ltac close_fdcu :=
  let rec fill :=
    lazymatch goal with
    | |- _ /\ _ => refine (conj _ _); [fill | fill]
    | |- exists _, _ => eexists; fill
    | |- _ => eassumption
    end in
  lazymatch goal with
  | |- FDCU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold FDCU, bitd_cells; fill
  end.
Ltac zn := zstep; znorm.
Ltac zbr :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in
      first [ if_cases K; zify_cond K; [solve [exfalso; lia] | ]
            | if_cases K; zify_cond K; [ | solve [exfalso; lia]]
            | fail 1 "zc: neither side refuted" ]
  | _ => idtac
  end.
Ltac zc := zn; zbr.
