(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep F_memcpy F_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).


Ltac unfold_ds_sizes_in X := unfold apart, blk_ok in X.

Lemma dlay_ranges : forall L, dlay_ok L ->
  (0 < dl_As L /\ dl_As L + 5968 < 2^62) /\ (0 < dl_Aw L /\ dl_Aw L + 65536 < 2^62) /\ (0 < dl_Ap L /\ dl_Ap L + 65536 < 2^62)
  /\ (0 < dl_Ah L /\ dl_Ah L + 65536 < 2^62) /\ (0 < dl_Ab L /\ dl_Ab L + 65536 < 2^62) /\ (0 < dl_S L /\ dl_S L + 112 < 2^63).
Proof.
  intros L H. destruct (lo_s L H) as (a1 & _ & a2 & _). destruct (lo_w L H) as (b1 & _ & b2 & _). destruct (lo_p L H) as (c1 & _ & c2 & _).
  destruct (lo_h L H) as (d1 & _ & d2 & _). destruct (lo_b L H) as (e1 & _ & e2 & _). destruct (lo_S L H) as (f1 & _ & f2).
  lia.
Qed.

Ltac lay_open LAY :=
  let R := fresh "LAYR" in
  pose proof (dlay_ranges _ LAY) as R;
  let a := fresh "Rs" in let b := fresh "Rw" in let c := fresh "Rp" in let d := fresh "Rh" in let e := fresh "Rb" in let f := fresh "RS" in
  destruct R as (a & b & c & d & e & f).

Ltac below_open BEL :=
  unfold dlay_below in BEL;
  let a := fresh "Bimg" in let b := fresh "Bs" in let c := fresh "Bw" in let d := fresh "Bp" in let e := fresh "Bh" in let f := fresh "Bb" in let g := fresh "BS" in
  destruct BEL as (a & b & c & d & e & f & g).

Ltac zsep_with LAY f :=
  let X := fresh "SEP" in pose proof (f _ LAY) as X || pose proof (f _ _ _ _ LAY) as X; unfold_ds_sizes_in X;
  first [ clear - X; lia | lia ].
Ltac zsep_io :=
  lazymatch goal with
  | IO : dio_sep ?L _ _ _ |- _ =>
      lazymatch goal with
      | |- context [dl_NO L] =>
          lazymatch goal with
          | |- context [dl_NI L] => zsep_with IO io_io
          | |- context [dl_As L] => zsep_with IO io_os
          | |- context [dl_Aw L] => zsep_with IO io_ow
          | |- context [dl_Ap L] => zsep_with IO io_op
          | |- context [dl_Ah L] => zsep_with IO io_oh
          | |- context [dl_Ab L] => zsep_with IO io_ob
          end
      | |- context [dl_NI L] =>
          lazymatch goal with
          | |- context [dl_As L] => zsep_with IO io_is
          | |- context [dl_Aw L] => zsep_with IO io_iw
          | |- context [dl_Ap L] => zsep_with IO io_ip
          | |- context [dl_Ah L] => zsep_with IO io_ih
          | |- context [dl_Ab L] => zsep_with IO io_ib
          end
      end
  end.
Ltac zsep_blk :=
  lazymatch goal with
  | LAY : dlay_ok ?L |- _ =>
      lazymatch goal with
      | |- context [dl_As L] =>
          lazymatch goal with
          | |- context [dl_Aw L] => zsep_with LAY lo_sw
          | |- context [dl_Ap L] => zsep_with LAY lo_sp
          | |- context [dl_Ah L] => zsep_with LAY lo_sh
          | |- context [dl_Ab L] => zsep_with LAY lo_sb
          end
      | |- context [dl_Aw L] =>
          lazymatch goal with
          | |- context [dl_Ap L] => zsep_with LAY lo_wp
          | |- context [dl_Ah L] => zsep_with LAY lo_wh
          | |- context [dl_Ab L] => zsep_with LAY lo_wb
          end
      | |- context [dl_Ap L] =>
          lazymatch goal with
          | |- context [dl_Ah L] => zsep_with LAY lo_ph
          | |- context [dl_Ab L] => zsep_with LAY lo_pb
          end
      | |- context [dl_Ah L] =>
          lazymatch goal with
          | |- context [dl_Ab L] => zsep_with LAY lo_hb
          end
      end
  end.

Ltac zsep := first [ zsep_io | zsep_blk ].

Ltac k1_clr_all := repeat match goal with H : _ |- _ => clear H end.
Ltac k1_lia_small := solve [ k1_clr_all; lia ].
Ltac k1_bnd :=
  match goal with
  | B : (0 < ?X /\ _)%Z |- context [?X] => solve [ clear - B; lia ]
  | B : (0 <= ?X /\ _)%Z |- context [?X] => solve [ clear - B; lia ]
  | B : (0 < ?X)%Z |- context [?X] => solve [ clear - B; lia ]
  end.
Ltac k1_stk :=
  match goal with
  | S : stk _ _ ?lo _ |- _ =>
      solve [ repeat match goal with
              | H : ?T |- _ => lazymatch T with context [lo] => fail | _ => clear H end
              end; lia ]
  end.
Ltac k1_zsep_fast_with LAY f :=
  let X := fresh "SEP" in (pose proof (f _ LAY) as X || pose proof (f _ _ _ _ LAY) as X); unfold_ds_sizes_in X;
  clear - X; lia.
Ltac k1_zsep_io :=
  lazymatch goal with
  | IO : dio_sep ?L _ _ _ |- _ =>
      lazymatch goal with
      | |- context [dl_NO L] =>
          lazymatch goal with
          | |- context [dl_NI L] => k1_zsep_fast_with IO io_io
          | |- context [dl_As L] => k1_zsep_fast_with IO io_os
          | |- context [dl_Aw L] => k1_zsep_fast_with IO io_ow
          | |- context [dl_Ap L] => k1_zsep_fast_with IO io_op
          | |- context [dl_Ah L] => k1_zsep_fast_with IO io_oh
          | |- context [dl_Ab L] => k1_zsep_fast_with IO io_ob
          end
      | |- context [dl_NI L] =>
          lazymatch goal with
          | |- context [dl_As L] => k1_zsep_fast_with IO io_is
          | |- context [dl_Aw L] => k1_zsep_fast_with IO io_iw
          | |- context [dl_Ap L] => k1_zsep_fast_with IO io_ip
          | |- context [dl_Ah L] => k1_zsep_fast_with IO io_ih
          | |- context [dl_Ab L] => k1_zsep_fast_with IO io_ib
          end
      end
  end.
Ltac k1_zsep_blk :=
  lazymatch goal with
  | LAY : dlay_ok ?L |- _ =>
      lazymatch goal with
      | |- context [dl_As L] =>
          lazymatch goal with
          | |- context [dl_Aw L] => k1_zsep_fast_with LAY lo_sw
          | |- context [dl_Ap L] => k1_zsep_fast_with LAY lo_sp
          | |- context [dl_Ah L] => k1_zsep_fast_with LAY lo_sh
          | |- context [dl_Ab L] => k1_zsep_fast_with LAY lo_sb
          end
      | |- context [dl_Aw L] =>
          lazymatch goal with
          | |- context [dl_Ap L] => k1_zsep_fast_with LAY lo_wp
          | |- context [dl_Ah L] => k1_zsep_fast_with LAY lo_wh
          | |- context [dl_Ab L] => k1_zsep_fast_with LAY lo_wb
          end
      | |- context [dl_Ap L] =>
          lazymatch goal with
          | |- context [dl_Ah L] => k1_zsep_fast_with LAY lo_ph
          | |- context [dl_Ab L] => k1_zsep_fast_with LAY lo_pb
          end
      | |- context [dl_Ah L] =>
          lazymatch goal with
          | |- context [dl_Ab L] => k1_zsep_fast_with LAY lo_hb
          end
      end
  end.

Ltac k1_zsep_fast := first [ k1_zsep_io | k1_zsep_blk ].
Ltac k1_side := first [ exact I | k1_zsep_fast | lia ].
Ltac k1_base a := lazymatch a with Z.add ?x _ => k1_base x | Z.sub ?x _ => k1_base x | _ => a end.
Ltac k1_pick_disj b :=
  lazymatch goal with
  | |- ((?lo <= _ /\ _ <= ?hi) \/ _)%Z =>
      first [ first [ let bl := k1_base lo in constr_eq bl b | let bh := k1_base hi in constr_eq bh b ]; left
            | right; k1_pick_disj b ]
  | |- (?lo <= _ /\ _ <= ?hi)%Z => first [ let bl := k1_base lo in constr_eq bl b | let bh := k1_base hi in constr_eq bh b ]
  end.
Ltac k1_inside :=
  solve [ simpl_sizes;
          lazymatch goal with |- context [(_ <= ?a /\ ?a + _ <= _)%Z] => let b := k1_base a in k1_pick_disj b end;
          lia ].

Ltac io_open IO :=
  let a := fresh "IOi" in let b := fresh "IOo" in
  pose proof (io_ni _ _ _ _ IO) as a; pose proof (io_no _ _ _ _ IO) as b.

Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::=
  first [ exact I | k1_zsep_fast
        | solve [ repeat (match goal with |- _ /\ _ => split end);
                  first [ exact I | k1_zsep_fast | lia | zsep ] ]
        | lia ].

Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; first [ k1_inside | simpl_sizes; slia ] ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.



Ltac open_zs H :=
  let p1 := fresh "zp1" in let p2 := fresh "zp2" in let p3 := fresh "zp3" in let r := fresh "zresv" in
  destruct H as (p1 & p2 & p3 & r & H); unfold zs_call_cells, zs_priv_cells in H; cbn [app] in H.
Ltac open_A H :=
  let h1 := fresh "hA1" in let h2 := fresh "hA2" in let h3 := fresh "hA3" in let h4 := fresh "hA4" in let h5 := fresh "hA5" in
  destruct H as (h1 & h2 & h3 & h4 & h5 & H); unfold dsA_cells in H.
Ltac open_B H :=
  let h1 := fresh "hB1" in let h2 := fresh "hB2" in let h3 := fresh "hB3" in
  destruct H as (h1 & h2 & h3 & H); unfold dsB_cells in H.
Ltac open_C H := unfold dsC, dsC_cells in H.
Ltac open_D H :=
  let h0 := fresh "hD0" in let h1 := fresh "hD1" in let h2 := fresh "hD2" in let h3 := fresh "hD3" in let h4 := fresh "hD4" in
  destruct H as (h0 & h1 & h2 & h3 & h4 & H); unfold dsD_cells in H.

Ltac open_win H := unfold dwin in H;
  lazymatch type of H with u8arr _ _ _ (av8 ?a ?n) => let LW := fresh "LW" in pose proof (av8_zlength a n ltac:(lia)) as LW end.
Ltac open_pend H := unfold dpend in H;
  lazymatch type of H with u8arr _ _ _ (av8 ?a ?n) => let LW := fresh "LPB" in pose proof (av8_zlength a n ltac:(lia)) as LW end.
Ltac open_dep H := unfold ddep in H;
  lazymatch type of H with u8arr _ _ _ (av8 ?a ?n) => let LW := fresh "LDEP" in pose proof (av8_zlength a n ltac:(lia)) as LW end.
Ltac open_u16 H := unfold dprev, dhead, dblc, u16arr in H;
  lazymatch type of H with u8arr _ _ _ (u16s (av16 ?a ?n)) => let LW := fresh "L16" in pose proof (av16_zlength a n ltac:(lia)) as LW end.
Ltac open_ct H := unfold dlt, ddt, dbt, u16arr in H;
  lazymatch type of H with u8arr _ _ _ (u16s (avct ?fc ?dl ?n)) => let LW := fresh "LCT" in pose proof (avct_zlength fc dl n ltac:(lia)) as LW end.

Ltac open_DST ST :=
  let HA := fresh "GA" in let HB := fresh "GB" in let HC := fresh "GC" in let HD := fresh "GD" in
  let Hlt := fresh "Glt" in let Hdt := fresh "Gdt" in let Hbt := fresh "Gbt" in let Hblc := fresh "Gblc" in
  let Hheap := fresh "Gheap" in let Hdep := fresh "Gdep" in
  let Hwin := fresh "Gwin" in let Hprev := fresh "Gprev" in let Hhead := fresh "Ghead" in let Hpend := fresh "Gpend" in
  let Hlens := fresh "LENS" in let Hlay := fresh "LAY" in
  destruct ST as [HA HB HC HD Hlt Hdt Hbt Hblc Hheap Hdep Hwin Hprev Hhead Hpend Hlens Hlay].

Ltac close_lens LENS :=
  let l1 := fresh in let l2 := fresh in let l3 := fresh in let l4 := fresh in let l5 := fresh in let l6 := fresh in let l7 := fresh in
  let l8 := fresh in let l9 := fresh in let l10 := fresh in let l11 := fresh in let l12 := fresh in let l13 := fresh in
  destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13];
  constructor; [exact l1| exact l2| exact l3| exact l4| exact l5| exact l6| exact l7| exact l8| exact l9| exact l10| exact l11| exact l12| exact l13].


Lemma cs_emit_out_len : forall c l, length (cs_out_rev (cs_emit c l)) = (length (cs_out_rev c) + length l)%nat.
Proof.
  intros c l. unfold cs_emit. destruct c as [ci cn ca o cao cti cto cm cd cad]. cbn [DeflateState.cs_out_rev cset_out_rev].
  rewrite rev_append_rev, length_app, length_rev. lia.
Qed.

Lemma arr_slice_length' : forall {X} (a : parr X) ofs n, length (arr_slice a ofs n) = Z.to_nat n.
Proof. intros. unfold arr_slice. apply arr_slice_nat_length. Qed.


Ltac tr_groups MUf WMf :=
  lazymatch type of MUf with
  | munch ?W ?ma ?mb =>
      repeat match goal with
      | H : dsA ma ?L ?s |- _ => apply (dsA_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dsB ma ?L ?s |- _ => apply (dsB_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dsBi ma ?L ?s |- _ => apply (dsBi_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dsC ma ?L ?s |- _ => apply (dsC_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dsD ma ?L ?s |- _ => apply (dsD_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dlt ma ?L ?s |- _ => apply (dlt_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : ddt ma ?L ?s |- _ => apply (ddt_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dbt ma ?L ?s |- _ => apply (dbt_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dblc ma ?L ?s |- _ => apply (dblc_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dheap ma ?L ?s |- _ => apply (dheap_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : ddep ma ?L ?s |- _ => apply (ddep_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dwin ma ?L ?s |- _ => apply (dwin_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dprev ma ?L ?s |- _ => apply (dprev_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dhead ma ?L ?s |- _ => apply (dhead_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dpend ma ?L ?s |- _ => apply (dpend_munch ma mb L s W) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      | H : dzs ma ?L ?c |- _ => apply (dzs_munch ma mb L W c) in H; [ | exact MUf | exact WMf | cbn [disjoint_from]; slia ]
      end
  end.


Lemma le4_refl_wz : forall (w : word) v, w = wz v -> le4 w = le4 (wz v).
Proof. intros w v ->. reflexivity. Qed.

Ltac cell_eq :=
  first [ reflexivity
        | f_equal; lia
        | apply Z_to_bv_eqm; rewrite ?wrap64_mod, ?wrap32_mod, ?Z.mod_mod by lia; first [ reflexivity | Z.div_mod_to_equations; lia ]
        | apply le4_wz_mod; rewrite ?Z_to_bv_unsigned, ?wrap32_mod; unfold bv_wrap, bv_modulus; cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul];
          Z.div_mod_to_equations; lia
        | apply le2_wz_mod; rewrite ?Z_to_bv_unsigned, ?wrap16_mod; unfold bv_wrap, bv_modulus; cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul];
          Z.div_mod_to_equations; lia ].

Ltac cells_sim_tac :=
  cbn [cells_sim cell_sim];
  repeat match goal with
  | |- _ /\ _ => split
  | |- True => exact I
  | |- _ => solve [cell_eq]
  end.

Ltac close_cells H := eapply rw_cells_sim; [exact H| cells_sim_tac].


Lemma rw_cells_read_lo4 : forall m A cs k v a,
  rw_cells usegs m A cs -> cell_at cs k = Some (C8 v) -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes usegs m a 4 = Some (le4 v).
Proof.
  intros m A cs k v a [[Hwf Hb] _] Hc ->.
  destruct (cell_at_split _ _ _ (C8 v) Hc) as (pre & post & E & Hsz & _). subst cs.
  apply cells_wf_app in Hwf. destruct Hwf as [Wpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
  rewrite (bytes_at_ov_read usegs m A _ k 4 Hb).
  2:{ rewrite !length_app, length_le8, (cells_bytes_length pre Wpre). lia. }
  rewrite skipn_app, skipn_all2 by (rewrite (cells_bytes_length pre Wpre); lia).
  rewrite (cells_bytes_length pre Wpre), Hsz, Nat.sub_diag. cbn [app]. rewrite skipn_O.
  rewrite firstn_app, length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Ltac rd_lo4 H kn :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let c := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs kn) in
      lazymatch c with
      | Some (C8 ?v) =>
          let k := eval vm_compute in (Z.of_nat kn) in
          let RD := fresh "RD" in
          pose proof (rw_cells_read_lo4 m A cs kn v (wa (A + k)) H ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as RD
      end
  end.


Lemma sx32_wz : forall v, - 2^31 <= v < 2^31 -> sx32 (wz v) = wz v.
Proof.
  intros v Hv. unfold sx32. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.div].
  change (2 ^ 31) with 2147483648 in Hv. change (4294967296 / 2) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Lemma zx32_wz : forall v, 0 <= v < 2^32 -> zx32 (wz v) = wz v.
Proof.
  intros v Hv. unfold zx32. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  change (2 ^ 32) with 4294967296 in *. rewrite (Z.mod_small v) by lia. apply Z.mod_small. lia.
Qed.

Lemma signed_wz : forall z, - 2^63 <= z < 2^63 -> bv_signed (wz z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change (2 ^ 63) with 9223372036854775808 in Hz.
  change (18446744073709551616 / 2) with 9223372036854775808. Z.div_mod_to_equations. lia.
Qed.

Lemma bv_swrap32_id : forall z, - 2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (2 ^ 31) with 2147483648 in Hz. change (4294967296 / 2) with 2147483648. Z.div_mod_to_equations. lia.
Qed.

Lemma le8_lit : forall z, 0 <= z < 2^64 -> Z_to_le_bytes 8 z = le8 (wz z).
Proof. intros z Hz. unfold le8, word_to_le_bytes. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, 0 <= z < 2^64 -> Z_to_le_bytes 4 z = le4 (wz z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le2_lit : forall z, 0 <= z < 2^64 -> Z_to_le_bytes 2 z = le2 (wz z).
Proof. intros z Hz. unfold le2. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  end.

Ltac zs := zstep; try (fix_litstore; mem_after_store_opt); rewrite ?sx32_wz, ?zx32_wz, ?bv_swrap32_id by lia.


Lemma bv8_small : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof. intros v Hv. apply Z_to_bv_small. unfold bv_modulus. cbn. lia. Qed.

Ltac ld8 ARR a n A idx RNG :=
  let RD := fresh "RD" in
  pose proof (u8arr_read usegs _ A (av8 a n) idx (Z_to_bv 8 (arr_get a idx)) (wa (A + idx)) ARR (av8_nth a n idx ltac:(lia)) ltac:(lia) eq_refl) as RD;
  zs; cbv beta; rewrite (bv8_small (arr_get a idx)) by RNG; clear RD.

Ltac ld16 ARR a n A idx RNG :=
  let RD := fresh "RD" in
  pose proof (u16arr_read usegs _ A (av16 a n) idx (wz (arr_get a idx)) (wa (A + 2 * idx)) ARR (av16_nth a n idx ltac:(lia)) ltac:(lia) eq_refl) as RD;
  zs; rewrite (zx16_small (arr_get a idx)) by RNG; clear RD.


Definition memcpyZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S n : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + n)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' D [CB (Z.to_nat n) src]
    /\ bytes_at usegs m' S src.

Lemma memcpy_Z : forall (D S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (src junk : list byte),
  bytes_at usegs m S src -> length src = Z.to_nat n ->
  rw_cells usegs m D [CB (Z.to_nat n) junk] ->
  (S + n <= D \/ D + n <= S) -> mem_inv usegs m ->
  0 <= n < 2^64 -> 0 <= D < 2^64 -> 0 <= S < 2^64 ->
  evt usegs (memcpyZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz S) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x2a4a4) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros SRC LEN DST SEP MI Hn HD HS.
  assert (ED : bv_unsigned (wz D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (wz n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec; [| | | | exact MI]; rewrite ?ED, ?ES, ?En; [exact SRC | exact LEN | exact DST | lia]. }
  intros ms' PO. unfold memcpy_post in PO. rewrite ED, ES, En in PO. exact PO.
Qed.
