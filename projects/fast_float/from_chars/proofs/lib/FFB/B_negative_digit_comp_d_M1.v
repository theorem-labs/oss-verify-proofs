(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require LiaTuning Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.LiaTuning OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl Wbig_tac Wdc_tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_cap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_negative_digit_comp_d_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt B_pow5_stmt B_shl_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_compare_stmt B_negative_digit_comp_d_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_negative_digit_comp_d_M2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_negative_digit_comp_d_M2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt.B_fakestack OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_shl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_normalize_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_compare_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_M2.B_negative_digit_comp_d_T OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_M2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac simpl_arr_sizes ::= tryif kp_sas_pre5 then (rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zeros_length, ?repeat_length in *) else idtac.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.
Definition stashed2 (P : Prop) : Prop := P.
Ltac clear_vals :=
  repeat match goal with
  | H : bval _ _ = _ |- _ => clear H
  | H : (bval _ _ + _)%Z = _ |- _ => clear H
  | H : (_ <= bval _ _)%Z |- _ => clear H
  | H : (_ < BIG_CAP)%Z |- _ => clear H
  | H : bnorm _ _ |- _ => clear H
  | H : boxed _ |- _ => clear H
  | H : stashed _ |- _ => clear H
  | H : stashed2 _ |- _ => clear H
  | H : forall j : nat, _ |- _ => clear H
  end.
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac lia0 := first [ LiaCap.lia_cap_s ltac:(zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker) ltac:(fail)
                   | zify_prune; Zify.zify; xlia zchecker
                   | lia_app2
                   | Zify.zify; xlia zchecker ].
Local Ltac lia ::= clear_vals; lia0.
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Ltac kp_ovl_in G :=      (* [comment removed for export] *)
  lazymatch G with
  | ((?a + ?n <= ?lo \/ ?hi <= ?a) /\ ?R)%Z =>
      first [ assert_succeeds (assert (lo < a + n /\ a < hi)%Z by (split; LiaFast.lia_fast_tiers)) | kp_ovl_in R ]
  | (?a + ?n <= ?lo \/ ?hi <= ?a)%Z => assert_succeeds (assert (lo < a + n /\ a < hi)%Z by (split; LiaFast.lia_fast_tiers))
  end.
Ltac kp_ovl := lazymatch goal with |- ?G => kp_ovl_in G end.
Ltac kp_lia0_cap := LiaCap.lia_cap_s ltac:(zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker) ltac:(fail).
Ltac kp_lia0_rest := first [ zify_prune; Zify.zify; xlia zchecker | lia_app2 | Zify.zify; xlia zchecker ].
Ltac kp_lia_g := clear_vals; first [ kp_lia0_cap | tryif kp_ovl then fail else kp_lia0_rest ].
Ltac vlia := first [ exact I | kp_lia_g | split; [kp_lia_g | exact I] ].      (* [comment removed for export] *)
Ltac flia := first [ assert_succeeds (clear_vals; clear_disj; lia0); clear_vals; clear_disj; lia0 | lia ].

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; vlia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; vlia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : shz segs m ?A2 ?n2 |- _ =>
      first [ apply (shz_transport segs W m m' A2 n2) in H; [ | exact MU | cbn [disjoint_from]; vlia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ => apply (stk_mono segs m m' loq hiq) in H; [ | exact WM ]
  | H : rdbl segs m ?A2 ?n2 |- _ => apply (rdbl_mono segs m m' A2 n2) in H; [ | exact WM ]
  | H : pristine m ?lo ?hi |- _ =>
      first [ apply (pristine_transport W m m' lo hi) in H; [ | exact MU | cbn [disjoint_from]; vlia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ match goal with S : sub_fp _ _ |- _ => exact S end | unfold sub_fp; cbn [outside]; intros; flia ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Ltac solve_W_ok_rt := solve_W_rt.  (* [comment removed for export] *)
Lemma stk_subC : forall m lo hi lo' hi',
  stk BSEGS m lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> (lo' <= hi')%Z -> stk BSEGS m lo' hi'.
Proof.
  intros m lo hi lo' hi' ST H1 H2 H3.
  destruct (stk_split BSEGS m lo lo' hi ST ltac:(lia)) as [_ ST1].
  destruct (stk_split BSEGS m lo' hi' hi ST1 ltac:(lia)) as [ST2 _]. exact ST2.
Qed.
Optimize Heap.
Lemma stk_join : forall m lo a b hi,
  stk BSEGS m lo a -> stk BSEGS m b hi -> (a = b)%Z -> (lo <= a <= hi)%Z -> stk BSEGS m lo hi.
Proof. intros m lo a b hi H1 H2 <- H. eapply stk_merge; [exact H1 | exact H2 | exact H]. Qed.
Lemma stk_eq : forall m lo hi lo' hi',
  stk BSEGS m lo hi -> (lo' = lo)%Z -> (hi' = hi)%Z -> stk BSEGS m lo' hi'.
Proof. intros m lo hi lo' hi' H -> ->. exact H. Qed.
Ltac ulit := repeat (rewrite unsigned_lit by lia).
Ltac zlia := ulit; first [lia | Z.div_mod_to_equations; lia].
Ltac side :=
  lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- RT _ _ => first [eassumption | eapply RT_transport; [eassumption | eassumption | solve_W_ok_rt]]
  | |- rt_disj _ _ _ => ulit; match goal with H : rt_disj _ _ _ |- _ => eapply rt_disj_sub; [exact H | lia | lia] end
  | |- shz _ _ _ _ => ulit; first [eassumption | match goal with H : shz _ _ _ _ |- _ => eapply shz_sub; [exact H | zlia | zlia | zlia] end]
  | |- stk _ _ _ _ => ulit; first [eassumption | match goal with H : stk _ _ _ _ |- _ => eapply stk_subC; [exact H | lia | lia | lia] end]
  | |- @eq word _ _ => first [eassumption | reflexivity | ulit; reflexivity]
  | |- _ => first [eassumption | reflexivity | zlia]
  end.

(* [comment removed for export] *)
Ltac gen_val e := let X := fresh "rv" in set (X := e) in *; clearbody X.
Ltac gen_big :=
  repeat match goal with
  | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
  | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
  | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
  | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
  | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
  | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
  | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
  | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
  | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
  | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
  | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
  | |- context [Some (zx8 ?a)] => gen_val (zx8 a)
  | |- context [Some (zx16 ?a)] => gen_val (zx16 a)
  | |- context [Some (sx32 ?a)] => gen_val (sx32 a)
  end.
Ltac gstep := step; gen_big.


(* [comment removed for export] *)
Ltac stash_but keep keepMU keepWM :=
  repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => tryif constr_eq H keep then fail else stash H
  | H : munch _ _ _ |- _ => tryif constr_eq H keepMU then fail else stash H
  | H : wmono _ _ _ |- _ => tryif constr_eq H keepWM then fail else stash H
  | H : u64arr _ _ _ _ |- _ => stash H
  | H : u8arr _ _ _ _ |- _ => stash H
  | H : bytes_at _ _ _ _ |- _ => stash H
  | H : u8ro _ _ _ _ |- _ => stash H
  | H : shz _ _ _ _ |- _ => stash H
  | H : ro_cells _ _ _ _ |- _ => stash H
  | H : pristine _ _ _ |- _ => stash H
  | H : stk _ _ _ _ |- _ => stash H
  | H : rdbl _ _ _ _ |- _ => stash H
  | H : _ \/ _ |- _ => stash H
  end.
Ltac transport1 m m' W MU WM H :=
  lazymatch type of H with
  | bytes_at _ _ ?A2 ?bs2 => apply (bytes_at_transport BSEGS W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
  | rw_cells _ _ ?A2 ?cs2 => apply (rw_cells_transport BSEGS W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; vlia ]
  | ro_cells _ _ ?A2 ?cs2 => apply (ro_cells_transport BSEGS W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; vlia ]
  | u8arr _ _ ?A2 ?xs => apply (u8arr_transport BSEGS W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
  | u64arr _ _ ?A2 ?xs => apply (u64arr_transport BSEGS W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
  | u8ro _ _ ?A2 ?xs => apply (u8ro_transport BSEGS W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
  | shz _ _ ?A2 ?n2 => apply (shz_transport BSEGS W m m' A2 n2) in H; [ | exact MU | cbn [disjoint_from]; vlia ]
  | stk _ _ ?loq ?hiq => apply (stk_mono BSEGS m m' loq hiq) in H; [ | exact WM ]
  | rdbl _ _ ?A2 ?n2 => apply (rdbl_mono BSEGS m m' A2 n2) in H; [ | exact WM ]
  | pristine _ ?lo ?hi => apply (pristine_transport W m m' lo hi) in H; [ | exact MU | cbn [disjoint_from]; vlia ]
  | munch ?Wq ?mq _ => apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ match goal with S : sub_fp _ _ |- _ => exact S end | unfold sub_fp; cbn [outside]; intros; flia ] | exact MU ] ]
  | wmono _ ?mq _ => apply (wmono_trans BSEGS mq m m') in H; [ | exact WM ]
  end.
Ltac unstash_props := repeat match goal with H : stashed ?T |- _ => lazymatch T with _ \/ _ => unfold stashed in H | _ => fail end end.
Ltac stash2 H := lazymatch type of H with ?T => change T with (stashed2 T) in H end.
Ltac unstash_chunks MU WM :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    repeat match goal with H : stashed ?T |- _ =>
      lazymatch T with
      | _ \/ _ => fail
      | _ => unfold stashed in H; first [ transport1 ma mb W MU WM H | change T with (stashed2 T) in H ]
      end end;
    unstash_props;
    repeat match goal with H : stashed2 ?T |- _ =>
      unfold stashed2 in H; first [ transport1 ma mb W MU WM H | idtac "note: dropping hypothesis (unstash):" H; clear H ]
    end
  end.


(* [comment removed for export] *)
Lemma u64arr_cons : forall m A v ws,
  rw_cells BSEGS m A [C8 v] -> u64arr BSEGS m (A + 8) ws -> u64arr BSEGS m A (v :: ws).
Proof.
  intros m A v ws [[_ Hb] Hw] [Hb2 Hw2]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize Nat.add] in Hw.
  split.
  - cbn [u64s map concat]. change (le8 v ++ u64s ws) with (le8 v ++ u64s ws).
    apply (proj2 (bytes_at_app BSEGS m A (le8 v) (u64s ws))). split; [exact Hb|].
    rewrite length_le8. exact Hb2.
  - cbn [length]. rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat (length ws)))%Z with (8 + 8 * Z.of_nat (length ws))%Z by lia0.
    apply (proj2 (wr_at_app BSEGS m A 8 (8 * Z.of_nat (length ws)) ltac:(lia0) ltac:(lia0))). split; [exact Hw| exact Hw2].
Qed.

Optimize Heap.
Ltac swrap_unfold_tac :=
  unfold bv_swrap, bv_wrap in *;
  replace (bv_half_modulus 32) with (2^31)%Z in * by reflexivity;
  replace (bv_modulus 32) with (2^32)%Z in * by reflexivity.

Lemma negw_val : forall e, (-2^30 <= e <= -1)%Z ->
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 e)))) = (- e)%Z.
Proof.
  intros e He. rewrite !unsigned_lit_wrap. swrap_unfold_tac.
  Z.div_mod_to_equations. lia0.
Qed.

Optimize Heap.
Lemma pow5_1300 : (5 ^ 1300 < 2 ^ 3019)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma cap_neg : forall b k, (0 <= b < 2^64)%Z -> (0 <= k <= 1300)%Z -> (b * 5 ^ k < BIG_CAP)%Z.
Proof.
  intros b k Hb Hk. unfold BIG_CAP.
  assert (5 ^ k <= 5 ^ 1300)%Z by (apply Z.pow_le_mono_r; lia0).
  assert (0 < 5 ^ k)%Z by (apply Z.pow_pos_nonneg; lia0).
  pose proof pow5_1300.
  assert (2 ^ 64 * 2 ^ 3019 <= 2 ^ 3968)%Z by (rewrite <- Z.pow_add_r by lia0; apply Z.pow_le_mono_r; lia0).
  nia.
Qed.

Optimize Heap.
(* [comment removed for export] *)
Lemma bval_1 : forall (w : word) ws, bval (w :: ws) 1 = bv_unsigned w.
Proof. intros. cbn [bval]. unfold limbZ. cbn [nth]. change (2 ^ (64 * Z.of_nat 0))%Z with 1%Z. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac cond_lean H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; zify_bool H;
  try (apply Bool.andb_false_iff in H); rewrite ?unsigned_lit_wrap in H.
Ltac clia H := first [ lia | Z.div_mod_to_equations; lia | destruct H as [H|H]; zify_bool H; rewrite ?unsigned_lit_wrap in H; first [lia | Z.div_mod_to_equations; lia] ].
Ltac slit_hyps := repeat match goal with H : context [bv_signed (Z_to_bv 64 _)] |- _ => rewrite !signed_lit in H by lia end.

(* [comment removed for export] *)
Fixpoint covered' (lo hi : Z) (W' : list ivl) : Prop :=
  match W' with
  | [] => (hi <= lo)%Z
  | (lo', hi') :: r => ((lo' <= lo)%Z /\ (hi <= hi')%Z) \/ covered' lo hi r
  end.
Lemma covered'_outside : forall W' lo hi x, covered' lo hi W' -> outside W' x -> ~ (lo <= x < hi)%Z.
Proof.
  induction W' as [|[lo' hi'] r IH]; cbn; intros lo hi x HC HO.
  - lia0.
  - destruct HO as [Hn HO']. destruct HC as [[H1 H2]|HC']; [lia0 | exact (IH lo hi x HC' HO')].
Qed.
Lemma sub_fp_nil' : forall W', sub_fp [] W'. Proof. intros W' x _. exact I. Qed.
Lemma sub_fp_cons' : forall lo hi W W', covered' lo hi W' -> sub_fp W W' -> sub_fp ((lo, hi) :: W) W'.
Proof. intros lo hi W W' HC HS x HO. cbn. split; [exact (covered'_outside W' lo hi x HC HO) | exact (HS x HO)]. Qed.
Ltac covered_tac' := cbn [covered']; repeat first [ left; split; [lia0 | lia0] | right ]; lia0.
Ltac sub_fp_fast' := repeat (apply sub_fp_cons'; [ solve [covered_tac'] | ]); apply sub_fp_nil'.

(* [comment removed for export] *)
Definition lean_keep (P : Prop) : Prop := P.
Ltac lean_clear KEEP := clear - KEEP; decompose [and] KEEP; clear KEEP.      (* [comment removed for export] *)
Ltac lean_ctx KEEP := try unfold lean_keep in KEEP;
  repeat match goal with H : length ?l = ?n |- context [length ?l] =>
    lazymatch n with context [length _] => fail | _ => rewrite !H end end;
  lean_clear KEEP;      (* [comment removed for export] *)
  try unfold stashed in *; try unfold stashed2 in *;
  repeat (rewrite unsigned_lit by (first [lia0 | Z.div_mod_to_equations; lia0])).
Ltac klean :=
  match goal with K : lean_keep _ |- _ =>
    solve [ lean_ctx K; first [ lia0 | Z.div_mod_to_equations; lia0 ] ] end.
Ltac klia := first [ klean | lia | Z.div_mod_to_equations; lia ].
Ltac ulit ::= repeat (rewrite unsigned_lit by klia).
Ltac zlia ::= ulit; klia.
Ltac solve_W_ok_rt ::= solve_W_rt.  (* [comment removed for export] *)
Ltac side ::=
  lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- RT _ _ => first [eassumption | eapply RT_transport; [eassumption | eassumption | solve_W_ok_rt]]
  | |- rt_disj _ _ _ => ulit; first [ match goal with H : rt_disj _ _ _ |- _ => eapply rt_disj_sub; [exact H | klean | klean] end
                               | match goal with H : rt_disj _ _ _ |- _ => eapply rt_disj_sub; [exact H | klia | klia] end ]
  | |- shz _ _ _ _ => ulit; first [eassumption | match goal with H : shz _ _ _ _ |- _ => eapply shz_sub; [exact H | klean | klean | klean] end
                                        | match goal with H : shz _ _ _ _ |- _ => eapply shz_sub; [exact H | zlia | zlia | zlia] end]
  | |- stk _ _ _ _ => ulit; first [eassumption | match goal with H : stk _ _ _ _ |- _ => eapply stk_subC; [exact H | klean | klean | klean] end
                                        | match goal with H : stk _ _ _ _ |- _ => eapply stk_subC; [exact H | klia | klia | klia] end]
  | |- @eq word _ _ => first [eassumption | reflexivity | ulit; reflexivity]
  | |- _ => first [eassumption | reflexivity | zlia]
  end.

Section Mid.
  Hypothesis asan_memset_spec : asan_memset_stmt.
  Hypothesis normalize_spec : normalize_stmt.
  Hypothesis pow5_spec : pow5_stmt.
  Hypothesis shl_spec : shl_stmt.
  Hypothesis compare_spec : compare_stmt.
  Hypothesis set_shadow_f5_spec : set_shadow_f5_stmt.
  Variables (sp va gp a1w a2w : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (ws : list word) (len e p2 : Z) (S1 Fr pos0 pos1 : Z) (v : rt_vals) (mR : word -> option byte).
  Variables (ra0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : word).
  Notation A := (bv_unsigned va).
  Notation FS := (rt_FS v).
  Notation F0 := (FS + FK4_LO + pos0 * 1024)%Z.
  Notation SP1 := (Z_to_bv 64 S1).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SFw := (Z_to_bv 64 (Fr / 8 + ASAN_B)).
  Notation SHZb := (Fr / 8 + 2147450884)%Z.
  Notation SF0 := (Fr / 8 + 2147450880)%Z.
  Notation FLADDR := (FS + 34816 + pos1)%Z.
  Notation S8 := (Z_to_bv 64 (Fr + 32)).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis NORM : bnorm ws (Z.to_nat len).
  Hypothesis Re : (-1300 <= e <= -1)%Z.
  Hypotheses (Hp2 : (bv_unsigned a2w = p2 mod 2 ^ 32)%Z) (Rp2 : (- 2 ^ 14 <= p2 <= 2 ^ 14)%Z).
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HS1 : (bv_unsigned sp - 176 <= S1 <= bv_unsigned sp - 160)%Z.
  Hypothesis HS1a : (S1 mod 16 = 0)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp - 2768)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis SPLO : (IMG_END <= bv_unsigned sp - 2768)%Z.
  Hypothesis SFS : (FS + FSSIZE <= bv_unsigned sp - 2768)%Z.
  Hypothesis RTX0 : RTX v fc.
  Hypotheses (KF1 : (app2r (FS) (FS + FSSIZE))%Z) (KF2 : (FS + FSSIZE <= KTOP)%Z) (KF8 : (FS mod 4096 = 0)%Z).
  Hypotheses (Hpos0 : (0 <= pos0 < 1024)%Z) (Hpos1 : (0 <= pos1 < 1024)%Z) (Hne1 : pos1 <> pos0).
  Hypotheses (HFrE : Fr = (FS + FK4_LO + pos1 * 1024)%Z) (HFrF0 : (Fr + 1024 <= F0 \/ F0 + 1024 <= Fr)%Z) (HFr8 : (Fr mod 1024 = 0)%Z).
  Hypotheses (HA1 : (F0 + 32 <= A)%Z) (HA2 : (A + 504 <= F0 + 1024)%Z).
  Hypothesis RTH : RT mR v.
  Hypothesis RD1 : rt_disj v (bv_unsigned sp - 2768) (bv_unsigned sp).
  Hypothesis RD3 : rt_disj v FS (FS + FSSIZE).
  Hypotheses (Kc1 : rt_app (rt_ctx v) 160) (Kc2 : (rt_ctx v + 160 <= KTOP)%Z) (Kt1 : rt_app (rt_thr v) 80)
             (Kt2 : (rt_thr v + 80 <= KTOP)%Z) (Kb1 : rt_app (rt_blk v) 32) (Kb2 : (rt_blk v + 32 <= KTOP)%Z).

  Notation WL := (negative_digit_comp_d_W (bv_unsigned sp) A FS pos0).
  Notation RS m := (rw_cells BSEGS m (bv_unsigned sp + -104)
     [C8 q11; C8 q10; C8 q9; C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 ra0]).
  Notation NDPOST := (negative_digit_comp_d_post ra0 sp gp (Z_to_bv 64 TPV) q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 F fc A v pos0 mR).
  Notation CMP_INV m wsr lenr wst lent h5' lj hw :=
    (cmp_inv sp va S1 Fr pos0 pos1 v mR ra0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 m wsr lenr wst lent lj hw h5').

  (* [comment removed for export] *)
  Notation W_SHZ := [(SHZb, SHZb + 63)]%Z.
  Notation W_MST := [(bv_unsigned SP1 - 2208, bv_unsigned SP1); (bv_unsigned (Z_to_bv 64 (Fr + 40)), bv_unsigned (Z_to_bv 64 (Fr + 40)) + bv_unsigned (Z_to_bv 64 496))]%Z.
  Notation W_NRM := (normalize_W (bv_unsigned S8) SP1).
  Notation W_P5 := (pow5_W (bv_unsigned SP1) (bv_unsigned S8) FS).
  Notation W_SHT := (shl_W (bv_unsigned SP1) (bv_unsigned S8)).
  Notation W_SHB := (shl_W (bv_unsigned SP1) (bv_unsigned va)).
  Ltac sfp := pose proof (unsigned_lit S1 ltac:(lia)) as U1; pose proof (unsigned_lit Fr ltac:(lia)) as U2;
              pose proof (unsigned_lit (Fr + 32) ltac:(lia)) as U3; pose proof (unsigned_lit (Fr + 40) ltac:(lia)) as U4;
              pose proof (unsigned_lit 496 ltac:(lia)) as U5;
              clear - U1 U2 U3 U4 U5 HS1 Rsp HFrE HFrF0 Hpos0 Hpos1 Hne1 KF1 KF2 KF8 KSP KSP2 HA1 HA2;
              cbv delta [negative_digit_comp_d_W pow5_W shl_W normalize_W]; first [ solve [sub_fp_fast'] | unfold sub_fp; cbn [outside]; intros; first [lia0 | Z.div_mod_to_equations; lia0] ].
  #[using="ws p2 S1 pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfM_shz_L : sub_fp W_SHZ WL. Proof. LiaFast.lf_pins (fun (ws p2 S1 pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="sp va ws p2 S1 pos0 pos1 v L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 Kc1 Kt1 Kb1"] Lemma sfM_shz_K : sub_fp W_SHZ W_SHZ. Proof. LiaFast.lf_pins (fun (sp va ws p2 S1 pos0 pos1 v L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="ws p2 pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfM_mst_L : sub_fp W_MST WL. Proof. LiaFast.lf_pins (fun (ws p2 pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="ws p2 pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfM_nrm_L : sub_fp W_NRM WL. Proof. LiaFast.lf_pins (fun (ws p2 pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="ws p2 pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfM_p5_L : sub_fp W_P5 WL. Proof. LiaFast.lf_pins (fun (ws p2 pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="ws p2 pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfM_sht_L : sub_fp W_SHT WL. Proof. LiaFast.lf_pins (fun (ws p2 pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="ws p2 Fr pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 Kc1 Kt1 Kb1"] Lemma sfM_shb_L : sub_fp W_SHB WL. Proof. LiaFast.lf_pins (fun (ws p2 Fr pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  Ltac pose_sf := pose proof sfM_shz_L; pose proof sfM_shz_K; pose proof sfM_mst_L; pose proof sfM_nrm_L; pose proof sfM_p5_L; pose proof sfM_sht_L; pose proof sfM_shb_L.
  Ltac clear_sf := repeat match goal with S : sub_fp _ _ |- _ => clear S end.
  Ltac pose_keep := pose proof I as KEEP; change True with (lean_keep True) in KEEP.      (* [comment removed for export] *)
  Ltac lean_clear KEEP ::= clear - Rsp AL HS1 HS1a KSP KSP2 SFS KF1 KF2 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HFr8 HA1 HA2 A8 L62 Hlen Kc1 Kc2 Kt1 Kt2 Kb1 Kb2.

  Ltac close_cmp :=
    unfold cmp_inv, fs_cells_ok, fk5_inv; repeat match goal with |- _ /\ _ => split end; try eassumption; try lia;
    try lazymatch goal with
        | |- munch _ _ _ => cbv delta [negative_digit_comp_d_W] in *; eassumption
        | |- stk _ _ ?lo (?lo + 1016)%Z => match goal with H : stk BSEGS _ lo (lo + 1024)%Z |- _ => eapply stk_subC; [exact H | lia | lia | lia] end
        | |- stk _ _ (?f / 8 + 2147450880)%Z _ => match goal with H : stk BSEGS _ (ASAN_B + f / 8)%Z _ |- _ => eapply stk_subC; [exact H | lia | lia | lia] end
        end.

  #[using="asan_memset_spec normalize_spec pow5_spec shl_spec compare_spec set_shadow_f5_spec L62 Hlen A8 Re Hp2 Rp2 AL Rsp HS1 HS1a KSP KSP2 SFS RTX0 KF1 KF2 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HFr8 HA1 HA2 RTH RD1 RD3 Kc1 Kc2 Kt1 Kt2 Kb1 Kb2"] Lemma ndc_mid_run : forall (x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x18 x24 x26 x27 x28 x29 x30 x31 : word)
      (m : word -> option byte) (h5 hw : word) (fj0 fj496 lj zsh : list byte),
      u64arr BSEGS m A ws -> rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells BSEGS m (Fr + 32) [CB 8 fj0] -> rw_cells BSEGS m (Fr + 40) [CB 496 fj496] ->
      rw_cells BSEGS m (Fr + 1016) [C8 (Z_to_bv 64 FLADDR)] ->
      stk BSEGS m Fr (Fr + 1024) -> stk BSEGS m (ASAN_B + Fr / 8) (ASAN_B + Fr / 8 + 128) ->
      rw_cells BSEGS m (S1 + 24) [CB 32 lj] ->
      rw_cells BSEGS m SHZb [CB 63 zsh] ->
      stk BSEGS m (bv_unsigned sp - 2768) S1 -> stk BSEGS m S1 (S1 + 24) -> stk BSEGS m (S1 + 56) (bv_unsigned sp - 104) ->
      RS m ->
      rw_cells BSEGS m (FS + 32) [C8 hw] ->
      u8arr BSEGS m (FS + 34816) (upd (upd (zeros 1024) (Z.to_nat pos0) (Z_to_bv 8 1)) (Z.to_nat pos1) (Z_to_bv 8 1)) ->
      fs_cells_ok FS m ->
      stk BSEGS m (FS + FK4_LO) F0 -> stk BSEGS m (F0 + 1024) (FS + FK4_HI) ->
      stk BSEGS m (ASAN_B + FS / 8 + FK4_SLO) (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128) ->
      stk BSEGS m (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128 + 128) (ASAN_B + FS / 8 + FK4_SHI) ->
      fk5_inv m FS h5 ->
      pristine m IMG_LO ROD_HI -> pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
      shz BSEGS m (ASAN_B + A / 8) 63 -> shz BSEGS m POW5TAB_SH POW5TAB_SHN ->
      rdbl BSEGS m (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N ->
      shz BSEGS m (ASAN_B + (bv_unsigned sp - 2768) / 8) 346 ->
      munch WL mR m -> wmono BSEGS mR m ->
      evt BSEGS NDPOST
        (MS (mkR x1 SP1 gp (Z_to_bv 64 TPV) x5 x6 x7 sp SP1 (Z_to_bv 64 Fr) x11 (Z_to_bv 64 p2) x13 x14 x15 x16 x17
                 x18 SFw a2w (Z_to_bv 64 e) va a1w x24 (Z_to_bv 64 Fr) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x96468) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (asan_memset_spec normalize_spec pow5_spec shl_spec compare_spec set_shadow_f5_spec L62 Hlen A8 Re Hp2 Rp2 AL Rsp HS1 HS1a KSP KSP2 SFS RTX0 KF1 KF2 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HFr8 HA1 HA2 RTH RD1 RD3 Kc1 Kc2 Kt1 Kt2 Kb1 Kb2 : LiaFast.U) => LiaFast.u0).
    intros x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x18 x24 x26 x27 x28 x29 x30 x31 m h5 hw fj0 fj496 lj zsh
           LIMBS LENC ZF0 ZM FLC STF STS LOCj SHZ ST ST0 ST2 SV HINT FL FSC SK4a SK4b SKS4a SKS4b FK5 PR PRG PRT SHX SHT RBF SHW MU0 WM0.
    unfold fs_cells_ok in FSC. destruct FK5 as (_ & HINT5 & FL5 & SK5 & SKS5).
    cbv delta [negative_digit_comp_d_W] in MU0.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as BdX. rewrite L62 in BdX.
    pose proof (unsigned_lit S1 ltac:(lia)) as ULs. pose proof (unsigned_lit Fr ltac:(lia)) as ULf.
    pose proof (unsigned_lit (Fr + 32) ltac:(lia)) as ULs8. pose proof (unsigned_lit A ltac:(lia)) as ULa.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *) rewrite uw_sub, (swrap32_id (0 - p2)) by lia. rewrite (Z.sub_0_l p2).
    step. (* [comment removed for export] *) rewrite ?word_sub_lit2, ?word_sub_lit. rewrite (Z.sub_0_l p2).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    assert (J10 : forall (u10 u11 u12 u13 u14 : word),
      evt BSEGS NDPOST
        (MS (mkR x1 SP1 gp (Z_to_bv 64 TPV) x5 x6 x7 sp SP1 u10 u11 u12 u13 u14 x15 x16 x17
                 a1w SFw a2w (Z_to_bv 64 e) va a1w x24 (Z_to_bv 64 Fr) (Z_to_bv 64 (- p2)) x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x96500) fc None m0 (seg_rom BSEGS)))
    end.
    { intros.
      step. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- context [Some (Z_to_bv 64 (Z.land ?u 9218868437227405312))] =>
        pose proof (land_range_r u 9218868437227405312 ltac:(lia)) as Hv;
        set (vv := Z.land u 9218868437227405312) in *; clearbody vv end.
      gstep. (* [comment removed for export] *)
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
      assert (J40 : forall (qq : Z) (u10 u11 u12 : word), (-1076 <= qq <= 971)%Z ->
        evt BSEGS NDPOST
          (MS (mkR x1 SP1 gp (Z_to_bv 64 TPV) x5 x6 x7 sp SP1 u10 u11 u12 u13 u14 x15 x16 x17
                   a1w SFw a2w (Z_to_bv 64 e) va va S8 (Z_to_bv 64 Fr) (Z_to_bv 64 (- p2)) (Z_to_bv 64 qq) x28 x29 x30 x31)
              F (Z_to_bv 64 0x96530) fc None m0 (seg_rom BSEGS)))
      end.
      { intros qq u10' u11' u12' Hqq.
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          pose proof (munch_refl W_SHZ mc) as MUs; pose proof (wmono_refl BSEGS mc) as WMs end.
        stash2 SHX. stash2 SHT. stash2 SHW.
        stash_but SHZ MUs WMs.
        do 21 step. Optimize Proof. Optimize Heap.
        do 21 step. Optimize Proof. Optimize Heap.
        do 21 step.
        pose_sf. unstash_chunks MUs WMs. clear MUs WMs. clear_sf. Optimize Proof. Optimize Heap.
        match goal with H : rw_cells BSEGS _ SHZb ?cs |- _ => rename H into SHZ1;
          pose proof (shz_of_rw_cells BSEGS _ _ cs SHZ1 ltac:(cbn [cells_bytes cbytes app]; repeat constructor)) as SHZt;
          let n' := eval vm_compute in (Z.of_nat (cells_size cs)) in change (Z.of_nat (cells_size cs)) with n' in SHZt; clear SHZ1 end.
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        lazymatch goal with |- context [Some (Z_to_bv 64 (bv_unsigned ?r + 1)%Z)] =>
          remember (Z_to_bv 64 (bv_unsigned r + 1)%Z) as s6w eqn:Hs6w; clear Hs6w end.
        (* [comment removed for export] *)
        lazymatch type of ZM with rw_cells _ _ _ [CB 496 ?l] =>
          assert (LJ : length l = 496%nat) by exact (proj1 (proj1 (proj1 ZM))) end.
        pose proof (u8arr_of_rw_cells _ _ _ _ _ ZM) as OLD. clear ZM.
        zstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose proof (unsigned_lit (Fr + 40) ltac:(lia)) as U40. pose proof (unsigned_lit 496 ltac:(lia)) as U496.
        step. (* [comment removed for export] *)
        pose_sf.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          eapply evt_cut; [ eapply asan_memset_spec with (v := v) (old := _) (c := 0%Z)
                                     (shlo := (ASAN_B + FS / 8 + FK_SH_LO)%Z) (shn := FK_SH_N)
                          | post_call BSEGS mc ] end.
        all: try (lazymatch goal with |- evt _ _ _ => idtac | _ => pose_keep end).
        all: try lazymatch goal with
             | |- evt _ _ _ => idtac
             | |- u8arr _ _ _ _ => rewrite U40; exact OLD
             | |- Z.of_nat _ = _ => rewrite U496, LJ; reflexivity
             | |- rdbl _ _ _ _ => exact RBF
             | |- RTX _ _ => exact RTX0
             | |- _ => side
             end.
        all: clear_sf.
        all: try clear KEEP.
        Optimize Proof. Optimize Heap.
        all: match goal with |- evt _ _ _ => idtac | |- ?g => idtac "REMAIN-MST" g end.
        rewrite ?ULs, ?U40, ?U496 in *. clear LJ.
        change (Z.to_nat 496) with 496%nat in *.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
          lazymatch goal with M : u8arr _ m' (Fr + 40) (repeat _ _) |- _ => destruct M as [ZB ZW]; rename m' into m1 end end.
        replace (repeat (Z_to_bv 8 0) 496) with (repeat (Z_to_bv 8 0) (8 * 61) ++ (repeat (Z_to_bv 8 0) 2 ++ repeat (Z_to_bv 8 0) 6))
          in ZB by reflexivity.
        apply bytes_at_app in ZB. destruct ZB as [ZBL ZB26]. rewrite repeat_length in ZB26.
        apply bytes_at_app in ZB26. destruct ZB26 as [ZB2 ZB6]. rewrite repeat_length in ZB6.
        rewrite repeat_length in ZW. change (Z.of_nat 496) with (488 + (2 + 6))%Z in ZW.
        apply wr_at_app in ZW; [|lia|lia]. destruct ZW as [ZWL ZW26].
        apply wr_at_app in ZW26; [|lia|lia]. destruct ZW26 as [ZW2 ZW6].
        change (Z.of_nat (8 * 61)) with 488%Z in ZB2, ZB6. change (Z.of_nat 2) with 2%Z in ZB6.
        replace (Fr + 40 + 488)%Z with (Fr + 528)%Z in ZB2, ZW2 by lia.
        replace (Fr + 40 + 488 + 2)%Z with (Fr + 530)%Z in ZB6, ZW6 by lia.
        pose proof (rw_cells_of_u8arr BSEGS _ _ _ (conj ZB2 ZW2)) as LENT. clear ZB2 ZW2. rewrite repeat_length in LENT.
        pose proof (rw_cells_of_u8arr BSEGS _ _ _ (conj ZB6 ZW6)) as PADT. clear ZB6 ZW6. rewrite repeat_length in PADT.
        pose proof (rw_cells_of_u8arr BSEGS _ _ _ (conj ZBL ZWL)) as LIML. clear ZBL ZWL. rewrite repeat_length in LIML.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => rename m' into m2 end.
        destruct (u64arr_of_rw_cells BSEGS _ _ 61 _ LIML) as (wsz & Lz & LIMBT). clear LIML.
        replace (Fr + 40)%Z with (Fr + 32 + 8)%Z in LIMBT by lia.
        match goal with H : rw_cells BSEGS m2 (Fr + 32) [C8 ?w] |- _ =>
          pose proof (u64arr_cons _ _ _ _ H LIMBT) as LIMT; clear H LIMBT end.
        assert (LT62 : length (s6w :: wsz) = 62%nat) by (cbn [length]; rewrite Lz; reflexivity).
        match goal with H : rw_cells BSEGS m2 (Fr + 32 + 496)%Z _ |- _ => replace (Fr + 32 + 496)%Z with (Fr + 528)%Z in H by lia; rename H into LENT1
                      | H : rw_cells BSEGS m2 (Fr + 528)%Z [C2 _] |- _ => rename H into LENT1 end.
        (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        assert (BC : ro_cells BSEGS m2 BCELL [C8 BB]).
        { match goal with MU : munch _ mR m2 |- _ =>
            pose proof (RT_transport mR m2 v _ RTH MU ltac:(solve_W_ok_rt)) as RTm end.
          open_RT_keep RTm.
          change [C8 (Z_to_bv 64 ASAN_B); C4 (Z_to_bv 64 1)] with ([C8 (Z_to_bv 64 ASAN_B)] ++ [C4 (Z_to_bv 64 1)]) in RT1.
          apply (proj1 (proj1 (ro_cells_app BSEGS m2 943736 _ _) RT1)). }
        step. (* [comment removed for export] *)
        pose_sf.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          eapply evt_cut; [ eapply normalize_spec with (ws := s6w :: wsz) (len := 1%Z) | post_call BSEGS mc ] end.
        all: try (lazymatch goal with |- evt _ _ _ => idtac | _ => pose_keep end).
        all: try lazymatch goal with
             | |- evt _ _ _ => idtac
             | |- u64arr _ _ _ _ => ulit; exact LIMT
             | |- rw_cells _ _ _ [C2 _] => ulit; replace (Fr + 32 + 496)%Z with (Fr + 528)%Z by lia; exact LENT1
             | |- pristine _ _ _ => exact PRG
             | |- ro_cells _ _ _ _ => exact BC
             | |- shz _ _ _ _ => ulit; replace (ASAN_B + (Fr + 32) / 8)%Z with SHZb by (clear - HFr8 HFrE KF1 KF8 Hpos1; Z.div_mod_to_equations; lia0); exact SHZt
             | |- stk _ _ _ _ => ulit; eapply stk_subC; [exact ST | lia | lia | lia]
             | |- _ => ulit; first [eassumption | reflexivity | lia]
             end.
        all: clear_sf.
        all: try clear KEEP.
        Optimize Proof. Optimize Heap.
        all: match goal with |- evt _ _ _ => idtac | |- ?g => idtac "REMAIN-NRM" g end.
        rewrite ?ULs, ?ULs8 in *. clear BC.
        match goal with H : stk BSEGS _ (S1 - 16)%Z S1 |- _ => clear H | _ => idtac end.
        match goal with H : rw_cells BSEGS _ (Fr + 32 + 496)%Z [C2 (Z_to_bv 64 (Z.of_nat ?n))] |- _ =>
          replace (Fr + 32 + 496)%Z with (Fr + 528)%Z in H by lia; rename H into LENT;
          set (nl := n) in LENT;
          assert (Hnl : (nl <= 1)%nat) by (subst nl; apply norm_len_le);
          assert (NORMT : bnorm (s6w :: wsz) (Z.to_nat (Z.of_nat nl))) by (rewrite Nat2Z.id; subst nl; apply norm_len_bnorm);
          assert (BVT : bval (s6w :: wsz) (Z.to_nat (Z.of_nat nl)) = bv_unsigned s6w)
            by (rewrite Nat2Z.id; subst nl; rewrite norm_len_bval; change (Z.to_nat 1) with 1%nat; apply bval_1);
          clearbody nl end.
        match goal with H : u64arr BSEGS ?mm (Fr + 32) (s6w :: wsz) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into LIMT3 end.
        (* [comment removed for export] *)
        step. (* [comment removed for export] *) rewrite uw_sub2, (swrap32_id (qq - e)) by lia.
        step. (* [comment removed for export] *) rewrite word_sub_lit2.
        step. (* [comment removed for export] *) if_not_taken.
        step. (* [comment removed for export] *) rewrite uw_sub, (swrap32_id (0 - e)) by lia. rewrite (Z.sub_0_l e).
        step. (* [comment removed for export] *) rewrite ?word_sub_lit2, ?word_sub_lit. rewrite (Z.sub_0_l e).
        step. (* [comment removed for export] *) if_not_taken.
        step. (* [comment removed for export] *) trap_dead.
        step. (* [comment removed for export] *)
        pose proof (unsigned_lit (- e) ltac:(lia)) as UA1.
        pose proof (bv_unsigned_in_range 64 s6w) as Rs6. unfold bv_modulus in Rs6.
        assert (CAPT : (bval (s6w :: wsz) (Z.to_nat (Z.of_nat nl)) * 5 ^ (- e) < BIG_CAP)%Z).
        { rewrite BVT. apply cap_neg; [clear - Rs6; lia0 | lia]. }
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          assert (FK5 : fk5_inv mc FS h5) by (split; [exact FSC | split; [exact HINT5 | split; [exact FL5 | split; [exact SK5 | exact SKS5]]]]) end.
        clear HINT5 FL5 SK5 SKS5.
        step. (* [comment removed for export] *)
        pose_sf.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          eapply evt_cut; [ eapply pow5_spec with (v := v) (ws := s6w :: wsz) (len := Z.of_nat nl) (h5 := h5)
                          | post_call BSEGS mc ] end.
        all: try (lazymatch goal with |- evt _ _ _ => idtac | _ => pose_keep end).
        all: try lazymatch goal with
             | |- evt _ _ _ => idtac
             | |- u64arr _ _ _ _ => rewrite ULs8; exact LIMT3
             | |- rw_cells _ _ _ [C2 _] => rewrite ULs8; replace (Fr + 32 + 496)%Z with (Fr + 528)%Z by lia; exact LENT
             | |- bnorm _ _ => exact NORMT
             | |- (_ + pow5_growth _ <= _)%Z => rewrite ?unsigned_lit by lia; match goal with |- (_ + pow5_growth ?k <= _)%Z => pose proof (neg_cap k ltac:(lia)) end; lia
             | |- (bv_unsigned _ < 2 ^ 31)%Z => rewrite UA1; lia
             | |- fk5_inv _ _ _ => exact FK5
             | |- rdbl _ _ (_ - 8) _ => rewrite ULs8; eapply rdbl_sub; [exact RBF | zlia | zlia]
             | |- rdbl _ _ _ _ => exact RBF
             | |- RTX _ _ => exact RTX0
             | |- shz _ _ (ASAN_B + (bv_unsigned SP1 - 2592) / 8)%Z _ => rewrite ULs; eapply shz_sub; [exact SHW | zlia | lia | zlia]
             | |- _ => side
             end.
        all: clear_sf.
        all: try clear KEEP.
        Optimize Proof. Optimize Heap.
        all: match goal with |- evt _ _ _ => idtac | |- ?g => idtac "REMAIN-P5" g end.
        rewrite ?ULs, ?ULs8 in *. rewrite -> ?UA1 in *.
        clear LT62 NORMT CAPT BVT FK5. try clear LIMT3. try clear LENT.
        (* [comment removed for export] *)
        match goal with H : fk5_inv ?mm FS ?h |- _ => destruct H as (FSC' & HINT5 & FL5 & SK5 & SKS5); clear FSC'; rename h into h5' end.
        match goal with H : u64arr BSEGS ?mm (Fr + 32) ?w |- _ => rename H into LIMT; rename w into wst end.
        match goal with H : rw_cells BSEGS ?mm (Fr + 32 + 496) _ |- _ => replace (Fr + 32 + 496)%Z with (Fr + 528)%Z in H by lia; rename H into LENT end.
        match type of LENT with rw_cells _ _ _ [C2 (Z_to_bv 64 ?l)] => rename l into lent end.
        match goal with H : length wst = 62%nat |- _ => rename H into LT62 end.
        match goal with H : (0 <= lent <= 62)%Z |- _ => rename H into HlenT end.
        match goal with H : RT ?mm v |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into RT5 end.
        (* [comment removed for export] *)
        assert (JE0 : forall (m4 : word -> option byte) (wsr wst' : list word) (lenr lent' : Z) (h5x : word) (ljx : list byte)
                             (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31 : word),
          CMP_INV m4 wsr lenr wst' lent' h5x ljx hw ->
          evt BSEGS NDPOST
            (MS (mkR y1 SP1 gp (Z_to_bv 64 TPV) y5 y6 y7 sp SP1 y10 y11 y12 y13 y14 y15 y16 y17
                     a1w SFw a2w (Z_to_bv 64 e) y22 va S8 (Z_to_bv 64 Fr) (Z_to_bv 64 (- p2)) (Z_to_bv 64 qq) y28 y29 y30 y31)
                F (Z_to_bv 64 0x966a0) fc None m4 (seg_rom BSEGS))).
        { intros. eapply (ndc_cmp_run compare_spec set_shadow_f5_spec) with (p2 := p2); try eassumption; try lia. }
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m4 _) =>
        assert (JSH : forall (vsh : Z) (onlocal : bool) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
          (0 < vsh < 2 ^ 31)%Z ->
          evt BSEGS NDPOST
            (MS (mkR (Z_to_bv 64 0x96684) SP1 gp (Z_to_bv 64 TPV) y5 y6 y7 sp SP1
                     (if onlocal then S8 else va) y11 y12 y13 y14 y15 y16 y17
                     a1w SFw a2w (Z_to_bv 64 e) (Z_to_bv 64 vsh) va S8 (Z_to_bv 64 Fr) (Z_to_bv 64 (- p2)) (Z_to_bv 64 qq) y28 y29 y30 y31)
                F (Z_to_bv 64 0x9668c) fc None m4 (seg_rom BSEGS)))
        end.
        { intros vsh onlocal. intros.
          step. (* [comment removed for export] *) rewrite (unsigned_lit vsh) by lia. rewrite (Z.shiftl_mul_pow2 vsh 32) by lia.
          step. (* [comment removed for export] *) rewrite (unsigned_lit (vsh * 2 ^ 32)) by lia. rewrite (Z.shiftr_div_pow2 _ 32) by lia.
          rewrite (Z.div_mul vsh (2 ^ 32)) by lia.
          destruct onlocal.
          - step. (* [comment removed for export] *)
            pose_sf.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
              eapply evt_cut; [ eapply shl_spec with (v := v) (ws := wst) (len := lent) | post_call BSEGS mc ] end.
            all: try (lazymatch goal with |- evt _ _ _ => idtac | _ => pose_keep end).
            all: try lazymatch goal with
                 | |- evt _ _ _ => idtac
                 | |- u64arr _ _ _ _ => rewrite ULs8; exact LIMT
                 | |- rw_cells _ _ _ [C2 _] => rewrite ULs8; replace (Fr + 32 + 496)%Z with (Fr + 528)%Z by lia; exact LENT
                 | |- RT _ _ => exact RT5
                 | |- rdbl _ _ _ _ => rewrite ULs8; eapply rdbl_sub; [exact RBF | zlia | zlia]
                 | |- _ => side
                 end.
            all: clear_sf.
            all: try clear KEEP.
        Optimize Proof. Optimize Heap.
            all: match goal with |- evt _ _ _ => idtac | |- ?g => idtac "REMAIN-SHT" g end.
            rewrite ?ULs, ?ULs8 in *.
            match goal with H : rw_cells BSEGS ?mm (Fr + 32 + 496) _ |- _ => replace (Fr + 32 + 496)%Z with (Fr + 528)%Z in H by lia | _ => idtac end.
            step. (* [comment removed for export] *)
            eapply JE0. close_cmp.
          - step. (* [comment removed for export] *)
            pose_sf.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
              eapply evt_cut; [ eapply shl_spec with (v := v) (ws := ws) (len := len) | post_call BSEGS mc ] end.
            all: try (lazymatch goal with |- evt _ _ _ => idtac | _ => pose_keep end).
            all: try lazymatch goal with
                 | |- evt _ _ _ => idtac
                 | |- RT _ _ => exact RT5
                 | |- rdbl _ _ _ _ => eapply rdbl_sub; [exact RBF | zlia | zlia]
                 | |- _ => side
                 end.
            all: clear_sf.
            all: try clear KEEP.
        Optimize Proof. Optimize Heap.
            all: match goal with |- evt _ _ _ => idtac | |- ?g => idtac "REMAIN-SHB" g end.
            rewrite ?ULs, ?ULa in *.
            step. (* [comment removed for export] *)
            eapply JE0. close_cmp. }
        (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hle.
        - cond_lean Hle. slit_hyps. assert (Hle' : (qq - e <= 0)%Z) by (clia Hle). clear Hle.
          step. (* [comment removed for export] *)
          if_cases Hlt.
          + cond_lean Hlt. slit_hyps. assert (Hlt' : (qq - e < 0)%Z) by (clia Hlt). clear Hlt.
            (* [comment removed for export] *)
            step. (* [comment removed for export] *) rewrite ?word_sub_lit2, ?word_sub_lit.
            step. (* [comment removed for export] *) rewrite uw_sub, (swrap32_id (0 - (qq - e))) by lia.
            step. (* [comment removed for export] *) if_not_taken.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            replace (0 - (qq - e))%Z with (e - qq)%Z by lia.
            apply (JSH (e - qq)%Z false). lia.
          + cond_lean Hlt. slit_hyps. assert (Hlt' : (qq - e = 0)%Z) by (clia Hlt). clear Hlt.
            (* [comment removed for export] *)
            eapply JE0. close_cmp.
        - cond_cleanup Hle. slit_hyps. assert (Hle' : (0 < qq - e)%Z) by mlia.
          step. (* [comment removed for export] *)
          apply (JSH (qq - e)%Z true). lia. }
      (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz.
      - clear Hz.
        step. (* [comment removed for export] *) rewrite (unsigned_lit vv) by lia. rewrite (Z.shiftr_div_pow2 vv 52) by lia.
        change (2 ^ 52)%Z with 4503599627370496%Z.
        assert (Hv2 : (0 <= vv / 4503599627370496 <= 2047)%Z).
        { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
        step. (* [comment removed for export] *)
        apply J40. lia.
      - clear Hz. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        apply J40. lia. }
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd.
    - cond_cleanup Hd. rewrite ?signed_lit in Hd by lia.
      (* [comment removed for export] *)
      step. (* [comment removed for export] *) rewrite uw_add, (swrap32_id (- p2 + 1)) by lia.
      step. (* [comment removed for export] *) trap_dead.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) rewrite Hp2, uw_mod32, Z.add_0_r, (swrap32_id p2) by lia.
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
      assert (JEC : forall (sh : Z), (1 <= sh <= 2 ^ 14 + 1)%Z ->
        evt BSEGS NDPOST
          (MS (mkR x1 SP1 gp (Z_to_bv 64 TPV) x5 x6 x7 sp SP1 (Z_to_bv 64 Fr) (Z_to_bv 64 p2) (Z_to_bv 64 sh) (Z_to_bv 64 64) (Z_to_bv 64 (- p2 + 1)) x15 x16 x17
                   x18 SFw a2w (Z_to_bv 64 e) va a1w x24 (Z_to_bv 64 Fr) (Z_to_bv 64 (- p2)) x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x964dc) fc None m0 (seg_rom BSEGS)))
      end.
      { intros sh Hsh.
        step. (* [comment removed for export] *) rewrite ?word_add_lit2.
        step. (* [comment removed for export] *) rewrite ?uw_add2, (swrap32_id (p2 + sh)) by lia.
        step. (* [comment removed for export] *) if_not_taken.
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        apply J10. }
      step. (* [comment removed for export] *)
      if_cases Hq.
      + cond_cleanup Hq. apply (JEC (- p2 + 1)%Z). lia.
      + cond_cleanup Hq. step. (* [comment removed for export] *) apply (JEC 64%Z). lia.
    - cond_cleanup Hd. rewrite ?signed_lit in Hd by lia.
      (* [comment removed for export] *)
      step. (* [comment removed for export] *) rewrite Hp2, uw_mod32, Z.add_0_r, (swrap32_id p2) by lia.
      step. (* [comment removed for export] *) rewrite Hp2, uw_mod32, (swrap32_id (p2 + 11)) by lia.
      step. (* [comment removed for export] *) trap_dead.
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
      assert (JBC : forall (u10 u11 u12 : word),
        evt BSEGS NDPOST
          (MS (mkR x1 SP1 gp (Z_to_bv 64 TPV) x5 x6 x7 sp SP1 u10 u11 u12 (Z_to_bv 64 2047) x14 x15 x16 x17
                   x18 SFw a2w (Z_to_bv 64 e) va a1w x24 (Z_to_bv 64 Fr) (Z_to_bv 64 (- p2)) x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x964ac) fc None m0 (seg_rom BSEGS)))
      end.
      { intros. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *) apply J10. }
      step. (* [comment removed for export] *)
      if_cases Hq.
      + clear Hq. apply JBC.
      + clear Hq. step. (* [comment removed for export] *) apply JBC.
  Qed.
  Optimize Heap.
End Mid.
(* [comment removed for export] *)
