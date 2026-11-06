(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import LiaTuning Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_negative_digit_comp_d_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt B_pow5_stmt B_shl_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_compare_stmt B_negative_digit_comp_d_stmt.

Module B_negative_digit_comp_d_P.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_negative_digit_comp_d_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt B_negative_digit_comp_d_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt.B_fakestack OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Perf.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
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
  | H : (_ * _ < 2 ^ 3968)%Z |- _ => clear H
  | H : (zsum _ _ + _ <= _)%Z |- _ => clear H
  | H : (_ <= zsum _ _ <= _)%Z |- _ => clear H
  | H : (_ <= 2 ^ (64 * _))%Z |- _ => clear H
  | H : (_ < 2 ^ (64 * _))%Z |- _ => clear H
  | H : _ = nth _ _ _ |- _ => clear H
  | H : bnorm _ _ |- _ => clear H
  | H : smul_inv _ _ _ _ _ |- _ => clear H
  | H : boxed _ |- _ => clear H
  | H : stashed _ |- _ => clear H
  | H : stashed2 _ |- _ => clear H
  | H : forall j : nat, _ |- _ => clear H
  end.
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac lia0 := first [ LiaCap.lia_cap_s ltac:(lia_t1) ltac:(fail) | lia_t2 | lia_d1 | lia_app2 | lia_t3 ].  (* [comment removed for export] *)
Local Ltac lia ::= clear_vals; lia0.
Local Ltac lia4 ::= first [ lia_t1 | lia_t2 | lia_d1 | lia_app2 | lia_t3 ].  (* [comment removed for export] *)
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
Ltac kp_lia0_cap := LiaCap.lia_cap_s ltac:(lia_t1) ltac:(fail).
Ltac kp_lia0_rest := first [ lia_t2 | lia_d1 | lia_app2 | lia_t3 ].
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
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ match goal with S : sub_fp _ _ |- _ => exact S end | sub_fp_tac ] | exact MU ] ]  (* [comment removed for export] *)
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
Lemma land_lnot31 : forall x, (0 <= x)%Z -> Z.land x (Z.lnot 31) = (x - x mod 32)%Z.
Proof.
  intros x Hx.
  assert (D : Z.land x 31 = (x mod 32)%Z). { change 31%Z with (Z.ones 5). rewrite Z.land_ones by lia0. reflexivity. }
  rewrite <- Z.ldiff_land.
  pose proof (Z.lor_ldiff_and x 31) as L.
  assert (Z1 : Z.land (Z.ldiff x 31) (Z.land x 31) = 0%Z).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.testbit (Z.ldiff x 31) n) eqn:E1; [|reflexivity].
    rewrite Z.ldiff_spec in E1. apply andb_prop in E1. destruct E1 as [_ E2].
    rewrite Z.land_spec. destruct (Z.testbit x n); [|reflexivity]. cbn.
    destruct (Z.testbit 31 n); [discriminate| reflexivity]. }
  pose proof (Z.add_nocarry_lxor _ _ Z1) as A. rewrite (Z.lxor_lor _ _ Z1), L in A. lia0.
Qed.
Optimize Heap.
Lemma land_align32 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof.
  intros x Hx. rewrite <- land_lnot31 by lia0.
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.ltb_spec0 n 64).
  - f_equal. rewrite Z.lnot_spec by lia0.
    assert (E : 18446744073709551584%Z = Z.lor (Z.shiftl (Z.ones 59) 5) 0) by reflexivity.
    rewrite E, Z.lor_0_r. rewrite Z.shiftl_spec by lia0.
    destruct (Z.ltb_spec0 n 5).
    + rewrite (Z.testbit_neg_r (Z.ones 59)) by lia0. symmetry.
      change 31%Z with (Z.ones 5). rewrite Z.ones_spec_low by lia0. reflexivity.
    + rewrite Z.ones_spec_low by lia0. change 31%Z with (Z.ones 5). rewrite Z.ones_spec_high by lia0. reflexivity.
  - assert (Tx : Z.testbit x n = false).
    { destruct (Z.eq_dec x 0) as [->|]. { apply Z.bits_0. } apply Z.bits_above_log2; [lia0|].
      apply (Z.lt_le_trans _ 64); [| lia0]. apply Z.log2_lt_pow2; lia0. }
    rewrite Tx. reflexivity.
Qed.

Optimize Heap.
(* [comment removed for export] *)
Lemma fk4_consts : forall FS, fk_nframes 4 = 1024%Z /\ fk_size 4 = 1024%Z /\ fk_hint FS 4 = (FS + 32)%Z /\ fk_flags FS 4 = (FS + 34816)%Z
                   /\ forall p, fk_frame FS 4 p = (FS + 4231168 + p * 1024)%Z.
Proof.
  intros FS. unfold fk_hint, fk_flags, fk_frame, fk_size, fk_nframes.
  change (Z.shiftl 1 (14 - 4)) with 1024%Z. change (Z.shiftl 1 (6 + 4)) with 1024%Z.
  change (32 * Z.shiftl (Z.shiftr 1023 (10 - 4)) (10 - 4))%Z with 30720%Z.
  repeat split; intros; lia0.
Qed.

Optimize Heap.
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
  | munch ?Wq ?mq _ => apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ match goal with S : sub_fp _ _ |- _ => exact S end | sub_fp_tac ] | exact MU ] ]  (* [comment removed for export] *)
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
Ltac solve_part := first [ eassumption | reflexivity | lia ].



Definition ndc_pro_post (ra sp gp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ws : list word) (len p2 : Z) (v : rt_vals) (h4 h5 : word) (pos0 : Z) (m0 : word -> option byte) : machine_state -> Prop :=
  let A := bv_unsigned a0 in let FS := rt_FS v in let F0 := (FS + FK4_LO + pos0 * 1024)%Z in
  fun ms' => exists (x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) (S1 Fr pos1 : Z)
                    (fj0 fj496 lj zsh : list byte),
    ms' = MS (mkR x1 (Z_to_bv 64 S1) gp (Z_to_bv 64 TPV) x5 x6 x7 sp (Z_to_bv 64 S1) (Z_to_bv 64 Fr) x11 (Z_to_bv 64 p2) x13 x14 x15 x16 x17
                 s2 (Z_to_bv 64 (Fr / 8 + ASAN_B)) a2 a3 a0 a1 s8 (Z_to_bv 64 Fr) s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x96468) fc None m' (seg_rom BSEGS)
    /\ munch (negative_digit_comp_d_W (bv_unsigned sp) A FS pos0) m0 m' /\ wmono BSEGS m0 m'
    /\ (bv_unsigned sp - 176 <= S1 <= bv_unsigned sp - 160)%Z /\ (S1 mod 16 = 0)%Z
    /\ (0 <= pos1 < 1024)%Z /\ pos1 <> pos0 /\ Fr = (FS + FK4_LO + pos1 * 1024)%Z
    /\ (Fr + 1024 <= F0 \/ F0 + 1024 <= Fr)%Z /\ (Fr mod 1024 = 0)%Z
    /\ u64arr BSEGS m' A ws /\ rw_cells BSEGS m' (A + 496) [C2 (Z_to_bv 64 len)]
    /\ rw_cells BSEGS m' (Fr + 32) [CB 8 fj0] /\ rw_cells BSEGS m' (Fr + 40) [CB 496 fj496]
    /\ rw_cells BSEGS m' (Fr + 1016) [C8 (Z_to_bv 64 (FS + 34816 + pos1))]
    /\ stk BSEGS m' Fr (Fr + 1024) /\ stk BSEGS m' (ASAN_B + Fr / 8) (ASAN_B + Fr / 8 + 128)
    /\ rw_cells BSEGS m' (S1 + 24) [CB 32 lj]
    /\ rw_cells BSEGS m' (Fr / 8 + 2147450884) [CB 63 zsh]
    /\ stk BSEGS m' (bv_unsigned sp - 2768) S1 /\ stk BSEGS m' S1 (S1 + 24) /\ stk BSEGS m' (S1 + 56) (bv_unsigned sp - 104)
    /\ rw_cells BSEGS m' (bv_unsigned sp + -104)
         [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells BSEGS m' (FS + 32) [C8 (Z_to_bv 64 ((bv_unsigned h4 + 1) mod 2 ^ 64))]
    /\ u8arr BSEGS m' (FS + 34816) (upd (upd (zeros 1024) (Z.to_nat pos0) (Z_to_bv 8 1)) (Z.to_nat pos1) (Z_to_bv 8 1))
    /\ fs_cells_ok FS m'
    /\ stk BSEGS m' (FS + FK4_LO) F0 /\ stk BSEGS m' (F0 + 1024) (FS + FK4_HI)
    /\ stk BSEGS m' (ASAN_B + FS / 8 + FK4_SLO) (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128)
    /\ stk BSEGS m' (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128 + 128) (ASAN_B + FS / 8 + FK4_SHI)
    /\ fk5_inv m' FS h5
    /\ pristine m' IMG_LO ROD_HI /\ pristine m' RELRO_LO RELRO_HI /\ pristine m' REALTAB_LO REALTAB_HI
    /\ shz BSEGS m' (ASAN_B + A / 8) 63 /\ shz BSEGS m' POW5TAB_SH POW5TAB_SHN
    /\ rdbl BSEGS m' (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N
    /\ shz BSEGS m' (ASAN_B + (bv_unsigned sp - 2768) / 8) 346.

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
Ltac lean_ctx KEEP :=
  repeat match goal with H : length ?l = ?n |- context [length ?l] =>
    lazymatch n with context [length _] => fail | _ => rewrite !H end end;
  clear - KEEP; decompose [and] KEEP; clear KEEP; try unfold stashed in *; try unfold stashed2 in *;
  repeat (rewrite unsigned_lit by (first [lia0 | Z.div_mod_to_equations; lia0])).
Ltac dj_lean KEEP :=
  cbn [disjoint_from]; simpl_sizes; try simpl_arr_sizes; rewrite ?u64s_length, ?upd_length, ?zeros_length, ?repeat_length; lean_ctx KEEP;
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia0 | Z.div_mod_to_equations; lia0].
Ltac sf_lean KEEP := first [ solve [sub_fp_fast] | unfold sub_fp; cbn [outside]; lean_ctx KEEP; intros; first [lia0 | Z.div_mod_to_equations; lia0] ].
Ltac transport_lean segs m m' MU WM KEEP :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | dj_lean KEEP ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | dj_lean KEEP ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | dj_lean KEEP ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_lean KEEP ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_lean KEEP ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : shz segs m ?A2 ?n2 |- _ =>
      first [ apply (shz_transport segs W m m' A2 n2) in H; [ | exact MU | dj_lean KEEP ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ => apply (stk_mono segs m m' loq hiq) in H; [ | exact WM ]
  | H : rdbl segs m ?A2 ?n2 |- _ => apply (rdbl_mono segs m m' A2 n2) in H; [ | exact WM ]
  | H : pristine m ?lo ?hi |- _ =>
      first [ apply (pristine_transport W m m' lo hi) in H; [ | exact MU | dj_lean KEEP ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ match goal with S : sub_fp _ _ |- _ => exact S end | sf_lean KEEP ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
(* [comment removed for export] *)
Ltac transport1_lean m m' W MU WM KEEP H :=
  lazymatch type of H with
  | bytes_at _ _ ?A2 ?bs2 => apply (bytes_at_transport BSEGS W m m' A2 bs2) in H; [ | exact MU | dj_lean KEEP ]
  | rw_cells _ _ ?A2 ?cs2 => apply (rw_cells_transport BSEGS W m m' A2 cs2) in H; [ | exact MU | exact WM | dj_lean KEEP ]
  | ro_cells _ _ ?A2 ?cs2 => apply (ro_cells_transport BSEGS W m m' A2 cs2) in H; [ | exact MU | dj_lean KEEP ]
  | u8arr _ _ ?A2 ?xs => apply (u8arr_transport BSEGS W m m' A2 xs) in H; [ | exact MU | exact WM | dj_lean KEEP ]
  | u64arr _ _ ?A2 ?xs => apply (u64arr_transport BSEGS W m m' A2 xs) in H; [ | exact MU | exact WM | dj_lean KEEP ]
  | u8ro _ _ ?A2 ?xs => apply (u8ro_transport BSEGS W m m' A2 xs) in H; [ | exact MU | dj_lean KEEP ]
  | shz _ _ ?A2 ?n2 => apply (shz_transport BSEGS W m m' A2 n2) in H; [ | exact MU | dj_lean KEEP ]
  | stk _ _ ?loq ?hiq => apply (stk_mono BSEGS m m' loq hiq) in H; [ | exact WM ]
  | rdbl _ _ ?A2 ?n2 => apply (rdbl_mono BSEGS m m' A2 n2) in H; [ | exact WM ]
  | pristine _ ?lo ?hi => apply (pristine_transport W m m' lo hi) in H; [ | exact MU | dj_lean KEEP ]
  | munch ?Wq ?mq _ => apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ match goal with S : sub_fp _ _ |- _ => exact S end | sf_lean KEEP ] | exact MU ] ]
  | wmono _ ?mq _ => apply (wmono_trans BSEGS mq m m') in H; [ | exact WM ]
  end.
Ltac unstash_lean MU WM KEEP :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    unstash_props;
    repeat match goal with H : stashed ?T |- _ =>
      unfold stashed in H; first [ transport1_lean ma mb W MU WM KEEP H | idtac "note: dropping hypothesis (unstash_lean):" H; clear H ]
    end;
    repeat match goal with H : stashed2 ?T |- _ =>
      unfold stashed2 in H; first [ transport1_lean ma mb W MU WM KEEP H | idtac "note: dropping hypothesis (unstash_lean):" H; clear H ]
    end
  end.
(* [comment removed for export] *)
Ltac post_call_lean segs m KEEP :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  lazymatch type of PO with
  | _ /\ _ => destruct PO as [MIc PO]
  | _ => rename PO into MIc
  end;
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let W' := eval hnf in W in
      change (munch W' m m') in MUc;
      transport_lean segs m m' MUc WMc KEEP; clear KEEP;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Section Pro.
  Hypothesis smalloc4_spec : smalloc4_stmt.

  (* [comment removed for export] *)
  #[using="smalloc4_spec"] Lemma ndc_pro_run :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len p2 : Z) (v : rt_vals) (h4 h5 : word) (pos0 : Z),
    let FS := rt_FS v in
    let F0 := (FS + FK4_LO + pos0 * 1024)%Z in
    stk BSEGS m (bv_unsigned sp - NDC_NEED) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (IMG_END <= bv_unsigned sp - NDC_NEED)%Z ->
    pristine m IMG_LO ROD_HI ->
    u64arr BSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells BSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z ->
    (bv_unsigned a2 = p2 mod 2 ^ 32)%Z -> (- 2 ^ 14 <= p2 <= 2 ^ 14)%Z ->
    tp = Z_to_bv 64 TPV ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v ->
    fk4_nest m FS h4 pos0 -> (0 <= pos0 < 1024)%Z -> (bv_unsigned h4 mod 1024 <> pos0)%Z ->
    fk5_inv m FS h5 ->
    (KHI <= bv_unsigned sp - NDC_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (FS + FSSIZE <= bv_unsigned sp - NDC_NEED)%Z ->
    (F0 + 32 <= bv_unsigned a0)%Z -> (bv_unsigned a0 + 504 <= F0 + 1024)%Z ->
    rt_disj v (bv_unsigned sp - NDC_NEED) (bv_unsigned sp) ->
    rt_disj v FS (FS + FSSIZE) ->
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    shz BSEGS m POW5TAB_SH POW5TAB_SHN ->
    rdbl BSEGS m (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N ->
    shz BSEGS m (ASAN_B + (bv_unsigned sp - NDC_NEED) / 8) 346 ->
    evt BSEGS (ndc_pro_post ra sp gp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ws len p2 v h4 h5 pos0 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 NDC_D_ENTRY) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (smalloc4_spec : LiaFast.U) => LiaFast.u0).
    intros until pos0. cbv zeta.
    intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 Hp2 Rp2 TP PRG PRT RTH FK4 Hpos0 Hne FK5 KSP KSP2 SFS HA1 HA2 RD1 RD3 SHX SHT RBF SHW.
    subst tp.
    pose proof (munch_refl (negative_digit_comp_d_W (bv_unsigned sp) (bv_unsigned a0) (rt_FS v) pos0) m) as MU0.
    cbv delta [negative_digit_comp_d_W] in MU0.
    pose proof (wmono_refl BSEGS m) as WM0.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 h4) as Rh4. unfold bv_modulus in Rh4.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as BdX. rewrite L62 in BdX.
    open_RT_keep RTH.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & KF1 & KF2 & KF8 & Kc1 & Kc2 & Kt1 & Kt2 & Kb1 & Kb2).
    clear RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb.
    destruct FK4 as (FSC & HINT & FL & SK4a & SK4b & SKS4a & SKS4b). unfold fs_cells_ok in FSC.
    destruct FK5 as (_ & HINT5 & FL5 & SK5 & SKS5).
    pose proof (fk4_consts (rt_FS v)) as (N4 & SZ4 & HI4 & FLG4 & FRM4).
    pose proof (Z.mod_pos_bound (bv_unsigned h4) 1024 ltac:(lia)) as Hm1.
    (* [comment removed for export] *)
    assert (STF1 : stk BSEGS m (rt_FS v + 4231168 + bv_unsigned h4 mod 1024 * 1024) (rt_FS v + 4231168 + bv_unsigned h4 mod 1024 * 1024 + 1024)).
    { destruct (Z.lt_ge_cases (bv_unsigned h4 mod 1024) pos0).
      - eapply stk_subC; [exact SK4a | clear - H Hm1; lia0 | clear - H Hm1; lia0 | lia].
      - eapply stk_subC; [exact SK4b | clear - H Hm1 Hne; lia0 | clear - H Hm1 Hne Hpos0; lia0 | lia]. }
    assert (STS1 : stk BSEGS m (ASAN_B + (rt_FS v + 4231168 + bv_unsigned h4 mod 1024 * 1024) / 8)
                                (ASAN_B + (rt_FS v + 4231168 + bv_unsigned h4 mod 1024 * 1024) / 8 + 128)).
    { destruct (Z.lt_ge_cases (bv_unsigned h4 mod 1024) pos0).
      - eapply stk_subC; [exact SKS4a | clear - H Hm1 KF8; zlia | clear - H Hm1 KF8; zlia | clear - KF8 Hm1; zlia].
      - eapply stk_subC; [exact SKS4b | clear - H Hm1 Hne KF8; zlia | clear - H Hm1 Hne Hpos0 KF8; zlia | clear - KF8 Hm1; zlia]. }
    (* [comment removed for export] *)
    carve_frame 160%nat ST.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp + -160 + 160)]%Z mc) as MUp; pose proof (wmono_refl BSEGS mc) as WMp end.
    stash_but FR MUp WMp.
    do 14 step. (* [comment removed for export] *)
    unstash_chunks MUp WMp. clear MUp WMp.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite (land_align32 (bv_unsigned sp + -160)) by lia.
    set (S1 := (bv_unsigned sp + -160 - (bv_unsigned sp + -160) mod 32)%Z).
    assert (HS1 : (bv_unsigned sp - 176 <= S1 <= bv_unsigned sp - 160)%Z) by (subst S1; clear - Rsp KSP AL; Z.div_mod_to_equations; lia0).
    assert (HS1a : (S1 mod 16 = 0)%Z) by (subst S1; clear - Rsp KSP AL; Z.div_mod_to_equations; lia0).
    clearbody S1.
    pose proof (unsigned_lit S1 ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    name_mem m1.
    chunk_split FR 2%nat FRlo SV.
    pose proof (stk_of_rw_cells BSEGS m1 _ _ FRlo) as STlo; clear FRlo.
    cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in STlo.
    assert (STK0 : stk BSEGS m1 (bv_unsigned sp - 2768) (bv_unsigned sp - 104))
      by (eapply stk_join; [exact ST | eapply stk_eq; [exact STlo | reflexivity | lia] | lia | lia]).
    clear ST STlo junk.
    destruct (stk_split BSEGS m1 _ S1 _ STK0 ltac:(lia)) as [ST STa]. clear STK0.
    destruct (stk_split BSEGS m1 _ (S1 + 24) _ STa ltac:(lia)) as [ST0 STb]. clear STa.
    destruct (stk_split BSEGS m1 _ (S1 + 56) _ STb ltac:(lia)) as [STc ST2]. clear STb.
    destruct (stk_carve BSEGS m1 (S1 + 24) (S1 + 56) 32%nat STc ltac:(lia)) as [_ [lj0 LOCj]]. clear STc.
    replace (S1 + 56 - Z.of_nat 32)%Z with (S1 + 24)%Z in LOCj by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    name_mem m2.
    eapply evt_cut; [ eapply smalloc4_spec with (v := v) (h := bv_unsigned h4) (fl := upd (zeros 1024) (Z.to_nat pos0) (Z_to_bv 8 1)) | ].
    all: try rewrite ?N4, ?SZ4, ?HI4, ?FLG4, ?FRM4.
    all: try lazymatch goal with
         | |- forall ms', _ -> _ => idtac
         | |- rw_cells _ _ _ [C8 _] => rewrite Z_to_bv_bv_unsigned; exact HINT
         | |- u8arr _ _ _ _ => exact FL
         | |- Z.of_nat _ = _ => rewrite upd_length, zeros_length; reflexivity
         | |- nth_error _ _ = _ => rewrite nth_error_upd_other by (clear - Hne Hm1 Hpos0; lia0); apply nth_error_zeros; clear - Hm1; lia0
         | |- stk _ _ _ _ => first [ exact STF1
                                   | change (1024 / 8)%Z with 128%Z; exact STS1
                                   | eapply stk_subC; [exact ST | lia | lia | lia] ]
         | |- fs_cells_ok _ _ => exact FSC
         | |- _ => side
         end.
    (* [comment removed for export] *)
    intros ms' PO. cbv beta zeta delta [smalloc_post smalloc_W] in PO.
    rewrite ?N4, ?SZ4, ?HI4, ?FLG4, ?FRM4, ?ULs in PO.
    change (Z.to_nat (1024 - 40)) with 984%nat in PO. change (1024 / 8)%Z with 128%Z in PO. change (Z.to_nat 128) with 128%nat in PO.
    set (pos1 := (bv_unsigned h4 mod 1024)%Z) in *.
    assert (Hpos1 : (0 <= pos1 < 1024)%Z) by (subst pos1; exact Hm1).
    assert (Hne1 : pos1 <> pos0) by (subst pos1; exact Hne).
    clearbody pos1. clear Hm1 Hne.
    set (Fr := (rt_FS v + 4231168 + pos1 * 1024)%Z) in PO.
    assert (HFrE : Fr = (rt_FS v + FK4_LO + pos1 * 1024)%Z) by reflexivity.
    assert (HFr1 : (rt_FS v + FK4_LO <= Fr)%Z) by (subst Fr; lia).
    assert (HFr2 : (Fr + 1024 <= rt_FS v + FK4_HI)%Z) by (subst Fr; lia).
    assert (HFr8 : (Fr mod 1024 = 0)%Z) by (subst Fr; clear - KF8 Hpos1; Z.div_mod_to_equations; lia0).
    assert (HFrF0 : (Fr + 1024 <= rt_FS v + FK4_LO + pos0 * 1024 \/ rt_FS v + FK4_LO + pos0 * 1024 + 1024 <= Fr)%Z) by (subst Fr; clear - Hpos1 Hne1 Hpos0; lia0).
    clearbody Fr.
    pose proof (unsigned_lit Fr ltac:(lia)) as ULf.
    destruct_exs PO. destruct PO as [E [MUc [WMc PO]]]. subst ms'.
    (* [comment removed for export] *)
    pose proof (conj Rsp (conj AL (conj KSP (conj KSP2 (conj HS1 (conj HS1a (conj KF1 (conj KF2 (conj Hpos0 (conj Hpos1 (conj Hne1
               (conj SFS (conj HFrE (conj HFr1 (conj HFr2 (conj HFrF0 (conj HA1 (conj HA2 L62)))))))))))))))))) as KEEP.
    clear HINT FL. (* [comment removed for export] *)
    lazymatch type of MUc with munch ?W _ ?m3 => transport_lean BSEGS m2 m3 MUc WMc KEEP end.
    clear KEEP.
    clear MUc WMc. destruct_ands PO.
    lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
    end.
    match goal with H : stk BSEGS _ (S1 - 208) S1 |- _ => clear H | _ => idtac end.
    match goal with H : rw_cells BSEGS _ Fr _ |- _ => rename H into FRM end.
    match goal with H : rw_cells BSEGS _ (ASAN_B + Fr / 8) _ |- _ => rename H into SHF;
      replace (ASAN_B + Fr / 8)%Z with (Fr / 8 + 2147450880)%Z in SHF by lia end.
    (* [comment removed for export] *)
    lazymatch type of SHF with rw_cells _ ?mm ?a [CB 128 ?zs] =>
      apply (rw_cells_split_CB BSEGS mm a [] 128%nat zs [] [76; 52]%nat) in SHF; [|reflexivity];
      cbn [mk_CB_cells app] in SHF end.
    chunk_split SHF 1%nat SHlo SHhi. clear SHhi.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_taken.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (munch_refl [(Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 76)]%Z mc) as MUs; pose proof (wmono_refl BSEGS mc) as WMs end.
    stash2 SHX. stash2 SHT.
    stash_but SHlo MUs WMs.
    do 4 step.
    step. (* [comment removed for export] *)
    rewrite Hp2, uw_mod32, Z.add_0_r, (swrap32_id p2) by lia.
    do 24 step. Optimize Proof. Optimize Heap.
    do 24 step. Optimize Proof. Optimize Heap.
    do 24 step.
    pose proof (conj Rsp (conj AL (conj KSP (conj KSP2 (conj HS1 (conj HS1a (conj KF1 (conj KF2 (conj Hpos0 (conj Hpos1 (conj Hne1
               (conj SFS (conj HFrE (conj HFr1 (conj HFr2 (conj HFrF0 (conj HA1 (conj HA2 L62)))))))))))))))))) as KEEP2.
    unstash_lean MUs WMs KEEP2. clear MUs WMs KEEP2.  (* [comment removed for export] *)
    (* [comment removed for export] *)
    name_mem mP.
    match goal with H : rw_cells BSEGS mP Fr ?cs |- _ =>
      lazymatch cs with [?c1; ?c2; ?c3; ?c4; CB 984 ?j; ?c6] =>
        apply (rw_cells_split_CB BSEGS mP Fr [c1; c2; c3; c4] 984%nat j [c6] [8; 496; 480]%nat) in H; [|reflexivity];
        cbn [mk_CB_cells app] in H end end.
    chunk_split FRM 4%nat FRH FR1. clear FRH.
    chunk_split FR1 1%nat ZF0 FR2. chunk_split FR2 1%nat ZM FR3. chunk_split FR3 1%nat REST FLC. clear REST.
    chunk_split SHlo 4%nat SHa SH1. clear SHa. chunk_split SH1 63%nat SHZc SHb. clear SHb.
    match type of SHZc with rw_cells _ _ ?a ?cs =>
      pose proof (rw_cells_merge BSEGS mP a [] cs [] ltac:(rewrite app_nil_r; exact SHZc)) as SHZ; clear SHZc; cbn [app] in SHZ;
      let n' := eval vm_compute in (cells_size cs) in change (cells_size cs) with n' in SHZ;
      replace a with (Fr / 8 + 2147450884)%Z in SHZ by lia end.
    apply evt_done. unfold ndc_pro_post. cbv zeta.
    do 14 eexists. eexists mP, S1, Fr, pos1. do 4 eexists.
    split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try eassumption; try lia.
    all: try lazymatch goal with
         | |- munch _ _ _ => cbv delta [negative_digit_comp_d_W] in *; eassumption
         | |- fs_cells_ok _ _ => eassumption
         | |- stk _ _ ?lo (?lo + 1024)%Z => rewrite HFrE; exact STF1
         | |- stk _ _ ?lo (?lo + 128)%Z => rewrite HFrE; exact STS1
         | |- fk5_inv _ _ _ => split; [eassumption | repeat match goal with |- _ /\ _ => split end; eassumption]
         end.
    all: match goal with |- ?g => idtac "REMAIN-PRO" g end.
  Qed.
  Optimize Heap.
End Pro.
End B_negative_digit_comp_d_P.

From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_negative_digit_comp_d_M2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_negative_digit_comp_d_M2 B_negative_digit_comp_d_M1.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt.B_fakestack OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_shl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_normalize_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_compare_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d.B_negative_digit_comp_d_P OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_M2.B_negative_digit_comp_d_T OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_M2 OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_M1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Perf.
Local Ltac lia4 ::= first [ lia_t1 | lia_t2 | lia_d1 | lia_app2 | lia_t3 ].  (* [comment removed for export] *)
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


Ltac solve_part := first [ eassumption | reflexivity | lia | zlia ].

Section Main.
  Hypothesis smalloc4_spec : smalloc4_stmt.
  Hypothesis asan_memset_spec : asan_memset_stmt.
  Hypothesis normalize_spec : normalize_stmt.
  Hypothesis pow5_spec : pow5_stmt.
  Hypothesis shl_spec : shl_stmt.
  Hypothesis compare_spec : compare_stmt.
  Hypothesis set_shadow_f5_spec : set_shadow_f5_stmt.

  #[using="smalloc4_spec asan_memset_spec normalize_spec pow5_spec shl_spec compare_spec set_shadow_f5_spec"] Lemma negative_digit_comp_d_spec : negative_digit_comp_d_stmt.
  Proof. LiaFast.lf_pins (fun (smalloc4_spec asan_memset_spec normalize_spec pow5_spec shl_spec compare_spec set_shadow_f5_spec : LiaFast.U) => LiaFast.u0).
    unfold negative_digit_comp_d_stmt. intros until pos0. cbv zeta.
    intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM Hp2 Rp2 He Re TP PRG PRT RTH FK4 Hpos0 Hne FK5 KSP KSP2 SFS HA1 HA2 RD1 RD3 SHX SHT RBF RTX0 SHW.
    subst a3 tp.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof RTH as RTH'. open_RT_keep RTH'.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & KF1 & KF2 & KF8 & Kc1 & Kc2 & Kt1 & Kt2 & Kb1 & Kb2).
    clear RT1 RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb RTH'.
    (* [comment removed for export] *)
    eapply evt_cut; [ eapply (ndc_pro_run smalloc4_spec) with (ws := ws) (len := len) (p2 := p2) (v := v) (h4 := h4) (h5 := h5) (pos0 := pos0);
                      first [eassumption | reflexivity | lia] | ].
    cbv zeta. intros ms' PO. destruct_exs PO.
    destruct PO as [E [MU0 [WM0 PO]]]. subst ms'. destruct_ands PO.
    clear ST LIMBS LENC FK4 FK5 PR PRG PRT SHX SHT RBF SHW.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mP end.
    match goal with H : (bv_unsigned sp - 176 <= ?s <= bv_unsigned sp - 160)%Z |- _ => rename s into S1 end.
    match goal with H : (?f mod 1024 = 0)%Z |- _ => rename f into Fr end.
    match goal with H : (0 <= ?q < 1024)%Z, H2 : ?q <> pos0 |- _ => rename q into pos1 end.
    (* [comment removed for export] *)
    eapply (ndc_mid_run asan_memset_spec normalize_spec pow5_spec shl_spec compare_spec set_shadow_f5_spec)
      with (ws := ws) (len := len) (e := e) (p2 := p2) (v := v) (pos1 := pos1); try eassumption.
    all: try lazymatch goal with
         | |- munch _ _ _ => cbv delta [negative_digit_comp_d_W] in *; eassumption
         | |- _ => solve_part
         end.
  Qed.
End Main.

(* [comment removed for export] *)
