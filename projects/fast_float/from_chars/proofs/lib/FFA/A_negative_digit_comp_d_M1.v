(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import LiaTuning Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_cap A_rt_stmt A_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_negative_digit_comp_d_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_long_mul_stmt A_pow5_stmt A_shl_stmt A_negative_digit_comp_d_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_negative_digit_comp_d_M2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_negative_digit_comp_d_M2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_cap OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_negative_digit_comp_d_stmt.A_fakestack OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_shl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_negative_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_negative_digit_comp_d_M2.A_negative_digit_comp_d_T OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_negative_digit_comp_d_M2.
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
  stk ASEGS m lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> (lo' <= hi')%Z -> stk ASEGS m lo' hi'.
Proof.
  intros m lo hi lo' hi' ST H1 H2 H3.
  destruct (stk_split ASEGS m lo lo' hi ST ltac:(lia)) as [_ ST1].
  destruct (stk_split ASEGS m lo' hi' hi ST1 ltac:(lia)) as [ST2 _]. exact ST2.
Qed.
Optimize Heap.
Lemma stk_join : forall m lo a b hi,
  stk ASEGS m lo a -> stk ASEGS m b hi -> (a = b)%Z -> (lo <= a <= hi)%Z -> stk ASEGS m lo hi.
Proof. intros m lo a b hi H1 H2 <- H. eapply stk_merge; [exact H1 | exact H2 | exact H]. Qed.
Lemma stk_eq : forall m lo hi lo' hi',
  stk ASEGS m lo hi -> (lo' = lo)%Z -> (hi' = hi)%Z -> stk ASEGS m lo' hi'.
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
  | bytes_at _ _ ?A2 ?bs2 => apply (bytes_at_transport ASEGS W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
  | rw_cells _ _ ?A2 ?cs2 => apply (rw_cells_transport ASEGS W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; vlia ]
  | ro_cells _ _ ?A2 ?cs2 => apply (ro_cells_transport ASEGS W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; vlia ]
  | u8arr _ _ ?A2 ?xs => apply (u8arr_transport ASEGS W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
  | u64arr _ _ ?A2 ?xs => apply (u64arr_transport ASEGS W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
  | u8ro _ _ ?A2 ?xs => apply (u8ro_transport ASEGS W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; vlia ]
  | shz _ _ ?A2 ?n2 => apply (shz_transport ASEGS W m m' A2 n2) in H; [ | exact MU | cbn [disjoint_from]; vlia ]
  | stk _ _ ?loq ?hiq => apply (stk_mono ASEGS m m' loq hiq) in H; [ | exact WM ]
  | rdbl _ _ ?A2 ?n2 => apply (rdbl_mono ASEGS m m' A2 n2) in H; [ | exact WM ]
  | pristine _ ?lo ?hi => apply (pristine_transport W m m' lo hi) in H; [ | exact MU | cbn [disjoint_from]; vlia ]
  | munch ?Wq ?mq _ => apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ match goal with S : sub_fp _ _ |- _ => exact S end | unfold sub_fp; cbn [outside]; intros; flia ] | exact MU ] ]
  | wmono _ ?mq _ => apply (wmono_trans ASEGS mq m m') in H; [ | exact WM ]
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
  rw_cells ASEGS m A [C8 v] -> u64arr ASEGS m (A + 8) ws -> u64arr ASEGS m A (v :: ws).
Proof.
  intros m A v ws [[_ Hb] Hw] [Hb2 Hw2]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize Nat.add] in Hw.
  split.
  - cbn [u64s map concat]. change (le8 v ++ u64s ws) with (le8 v ++ u64s ws).
    apply (proj2 (bytes_at_app ASEGS m A (le8 v) (u64s ws))). split; [exact Hb|].
    rewrite length_le8. exact Hb2.
  - cbn [length]. rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat (length ws)))%Z with (8 + 8 * Z.of_nat (length ws))%Z by lia0.
    apply (proj2 (wr_at_app ASEGS m A 8 (8 * Z.of_nat (length ws)) ltac:(lia0) ltac:(lia0))). split; [exact Hw| exact Hw2].
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
Section Mid.
  Hypothesis asan_memset_spec : asan_memset_stmt.
  Hypothesis pow5_spec : pow5_stmt.
  Hypothesis shl_spec : shl_stmt.
  Hypothesis set_shadow_f5_spec : set_shadow_f5_stmt.
  Variables (sp va gp a1w a2w : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (ws : list word) (len e : Z) (S1 Fr pos0 pos1 : Z) (v : rt_vals) (mR : word -> option byte).
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
  Notation RS m := (rw_cells ASEGS m (bv_unsigned sp + -104)
     [C8 q11; C8 q10; C8 q9; C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 ra0]).
  Notation NDPOST := (negative_digit_comp_d_post ra0 sp gp (Z_to_bv 64 TPV) q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 F fc A v pos0 mR).
  Notation CMP_INV m wsr lenr wst lent h5' lj hw :=
    (cmp_inv sp va S1 Fr pos0 pos1 v mR ra0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 m wsr lenr wst lent a1w lj hw h5').

  (* [comment removed for export] *)
  Notation W_SHZ := [(SHZb, SHZb + 63)]%Z.
  Notation W_MST := [(bv_unsigned SP1 - 2208, bv_unsigned SP1); (bv_unsigned (Z_to_bv 64 (Fr + 40)), bv_unsigned (Z_to_bv 64 (Fr + 40)) + bv_unsigned (Z_to_bv 64 496))]%Z.
  Notation W_P5 := (pow5_W (bv_unsigned SP1) (bv_unsigned S8) FS).
  Notation W_SHT := (shl_W (bv_unsigned SP1) (bv_unsigned S8)).
  Notation W_SHB := (shl_W (bv_unsigned SP1) (bv_unsigned va)).
  Ltac sfp := pose proof (unsigned_lit S1 ltac:(lia)) as U1; pose proof (unsigned_lit Fr ltac:(lia)) as U2;
              pose proof (unsigned_lit (Fr + 32) ltac:(lia)) as U3; pose proof (unsigned_lit (Fr + 40) ltac:(lia)) as U4;
              pose proof (unsigned_lit 496 ltac:(lia)) as U5;
              clear - U1 U2 U3 U4 U5 HS1 Rsp HFrE HFrF0 Hpos0 Hpos1 Hne1 KF1 KF2 KF8 KSP KSP2 HA1 HA2;
              cbv delta [negative_digit_comp_d_W pow5_W shl_W]; unfold sub_fp; cbn [outside]; intros; first [lia0 | Z.div_mod_to_equations; lia0].
  #[using="ws S1 pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfM_shz_L : sub_fp W_SHZ WL. Proof. LiaFast.lf_pins (fun (ws S1 pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="sp va ws S1 pos0 pos1 v L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 Kc1 Kt1 Kb1"] Lemma sfM_shz_K : sub_fp W_SHZ W_SHZ. Proof. LiaFast.lf_pins (fun (sp va ws S1 pos0 pos1 v L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="ws pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfM_mst_L : sub_fp W_MST WL. Proof. LiaFast.lf_pins (fun (ws pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="ws pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfM_p5_L : sub_fp W_P5 WL. Proof. LiaFast.lf_pins (fun (ws pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="ws pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfM_sht_L : sub_fp W_SHT WL. Proof. LiaFast.lf_pins (fun (ws pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="ws Fr pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfM_shb_L : sub_fp W_SHB WL. Proof. LiaFast.lf_pins (fun (ws Fr pos1 L62 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  Ltac pose_sf := pose proof sfM_shz_L; pose proof sfM_shz_K; pose proof sfM_mst_L; pose proof sfM_p5_L; pose proof sfM_sht_L; pose proof sfM_shb_L.
  Ltac clear_sf := repeat match goal with S : sub_fp _ _ |- _ => clear S end.

  Ltac close_cmp :=
    unfold cmp_inv, fs_cells_ok, fk5_inv; repeat match goal with |- _ /\ _ => split end; try eassumption; try lia;
    try lazymatch goal with
        | |- munch _ _ _ => cbv delta [negative_digit_comp_d_W] in *; eassumption
        | |- stk _ _ ?lo (?lo + 1016)%Z => match goal with H : stk ASEGS _ lo (lo + 1024)%Z |- _ => eapply stk_subC; [exact H | lia | lia | lia] end
        | |- stk _ _ (?f / 8 + 2147450880)%Z _ => match goal with H : stk ASEGS _ (ASAN_B + f / 8)%Z _ |- _ => eapply stk_subC; [exact H | lia | lia | lia] end
        end.

  #[using="asan_memset_spec pow5_spec shl_spec set_shadow_f5_spec L62 Hlen A8 Re AL Rsp HS1 HS1a KSP KSP2 SFS RTX0 KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HFr8 HA1 HA2 RTH RD1 RD3 Kc1 Kt1 Kb1"] Lemma ndc_mid_run : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word)
      (m : word -> option byte) (h5 hw : word) (fj0 fj496 lj zsh : list byte),
      u64arr ASEGS m A ws -> rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells ASEGS m (Fr + 32) [CB 8 fj0] -> rw_cells ASEGS m (Fr + 40) [CB 496 fj496] ->
      rw_cells ASEGS m (Fr + 1016) [C8 (Z_to_bv 64 FLADDR)] ->
      stk ASEGS m Fr (Fr + 1024) -> stk ASEGS m (ASAN_B + Fr / 8) (ASAN_B + Fr / 8 + 128) ->
      rw_cells ASEGS m (S1 + 24) [CB 32 lj] ->
      rw_cells ASEGS m SHZb [CB 63 zsh] ->
      stk ASEGS m (bv_unsigned sp - 2768) S1 -> stk ASEGS m S1 (S1 + 24) -> stk ASEGS m (S1 + 56) (bv_unsigned sp - 104) ->
      RS m ->
      rw_cells ASEGS m (FS + 32) [C8 hw] ->
      u8arr ASEGS m (FS + 34816) (upd (upd (zeros 1024) (Z.to_nat pos0) (Z_to_bv 8 1)) (Z.to_nat pos1) (Z_to_bv 8 1)) ->
      fs_cells_ok FS m ->
      stk ASEGS m (FS + FK4_LO) F0 -> stk ASEGS m (F0 + 1024) (FS + FK4_HI) ->
      stk ASEGS m (ASAN_B + FS / 8 + FK4_SLO) (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128) ->
      stk ASEGS m (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128 + 128) (ASAN_B + FS / 8 + FK4_SHI) ->
      fk5_inv m FS h5 ->
      pristine m IMG_LO ROD_HI -> pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
      shz ASEGS m (ASAN_B + A / 8) 63 -> shz ASEGS m POW5TAB_SH POW5TAB_SHN ->
      rdbl ASEGS m (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N ->
      munch WL mR m -> wmono ASEGS mR m ->
      evt ASEGS NDPOST
        (MS (mkR x1 SP1 gp (Z_to_bv 64 TPV) x5 x6 x7 sp SP1 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 Fr) a2w SFw a1w va (Z_to_bv 64 e) x24 x25 (Z_to_bv 64 Fr) BB x28 x29 x30 x31)
            F (Z_to_bv 64 0x95de4) fc None m (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins (fun (asan_memset_spec pow5_spec shl_spec set_shadow_f5_spec L62 Hlen A8 Re AL Rsp HS1 HS1a KSP KSP2 SFS RTX0 KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HFr8 HA1 HA2 RTH RD1 RD3 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0).
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 m h5 hw fj0 fj496 lj zsh
           LIMBS LENC ZF0 ZM FLC STF STS LOCj SHZ ST ST0 ST2 SV HINT FL FSC SK4a SK4b SKS4a SKS4b FK5 PR PRG PRT SHX SHT RBF MU0 WM0.
    unfold fs_cells_ok in FSC. destruct FK5 as (_ & HINT5 & FL5 & SK5 & SKS5).
    cbv delta [negative_digit_comp_d_W] in MU0.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as BdX. rewrite L62 in BdX.
    pose proof (unsigned_lit S1 ltac:(lia)) as ULs. pose proof (unsigned_lit Fr ltac:(lia)) as ULf.
    pose proof (unsigned_lit (Fr + 32) ltac:(lia)) as ULs8.
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    assert (J98 : forall (u10 u11 u12 u13 u14 u25 : word),
      evt ASEGS NDPOST
        (MS (mkR x1 SP1 gp (Z_to_bv 64 TPV) x5 x6 x7 sp SP1 u10 u11 u12 u13 u14 x15 x16 x17
                 (Z_to_bv 64 Fr) a2w SFw va va (Z_to_bv 64 e) S8 u25 (Z_to_bv 64 Fr) BB x28 x29 x30 x31)
            F (Z_to_bv 64 0x95e90) fc None m0 (seg_rom ASEGS)))
    end.
    { intros.
      step. (* [comment removed for export] *)
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        pose proof (munch_refl W_SHZ mc) as MUs; pose proof (wmono_refl ASEGS mc) as WMs end.
      stash2 SHX. stash2 SHT.
      stash_but SHZ MUs WMs.
      do 21 step. Optimize Proof. Optimize Heap.
      do 21 step. Optimize Proof. Optimize Heap.
      do 21 step.
      pose_sf. unstash_chunks MUs WMs. clear MUs WMs. clear_sf.
      match goal with H : rw_cells ASEGS _ SHZb ?cs |- _ => rename H into SHZ1;
        pose proof (shz_of_rw_cells ASEGS _ _ cs SHZ1 ltac:(cbn [cells_bytes cbytes app]; repeat constructor)) as SHZt;
        let n' := eval vm_compute in (Z.of_nat (cells_size cs)) in change (Z.of_nat (cells_size cs)) with n' in SHZt; clear SHZ1 end.
      step. (* [comment removed for export] *)
      lazymatch goal with |- context [Some (Z_to_bv 64 (Z.shiftl ?u 1 + 1)%Z)] =>
        assert (Hs6 : bv_unsigned (Z_to_bv 64 (Z.shiftl u 1 + 1)%Z) <> 0%Z)
          by (rewrite Z.shiftl_mul_pow2 by lia; rewrite !unsigned_lit_wrap;
              pose proof (bv_unsigned_in_range 64 u10) as R10; unfold bv_modulus in R10;
              clear - R10; Z.div_mod_to_equations; lia0);
        remember (Z_to_bv 64 (Z.shiftl u 1 + 1)%Z) as s6w eqn:Hs6w; clear Hs6w end.
      gen_big.
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
                        | post_call ASEGS mc ] end.
      all: try lazymatch goal with
           | |- evt _ _ _ => idtac
           | |- u8arr _ _ _ _ => rewrite U40; exact OLD
           | |- Z.of_nat _ = _ => rewrite U496, LJ; reflexivity
           | |- rdbl _ _ _ _ => exact RBF
           | |- RTX _ _ => exact RTX0
           | |- _ => side
           end.
      all: clear_sf.
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
      pose proof (rw_cells_of_u8arr ASEGS _ _ _ (conj ZB2 ZW2)) as LENT. clear ZB2 ZW2. rewrite repeat_length in LENT.
      pose proof (rw_cells_of_u8arr ASEGS _ _ _ (conj ZB6 ZW6)) as PADT. clear ZB6 ZW6. rewrite repeat_length in PADT.
      pose proof (rw_cells_of_u8arr ASEGS _ _ _ (conj ZBL ZWL)) as LIML. clear ZBL ZWL. rewrite repeat_length in LIML.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => rename m' into m2 end.
      destruct (u64arr_of_rw_cells ASEGS _ _ 61 _ LIML) as (wsz & Lz & LIMBT). clear LIML.
      replace (Fr + 40)%Z with (Fr + 32 + 8)%Z in LIMBT by lia.
      match goal with H : rw_cells ASEGS m2 (Fr + 32) [C8 ?w] |- _ =>
        pose proof (u64arr_cons _ _ _ _ H LIMBT) as LIMT; clear H LIMBT end.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He0. { cond_cleanup He0. exfalso. clear - He0 Re. Z.div_mod_to_equations. lia0. }
      clear He0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (negw_val e ltac:(lia)) as UA1.
      assert (LT62 : length (s6w :: wsz) = 62%nat) by (cbn [length]; rewrite Lz; reflexivity).
      assert (NORMT : bnorm (s6w :: wsz) (Z.to_nat 1)).
      { right. cbn. unfold limbZ. cbn. exact Hs6. }
      assert (CAPT : (bval (s6w :: wsz) (Z.to_nat 1) * 5 ^ (- e) < BIG_CAP)%Z).
      { apply cap_neg; [|lia]. change (Z.to_nat 1) with 1%nat. cbn [bval]. unfold limbZ. cbn [nth].
        pose proof (bv_unsigned_in_range 64 s6w) as R7. unfold bv_modulus in R7. change (2 ^ (64 * Z.of_nat 0))%Z with 1%Z. clear - R7. lia0. }
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (FK5 : fk5_inv mc FS h5) by (split; [exact FSC | split; [exact HINT5 | split; [exact FL5 | split; [exact SK5 | exact SKS5]]]]) end.
      clear HINT5 FL5 SK5 SKS5.
      step. (* [comment removed for export] *)
      pose_sf.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_cut; [ eapply pow5_spec with (v := v) (ws := s6w :: wsz) (len := 1%Z) (h5 := h5)
                        | post_call ASEGS mc ] end.
      all: try lazymatch goal with
           | |- evt _ _ _ => idtac
           | |- u64arr _ _ _ _ => rewrite ULs8; exact LIMT
           | |- rw_cells _ _ _ [C2 _] => rewrite ULs8; replace (Fr + 32 + 496)%Z with (Fr + 528)%Z by lia; exact LENT
           | |- bnorm _ _ => exact NORMT
           | |- (_ + pow5_growth _ <= LM_T)%Z => try rewrite UA1; apply neg_cap; lia
           | |- (bv_unsigned _ < 2 ^ 31)%Z => rewrite UA1; lia
           | |- fk5_inv _ _ _ => exact FK5
           | |- rdbl _ _ (_ - 8) _ => rewrite ULs8; eapply rdbl_sub; [exact RBF | zlia | zlia]
           | |- rdbl _ _ _ _ => exact RBF
           | |- RTX _ _ => exact RTX0
           | |- _ => side
           end.
      all: clear_sf.
      rewrite ?ULs, ?ULs8 in *. rewrite -> ?UA1 in *.
      clear LT62 NORMT CAPT UA1 FK5. try clear LIMT. try clear LENT.
      (* [comment removed for export] *)
      match goal with H : fk5_inv ?mm FS ?h |- _ => destruct H as (FSC' & HINT5 & FL5 & SK5 & SKS5); clear FSC'; rename h into h5' end.
      match goal with H : u64arr ASEGS ?mm (Fr + 32) ?w |- _ => rename H into LIMT; rename w into wst end.
      match goal with H : rw_cells ASEGS ?mm (Fr + 32 + 496) _ |- _ => replace (Fr + 32 + 496)%Z with (Fr + 528)%Z in H by lia; rename H into LENT end.
      match type of LENT with rw_cells _ _ _ [C2 (Z_to_bv 64 ?l)] => rename l into lent end.
      match goal with H : length wst = 62%nat |- _ => rename H into LT62 end.
      match goal with H : (0 <= lent <= 62)%Z |- _ => rename H into HlenT end.
      match goal with H : RT ?mm v |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into RT5 end.
      (* [comment removed for export] *)
      assert (JA0 : forall (m4 : word -> option byte) (wsr wst' : list word) (lenr lent' : Z) (h5x : word) (ljx : list byte)
                           (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y25 y28 y29 y30 y31 : word),
        CMP_INV m4 wsr lenr wst' lent' h5x ljx hw ->
        evt ASEGS NDPOST
          (MS (mkR y1 SP1 gp (Z_to_bv 64 TPV) y5 y6 y7 sp SP1 y10 y11 y12 y13 y14 y15 y16 y17
                   (Z_to_bv 64 Fr) a2w SFw va y22 y23 S8 y25 (Z_to_bv 64 Fr) BB y28 y29 y30 y31)
              F (Z_to_bv 64 0x95fdc) fc None m4 (seg_rom ASEGS))).
      { intros. eapply (ndc_cmp_run set_shadow_f5_spec); try eassumption; try lia. }
      step. (* [comment removed for export] *)
      if_cases Hle.
      - clear Hle.
        step. (* [comment removed for export] *)
        if_cases Hlt.
        + clear Hlt. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          pose_sf.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
            eapply evt_cut; [ eapply shl_spec with (v := v) (ws := ws) (len := len) | post_call ASEGS mc ] end.
          all: try lazymatch goal with
               | |- evt _ _ _ => idtac
               | |- RT _ _ => exact RT5
               | |- rdbl _ _ _ _ => eapply rdbl_sub; [exact RBF | zlia | zlia]
               | |- _ => side
               end.
          all: clear_sf.
          rewrite ?ULs in *.
          step. (* [comment removed for export] *)
          eapply JA0. close_cmp.
        + clear Hlt. (* [comment removed for export] *)
          eapply JA0. close_cmp.
      - clear Hle. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose_sf.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          eapply evt_cut; [ eapply shl_spec with (v := v) (ws := wst) (len := lent) | post_call ASEGS mc ] end.
        all: try lazymatch goal with
             | |- evt _ _ _ => idtac
             | |- u64arr _ _ _ _ => rewrite ULs8; exact LIMT
             | |- rw_cells _ _ _ [C2 _] => rewrite ULs8; replace (Fr + 32 + 496)%Z with (Fr + 528)%Z by lia; exact LENT
             | |- RT _ _ => exact RT5
             | |- rdbl _ _ _ _ => rewrite ULs8; eapply rdbl_sub; [exact RBF | zlia | zlia]
             | |- _ => side
             end.
        all: clear_sf.
        rewrite ?ULs, ?ULs8 in *.
        match goal with H : rw_cells ASEGS ?mm (Fr + 32 + 496) _ |- _ => replace (Fr + 32 + 496)%Z with (Fr + 528)%Z in H by lia | _ => idtac end.
        step. (* [comment removed for export] *)
        eapply JA0. close_cmp.
 }
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    assert (J58 : forall v10 v11 v12 v13 v14 : word,
      evt ASEGS NDPOST
        (MS (mkR x1 SP1 gp (Z_to_bv 64 TPV) x5 x6 x7 sp SP1 v10 v11 v12 v13 v14 x15 x16 x17
                 (Z_to_bv 64 Fr) a2w SFw a1w va (Z_to_bv 64 e) x24 x25 (Z_to_bv 64 Fr) BB x28 x29 x30 x31)
            F (Z_to_bv 64 0x95e50) fc None m0 (seg_rom ASEGS)))
    end.
    { intros.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz.
      - clear Hz. gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J98.
      - clear Hz. gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J98. }
    if_cases Hd.
    - clear Hd. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
      assert (J40 : forall w11 w12 : word,
        evt ASEGS NDPOST
          (MS (mkR x1 SP1 gp (Z_to_bv 64 TPV) x5 x6 x7 sp SP1 rv w11 w12 (Z_to_bv 64 64) x14 x15 x16 x17
                   (Z_to_bv 64 Fr) a2w SFw a1w va (Z_to_bv 64 e) x24 x25 (Z_to_bv 64 Fr) BB x28 x29 x30 x31)
              F (Z_to_bv 64 0x95e38) fc None m0 (seg_rom ASEGS)))
      end.
      { intros. do 6 gstep. (* [comment removed for export] *) apply J58. }
      if_cases Hb; [clear Hb; apply J40 | clear Hb; step; (* [comment removed for export] *) apply J40].
    - clear Hd. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
      assert (J1c : forall w11 w12 w13 w14 : word,
        evt ASEGS NDPOST
          (MS (mkR x1 SP1 gp (Z_to_bv 64 TPV) x5 x6 x7 sp SP1 rv w11 w12 w13 w14 x15 x16 x17
                   (Z_to_bv 64 Fr) a2w SFw a1w va (Z_to_bv 64 e) x24 x25 (Z_to_bv 64 Fr) BB x28 x29 x30 x31)
              F (Z_to_bv 64 0x95e14) fc None m0 (seg_rom ASEGS)))
      end.
      { intros. gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J58. }
      if_cases Hb; [clear Hb; apply J1c | clear Hb; gstep; (* [comment removed for export] *) apply J1c].
  Qed.
  Optimize Heap.
End Mid.
