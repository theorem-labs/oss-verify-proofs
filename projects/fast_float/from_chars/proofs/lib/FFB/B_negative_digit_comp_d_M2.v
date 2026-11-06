(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt B_compare_stmt B_negative_digit_comp_d_stmt.

Module B_negative_digit_comp_d_T.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt B_negative_digit_comp_d_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt.B_fakestack OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt.
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
Lemma upd_upd_eq {X} : forall (l : list X) i x y, upd (upd l i x) i y = upd l i y.
Proof. induction l as [|a l IH]; intros [|i] x y; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma upd_comm {X} : forall (l : list X) i j x y, i <> j -> upd (upd l i x) j y = upd (upd l j y) i x.
Proof. induction l as [|a l IH]; intros [|i] [|j] x y Hij; cbn; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.
Lemma upd_zeros_zero : forall n i, upd (zeros n) i (Z_to_bv 8 0) = zeros n.
Proof. induction n as [|n IH]; intros [|i]; cbn; try reflexivity. unfold zeros in IH. rewrite IH. reflexivity. Qed.
Lemma flags_restore : forall n p0 p1, p1 <> p0 ->
  upd (upd (upd (zeros n) p0 (Z_to_bv 8 1)) p1 (Z_to_bv 8 1)) p1 (Z_to_bv 8 0) = upd (zeros n) p0 (Z_to_bv 8 1).
Proof.
  intros n p0 p1 H. rewrite upd_upd_eq. rewrite upd_comm by lia. rewrite upd_zeros_zero. reflexivity.
Qed.

Section Tail.
  Hypothesis set_shadow_f5_spec : set_shadow_f5_stmt.
  Variables (sp va gp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (S1 Fr pos0 pos1 : Z) (v : rt_vals) (mR : word -> option byte).
  (* [comment removed for export] *)
  Variables (ra0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : word).
  Notation A := (bv_unsigned va).
  Notation FS := (rt_FS v).
  Notation F0 := (FS + FK4_LO + pos0 * 1024)%Z.
  Notation SP1 := (Z_to_bv 64 S1).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation SFw := (Z_to_bv 64 (Fr / 8 + ASAN_B)).
  Notation SHZb := (Fr / 8 + 2147450884)%Z.    (* [comment removed for export] *)
  Notation SF0 := (Fr / 8 + 2147450880)%Z.     (* [comment removed for export] *)
  Notation FLADDR := (FS + 34816 + pos1)%Z.
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HS1 : (bv_unsigned sp - 176 <= S1 <= bv_unsigned sp - 160)%Z.
  Hypothesis HS1a : (S1 mod 16 = 0)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp - 2768)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis SPLO : (IMG_END <= bv_unsigned sp - 2768)%Z.
  Hypothesis SFS : (FS + FSSIZE <= bv_unsigned sp - 2768)%Z.
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
  Notation W_SHZ := [(SHZb, SHZb + 63)]%Z.
  Notation W_SSH := [(bv_unsigned SFw, bv_unsigned SFw + bv_unsigned (Z_to_bv 64 128))]%Z.
  Notation W_FLG := [(FLADDR, FLADDR + 1)]%Z.
  Ltac sfp := pose proof (unsigned_lit S1 ltac:(lia)) as U1; pose proof (unsigned_lit Fr ltac:(lia)) as U2;
              pose proof (unsigned_lit (Fr / 8 + ASAN_B) ltac:(lia)) as U3; pose proof (unsigned_lit 128 ltac:(lia)) as U4;
              clear - U1 U2 U3 U4 HS1 Rsp HFrE HFrF0 Hpos0 Hpos1 Hne1 KF1 KF2 KF8 KSP KSP2 HA1 HA2;
              cbv delta [negative_digit_comp_d_W]; unfold sub_fp; cbn [outside]; intros; first [lia0 | Z.div_mod_to_equations; lia0].
  #[using="S1 pos1 Rsp HS1 KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfT_shz_L : sub_fp W_SHZ WL. Proof. LiaFast.lf_pins (fun (S1 pos1 Rsp HS1 KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="S1 pos1 Rsp HS1 KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfT_ssh_L : sub_fp W_SSH WL. Proof. LiaFast.lf_pins (fun (S1 pos1 Rsp HS1 KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="S1 Fr Rsp HS1 KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1"] Lemma sfT_flg_L : sub_fp W_FLG WL. Proof. LiaFast.lf_pins (fun (S1 Fr Rsp HS1 KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HA1 HA2 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="sp S1 pos0 pos1 v Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE Kc1 Kt1 Kb1"] Lemma sfT_shz_K : sub_fp W_SHZ W_SHZ. Proof. LiaFast.lf_pins (fun (sp S1 pos0 pos1 v Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="sp S1 pos0 pos1 v Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE Kc1 Kt1 Kb1"] Lemma sfT_ssh_K : sub_fp W_SSH W_SSH. Proof. LiaFast.lf_pins (fun (sp S1 pos0 pos1 v Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  #[using="sp S1 Fr pos0 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE Kc1 Kt1 Kb1"] Lemma sfT_flg_K : sub_fp W_FLG W_FLG. Proof. LiaFast.lf_pins (fun (sp S1 Fr pos0 Rsp HS1 KSP KSP2 SFS KF1 Hpos0 Hpos1 Hne1 HFrE Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0). sfp. Qed.
  Ltac pose_sf := pose proof sfT_shz_L; pose proof sfT_ssh_L; pose proof sfT_flg_L; pose proof sfT_shz_K; pose proof sfT_ssh_K; pose proof sfT_flg_K.
  Ltac clear_sf := repeat match goal with S : sub_fp _ _ |- _ => clear S end.

  Notation RS m := (rw_cells BSEGS m (bv_unsigned sp + -104)
     [C8 q11; C8 q10; C8 q9; C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 ra0]).
  Notation POST := (negative_digit_comp_d_post ra0 sp gp (Z_to_bv 64 TPV) q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 F fc A v pos0 mR).

  #[using="set_shadow_f5_spec Rsp HS1 HS1a KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HFr8 HA1 HA2 RTH RD1 RD3 Kc1 Kt1 Kb1"] Lemma ndc_tail_run : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (m : word -> option byte) (wsr : list word) (lenr : Z) (mw : word) (lj : list byte) (hw h5 : word),
      u64arr BSEGS m A wsr -> length wsr = 62%nat ->
      rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 lenr)] -> (0 <= lenr <= 62)%Z ->
      rw_cells BSEGS m (S1 + 24) [C8 mw; CB 16 lj; C8 (Z_to_bv 64 Fr)] -> RS m ->
      stk BSEGS m (bv_unsigned sp - 2768) S1 -> stk BSEGS m S1 (S1 + 24) -> stk BSEGS m (S1 + 56) (bv_unsigned sp - 104) ->
      stk BSEGS m Fr (Fr + 1016) -> rw_cells BSEGS m (Fr + 1016) [C8 (Z_to_bv 64 FLADDR)] ->
      stk BSEGS m SF0 (SF0 + 128) ->
      rw_cells BSEGS m (FS + 32) [C8 hw] ->
      u8arr BSEGS m (FS + 34816) (upd (upd (zeros 1024) (Z.to_nat pos0) (Z_to_bv 8 1)) (Z.to_nat pos1) (Z_to_bv 8 1)) ->
      fs_cells_ok FS m ->
      stk BSEGS m (FS + FK4_LO) F0 -> stk BSEGS m (F0 + 1024) (FS + FK4_HI) ->
      stk BSEGS m (ASAN_B + FS / 8 + FK4_SLO) (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128) ->
      stk BSEGS m (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128 + 128) (ASAN_B + FS / 8 + FK4_SHI) ->
      fk5_inv m FS h5 ->
      pristine m IMG_LO ROD_HI -> pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
      munch WL mR m -> wmono BSEGS mR m ->
      evt BSEGS POST
        (MS (mkR x1 SP1 gp (Z_to_bv 64 TPV) x5 x6 x7 sp SP1 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 Fr) SFw x20 x21 x22 x23 x24 (Z_to_bv 64 Fr) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x96778) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (set_shadow_f5_spec Rsp HS1 HS1a KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HFr8 HA1 HA2 RTH RD1 RD3 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0).
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 m wsr lenr mw lj hw h5
           XA Lx LENC Hlenr LO SV ST ST0 ST2 STF FLC STS HINT FL FSC SK4a SK4b SKS4a SKS4b FK5 PR PRG PRT MU0 WM0.
    unfold fs_cells_ok in FSC. destruct FK5 as (_ & HINT5 & FL5 & SK5 & SKS5).
    cbv delta [negative_digit_comp_d_W] in MU0.
    pose proof (u64arr_bound _ _ _ _ XA) as BdX. rewrite Lx in BdX.
    pose proof (unsigned_lit S1 ltac:(lia)) as ULs. pose proof (unsigned_lit Fr ltac:(lia)) as ULf.
    pose proof (unsigned_lit (Fr / 8 + ASAN_B) ltac:(lia)) as ULsf.
    (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    destruct (stk_split BSEGS _ SF0 SHZb (SF0 + 128) STS ltac:(lia)) as [STa STbc].
    destruct (stk_split BSEGS _ SHZb (SHZb + 63) (SF0 + 128) STbc ltac:(lia)) as [STb STc]. clear STS STbc.
    destruct (stk_carve BSEGS _ SHZb (SHZb + 63) 63%nat STb ltac:(lia)) as [_ [zj SHC]]. clear STb.
    replace (SHZb + 63 - Z.of_nat 63)%Z with SHZb in SHC by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (munch_refl W_SHZ m1) as MUs; pose proof (wmono_refl BSEGS m1) as WMs end.
    stash_but SHC MUs WMs.
    do 63 step.
    pose_sf. unstash_chunks MUs WMs. clear MUs WMs. clear_sf.
    match goal with H : rw_cells BSEGS ?m1 SHZb ?cs |- _ =>
      pose proof (stk_of_rw_cells BSEGS m1 SHZb cs H) as STb; clear H;
      cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in STb end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (STS : stk BSEGS m1 SF0 (SF0 + 128))
        by (eapply stk_merge; [exact STa | eapply stk_merge; [exact STb | exact STc | lia] | lia]);
      clear STa STb STc;
      destruct (stk_carve BSEGS m1 SF0 (SF0 + 128) 128%nat STS ltac:(lia)) as [_ [shj SHALL]]; clear STS;
      replace (SF0 + 128 - Z.of_nat 128)%Z with SF0 in SHALL by lia end.
    lazymatch type of SHALL with rw_cells _ _ _ [CB 128 ?l] =>
      assert (LSH : length l = 128%nat) by exact (proj1 (proj1 (proj1 SHALL))) end.
    apply u8arr_of_rw_cells in SHALL.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      destruct (stk_carve BSEGS m1 Fr (Fr + 1016) 1016%nat STF ltac:(lia)) as [_ [fj FRJ]]; clear STF;
      replace (Fr + 1016 - Z.of_nat 1016)%Z with Fr in FRJ by lia end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose_sf. pose proof (unsigned_lit 128 ltac:(lia)) as U128.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      eapply evt_cut; [ eapply set_shadow_f5_spec with (old := shj) | post_call BSEGS m1 ] end.
    all: try lazymatch goal with
         | |- evt _ _ _ => idtac
         | |- u8arr _ _ _ _ => rewrite ULsf; exact SHALL
         | |- Z.of_nat _ = _ => rewrite LSH; ulit; reflexivity
         | |- pristine _ _ _ => assumption
         | |- _ => side
         end.
    all: clear_sf.
    rewrite ?ULs, ?ULf, ?ULsf in *.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit FLADDR ltac:(lia)) as ULfl.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (u8arr_store_ok BSEGS m1 _ _ pos1 (Z_to_bv 64 FLADDR) FL ltac:(rewrite !upd_length, zeros_length; lia) eq_refl) as SOK;
      pose proof (munch_refl W_FLG m1) as MUw; pose proof (wmono_refl BSEGS m1) as WMw end.
    stash_but SOK MUw WMw.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ _) _) =>
      pose proof (u8arr_write BSEGS m1 _ _ pos1 (Z_to_bv 8 0) FL ltac:(rewrite !upd_length, zeros_length; lia)) as FL2 end.
    change [Z_to_bv 8 0] with (le1 (Z_to_bv 64 0)) in FL2.
    store_done.
    clear FL. pose_sf. unstash_chunks MUw WMw. clear MUw WMw. clear_sf.
    rewrite (flags_restore 1024 (Z.to_nat pos0) (Z.to_nat pos1)) in FL2 by lia.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    do 13 step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    replace (Z_to_bv 64 (bv_unsigned sp + -160 + 160)) with sp
      by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    name_mem mf.
    apply evt_done. unfold negative_digit_comp_d_post.
    (* [comment removed for export] *)
    match goal with FR : rw_cells BSEGS mf Fr ?cs |- _ =>
      pose proof (stk_of_rw_cells BSEGS mf Fr cs FR) as STF; clear FR;
      cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in STF end.
    match goal with H : u8arr BSEGS mf _ (repeat (Z_to_bv 8 245) _) |- _ =>
      pose proof (stk_of_rw_cells BSEGS mf _ _ (rw_cells_of_u8arr _ _ _ _ H)) as STS; clear H;
      cbv [cells_size csize Nat.add] in STS; rewrite repeat_length in STS;
      cbv [Z.of_nat Pos.of_succ_nat Pos.succ Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in STS end.
    (* [comment removed for export] *)
    match goal with H : rw_cells BSEGS mf (S1 + 24) ?cs |- _ =>
      pose proof (stk_of_rw_cells BSEGS mf _ cs H) as STL; clear H;
      cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in STL end.
    match goal with H : rw_cells BSEGS mf (bv_unsigned sp + -104) ?cs |- _ =>
      pose proof (stk_of_rw_cells BSEGS mf _ cs H) as STV; clear H;
      cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in STV end.
    assert (STV' : stk BSEGS mf (bv_unsigned sp + -104) (bv_unsigned sp)) by (eapply stk_eq; [exact STV | lia | lia]).
    assert (STK : stk BSEGS mf (bv_unsigned sp - 2768) (bv_unsigned sp)).
    { eapply stk_join; [exact ST | eapply stk_join; [exact ST0 | eapply stk_join; [exact STL | eapply stk_join; [exact ST2 |
        exact STV' | lia | lia] | lia | lia] | lia | lia] | lia | lia]. }
    do 15 eexists. eexists mf, wsr, lenr, _, _.
    split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try eassumption; try lia.
    all: try lazymatch goal with
         | |- munch _ _ _ => cbv delta [negative_digit_comp_d_W]; assumption
         | |- RT _ _ => eapply RT_transport; [exact RTH | eassumption | solve_W_ok_rt]
         | |- fk4_nest _ _ _ _ => unfold fk4_nest, fs_cells_ok; repeat match goal with |- _ /\ _ => split end; try eassumption
         | |- fk5_inv _ _ _ => unfold fk5_inv, fs_cells_ok; repeat match goal with |- _ /\ _ => split end; try eassumption
         end.
  Qed.
End Tail.
End B_negative_digit_comp_d_T.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt.B_fakestack OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_compare_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_M2.B_negative_digit_comp_d_T.
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
Ltac ms_leaf_eq :=
  first [ reflexivity
        | word_eq_tac
        | symmetry; word_eq_tac
        | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia
        | lazymatch goal with
          | |- ?a = Z_to_bv 64 ?e =>
              transitivity (Z_to_bv 64 (bv_unsigned a)); [ symmetry; apply Z_to_bv_bv_unsigned | word_eq_tac ]
          | |- Z_to_bv 64 ?e = ?a =>
              transitivity (Z_to_bv 64 (bv_unsigned a)); [ word_eq_tac | apply Z_to_bv_bv_unsigned ]
          end ].
Ltac ms_eq_tac :=
  cbv beta delta [mkR];
  repeat first [ reflexivity | ms_leaf_eq | progress f_equal ].
Tactic Notation "goto" tactic3(tac) := (eapply evt_eq; [ | tac ]; [ ms_eq_tac | .. ]).

Section Cmp.
  Hypothesis compare_spec : compare_stmt.
  Hypothesis set_shadow_f5_spec : set_shadow_f5_stmt.
  Variables (sp va gp a2w : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (S1 Fr pos0 pos1 p2 : Z) (v : rt_vals) (mR : word -> option byte).
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
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HS1 : (bv_unsigned sp - 176 <= S1 <= bv_unsigned sp - 160)%Z.
  Hypothesis HS1a : (S1 mod 16 = 0)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp - 2768)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis SPLO : (IMG_END <= bv_unsigned sp - 2768)%Z.
  Hypothesis SFS : (FS + FSSIZE <= bv_unsigned sp - 2768)%Z.
  Hypotheses (KF1 : (app2r (FS) (FS + FSSIZE))%Z) (KF2 : (FS + FSSIZE <= KTOP)%Z) (KF8 : (FS mod 4096 = 0)%Z).
  Hypotheses (Hpos0 : (0 <= pos0 < 1024)%Z) (Hpos1 : (0 <= pos1 < 1024)%Z) (Hne1 : pos1 <> pos0).
  Hypotheses (HFrE : Fr = (FS + FK4_LO + pos1 * 1024)%Z) (HFrF0 : (Fr + 1024 <= F0 \/ F0 + 1024 <= Fr)%Z) (HFr8 : (Fr mod 1024 = 0)%Z).
  Hypotheses (HA1 : (F0 + 32 <= A)%Z) (HA2 : (A + 504 <= F0 + 1024)%Z) (A8 : (A mod 8 = 0)%Z).
  Hypotheses (Hp2 : (bv_unsigned a2w = p2 mod 2 ^ 32)%Z) (Rp2 : (- 2 ^ 14 <= p2 <= 2 ^ 14)%Z).
  Hypothesis RTH : RT mR v.
  Hypothesis RD1 : rt_disj v (bv_unsigned sp - 2768) (bv_unsigned sp).
  Hypothesis RD3 : rt_disj v FS (FS + FSSIZE).
  Hypotheses (Kc1 : rt_app (rt_ctx v) 160) (Kc2 : (rt_ctx v + 160 <= KTOP)%Z) (Kt1 : rt_app (rt_thr v) 80)
             (Kt2 : (rt_thr v + 80 <= KTOP)%Z) (Kb1 : rt_app (rt_blk v) 32) (Kb2 : (rt_blk v + 32 <= KTOP)%Z).

  Notation WL := (negative_digit_comp_d_W (bv_unsigned sp) A FS pos0).
  Notation RS m := (rw_cells BSEGS m (bv_unsigned sp + -104)
     [C8 q11; C8 q10; C8 q9; C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 ra0]).
  Notation POST := (negative_digit_comp_d_post ra0 sp gp (Z_to_bv 64 TPV) q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 F fc A v pos0 mR).
  Notation W_CMP := [(bv_unsigned SP1 - 16, bv_unsigned SP1)]%Z.
  #[using="Fr p2 Rsp HS1 KSP KSP2"] Lemma sfC_cmp_L : sub_fp W_CMP WL.
  Proof. LiaFast.lf_pins (fun (Fr p2 Rsp HS1 KSP KSP2 : LiaFast.U) => LiaFast.u0). pose proof (unsigned_lit S1 ltac:(lia)) as U1. clear - U1 HS1 Rsp KSP KSP2.
         cbv delta [negative_digit_comp_d_W]; unfold sub_fp; cbn [outside]; intros; lia0. Qed.

  (* [comment removed for export] *)
  Definition cmp_inv (m : word -> option byte) (wsr : list word) (lenr : Z) (wst : list word) (lent : Z)
             (lj : list byte) (hw h5 : word) : Prop :=
       u64arr BSEGS m A wsr /\ length wsr = 62%nat
    /\ rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 lenr)] /\ (0 <= lenr <= 62)%Z
    /\ u64arr BSEGS m (Fr + 32) wst /\ length wst = 62%nat
    /\ rw_cells BSEGS m (Fr + 528) [C2 (Z_to_bv 64 lent)] /\ (0 <= lent <= 62)%Z
    /\ rw_cells BSEGS m (S1 + 24) [C8 (Z_to_bv 64 Fr); CB 16 lj; C8 (Z_to_bv 64 Fr)] /\ RS m
    /\ stk BSEGS m (bv_unsigned sp - 2768) S1 /\ stk BSEGS m S1 (S1 + 24) /\ stk BSEGS m (S1 + 56) (bv_unsigned sp - 104)
    /\ stk BSEGS m Fr (Fr + 1016) /\ rw_cells BSEGS m (Fr + 1016) [C8 (Z_to_bv 64 FLADDR)]
    /\ stk BSEGS m SF0 (SF0 + 128)
    /\ rw_cells BSEGS m (FS + 32) [C8 hw]
    /\ u8arr BSEGS m (FS + 34816) (upd (upd (zeros 1024) (Z.to_nat pos0) (Z_to_bv 8 1)) (Z.to_nat pos1) (Z_to_bv 8 1))
    /\ fs_cells_ok FS m
    /\ stk BSEGS m (FS + FK4_LO) F0 /\ stk BSEGS m (F0 + 1024) (FS + FK4_HI)
    /\ stk BSEGS m (ASAN_B + FS / 8 + FK4_SLO) (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128)
    /\ stk BSEGS m (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128 + 128) (ASAN_B + FS / 8 + FK4_SHI)
    /\ fk5_inv m FS h5
    /\ pristine m IMG_LO ROD_HI /\ pristine m RELRO_LO RELRO_HI /\ pristine m REALTAB_LO REALTAB_HI
    /\ shz BSEGS m (ASAN_B + A / 8) 63 /\ shz BSEGS m SHZb 63
    /\ munch WL mR m /\ wmono BSEGS mR m.

  #[using="compare_spec set_shadow_f5_spec Rsp HS1 HS1a KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HFr8 HA1 HA2 A8 Hp2 Rp2 RTH RD1 RD3 Kc1 Kt1 Kb1"] Lemma ndc_cmp_run : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x27 x28 x29 x30 x31 : word)
      (m : word -> option byte) (wsr : list word) (lenr : Z) (wst : list word) (lent : Z) (lj : list byte) (hw h5 : word),
      cmp_inv m wsr lenr wst lent lj hw h5 ->
      evt BSEGS POST
        (MS (mkR x1 SP1 gp (Z_to_bv 64 TPV) x5 x6 x7 sp SP1 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 SFw a2w x21 x22 va S8 (Z_to_bv 64 Fr) (Z_to_bv 64 (- p2)) x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x966a0) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (compare_spec set_shadow_f5_spec Rsp HS1 HS1a KSP KSP2 SFS KF1 KF8 Hpos0 Hpos1 Hne1 HFrE HFrF0 HFr8 HA1 HA2 A8 Hp2 Rp2 RTH RD1 RD3 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0).
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x27 x28 x29 x30 x31 m wsr lenr wst lent lj hw h5 INV.
    destruct INV as (LIR & LR & LER & HLR & LIT & LT & LET & HLT & LO & SV & ST & ST0 & ST2 & STF & FLC & STS & HINT & FL & FSC
                     & SK4a & SK4b & SKS4a & SKS4b & FK5 & PR & PRG & PRT & SHX & SHZ & MU0 & WM0).
    pose proof (u64arr_bound _ _ _ _ LIR) as BR. rewrite LR in BR.
    pose proof (u64arr_bound _ _ _ _ LIT) as BT. rewrite LT in BT.
    pose proof (unsigned_lit S1 ltac:(lia)) as ULs. pose proof (unsigned_lit Fr ltac:(lia)) as ULf.
    pose proof (unsigned_lit (Fr + 32) ltac:(lia)) as ULs8. pose proof (unsigned_lit A ltac:(lia)) as ULa.
    cbv delta [negative_digit_comp_d_W] in MU0.
    destruct FK5 as (_ & HINT5 & FL5 & SK5 & SKS5). unfold fs_cells_ok in FSC.
    (* [comment removed for export] *)
    assert (BC : ro_cells BSEGS m BCELL [C8 BB]).
    { pose proof (RT_transport mR m v _ RTH MU0 ltac:(solve_W_ok_rt)) as RTm. open_RT_keep RTm.
      change [C8 (Z_to_bv 64 ASAN_B); C4 (Z_to_bv 64 1)] with ([C8 (Z_to_bv 64 ASAN_B)] ++ [C4 (Z_to_bv 64 1)]) in RT1.
      apply (proj1 (proj1 (ro_cells_app BSEGS m 943736 _ _) RT1)). }
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof sfC_cmp_L as SFC.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply compare_spec with (xs := wsr) (xlen := lenr) (ys := wst) (ylen := lent) | post_call BSEGS mc ] end.
    all: try lazymatch goal with
         | |- evt _ _ _ => idtac
         | |- u64arr _ _ (bv_unsigned va) _ => exact LIR
         | |- u64arr _ _ _ _ => ulit; exact LIT
         | |- rw_cells _ _ (bv_unsigned va + 496)%Z _ => exact LER
         | |- rw_cells _ _ _ [C2 _] => ulit; replace (Fr + 32 + 496)%Z with (Fr + 528)%Z by lia; exact LET
         | |- pristine _ _ _ => exact PRG
         | |- ro_cells _ _ _ _ => exact BC
         | |- shz _ _ (ASAN_B + bv_unsigned S8 / 8)%Z _ => ulit; replace (ASAN_B + (Fr + 32) / 8)%Z with SHZb by (clear - HFr8 HFrE KF1 KF8 Hpos1; Z.div_mod_to_equations; lia0); exact SHZ
         | |- shz _ _ _ _ => ulit; exact SHX
         | |- stk _ _ _ _ => ulit; eapply stk_subC; [exact ST | lia | lia | lia]
         | |- _ => ulit; first [eassumption | reflexivity | lia]
         end.
    all: clear SFC.
    all: match goal with |- evt _ _ _ => idtac | |- ?g => idtac "REMAIN-CMP" g end.
    rewrite ?ULs, ?ULa, ?ULs8 in *.
    match goal with H : stk BSEGS _ (S1 - 16)%Z S1 |- _ => clear H | _ => idtac end.
    name_mem m5.
    (* [comment removed for export] *)
    assert (TAILK : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y24 y26 y27 y28 y29 y30 y31 : word),
      evt BSEGS POST
        (MS (mkR y1 SP1 gp (Z_to_bv 64 TPV) y5 y6 y7 sp SP1 y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 Fr) SFw y20 y21 y22 y23 y24 (Z_to_bv 64 Fr) y26 y27 y28 y29 y30 y31)
            F (Z_to_bv 64 0x96778) fc None m5 (seg_rom BSEGS))).
    { intros. eapply (ndc_tail_run set_shadow_f5_spec) with (pos1 := pos1); try eassumption; try lia.
      all: try lazymatch goal with
           | |- munch _ _ _ => cbv delta [negative_digit_comp_d_W] in *; eassumption
           | |- fs_cells_ok _ _ => exact FSC
           | |- fk5_inv _ _ _ => split; [exact FSC | split; [exact HINT5 | split; [exact FL5 | split; [exact SK5 | exact SKS5]]]]
           end.
      all: match goal with |- ?g => idtac "REMAIN-TAILK" g end. }
    clear LIR LIT LER LET SHX SHZ BC.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (J64 : forall u1 u5 u6 u7 u28 u29 u30 u31 : word, forall u10 u11 u12 u13 u14 u15 u16 u17 u21 u22 : word,
      evt BSEGS POST
        (MS (mkR u1 SP1 gp (Z_to_bv 64 TPV) u5 u6 u7 sp SP1 u10 u11 u12 u13 u14 u15 u16 u17
                 (Z_to_bv 64 Fr) SFw a2w u21 u22 va S8 (Z_to_bv 64 Fr) (Z_to_bv 64 (- p2)) x27 u28 u29 u30 u31)
            F (Z_to_bv 64 0x96754) fc None m5 (seg_rom BSEGS))).
    { intros. gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) apply TAILK. }
    (* [comment removed for export] *)
    assert (J54 : forall u1 u5 u6 u7 u28 u29 u30 u31 : word, forall u10 u11 u12 u13 u14 u15 u16 u17 u21 u22 : word,
      evt BSEGS POST
        (MS (mkR u1 SP1 gp (Z_to_bv 64 TPV) u5 u6 u7 sp SP1 u10 u11 u12 u13 u14 u15 u16 u17
                 (Z_to_bv 64 Fr) SFw a2w u21 u22 va S8 (Z_to_bv 64 Fr) (Z_to_bv 64 (- p2)) x27 u28 u29 u30 u31)
            F (Z_to_bv 64 0x96744) fc None m5 (seg_rom BSEGS))).
    { intros. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq; [ clear Hq; apply J64 | clear Hq; step; (* [comment removed for export] *) apply J64 ]. }
    (* [comment removed for export] *)
    assert (J28 : forall u1 u5 u6 u7 u28 u29 u30 u31 : word, forall u10 u11 u13 u14 u15 u16 u17 u18 u21 u22 : word,
      evt BSEGS POST
        (MS (mkR u1 SP1 gp (Z_to_bv 64 TPV) u5 u6 u7 sp SP1 u10 u11 (Z_to_bv 64 (p2 + 11)) u13 u14 u15 u16 u17
                 u18 SFw a2w u21 u22 va S8 (Z_to_bv 64 Fr) (Z_to_bv 64 (- p2)) x27 u28 u29 u30 u31)
            F (Z_to_bv 64 0x96718) fc None m5 (seg_rom BSEGS))).
    { intros.
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq.
      - clear Hq.
        step. (* [comment removed for export] *) rewrite uw_add, (swrap32_id (p2 + 11 + 1)) by lia.
        step. (* [comment removed for export] *) trap_dead.
        step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J54.
      - clear Hq. gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J54. }
    (* [comment removed for export] *)
    assert (J78 : forall u1 u5 u6 u7 u28 u29 u30 u31 : word, forall u10 u11 u12 u13 u14 u15 u16 u17 u18 u21 u22 : word,
      evt BSEGS POST
        (MS (mkR u1 SP1 gp (Z_to_bv 64 TPV) u5 u6 u7 sp SP1 u10 u11 u12 u13 u14 u15 u16 u17
                 u18 SFw a2w u21 u22 va S8 (Z_to_bv 64 Fr) (Z_to_bv 64 (- p2)) x27 u28 u29 u30 u31)
            F (Z_to_bv 64 0x96768) fc None m5 (seg_rom BSEGS))).
    { intros. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) apply TAILK. }
    (* [comment removed for export] *)
    assert (JF4 : forall (sh : Z) (u1 u5 u6 u7 u28 u29 u30 u31 u10 u13 u14 u15 u16 u17 u18 u21 u22 : word), (0 <= sh <= 2 ^ 14)%Z ->
      evt BSEGS POST
        (MS (mkR u1 SP1 gp (Z_to_bv 64 TPV) u5 u6 u7 sp SP1 u10 (Z_to_bv 64 p2) (Z_to_bv 64 sh) u13 u14 u15 u16 u17
                 u18 SFw a2w u21 u22 va S8 (Z_to_bv 64 Fr) (Z_to_bv 64 (- p2)) x27 u28 u29 u30 u31)
            F (Z_to_bv 64 0x966e4) fc None m5 (seg_rom BSEGS))).
    { intros sh. intros until u22. intros Hsh.
      zstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *) rewrite ?word_add_lit2.
      step. (* [comment removed for export] *) rewrite ?uw_add2, (swrap32_id (p2 + (sh + 1))) by lia.
      step. (* [comment removed for export] *) if_not_taken.
      gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq.
      - clear Hq. gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) apply J78.
      - clear Hq. step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J78. }
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hden.
    - cond_cleanup Hden. rewrite ?signed_lit in Hden by lia.
      (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) rewrite Hp2, uw_mod32, Z.add_0_r, (swrap32_id p2) by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq.
      + cond_cleanup Hq. rewrite ?unsigned_lit in Hq by lia. apply (JF4 (- p2)%Z); lia.
      + cond_cleanup Hq. step. (* [comment removed for export] *) apply (JF4 63%Z); lia.
    - cond_cleanup Hden. rewrite ?signed_lit in Hden by lia.
      (* [comment removed for export] *)
      step. (* [comment removed for export] *) rewrite Hp2, uw_mod32, Z.add_0_r, (swrap32_id p2) by lia.
      step. (* [comment removed for export] *) rewrite Hp2, uw_mod32, (swrap32_id (p2 + 11)) by lia.
      step. (* [comment removed for export] *) trap_dead.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq.
      + clear Hq. gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) apply J28.
      + clear Hq. step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J28.
  Qed.
End Cmp.
(* [comment removed for export] *)
