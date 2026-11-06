(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ms_eq_tac ::=
  cbv beta delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with |- @eq (bv _) _ _ => ms_leaf_eq end
               | progress f_equal ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lia_t1 := zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac lia_t2 := zify_prune; Zify.zify; xlia zchecker.
Ltac lia_t12 := first [ lia_t1 | lia_t2 ].
Ltac lia_t3 := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Ltac lia_split_disj_conj :=
  repeat match goal with
  | H : ?A /\ ?B |- _ =>
      lazymatch type of H with context [_ \/ _] => destruct H | _ => fail end
  end.
(* [comment removed for export] *)
Ltac lia_d1 :=
  lia_split_disj_conj;
  match goal with
  | H : _ \/ _ |- _ => solve [ destruct H; lia_t12 ]
  end.
(* [comment removed for export] *)
Ltac lia4 := first [ LiaCap.lia_cap_s ltac:(lia_t1) ltac:(fail) | lia_t2 | lia_d1 | lia_t3 ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint covered (lo hi : Z) (W' : list ivl) : Prop :=
  match W' with
  | [] => (hi <= lo)%Z
  | (lo', hi') :: r => ((lo' <= lo)%Z /\ (hi <= hi')%Z) \/ covered lo hi r
  end.

Lemma covered_outside : forall W' lo hi x,
  covered lo hi W' -> outside W' x -> ~ (lo <= x < hi)%Z.
Proof.
  induction W' as [|[lo' hi'] r IH]; cbn; intros lo hi x HC HO.
  - lia.
  - destruct HO as [Hn HO']. destruct HC as [[H1 H2]|HC'].
    + lia.
    + exact (IH lo hi x HC' HO').
Qed.

Lemma sub_fp_nil_l : forall W', sub_fp [] W'.
Proof. intros W' x _. exact I. Qed.

Lemma sub_fp_cons_l : forall lo hi W W',
  covered lo hi W' -> sub_fp W W' -> sub_fp ((lo, hi) :: W) W'.
Proof.
  intros lo hi W W' HC HS x HO. cbn. split.
  - exact (covered_outside W' lo hi x HC HO).
  - exact (HS x HO).
Qed.

Ltac covered_tac :=
  cbn [covered];
  repeat first [ left; split; lia_t12 | right ];
  (* [comment removed for export] *)
  lia_t12.
Ltac sub_fp_fast := repeat (apply sub_fp_cons_l; [ solve [covered_tac] | ]); apply sub_fp_nil_l.
(* [comment removed for export] *)
Ltac sub_fp_tac :=
  first [ solve [ sub_fp_fast ]
        | unfold sub_fp; cbn [outside]; intros; slia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac slia ::=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; slia
  | _ => tryif kp_ovs then fail else lia4      (* [comment removed for export] *)
  end.

Ltac transport_after_call_orig_P segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : shz segs m ?A2 ?n2 |- _ =>
      first [ apply (shz_transport segs W m m' A2 n2) in H; [ | exact MU | cbn [disjoint_from]; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ => apply (stk_mono segs m m' loq hiq) in H; [ | exact WM ]
  | H : rdbl segs m ?A2 ?n2 |- _ => apply (rdbl_mono segs m m' A2 n2) in H; [ | exact WM ]
  | H : pristine m ?lo ?hi |- _ =>
      first [ apply (pristine_transport W m m' lo hi) in H; [ | exact MU | cbn [disjoint_from]; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ sub_fp_tac | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac transport_after_call_cc_P segs m m' MU WM CC X B :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ tr_lits H (bytes_at_transport_lit segs m m' X B A2 bs2 CC) B A2 constr:(Z.of_nat (@length byte bs2))
            | tr_sb H (bytes_at_transport_sb segs m m' X B) (bytes_at_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte bs2)) CC
            | apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lits H (rw_cells_transport_lit segs m m' X B A2 cs2 CC) B A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (rw_cells_transport_sb segs m m' X B) (rw_cells_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (cells_size cs2)) CC
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lits H (ro_cells_transport_lit segs m m' X B A2 cs2 CC) B A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (ro_cells_transport_sb segs m m' X B) (ro_cells_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (cells_size cs2)) CC
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u8arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8arr_transport_sb segs m m' X B) (u8arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte xs)) CC
            | apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u32arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u32arr_transport_sb segs m m' X B) (u32arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:((4 * Z.of_nat (@length word xs))%Z) CC
            | apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u64arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u64arr_transport_sb segs m m' X B) (u64arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:((8 * Z.of_nat (@length word xs))%Z) CC
            | apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u8ro_transport_lit segs m m' X B A2 xs CC) B A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8ro_transport_sb segs m m' X B) (u8ro_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte xs)) CC
            | apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : shz segs m ?A2 ?n2 |- _ =>
      first [ tr_lits H (shz_transport_lit segs m m' X B A2 n2 CC) B A2 n2
            | tr_sb H (shz_transport_sb segs m m' X B) (shz_transport_sb0 segs m m' X B) chks_sb B X A2 n2 CC
            | apply (shz_transport segs W m m' A2 n2) in H; [ | exact MU | cbn [disjoint_from]; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ => apply (stk_mono segs m m' loq hiq) in H; [ | exact WM ]
  | H : rdbl segs m ?A2 ?n2 |- _ => apply (rdbl_mono segs m m' A2 n2) in H; [ | exact WM ]
  | H : pristine m ?lo ?hi |- _ =>
      first [ tr_lits_pr H (pristine_transport_lit segs m m' X B lo hi CC) B lo hi
            | apply (pristine_transport W m m' lo hi) in H; [ | exact MU | cbn [disjoint_from]; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ sub_fp_tac | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
Ltac transport_after_call segs m m' MU WM ::=
  call_ctx_pose segs m m' MU WM ltac:(lia)
    ltac:(fun CC X B => transport_after_call_cc_P segs m m' MU WM CC X B)
    ltac:(transport_after_call_orig_P segs m m' MU WM).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac is_chunk_fact T :=
  lazymatch T with
  | bytes_at _ _ _ _ => idtac | rw_cells _ _ _ _ => idtac | ro_cells _ _ _ _ => idtac
  | u8arr _ _ _ _ => idtac | u32arr _ _ _ _ => idtac | u64arr _ _ _ _ => idtac | u8ro _ _ _ _ => idtac
  | shz _ _ _ _ => idtac | rdbl _ _ _ _ => idtac | pristine _ _ _ => idtac | stk _ _ _ _ => idtac
  end.
(* [comment removed for export] *)
Ltac stash_all_but m K :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | stashed _ => fail
      | _ => is_chunk_fact T;
             lazymatch T with context [m] => idtac end;
             lazymatch H with K => fail | _ => stash H end
      end
  end.
Ltac stash_all_but2 m K1 K2 :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | stashed _ => fail
      | _ => is_chunk_fact T;
             lazymatch T with context [m] => idtac end;
             lazymatch H with K1 => fail | K2 => fail | _ => stash H end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.AmoStep.
Ltac amo_vals_in H :=
  rewrite ?amo_swapN in H; rewrite ?amo_swapN;
  rewrite ?amo_add32, ?amo_add64, ?amo_or32 in H; rewrite ?amo_add32, ?amo_add64, ?amo_or32;
  rewrite ?amo_add64w, ?amo_or64w in H; rewrite ?amo_add64w, ?amo_or64w;
  rewrite ?amo_old32, ?amo_old64, ?low32_unsigned, ?le_bytes_to_word_le8 in H;
  rewrite ?amo_old32, ?amo_old64, ?low32_unsigned, ?le_bytes_to_word_le8;
  repeat (rewrite unsigned_lit32 in H by lia); repeat (rewrite unsigned_lit32 by lia);
  repeat (rewrite unsigned_lit in H by lia); repeat (rewrite unsigned_lit by lia).
(* [comment removed for export] *)
Ltac amo_vals_h H := amo_vals_in H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac stash_frame_facts m MUs WMs :=
  repeat match goal with
  | H : munch _ _ m |- _ => lazymatch H with MUs => fail | _ => stash H end
  | H : wmono _ _ m |- _ => lazymatch H with WMs => fail | _ => stash H end
  | H : stk _ m _ _ |- _ => stash H
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac word_eq_fast :=
  first [ exact eq_refl
        | f_equal; lia_t12
        | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia_t12 ].
Ltac addr_eq_fast :=
  first [ symmetry; apply wa_of_Z_to_bv; lia_t12
        | symmetry; apply wa_of_var; lia_t12
        | apply wa_of_Z_to_bv; lia_t12
        | apply wa_of_var; lia_t12
        | unfold wa; f_equal; lia_t12
        | symmetry; unfold wa; f_equal; lia_t12 ].
(* [comment removed for export] *)
Ltac addr_diff_opt E A :=
  match E with
  | _ => let k := addr_diff E A in constr:(Some k)
  | _ => constr:(@None Z)
  end.
Ltac solve_load_cells :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let kok := eval vm_compute in (Z.leb 0 k) in
        lazymatch kok with true => idtac end;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_fast])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let kok := eval vm_compute in (Z.leb 0 k) in
        lazymatch kok with true => idtac end;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_fast])
        end
    end
  end;
  load_post.
(* [comment removed for export] *)
Ltac solve_load_hr_with eqtac :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | let E' := addr_expr a' in
                let d := addr_diff_opt E E' in
                lazymatch d with
                | Some ?k => lazymatch k with 0%Z => idtac end
                | None => idtac
                end;
                replace (ov_read_bytes segs m a n) with (Some bs) by (rewrite <- HR; f_equal; eqtac) ]
    end
  end;
  load_post.
Ltac solve_load_hr_fast := solve_load_hr_with ltac:(first [word_eq_fast | addr_eq_fast]).
(* [comment removed for export] *)
Ltac solve_load_hr_full := solve_load_hr_with ltac:(first [word_eq_tac | addr_eq_tac]).
Ltac solve_load_base ::= first [ solve_load_cells | solve_load_hr_fast | solve_load_hr_full ].
(* [comment removed for export] *)
Ltac solve_load ::=
  first [ solve_load_cells; fold_byte_lits; fold_ext_lit
        | solve_load_image; fold_ext_lit
        | solve_load_hr_fast; fold_byte_lits; fold_ext_lit
        | solve_load_shadow
        | solve_load_hr_full; fold_byte_lits; fold_ext_lit ].
