(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Zify.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module CJ_shfast.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.micromega.Zify.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Ltac sh_only_shv tac :=
  match goal with
  | Chi : ?v <= 7, Clo : _ <= ?v |- _ => is_var v; clear - Clo Chi; tac
  end.

(* [comment removed for export] *)
Ltac sh_sc :=
  first [ (let MK := fresh "shMK" in pose proof I as MK; clear - MK; Zify.zify; xlia zchecker)
        | sh_only_shv ltac:(Zify.zify; xlia zchecker)
        | Z.div_mod_to_equations; lia ].

Ltac sh_cond_prep_fast :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  fold_lit_ux;
  rewrite ?land7_mod by lia;
  rewrite ?signed_lit_small by sh_sc;
  rewrite ?unsigned_lit by sh_sc;
  rewrite ?Z_to_bv_unsigned; unfold bv_wrap;
  change (bv_modulus 64) with 18446744073709551616%Z.

(* [comment removed for export] *)
Ltac sh_close1 := first [ Zify.zify; xlia zchecker | Z.div_mod_to_equations; Zify.zify; xlia zchecker ].
Ltac sh_solve_cond_rec1 :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); sh_solve_cond_rec1
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); sh_solve_cond_rec1
  | |- (?a <? ?b) = true => first [reflexivity | apply Z.ltb_lt; sh_close1]
  | |- (?a <? ?b) = false => first [reflexivity | apply Z.ltb_ge; sh_close1]
  | |- (?a <=? ?b) = true => first [reflexivity | apply Z.leb_le; sh_close1]
  | |- (?a <=? ?b) = false => first [reflexivity | apply Z.leb_gt; sh_close1]
  | |- (?a =? ?b) = true => first [reflexivity | apply Z.eqb_eq; sh_close1]
  | |- (?a =? ?b) = false => first [reflexivity | apply Z.eqb_neq; sh_close1]
  end.

Ltac sh_cheap := first [ reflexivity | sh_only_shv ltac:(sh_solve_cond_rec1) ].

Ltac sh_fast_false :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; sh_cond_prep_fast; sh_cheap]
  end.
Ltac sh_fast_true :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; sh_cond_prep_fast; sh_cheap]
  end.

(* [comment removed for export] *)
Ltac sh_resolve_if_fast :=
  first [ lazymatch goal with
          | Chi : ?v <= 7, Clo : _ <= ?v |- _ => first [ sh_fast_true | sh_fast_false ]
          | _ => first [ sh_fast_false | sh_fast_true ]
          end
        | sh_if_false | sh_if_true
        | fail 1 "asan check: cannot decide the branch (shadow fact too weak / address mismatch?)" ].

(* [comment removed for export] *)
Ltac sh_join_fast v Cv rdk :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?T1 else Z_to_bv 64 ?T2) ?fc ?rv ?m ?ro) =>
    let okslow := lazymatch c with
                  | negb (bv_eqb _ _) => constr:((T2, T1))
                  | bv_eqb _ _ => constr:((T1, T2))
                  end in
    lazymatch okslow with
    | (?OK, ?SLOW) =>
      let i := instr_at segs SLOW in
      let i := lazymatch i with
               | Jal _ ?off => let tgt := eval vm_compute in (bv_unsigned (Z_to_bv 64 SLOW + sext 64 off : word)) in
                               instr_at segs tgt
               | _ => i end in
      let ruk := lazymatch i with
                 | OpImm ALU_AND ?ru _ _ => eval vm_compute in (bv_key ru)
                 | _ => rdk
                 end in
      apply (evt_cut segs (chk_post R F (Z_to_bv 64 OK) fc rv m ro rdk ruk) Q);
      [ lazymatch type of Cv with
        | _ \/ _ =>
          let Clo := fresh "Clo" in let Chi := fresh "Chi" in
          destruct Cv as [-> | [Clo Chi]];
          [ sh_run_until segs OK; sh_finish rdk ruk
          | first [ exfalso; clear - Clo Chi; Zify.zify; xlia zchecker
                  | rewrite ?(sxb_zb_small v), ?(zxb_zb_w v) by (first [ clear - Clo Chi; Zify.zify; xlia zchecker | lia ]);
                    sh_run_until segs OK; sh_finish rdk ruk ] ]
        | v = 0 => subst v; sh_run_until segs OK; sh_finish rdk ruk
        end
      | let ms1 := fresh "ms" in let sv := fresh "sv" in let u := fresh "u" in
        intros ms1 nelH_; (nelim nelH_ 3%nat; intros sv u ->); cbv beta iota delta [tset]; regs_fold_fix (* [comment removed for export] *); try clear Cv; try clear v ]
    end
  end.

(* [comment removed for export] *)
Ltac sh_tv_close := first [ lia | Z.div_mod_to_equations; lia ].
Ltac sh_transport_via_fast MU H :=
  lazymatch type of H with
  | shb _ _ _ => apply (fun HH => shb_munch_disjoint _ _ _ _ _ HH MU) in H;
                 [| unfold SH, SHADOW_OFFSET; sh_tv_close | cbn [disjoint_from]; unfold SH, SHADOW_OFFSET; sh_tv_close ]
  | shchk _ _ _ => apply (fun HH => shchk_munch_disjoint _ _ _ _ _ HH MU) in H;
                 [| unfold SH, SHADOW_OFFSET; sh_tv_close | cbn [disjoint_from]; unfold SH, SHADOW_OFFSET; sh_tv_close ]
  | sh_zero _ _ _ => apply (fun HH => sh_zero_munch _ _ _ _ _ HH MU) in H;
                 [| unfold SH, SHADOW_OFFSET; sh_tv_close
                  | unfold SH, SHADOW_OFFSET; sh_tv_close
                  | cbn [disjoint_from]; unfold SH, SHADOW_OFFSET; sh_tv_close ]
  | shadow_ok _ _ _ => apply (fun HH => shadow_ok_munch _ _ _ _ _ HH MU) in H;
                 [| lia
                  | unfold SH, SHADOW_OFFSET; sh_tv_close
                  | unfold SH, SHADOW_OFFSET; sh_tv_close
                  | cbn [disjoint_from]; unfold SH, SHADOW_OFFSET; sh_tv_close ]
  end.
End CJ_shfast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_bandM BImg RT_defs CJ_iface AShadow CJ_tree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegFold.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegFold.simp_regs_raw.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StepFast.SF.sf_mode := 0.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition esc_extra (c : Z) : Z :=
  if (c =? 34) || (c =? 92) || (c =? 8) || (c =? 12) || (c =? 10) || (c =? 13) || (c =? 9) then 1
  else if c <? 32 then 5 else 0.

Fixpoint esc_count (s : list byte) : Z :=
  match s with [] => 0 | b :: s' => esc_extra (bv_unsigned b) + esc_count s' end.

Lemma esc_extra_range : forall c, 0 <= esc_extra c <= 5.
Proof. intros c. unfold esc_extra. destruct (_ || _); [lia|]. destruct (c <? 32); lia. Qed.

Lemma esc_count_app : forall a b, esc_count (a ++ b) = esc_count a + esc_count b.
Proof. induction a as [|x a IH]; intros b; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma esc_count_range : forall s, 0 <= esc_count s <= 5 * Z.of_nat (length s).
Proof. induction s as [|b s IH]; cbn; [lia|]. pose proof (esc_extra_range (bv_unsigned b)). lia. Qed.

Lemma esc_count_firstn_le : forall s i, esc_count (firstn i s) <= esc_count s.
Proof.
  intros s i. rewrite <- (firstn_skipn i s) at 2. rewrite esc_count_app. pose proof (esc_count_range (skipn i s)). lia.
Qed.

Lemma firstn_S_snoc : forall {A} (pre post : list A) (b : A), firstn (S (length pre)) (pre ++ b :: post) = pre ++ [b].
Proof. intros A pre post b. induction pre as [|x pre IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma firstn_len_app : forall {A} (pre post : list A), firstn (length pre) (pre ++ post) = pre.
Proof. intros A pre post. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma esc_count_firstn_S : forall s i b, nth_error s i = Some b ->
  esc_count (firstn (S i) s) = esc_count (firstn i s) + esc_extra (bv_unsigned b).
Proof.
  intros s i b H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen). subst i.
  rewrite firstn_S_snoc, firstn_len_app, esc_count_app. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition RMASK : Z := 0x400003700.
Definition resc1b (c : Z) : bool := (c =? 8) || (c =? 9) || (c =? 10) || (c =? 12) || (c =? 13) || (c =? 34).

Lemma rmask_bit : forall c, 0 <= c <= 34 ->
  Z.land (Z.shiftr RMASK (Z.land c 63)) 1 = if resc1b c then 1 else 0.
Proof.
  intros c Hc.
  assert (G : forall n : nat, (n <= 34)%nat -> Z.land (Z.shiftr RMASK (Z.land (Z.of_nat n) 63)) 1 = if resc1b (Z.of_nat n) then 1 else 0).
  { intros n Hn. do 35 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. }
  specialize (G (Z.to_nat c) ltac:(lia)). rewrite Z2Nat.id in G by lia. exact G.
Qed.

Lemma rmask_bit' : forall c, 0 <= c <= 34 ->
  Z.land (Z.shiftr RMASK c) 1 = if resc1b c then 1 else 0.
Proof.
  intros c Hc.
  assert (G : forall n : nat, (n <= 34)%nat -> Z.land (Z.shiftr RMASK (Z.of_nat n)) 1 = if resc1b (Z.of_nat n) then 1 else 0).
  { intros n Hn. do 35 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. }
  specialize (G (Z.to_nat c) ltac:(lia)). rewrite Z2Nat.id in G by lia. exact G.
Qed.

Lemma resc1b_extra : forall c, 0 < c <= 34 -> esc_extra c = if resc1b c then 1 else if c <? 32 then 5 else 0.
Proof.
  intros c Hc. unfold esc_extra, resc1b.
  destruct (Z.eqb_spec c 34), (Z.eqb_spec c 92), (Z.eqb_spec c 8), (Z.eqb_spec c 12), (Z.eqb_spec c 10), (Z.eqb_spec c 13), (Z.eqb_spec c 9); cbn [orb]; try reflexivity; try lia.
Qed.

Lemma esc_extra_gt34 : forall c, 34 < c -> esc_extra c = if c =? 92 then 1 else 0.
Proof.
  intros c Hc. unfold esc_extra.
  destruct (Z.eqb_spec c 34), (Z.eqb_spec c 92), (Z.eqb_spec c 8), (Z.eqb_spec c 12), (Z.eqb_spec c 10), (Z.eqb_spec c 13), (Z.eqb_spec c 9); cbn [orb]; try reflexivity; try lia.
  destruct (Z.ltb_spec c 32); [lia| reflexivity].
Qed.

Lemma unsigned_lit8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact Hc. Qed.

Lemma neg_flag5 : forall b, Z.land (bv_swrap 32 (0 - Z.b2z b) mod 18446744073709551616) 5 = if b then 5 else 0.
Proof. intros [|]; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Str.
  Variables (S : Z) (str tail : list byte).
  Hypothesis NONUL : ~ In (wb 0) str.

  Notation full := (str ++ wb 0 :: tail).
  Notation L := (Z.of_nat (length str)).
  Notation E := (esc_count str).

  Lemma full_nth_lt : forall i, 0 <= i < L ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ nth_error str (Z.to_nat i) = Some b /\ 0 < bv_unsigned b < 256.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:EQ.
    - exists b. split. { rewrite nth_error_app1 by lia. exact EQ. } split; [reflexivity|].
      pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
      enough (bv_unsigned b <> 0) by lia.
      intros Hb. apply NONUL. replace (wb 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in EQ. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat L) = Some (wb 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition chb (i : Z) : byte := nth (Z.to_nat i) full (wb 0).
  Notation ch i := (bv_unsigned (chb i)).

  Lemma chb_nth : forall i, 0 <= i <= L -> nth_error full (Z.to_nat i) = Some (chb i).
  Proof.
    intros i Hi. unfold chb. destruct (nth_error full (Z.to_nat i)) as [b|] eqn:EQ.
    - f_equal. symmetry. apply nth_error_nth. exact EQ.
    - apply nth_error_None in EQ. rewrite length_app in EQ. cbn [length] in EQ. lia.
  Qed.

  Lemma ch_L : ch L = 0.
  Proof. pose proof (chb_nth L ltac:(lia)) as H. rewrite full_nth_len in H. injection H as <-. reflexivity. Qed.

  Lemma ch_lt : forall i, 0 <= i < L -> nth_error str (Z.to_nat i) = Some (chb i) /\ 0 < ch i < 256.
  Proof.
    intros i Hi. destruct (full_nth_lt i Hi) as (b & H1 & H2 & H3).
    rewrite (chb_nth i ltac:(lia)) in H1. injection H1 as ->. auto.
  Qed.

  Lemma ch_range : forall i, 0 <= i <= L -> 0 <= ch i < 256 /\ (ch i = 0 <-> i = L).
  Proof.
    intros i Hi. destruct (Z.eq_dec i L) as [->|NE].
    - rewrite ch_L. lia.
    - destruct (ch_lt i ltac:(lia)) as [_ H]. lia.
  Qed.

  Lemma ch_read : forall m i, bytes_at bsegs m S full -> 0 <= i <= L -> ov_read_bytes bsegs m (wa (S + i)) 1 = Some [chb i].
  Proof. intros m i STR Hi. eapply u8ro_read; [exact STR| apply chb_nth; exact Hi| lia| reflexivity]. Qed.

  Lemma esc_step : forall i, 0 <= i < L -> esc_count (firstn (Z.to_nat (i + 1)) str) = esc_count (firstn (Z.to_nat i) str) + esc_extra (ch i).
  Proof.
    intros i Hi. destruct (ch_lt i Hi) as [H2 _].
    replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia. apply esc_count_firstn_S. exact H2.
  Qed.

  (* [comment removed for export] *)
  Definition pos (i : Z) : Z := i + esc_count (firstn (Z.to_nat i) str).

  Lemma pos_0 : pos 0 = 0.
  Proof. reflexivity. Qed.

  Lemma pos_step : forall i, 0 <= i < L -> pos (i + 1) = pos i + 1 + esc_extra (ch i).
  Proof. intros i Hi. unfold pos. rewrite esc_step by exact Hi. lia. Qed.

  Lemma pos_bound : forall i, 0 <= i <= L -> i <= pos i /\ pos i + (L - i) <= L + E.
  Proof.
    intros i Hi. unfold pos. pose proof (esc_count_range (firstn (Z.to_nat i) str)) as R1.
    pose proof (esc_count_firstn_le str (Z.to_nat i)) as R2. lia.
  Qed.

  Lemma pos_next_bound : forall i, 0 <= i < L -> pos i + 1 + esc_extra (ch i) + (L - i - 1) <= L + E.
  Proof. intros i Hi. rewrite <- pos_step by exact Hi. pose proof (pos_bound (i + 1) ltac:(lia)). lia. Qed.

  Lemma pos_L : pos L = L + E.
  Proof. unfold pos. rewrite Nat2Z.id, firstn_all. reflexivity. Qed.

 (* [comment removed for export] *)
 (* [comment removed for export] *)
 Section Count.
  Variables (m : word -> option byte) (n : Z).
  Hypothesis STR : bytes_at bsegs m S full.
  Hypothesis SO : shadow_ok m S n.
  Hypothesis LENN : L + 1 + Z.of_nat (length tail) = n.
  Hypothesis SR : AIMG_HI <= S /\ S + n <= alloc_ceiling.

  Lemma S_bound : 0 <= S /\ S + L + 1 + Z.of_nat (length tail) <= 2^64.
  Proof. pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite length_app in B. cbn [length] in B. lia. Qed.

  Lemma str_shchk : forall i, 0 <= i <= L -> shchk m (S + i) 1.
  Proof. intros i Hi. eapply shadow_ok_shchk1; [exact SO| lia]. Qed.

  (* [comment removed for export] *)
  Variables (x1 x2 x3 x4 x5 x6 x7 x9 x12 x18 x19 x20 x21 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32).
  Notation CST pc a0v i e x16 x17 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 S) x9 a0v (Z_to_bv 64 34) x12 (Z_to_bv 64 92) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17179883264) x16 x17
             x18 x19 x20 x21 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 i) (Z_to_bv 64 e) x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).
  Definition count_end : machine_state -> Prop :=
    fun ms' => exists x16 x17, ms' = CST 0x869b0 (Z_to_bv 64 (S + L)) L E x16 x17.

  (* [comment removed for export] *)
  Definition PA4 (i : Z) : Prop := forall x16 x17,
    evt bsegs count_end (CST 0x86958 (Z_to_bv 64 (S + i)) i (esc_count (firstn (Z.to_nat i) str)) x16 x17).
  (* [comment removed for export] *)
  Definition ADV (i : Z) : Prop := forall x10 x16 x17,
    evt bsegs count_end (CST 0x86974 x10 i (esc_count (firstn (Z.to_nat (i + 1)) str)) x16 x17).

  Lemma adv_of : forall i, 0 <= i < L -> PA4 (i + 1) -> ADV i.
  Proof.
    intros i Hi K x10 x16 x17. unfold PA4 in K. pose proof S_bound as SB. pose proof SR as [SR1 SR2]. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in SR1. bandM. sepM. try rewrite alloc_ceiling_eq in SR2.
    zstep. zstep. zstep. zstep.
    pose proof (str_shchk (i + 1) ltac:(lia)) as CK. asan_chk CK.
    apply K.
  Qed.

  Lemma pa4_step : forall i, 0 <= i < L -> ADV i -> PA4 i.
  Proof.
    intros i Hi K x16 x17. unfold ADV in K. pose proof S_bound as SB. pose proof SR as [SR1 SR2]. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in SR1. bandM. sepM. try rewrite alloc_ceiling_eq in SR2.
    pose proof (ch_read m i STR ltac:(lia)) as RD. destruct (ch_lt i Hi) as [_ CR]. pose proof (esc_step i Hi) as ES.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K34; zify_cond K34.
    - (* [comment removed for export] *)
      zstep. if_cases K92; zify_cond K92.
      + zstep.
        replace (esc_count (firstn (Z.to_nat i) str) + 1) with (esc_count (firstn (Z.to_nat (i + 1)) str))
          by (rewrite ES, esc_extra_gt34, K92 by lia; cbn; lia).
        ugd. apply K.
      + zstep. zstep. zstep. rewrite neg_flag5. zstep.
        replace (esc_count (firstn (Z.to_nat i) str) + (if ch i <? 32 then 5 else 0)) with (esc_count (firstn (Z.to_nat (i + 1)) str))
          by (rewrite ES, esc_extra_gt34 by lia; replace (ch i =? 92) with false by (symmetry; apply Z.eqb_neq; lia);
              replace (ch i <? 32) with false by (symmetry; apply Z.ltb_ge; lia); lia).
        ugd. apply K.
    - (* [comment removed for export] *)
      zstep. zstep. rewrite (Z.mod_small (ch i) 64) by lia. rewrite rmask_bit' by lia.
      destruct (resc1b (ch i)) eqn:RB.
      + zstep. if_cases Kb; zify_cond Kb; [exfalso; lia|]. clear Kb.
        zstep. ugd.
        replace (esc_count (firstn (Z.to_nat i) str) + 1) with (esc_count (firstn (Z.to_nat (i + 1)) str))
          by (rewrite ES, resc1b_extra, RB by lia; lia).
        apply K.
      + zstep. if_cases Kb; zify_cond Kb; [| exfalso; lia]. clear Kb.
        zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
        zstep. if_cases K92; zify_cond K92; [exfalso; lia|].
        zstep. zstep. zstep. rewrite neg_flag5. zstep.
        replace (esc_count (firstn (Z.to_nat i) str) + (if ch i <? 32 then 5 else 0)) with (esc_count (firstn (Z.to_nat (i + 1)) str))
          by (rewrite ES, resc1b_extra, RB by lia; lia).
        ugd. apply K.
  Qed.

  Lemma pa4_L : PA4 L.
  Proof.
    intros x16 x17. pose proof S_bound as SB. pose proof SR as [SR1 SR2]. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in SR1. bandM. sepM. try rewrite alloc_ceiling_eq in SR2.
    pose proof (ch_read m L STR ltac:(lia)) as RD.
    zstep. cbv beta. rewrite ch_L. zstep. if_cases K34; zify_cond K34; [exfalso; lia|].
    zstep. zstep. try change (Z.land (Z.shiftr 17179883264 0) 1) with 0.
    zstep. if_cases Kb; zify_cond Kb; [| exfalso; lia].
    zstep. if_cases Kz; zify_cond Kz; [| exfalso; lia].
    apply evt_done. unfold count_end. rewrite firstn_all2 by lia. do 2 eexists. reflexivity.
  Qed.

  Lemma count_all : forall (k : nat) (i : Z), Z.of_nat k = L - i -> 0 <= i <= L -> PA4 i.
  Proof.
    induction k as [|k IH]; intros i Hk Hi.
    - replace i with L by lia. apply pa4_L.
    - apply pa4_step; [lia|]. apply adv_of; [lia|]. apply IH; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma count_loop : forall x16 x17, evt bsegs count_end (CST 0x86940 (Z_to_bv 64 S) 0 0 x16 x17).
  Proof.
    intros x16 x17. pose proof S_bound as SB. pose proof SR as [SR1 SR2]. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in SR1. bandM. sepM. try rewrite alloc_ceiling_eq in SR2.
    pose proof (count_all (Z.to_nat L) 0 ltac:(lia) ltac:(lia)) as H. unfold PA4 in H. cbn [Z.to_nat firstn esc_count] in H.
    replace (S + 0) with S in H by lia.
    zstep. zstep.
    pose proof (str_shchk 0 ltac:(lia)) as CK. replace (S + 0) with S in CK by lia. asan_chk CK.
    apply H.
  Qed.
 End Count.
End Str.


End CeilWrap.
(* [comment removed for export] *)
Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).
