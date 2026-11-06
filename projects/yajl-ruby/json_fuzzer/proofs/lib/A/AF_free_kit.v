(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Export StepA StepA2 AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Export Mem Arr Frame Cells Step.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac cstep := stepA; try first [if_true | if_false].
(* [comment removed for export] *)
Ltac amo_phase1 ::=
  match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let H := fresh "AL" in
      first [ assert (H : amo_aligned wd a = true) by prove_amo_aligned
            | fail 100 "stepA: cannot prove natural alignment of the atomic access at" a ];
      rewrite H; clear H; cbv beta iota delta [negb];
      exec_cbvA; simp_is_x0; simp_regs;
      repeat match goal with
      | |- context [Z.eqb ?x ?x] => rewrite (Z.eqb_refl x); cbv beta iota
      | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
          replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with true by (symmetry; apply Z.eqb_eq; first [reflexivity | zsimp; lia]);
          cbv beta iota
      end
  | _ => idtac
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Notation zb0 := (Z_to_bv 8 0).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma bytes_at_snoc0 : forall m a k, 0 <= a -> a + Z.of_nat k + 1 <= 2^64 ->
  bytes_at asegs m a (repeat zb0 k) ->
  bytes_at asegs (write_to_mem m (wa (a + Z.of_nat k)) [zb0]) a (repeat zb0 (S k)).
Proof. aceil.
  intros m a k A0 AK BA. replace (repeat zb0 (S k)) with (repeat zb0 k ++ [zb0]) by (rewrite <- repeat_cons; cbn; rewrite repeat_cons; reflexivity).
  apply (proj2 (bytes_at_app asegs _ a _ _)). rewrite repeat_length. split.
  - apply bytes_at_write_other; [exact BA| lia| cbn; lia| rewrite repeat_length; cbn; lia].
  - apply bytes_at_write_same; [lia| cbn; lia].
Qed.

Lemma bytes_at_app0 : forall m a k j, 0 <= a -> a + Z.of_nat k + Z.of_nat j <= 2^64 ->
  bytes_at asegs m a (repeat zb0 k) ->
  bytes_at asegs (write_to_mem m (wa (a + Z.of_nat k)) (repeat zb0 j)) a (repeat zb0 (k + j)).
Proof. aceil.
  intros m a k j A0 AK BA. rewrite repeat_app.
  apply (proj2 (bytes_at_app asegs _ a _ _)). rewrite repeat_length. split.
  - apply bytes_at_write_other; [exact BA| lia| rewrite repeat_length; lia| rewrite !repeat_length; lia].
  - apply bytes_at_write_same; [lia| rewrite repeat_length; lia].
Qed.

Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof. aceil.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma rw_cells_reshape : forall segs m A cs cs',
  cells_wf cs' -> map bv_unsigned (cells_bytes cs') = map bv_unsigned (cells_bytes cs) -> rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof. aceil.
  intros segs m A cs cs' WF EB0 [[WF0 BA] WR]. pose proof (bytes_eq_of_unsigned _ _ EB0) as EB.
  split; [split; [exact WF| rewrite EB; exact BA]|].
  rewrite <- (cells_bytes_length cs' WF), EB, (cells_bytes_length cs WF0). exact WR.
Qed.

Lemma wr_at_sub : forall segs m a n a' n', wr_at segs m a n -> a <= a' -> a' + n' <= a + n -> wr_at segs m a' n'.
Proof. aceil.
  intros segs m a n a' n' (A0 & AN & W) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
Qed.

(* [comment removed for export] *)
End RC__1.
(* [comment removed for export] *)
Inductive boxed (X : Prop) : Prop := Box : X -> boxed X.
Definition unbox {X : Prop} (b : boxed X) : X := match b with Box _ h => h end.

(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[global] Set Default Proof Mode "Classic".
(* [comment removed for export] *)
Ltac dlia_box1 D := destruct (unbox D) as [XD|XD]; LiaA.lia_probe.
Ltac sub_neg1 H := let C := fresh "C" in intros C; apply H; LiaA.lia_probe.
Ltac2 rk_subset (xs : ident list) (ys : ident list) : bool :=
  List.for_all (fun x => List.exist (Ident.equal x) ys) xs.
Ltac2 rk_count (xs : ident list) (ys : ident list) : int :=
  List.fold_left (fun n x => if List.exist (Ident.equal x) ys then Int.add n 1 else n) 0 xs.
(* [comment removed for export] *)
Ltac2 rk_rank (cands : (ident * ident list) list) : ident list :=
  let gv := StoreFast.SF2.vars_of [] (Control.goal ()) in
  let scored := List.map (fun b => let (id, hv) := b in
                  let c := rk_count hv gv in
                  let s := Int.add (Int.mul 2 c) (if rk_subset hv gv then 1 else 0) in (s, id)) cands in
  let sorted := List.sort (fun a b => let (sa, _) := a in let (sb, _) := b in Int.compare sb sa) scored in
  List.map (fun p => let (_, id) := p in id) sorted.
Ltac2 rk_try (ids : ident list) (close1 : Ltac1.t) : unit :=
  let rec go ids := match ids with
    | [] => Control.zero (Tactic_failure None)
    | id :: rest =>
        Control.plus (fun () => Ltac1.apply close1 [Ltac1.of_constr (Control.hyp id)] (fun t => Ltac1.run t))
                     (fun _ => go rest)
    end in
  Control.once (fun () => go ids).
Ltac2 rk_boxes () : (ident * ident list) list :=
  List.map_filter (fun h => let (id, _, ty) := h in
    lazy_match! ty with
    | boxed (_ \/ _) => Some (id, StoreFast.SF2.vars_of [] ty)
    | _ => None
    end) (List.rev (Control.hyps ())).
Ltac2 rk_negs () : (ident * ident list) list :=
  (* [comment removed for export] *)
  let xv := lazy_match! Control.goal () with
            | ~ (_ <= ?x < _)%Z => StoreFast.SF2.vars_of [] x
            | _ => []
            end in
  List.map_filter (fun h => let (id, _, ty) := h in
    lazy_match! ty with
    | ~ _ => Some (id, List.filter (fun v => Bool.neg (List.exist (Ident.equal v) xv)) (StoreFast.SF2.vars_of [] ty))
    | _ => None
    end) (List.rev (Control.hyps ())).
(* [comment removed for export] *)
Ltac rk_boxes_lia := ltac2:(Control.enter (fun () => rk_try (rk_rank (rk_boxes ())) ltac1val:(fun D => dlia_box1 D))).
Ltac rk_negs_lia := ltac2:(Control.enter (fun () => rk_try (rk_rank (rk_negs ())) ltac1val:(fun H => sub_neg1 H))).
Ltac2 rk_ors () : (ident * ident list) list :=
  List.map_filter (fun h => let (id, _, ty) := h in
    lazy_match! ty with
    | _ \/ _ => Some (id, StoreFast.SF2.vars_of [] ty)
    | _ => None
    end) (List.rev (Control.hyps ())).
Ltac dlia_or1 D := destruct D as [XD|XD]; LiaA.lia_probe.
Ltac rk_ors_lia := ltac2:(Control.enter (fun () => rk_try (rk_rank (rk_ors ())) ltac1val:(fun D => dlia_or1 D))).
(* [comment removed for export] *)
Ltac dlia := first [ LiaA.lia_probe | rk_boxes_lia | rk_ors_lia | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Definition carry_skip (P : Prop) := P.
Ltac skipH H := lazymatch type of H with ?TS => change TS with (carry_skip TS) in H end.
Ltac unskip_all := repeat match goal with H : carry_skip _ |- _ => unfold carry_skip in H end.
Ltac carry_rw H MU WM := eapply rw_cells_transport in H; [| exact MU| exact WM| cbn; lia].

(* [comment removed for export] *)
Ltac sub_fp_fast :=
  let xq := fresh "xq" in let Hq := fresh "Hq" in
  intros xq Hq; cbn [outside app] in Hq |- *; decompose [and] Hq; clear Hq;
  repeat match goal with |- _ /\ _ => split end; try exact I;
  match goal with O : ~ (_ <= xq < _)%Z |- _ => clear -O; let R := fresh in intros R; apply O; lia end.

(* [comment removed for export] *)
Ltac carry_all mc m' MUc WMc :=
  repeat match goal with
  | H : rw_cells asegs mc _ _ |- _ => first [ carry_rw H MUc WMc | skipH H ]
  | H : bytes_at asegs mc _ _ |- _ => first [ eapply bytes_at_transport in H; [| exact MUc| cbn [disjoint_from length]; rewrite ?repeat_length, ?length_le8, ?length_le4; lia] | skipH H ]
  | H : stk asegs mc _ _ |- _ => first [ eapply stk_transport in H; [| exact MUc| exact WMc| intros; left; cbn; lia] | skipH H ]
  | H : wr_at asegs mc _ _ |- _ => first [ eapply wr_at_transport in H; [| exact WMc] | skipH H ]
  | H : u8arr asegs mc _ _ |- _ => first [ eapply u8arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; rewrite ?repeat_length; lia] | skipH H ]
  | H : u64arr asegs mc _ _ |- _ => first [ eapply u64arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : u32arr asegs mc _ _ |- _ => first [ eapply u32arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : munch ?W ?ma mc |- _ =>
      let H2 := fresh in
      first [ assert (H2 : munch W ma m')
          by (eapply munch_trans; [exact H| eapply munch_weaken; [| exact MUc];
              first [ sub_fp_fast
                    | let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq;
                      first [ solve [ clear -Hq; cbn in Hq |- *; intuition (first [lia | assumption | exact I]) ]
                            | cbn in Hq |- *; intuition (first [lia | assumption | exact I]) ] ] ]);
        clear H; rename H2 into H | skipH H ]
  | H : wmono asegs ?ma mc |- _ =>
      let H2 := fresh in
      assert (H2 : wmono asegs ma m') by (eapply wmono_trans; [exact H| exact WMc]);
      clear H; rename H2 into H
  end;
  unskip_all.

(* [comment removed for export] *)
Ltac after_call mc m' MUc WMc := carry_all mc m' MUc WMc; clear MUc WMc; try clear mc.

(* [comment removed for export] *)
Ltac hideH H := lazymatch type of H with ?TS => change TS with (StoreFast.sf_hide TS) in H end.
Ltac hide_mem_except m FR :=
  repeat match goal with
  | H : rw_cells asegs m _ _ |- _ => tryif constr_eq H FR then fail else hideH H
  | H : bytes_at asegs m _ _ |- _ => hideH H
  | H : u8arr asegs m _ _ |- _ => hideH H
  | H : u32arr asegs m _ _ |- _ => hideH H
  | H : u64arr asegs m _ _ |- _ => hideH H
  | H : wr_at asegs m _ _ |- _ => hideH H
  end.
Ltac carry_hidden MU0 WM0 :=
  repeat match goal with
  | H : StoreFast.sf_hide ?TS |- _ =>
      unfold StoreFast.sf_hide in H;
      lazymatch TS with
      | rw_cells _ _ _ _ => carry_rw H MU0 WM0
      | bytes_at _ _ _ _ => eapply bytes_at_transport in H; [| exact MU0| cbn [disjoint_from length]; rewrite ?repeat_length, ?length_le8, ?length_le4; lia]
      | wr_at _ _ _ _ => eapply wr_at_transport in H; [| exact WM0]
      | u8arr _ _ _ _ => eapply u8arr_transport in H; [| exact MU0| exact WM0| cbn [disjoint_from length]; rewrite ?repeat_length; lia]
      | u64arr _ _ _ _ => eapply u64arr_transport in H; [| exact MU0| exact WM0| cbn [disjoint_from length]; lia]
      | u32arr _ _ _ _ => eapply u32arr_transport in H; [| exact MU0| exact WM0| cbn [disjoint_from length]; lia]
      end
  end.
Ltac frame_stores_tac n FR :=
  lazymatch type of FR with
  | rw_cells asegs ?m ?fa ?cs =>
      let sz := eval cbv in (Z.of_nat (cells_size cs)) in
      let MU0 := fresh "MUf" in let WM0 := fresh "WMf" in
      assert (MU0 : munch [(fa, fa + sz)] m m) by apply munch_refl;
      assert (WM0 : wmono asegs m m) by apply wmono_refl;
      hide_mem_except m FR;
      do n zstepA;
      carry_hidden MU0 WM0; clear MU0 WM0; try clear m
  end.
Tactic Notation "frame_stores" integer(n) constr(FR) := frame_stores_tac n FR.

(* [comment removed for export] *)
Ltac cells_wf_triv := cbn; clear; repeat first [exact I | split].

(* [comment removed for export] *)
Ltac settle_store A BS SOK :=
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ (write_to_mem ?mc ?w ?bs) _) =>
    change (write_to_mem mc w bs) with (write_to_mem mc (wa A) BS);
    let k := eval cbv in (Z.of_nat (length BS)) in
    let MUw := fresh "MUw" in let WMw := fresh "WMw" in
    assert (MUw : munch [(A, A + k)] mc (write_to_mem mc (wa A) BS)) by (apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; left; lia]);
    assert (WMw : wmono asegs mc (write_to_mem mc (wa A) BS)) by (apply wmono_write; apply wmono_refl);
    carry_all mc (write_to_mem mc (wa A) BS) MUw WMw;
    lazymatch goal with H : mem_inv asegs mc |- _ => apply (mem_inv_store asegs mc (wa A) BS) in H; [| rewrite ?length_le8, ?length_le4; cbn [length]; exact SOK] end;
    let BAw := fresh "BAw" in
    assert (BAw : bytes_at asegs (write_to_mem mc (wa A) BS) A BS) by (apply bytes_at_write_same; [lia| cbn; lia]);
    clear MUw WMw SOK;
    let m' := fresh "m" in remember (write_to_mem mc (wa A) BS) as m' eqn:Heqm; clear Heqm; try clear mc
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma rwc_split : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. aceil.
  intros segs m A cs1 cs2 [[WF B] W]. apply cells_wf_app in WF. destruct WF as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2]. rewrite (cells_bytes_length _ W1) in B2.
  rewrite cells_size_app in W. destruct W as (Wa & Wb & Wr).
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Wr. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Wr. lia.
Qed.
Lemma rwc_join : forall segs m A cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof. aceil.
  intros segs m A cs1 cs2 [[W1 B1] (Wa & Wb & Wr)] [[W2 B2] (Va & Vb & Vr)]. split; [split|].
  - apply cells_wf_app. auto.
  - rewrite cells_bytes_app. apply bytes_at_app. rewrite (cells_bytes_length _ W1). auto.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))); [apply Wr; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply Vr. lia.
Qed.
(* [comment removed for export] *)
Lemma rwc_join_at : forall segs m A A2 cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m A2 cs2 -> A2 = A + Z.of_nat (cells_size cs1) -> rw_cells segs m A (cs1 ++ cs2).
Proof. aceil. intros segs m A A2 cs1 cs2 H1 H2 ->. apply rwc_join; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma k_bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof. aceil.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

Lemma k_Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof. aceil.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  pose proof (k_bytes_le_to_Z_range bs) as HR.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
    2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.ltb_spec0 i 8).
        - rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite Z.ones_spec_high by lia. apply andb_false_r. }
    rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
    rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof. aceil.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (k_bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?z) with (z mod 2^64). rewrite Z.mod_small by lia.
  rewrite <- HL. apply k_Z_to_le_bytes_to_Z.
Qed.

Lemma u64arr_of_cb : forall segs m A bs k,
  rw_cells segs m A [CB (8 * k) bs] -> exists ws, length ws = k /\ u64arr segs m A ws.
Proof. aceil.
  intros segs m A bs k [[WF Hb] Hw]. cbn in WF. destruct WF as [HL _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize Nat.add] in Hw. rewrite Nat.add_0_r in Hw.
  assert (G : forall k bs, length bs = (8 * k)%nat -> exists ws, length ws = k /\ u64s ws = bs).
  { clear. induction k as [|k IH]; intros bs HL.
    - exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
    - destruct (IH (skipn 8 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hlen & Hu).
      exists (le_bytes_to_word (firstn 8 bs) :: ws). split; [cbn; lia|].
      cbn [u64s]. rewrite Hu, le8_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn. }
  destruct (G k bs HL) as (ws & Hlen & Hu). exists ws. split; [exact Hlen|]. split.
  - rewrite Hu. exact Hb.
  - rewrite Hlen. replace (8 * Z.of_nat k)%Z with (Z.of_nat (8 * k)) by lia. exact Hw.
Qed.

Lemma cb_of_u64arr : forall segs m A ws, u64arr segs m A ws -> rw_cells segs m A [CB (8 * length ws) (u64s ws)].
Proof. aceil.
  intros segs m A ws [Hb Hw]. split; [split|].
  - cbn. rewrite u64s_length. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws))%Z by lia. exact Hw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma find_segment_In : forall segs a n s, find_segment segs a n = Some s -> In s segs.
Proof. aceil.
  induction segs as [|x segs IH]; cbn; intros a n s H; [discriminate|].
  destruct (_ && _); [injection H; auto| right; eapply IH; exact H].
Qed.

Lemma asegs_readable : Forall (fun s => seg_readable s = true) asegs.
Proof. unfold asegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments. repeat (apply Forall_cons; [reflexivity|]). apply Forall_nil. Qed.

Lemma wr_at_mrd : forall m a n i, wr_at asegs m a n -> 0 <= i < n -> exists b, mrd asegs m (wa (a + i)) = Some b.
Proof. aceil.
  intros m a n i (A0 & AN & W) Hi. specialize (W i Hi). unfold mrd. unfold wview in W.
  destruct (m (wa (a + i))) as [b|] eqn:E; [exists b; reflexivity|].
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1%Z.
  destruct (find_segment asegs (bv_unsigned (wa (a + i))) 1) as [sg|] eqn:FS; [| exfalso; apply W; reflexivity].
  pose proof (proj1 (Forall_forall _ _) asegs_readable sg (find_segment_In _ _ _ _ FS)) as RD. cbn beta in RD. rewrite RD.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (seg_writable sg); [| exfalso; apply W; reflexivity].
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (wa (a + i)) - Z.of_N (seg_base sg)))) as [b|] eqn:SB;
    [| exfalso; apply W; reflexivity].
  cbn. eexists. reflexivity.
Qed.

Lemma wr_at_bytes : forall m a n, wr_at asegs m a n -> 0 <= n -> exists bs, length bs = Z.to_nat n /\ bytes_at asegs m a bs.
Proof. aceil.
  intros m a n WR N0. pose proof WR as (A0 & AN & _).
  exists (map (fun i => match mrd asegs m (wa (a + Z.of_nat i)) with Some b => b | None => zb0 end) (seq 0 (Z.to_nat n))).
  split; [rewrite length_map, length_seq; reflexivity|].
  split; [lia|]. split; [rewrite length_map, length_seq, Z2Nat.id by exact N0; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite nth_error_map, nth_error_seq. replace (Nat.ltb i (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [option_map Nat.add].
  destruct (wr_at_mrd m a n (Z.of_nat i) WR ltac:(lia)) as [b Hb]. rewrite Hb. reflexivity.
Qed.

Lemma wr_at_c8c8 : forall m a, wr_at asegs m a 16 -> exists v w, rw_cells asegs m a [C8 v; C8 w].
Proof. aceil.
  intros m a WR. destruct (wr_at_bytes m a 16 WR ltac:(lia)) as (bs & L & B).
  assert (CBH : rw_cells asegs m a [CB (8 * 2) bs]).
  { split; [split; [cbn; split; [exact L| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]|]. cbn [cells_size csize Nat.mul Nat.add]. exact WR. }
  destruct (u64arr_of_cb asegs m a bs 2 CBH) as (ws & LW & ARR).
  destruct ws as [|v [|w [|? ?]]]; cbn in LW; try lia.
  exists v, w. pose proof (cb_of_u64arr asegs m a [v; w] ARR) as X. cbn [length Nat.mul u64s] in X.
  eapply rw_cells_reshape; [| | exact X]; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma skipn_repeat0 : forall {A} (x : A) n k, skipn k (repeat x n) = repeat x (n - k).
Proof. aceil. intros A x n; induction n as [|n IH]; intros [|k]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma firstn_repeat0 : forall {A} (x : A) n k, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. aceil. intros A x n; induction n as [|n IH]; intros [|k] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.

(* [comment removed for export] *)
End RC__2.
Tactic Notation "leafA" uconstr(SPEC) :=
  eapply evtA_cut; [eapply SPEC|]; [..| cbv beta; let ms := fresh "ms'" in intros ms ->; ret_pc_lit].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma land_high_low : forall hi lo k, 0 <= hi -> 0 <= k -> 0 <= lo < 2^k -> Z.land (hi * 2^k) lo = 0.
Proof. aceil.
  intros hi lo k Hh Hk Hl. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k).
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - destruct (Z.eq_dec lo 0) as [->|]. { rewrite Z.bits_0. apply andb_false_r. }
    rewrite (Z.bits_above_log2 lo i); [apply andb_false_r| lia|].
    apply (Z.lt_le_trans _ k); [| lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lor_shiftl : forall hi lo k, 0 <= hi -> 0 <= k -> 0 <= lo < 2^k -> Z.lor (Z.shiftl hi k) lo = hi * 2^k + lo.
Proof. aceil.
  intros hi lo k Hh Hk Hl. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite <- Z.lxor_lor by (apply land_high_low; lia). symmetry. apply Z.add_nocarry_lxor. apply land_high_low; lia.
Qed.
Lemma fsx32_small' : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof. aceil.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap. change (bv_swrap 32 ?z) with ((z + 2^31) mod 2^32 - 2^31).
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.
Lemma fzx32_small' : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. aceil. intros. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma fzx16_small : forall x, 0 <= x < 2^16 -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. aceil. intros. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma u8_lit : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. aceil. intros. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition iv_sep (iv jv : Z * Z) : Prop := snd iv <= fst jv \/ snd jv <= fst iv.

Record depot_ifc := mkDepotIfc {
  DS : Type;
  DR : DS -> (word -> option byte) -> Prop;
  down : DS -> Z * Z -> Prop;
  dput : DS -> list Z -> DS * Z;
  dr_frame : forall ds m m' W, DR ds m -> munch W m m' -> wmono asegs m m' ->
             Forall (fun iv => forall jv, down ds jv -> iv_sep iv jv) W -> DR ds m'
}.

Definition depot_put_spec (D : depot_ifc) (P : acc -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop) (m : mem) (lo hi A len : Z) (ws : list word) (ds : DS D),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 224 -> bv_unsigned sp <= hi -> hi < 2^47 ->
  mem_inv asegs m -> DR D ds m ->
  u64arr asegs m A ws -> 1 <= len <= Z.of_nat (length ws) -> Z.of_nat (length ws) <= 30 ->
  bv_unsigned sp <= A -> A + 8 * Z.of_nat (length ws) <= hi ->
  (forall jv, down D ds jv -> iv_sep (lo, hi) jv) ->
  (forall a k, lo <= a -> a + Z.of_nat k <= hi -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x31000 -> P (Z_to_bv 64 a, k)) ->
  (forall jv a k, down D ds jv -> fst jv <= a -> a + Z.of_nat k <= snd jv -> P (Z_to_bv 64 a, k)) ->
  (forall m' (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (W : list (Z * Z)),
     let r := dput D ds (map bv_unsigned (firstn (Z.to_nat len) ws)) in
     mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> wmono asegs m m' ->
     munch ((bv_unsigned sp - 224, bv_unsigned sp) :: W) m m' -> Forall (down D ds) W ->
     DR D (fst r) m' -> 0 <= snd r < 2^32 ->
     (forall jv, down D (fst r) jv -> down D ds jv) ->     (* [comment removed for export] *)
     evtA asegs P Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (snd r)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x73f64) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Lemma disjoint_from_down : forall (D : depot_ifc) ds W a n,
  Forall (down D ds) W -> (forall jv, down D ds jv -> iv_sep (a, a + n) jv) -> disjoint_from W a n.
Proof. aceil.
  intros D ds W a n HW SEP. induction W as [|[u v] W IH]; cbn; [exact I|].
  inversion HW as [|? ? DI HW']; subst. split; [| apply IH; exact HW'].
  specialize (SEP (u, v) DI). unfold iv_sep in SEP. cbn in SEP. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. aceil. induction W1 as [|[a b] W1 IH]; cbn; intros; [tauto|]. rewrite IH. tauto. Qed.
Lemma munch_app_l : forall W1 W2 m m', munch W1 m m' -> munch (W1 ++ W2) m m'.
Proof. aceil. intros W1 W2 m m' H x Hx. apply H. apply (proj1 (outside_app _ _ _)) in Hx. tauto. Qed.
Lemma munch_app_r : forall W1 W2 m m', munch W2 m m' -> munch (W1 ++ W2) m m'.
Proof. aceil. intros W1 W2 m m' H x Hx. apply H. apply (proj1 (outside_app _ _ _)) in Hx. tauto. Qed.
Lemma munch_cons_sub : forall a b a' b' W m m', munch ((a, b) :: W) m m' -> a' <= a -> b <= b' -> munch ((a', b') :: W) m m'.
Proof. aceil. intros a b a' b' W m m' H Ha Hb x Hx. apply H. cbn in Hx |- *. destruct Hx as [H1 H2]. split; [lia| exact H2]. Qed.
Lemma disjoint_from_app : forall W1 W2 a n, disjoint_from W1 a n -> disjoint_from W2 a n -> disjoint_from (W1 ++ W2) a n.
Proof. aceil. induction W1 as [|[u v] W1 IH]; cbn; intros; [assumption|]. split; [tauto|]. apply IH; tauto. Qed.
Lemma Forall_sep_app : forall (Pv : Z * Z -> Prop) W1 W2, Forall Pv W1 -> Forall Pv W2 -> Forall Pv (W1 ++ W2).
Proof. aceil. intros. apply Forall_app. auto. Qed.


(* [comment removed for export] *)
End RC__3.
(* [comment removed for export] *)
Ltac sep_probe1 S :=
  match goal with Hj : down _ _ ?jv |- iv_sep _ ?jv =>
    let X := fresh "X" in pose proof (S jv Hj) as X; unfold iv_sep in X |- *; cbn in X |- *; destruct X as [X|X]; LiaA.lia_probe end.
Ltac sep_full1 S :=
  match goal with Hj : down _ _ ?jv |- iv_sep _ ?jv =>
    let X := fresh "X" in pose proof (S jv Hj) as X; unfold iv_sep in X |- *; cbn in X |- *; lia end.
Ltac2 rk_seps () : (ident * ident list) list :=
  List.map_filter (fun h => let (id, _, ty) := h in
    lazy_match! ty with
    | forall jv0, down _ _ jv0 -> iv_sep ?iv jv0 => Some (id, StoreFast.SF2.vars_of [] iv)
    | _ => None
    end) (List.rev (Control.hyps ())).
Ltac rk_seps_probe := ltac2:(Control.enter (fun () => rk_try (rk_rank (rk_seps ())) ltac1val:(fun S => sep_probe1 S))).
Ltac rk_seps_full := ltac2:(Control.enter (fun () => rk_try (rk_rank (rk_seps ())) ltac1val:(fun S => sep_full1 S))).
(* [comment removed for export] *)
Ltac solve_sep1 :=
  let jv := fresh "jv" in let Hj := fresh "Hj" in
  intros jv Hj;
  repeat match goal with CV : (forall jv0, down _ ?dsn jv0 -> down _ _ jv0) |- _ =>
    lazymatch type of Hj with down _ dsn _ => apply CV in Hj end end;
  first [ rk_seps_probe | rk_seps_full ].
Ltac solve_seps := repeat (apply Forall_cons; [solve_sep1|]); apply Forall_nil.

(* [comment removed for export] *)
Ltac carry_allD mc m' MUc WMc :=
  carry_all mc m' MUc WMc;
  repeat match goal with
  | H : DR ?D ?ds mc |- _ => first [ eapply (dr_frame D) in H; [| exact MUc| exact WMc| solve_seps] | skipH H ]
  end; unskip_all.
Ltac after_callD mc m' MUc WMc := carry_allD mc m' MUc WMc; clear MUc WMc; try clear mc.
Ltac settle_storeD A BS SOK :=
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ (write_to_mem ?mc ?w ?bs) _) =>
    change (write_to_mem mc w bs) with (write_to_mem mc (wa A) BS);
    let k := eval cbv in (Z.of_nat (length BS)) in
    let MUw := fresh "MUw" in let WMw := fresh "WMw" in
    assert (MUw : munch [(A, A + k)] mc (write_to_mem mc (wa A) BS)) by (apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; left; lia]);
    assert (WMw : wmono asegs mc (write_to_mem mc (wa A) BS)) by (apply wmono_write; apply wmono_refl);
    carry_allD mc (write_to_mem mc (wa A) BS) MUw WMw;
    lazymatch goal with H : mem_inv asegs mc |- _ => apply (mem_inv_store asegs mc (wa A) BS) in H; [| rewrite ?length_le8, ?length_le4; cbn [length]; exact SOK] end;
    let BAw := fresh "BAw" in
    assert (BAw : bytes_at asegs (write_to_mem mc (wa A) BS) A BS) by (apply bytes_at_write_same; [lia| cbn; lia]);
    clear MUw WMw SOK;
    let m' := fresh "m" in remember (write_to_mem mc (wa A) BS) as m' eqn:Heqm; clear Heqm; try clear mc
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac solve_dj :=
  cbn [disjoint_from cells_size csize length Nat.add Nat.mul app];
  rewrite ?repeat_length, ?length_le8, ?length_le4, ?upd_length;
  repeat first [ exact I
               | split; [dlia|]
               | (eapply disjoint_from_down; [eassumption| solve_sep1])
               | dlia ].
Ltac carry_allX mc m' MUc WMc :=
  repeat match goal with
  | H : rw_cells asegs mc _ _ |- _ => first [ eapply rw_cells_transport in H; [| exact MUc| exact WMc| solve [solve_dj] ] | skipH H ]
  | H : bytes_at asegs mc _ _ |- _ => first [ eapply bytes_at_transport in H; [| exact MUc| solve [solve_dj] ] | skipH H ]
  | H : stk asegs mc _ _ |- _ => first [ eapply stk_transport in H; [| exact MUc| exact WMc| intros; left; cbn; lia] | skipH H ]
  | H : wr_at asegs mc _ _ |- _ => first [ eapply wr_at_transport in H; [| exact WMc] | skipH H ]
  | H : u8arr asegs mc _ _ |- _ => first [ eapply u8arr_transport in H; [| exact MUc| exact WMc| solve [solve_dj] ] | skipH H ]
  | H : u64arr asegs mc _ _ |- _ => first [ eapply u64arr_transport in H; [| exact MUc| exact WMc| solve [solve_dj] ] | skipH H ]
  | H : u32arr asegs mc _ _ |- _ => first [ eapply u32arr_transport in H; [| exact MUc| exact WMc| solve [solve_dj] ] | skipH H ]
  | H : wmono asegs ?ma mc |- _ =>
      let H2 := fresh in
      assert (H2 : wmono asegs ma m') by (eapply wmono_trans; [exact H| exact WMc]);
      clear H; rename H2 into H
  | H : DR ?D ?ds mc |- _ => first [ eapply (dr_frame D) in H; [| exact MUc| exact WMc| solve_seps] | skipH H ]
  end;
  unskip_all.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__4.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition qb3 : Type := (Z * Z * Z)%type.
Definition qaddr (b : qb3) : Z := fst (fst b).
Definition qsize (b : qb3) : Z := snd (fst b).
Definition qcnt (b : qb3) : Z := snd b.
(* [comment removed for export] *)
Definition hd_or (l : list qb3) (n : Z) : Z := match l with [] => n | b :: _ => qaddr b end.
End RC__4.
Notation hd_addr l := (hd_or l 0).
Section RC__5.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Fixpoint last_addr (l : list qb3) : Z := match l with [] => 0 | [b] => qaddr b | _ :: rest => last_addr rest end.
Fixpoint qsum (l : list qb3) : Z := match l with [] => 0 | b :: rest => qsize b + qsum rest end.
(* [comment removed for export] *)
Fixpoint qcellsn (m : word -> option byte) (l : list qb3) (n : Z) : Prop :=
  match l with
  | [] => True
  | b :: rest => rw_cells asegs m (qaddr b) [C8 (Z_to_bv 64 (hd_or rest n)); C8 (Z_to_bv 64 (qsize b)); C8 (Z_to_bv 64 (qcnt b))] /\ qcellsn m rest n
  end.
End RC__5.
Notation qcells m l := (qcellsn m l 0).
(* [comment removed for export] *)
Section RC__6.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition qbatch_ok (lo T : Z) (b : qb3) : Prop :=
  0x10007fff8000 (* [comment removed for export] *) <= qaddr b /\ qaddr b + 8192 <= lo /\ (qaddr b + 8192 <= T \/ T + 4096 <= qaddr b) /\ 8192 <= qsize b < 2^40 /\ 0 <= qcnt b <= 1021.
Definition qapart (l : list qb3) : Prop :=
  forall i j bi bj, nth_error l i = Some bi -> nth_error l j = Some bj -> i <> j -> qaddr bi + 8192 <= qaddr bj \/ qaddr bj + 8192 <= qaddr bi.

Lemma qsum_app : forall l1 l2, qsum (l1 ++ l2) = qsum l1 + qsum l2.
Proof. aceil. induction l1; cbn; intros; [lia|]. rewrite IHl1. lia. Qed.
Lemma qsum_lb : forall lo T l, Forall (qbatch_ok lo T) l -> 8192 * Z.of_nat (length l) <= qsum l.
Proof. aceil. induction l; cbn; intros H; [lia|]. inversion H; subst. unfold qbatch_ok in *. specialize (IHl ltac:(assumption)). lia. Qed.
Lemma qcellsn_transport : forall W m m' l n,
  qcellsn m l n -> munch W m m' -> wmono asegs m m' -> Forall (fun b => disjoint_from W (qaddr b) 24) l -> qcellsn m' l n.
Proof. aceil.
  induction l as [|b l IH]; cbn; intros n QCx MU WM HF; [exact I|].
  inversion HF; subst. destruct QCx as [Hb Hl]. split; [| apply IH; assumption].
  eapply rw_cells_transport; [exact Hb| exact MU| exact WM| cbn; assumption].
Qed.
Lemma qcellsn_app : forall m l1 l2 n, qcellsn m (l1 ++ l2) n <-> qcellsn m l1 (hd_or l2 n) /\ qcellsn m l2 n.
Proof. aceil.
  induction l1 as [|b l1 IH]; cbn; intros l2 n; [tauto|].
  rewrite IH. destruct l1; cbn; tauto.
Qed.
Lemma last_addr_app1 : forall l b, last_addr (l ++ [b]) = qaddr b.
Proof. aceil. induction l as [|x l IH]; cbn; intros; [reflexivity|]. rewrite IH. destruct (l ++ [b]) eqn:E; [| reflexivity]. destruct l; discriminate. Qed.
Lemma hd_or_app : forall l1 l2 n, l1 <> [] -> hd_or (l1 ++ l2) n = hd_or l1 n.
Proof. aceil. intros [|b l1] l2 n H; [congruence| reflexivity]. Qed.
Lemma qapart_tl : forall b l, qapart (b :: l) -> qapart l.
Proof. aceil. intros b l H i j bi bj Hi Hj Hij. apply (H (S i) (S j) bi bj Hi Hj). lia. Qed.
Lemma qapart_hd : forall b l b', qapart (b :: l) -> In b' l -> qaddr b + 8192 <= qaddr b' \/ qaddr b' + 8192 <= qaddr b.
Proof. aceil.
  intros b l b' H Hin. apply In_nth_error in Hin. destruct Hin as [j Hj]. apply (H 0%nat (S j) b b' eq_refl Hj). lia.
Qed.
Lemma qapart_app_inv : forall l1 l2, qapart (l1 ++ l2) -> qapart l2.
Proof. aceil. induction l1; cbn; intros l2 H; [exact H|]. apply IHl1. eapply qapart_tl. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qcellsn_frame : forall m l nx a bs,
  qcellsn m l nx -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  Forall (fun b => qaddr b + 24 <= a \/ a + Z.of_nat (length bs) <= qaddr b) l ->
  qcellsn (write_to_mem m (wa a) bs) l nx.
Proof. aceil.
  induction l as [|b l IH]; cbn; intros nx a0 bs0 QCx Ha Hl HF; [exact I|].
  inversion HF; subst. destruct QCx as [Hb Hr]. split; [| apply IH; assumption].
  apply rw_cells_frame; [exact Hb| lia| lia| cbn [cells_size csize Nat.add]; lia].
Qed.
Lemma DR_store : forall (D : depot_ifc) ds m a bs,
  DR D ds m -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (forall jv, down D ds jv -> iv_sep (a, a + Z.of_nat (length bs)) jv) -> DR D ds (write_to_mem m (wa a) bs).
Proof. aceil.
  intros D ds m a bs H Ha Hl SEP. eapply (dr_frame D ds m _ [(a, a + Z.of_nat (length bs))]); [exact H| | apply wmono_write; apply wmono_refl|].
  - apply munch_write; [apply munch_refl| lia| lia| cbn; left; lia].
  - constructor; [exact SEP| constructor].
Qed.
Lemma qcellsn_transportF : forall W m m' l n,
  qcellsn m l n -> munch W m m' -> wmono asegs m m' -> Forall (fun b => disjoint_from W (qaddr b) 24) l -> qcellsn m' l n.
Proof. aceil. intros. eapply qcellsn_transport; eassumption. Qed.

(* [comment removed for export] *)
End RC__6.
Ltac solve_qforall :=
  cbn [disjoint_from length]; rewrite ?length_le8, ?length_le4;
  first [ apply Forall_nil
        | match goal with
          | F : Forall _ ?l |- Forall _ ?l =>
              refine (Forall_impl _ _ _ F); cbv beta;
              let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; unfold qbatch_ok in Hb;
              decompose [and] Hb; repeat split; try exact I; lia
          end ].

Ltac transport_chunks segs m a bs ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : qcellsn m ?l ?nx |- _ =>
      first [ apply (qcellsn_frame m l nx a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; solve_qforall ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : DR ?D ?ds m |- _ =>
      first [ apply (DR_store D ds m a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; solve_sep1 ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
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
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  | H : qcellsn m ?l ?nx |- _ =>
      first [ apply (qcellsn_transportF W m m' l nx) in H; [ | exact MU | exact WM | solve_qforall ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : DR ?D ?ds m |- _ =>
      first [ apply (dr_frame D ds m m' W) in H; [ | exact MU | exact WM | solve_seps ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  end.
