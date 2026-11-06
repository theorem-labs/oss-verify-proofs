(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Export PropExec MState Mem Cells Exec Step Frame Arr Image.
(* [comment removed for export] *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Export RegFold JunkAbs.
(* [comment removed for export] *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import StepFast.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac is_concrete_map R ::=
  lazymatch R with
  | TNode _ _ _ => idtac
  | TEmpty => idtac
  | mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.
Ltac map_cbv_get ::=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota delta [tget mkR] in g in set_concl g'.
Ltac map_cbv_set ::=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota delta [tset mkR] in g in set_concl g'.

(* [comment removed for export] *)
Ltac solve_load_image :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      let E := addr_expr a in
      let Ez := zlit E in
      lazymatch goal with
      | HI : mem_inv segs m |- _ =>
          let obs := eval vm_compute in (image_bytes segs Ez n) in
          lazymatch obs with
          | Some ?bs =>
              let RO := fresh "ROimg" in
              assert (RO : ro_cells segs m Ez [CB n bs])
                by (apply (ro_cells_image segs m Ez bs HI); [vm_compute; reflexivity | lia | cbn; lia]);
              rewrite (ro_cells_read_at segs m Ez [CB n bs] 0%nat (CB n bs) n a RO)
                by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
              clear RO; load_post
          | None => fail "no readable image bytes at" Ez
          end
      end
  end.
Ltac solve_load ::= first [ solve_load_base | solve_load_image ].

(* [comment removed for export] *)
Ltac simpl_arr_sizes := rewrite ?u32s_length, ?u64s_length, ?upd_length in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfact (P : Prop) : Prop := P.

Record ibnd := IB { ib_l : option Z; ib_h : option Z; ib_L : option Z; ib_U : option Z; ib_PQ : option (Z * Z) }.

Definition opt_holds (o : option Z) (P : Z -> Prop) : Prop :=
  match o with Some z => P z | None => True end.

Definition ib_ok (X lo hi : Z) (b : ibnd) : Prop :=
  opt_holds (ib_l b) (fun l => lo = X + l)%Z /\ opt_holds (ib_h b) (fun h => hi = X + h)%Z /\
  opt_holds (ib_L b) (fun L => L <= lo)%Z /\ opt_holds (ib_U b) (fun U => hi <= U)%Z /\
  match ib_PQ b with Some (P, Q) => (hi <= P \/ Q <= lo)%Z | None => True end.

Definition opt_leb (x : Z) (o : option Z) : bool := match o with Some z => Z.leb x z | None => false end.
Definition opt_geb (x : Z) (o : option Z) : bool := match o with Some z => Z.leb z x | None => false end.

(* [comment removed for export] *)
Definition chk_lit (b : ibnd) (A s : Z) : bool :=
  orb (orb (opt_leb (A + s) (ib_L b)) (opt_geb A (ib_U b)))
      (match ib_PQ b with Some (P, Q) => andb (Z.leb P A) (Z.leb (A + s) Q) | None => false end).
(* [comment removed for export] *)
Definition chk_sb (b : ibnd) (c s : Z) : bool := orb (opt_leb (c + s) (ib_l b)) (opt_geb c (ib_h b)).

Lemma chk_lit_sound : forall X lo hi b A s,
  ib_ok X lo hi b -> chk_lit b A s = true -> (A + s <= lo \/ hi <= A)%Z.
Proof.
  intros X lo hi [l h L U PQ] A s (_ & _ & HL & HU & HPQ) Hc. unfold chk_lit in Hc. cbn in *.
  apply Bool.orb_true_iff in Hc. destruct Hc as [Hc|Hc]; [apply Bool.orb_true_iff in Hc; destruct Hc as [Hc|Hc]|].
  - destruct L as [L|]; cbn in *; [|discriminate]. apply Z.leb_le in Hc. lia.
  - destruct U as [U|]; cbn in *; [|discriminate]. apply Z.leb_le in Hc. lia.
  - destruct PQ as [[P Q]|]; [|discriminate]. apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma chk_sb_sound : forall X lo hi b c s,
  ib_ok X lo hi b -> chk_sb b c s = true -> (X + c + s <= lo \/ hi <= X + c)%Z.
Proof.
  intros X lo hi [l h L U PQ] c s (Hl & Hh & _ & _ & _) Hc. unfold chk_sb in Hc. cbn in *.
  apply Bool.orb_true_iff in Hc. destruct Hc as [Hc|Hc].
  - destruct l as [l|]; cbn in *; [|discriminate]. apply Z.leb_le in Hc. lia.
  - destruct h as [h|]; cbn in *; [|discriminate]. apply Z.leb_le in Hc. lia.
Qed.

Lemma chk_sb0_sound : forall X lo hi b s,
  ib_ok X lo hi b -> chk_sb b 0 s = true -> (X + s <= lo \/ hi <= X)%Z.
Proof. intros X lo hi b s Hb Hc. pose proof (chk_sb_sound X lo hi b 0 s Hb Hc). lia. Qed.

(* [comment removed for export] *)
Fixpoint ibs_ok (X : Z) (W : list ivl) (B : list ibnd) : Prop :=
  match W, B with
  | [], [] => True
  | (lo, hi) :: W', b :: B' => ib_ok X lo hi b /\ ibs_ok X W' B'
  | _, _ => False
  end.

Fixpoint chks_lit (B : list ibnd) (A s : Z) : bool :=
  match B with [] => true | b :: B' => andb (chk_lit b A s) (chks_lit B' A s) end.
Fixpoint chks_sb (B : list ibnd) (c s : Z) : bool :=
  match B with [] => true | b :: B' => andb (chk_sb b c s) (chks_sb B' c s) end.

Lemma chks_lit_sound : forall X W B A s, ibs_ok X W B -> chks_lit B A s = true -> disjoint_from W A s.
Proof.
  intros X W. induction W as [|[lo hi] W IH]; intros [|b B] A s Hok Hc; cbn in *; try exact I; try contradiction.
  apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2]. destruct Hok as [Hb HB].
  split; [eapply chk_lit_sound; eauto | eapply IH; eauto].
Qed.

Lemma chks_sb_sound : forall X W B c s, ibs_ok X W B -> chks_sb B c s = true -> disjoint_from W (X + c) s.
Proof.
  intros X W. induction W as [|[lo hi] W IH]; intros [|b B] c s Hok Hc; cbn in *; try exact I; try contradiction.
  apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2]. destruct Hok as [Hb HB].
  split; [eapply chk_sb_sound; eauto | eapply IH; eauto].
Qed.

Lemma chks_sb0_sound : forall X W B s, ibs_ok X W B -> chks_sb B 0 s = true -> disjoint_from W X s.
Proof. intros X W B s Hok Hc. pose proof (chks_sb_sound X W B 0 s Hok Hc) as D. rewrite Z.add_0_r in D. exact D. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition store_ctx (a n X : Z) (b : ibnd) : Prop :=
  (0 <= a)%Z /\ (a + n <= 2^64)%Z /\ ib_ok X a (a + n) b.

Lemma store_ctx_intro : forall a n X b,
  (0 <= a)%Z -> (a + n <= 2^64)%Z -> ib_ok X a (a + n) b -> store_ctx a n X b.
Proof. intros a n X b Ha Hl Hb. exact (conj Ha (conj Hl Hb)). Qed.

Lemma rw_cells_frame_lit : forall m a bs X b A cs,
  store_ctx a (Z.of_nat (length bs)) X b -> rw_cells segs m A cs ->
  chk_lit b A (Z.of_nat (cells_size cs)) = true ->
  rw_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H Hc. apply rw_cells_frame; auto. eapply chk_lit_sound; eauto. Qed.

Lemma rw_cells_frame_sb : forall m a bs X b c cs,
  store_ctx a (Z.of_nat (length bs)) X b -> rw_cells segs m (X + c) cs ->
  chk_sb b c (Z.of_nat (cells_size cs)) = true ->
  rw_cells segs (write_to_mem m (wa a) bs) (X + c) cs.
Proof. intros m a bs X b c cs (Ha & Hl & Hb) H Hc. apply rw_cells_frame; auto. eapply chk_sb_sound; eauto. Qed.

Lemma rw_cells_frame_sb0 : forall m a bs X b cs,
  store_ctx a (Z.of_nat (length bs)) X b -> rw_cells segs m X cs ->
  chk_sb b 0 (Z.of_nat (cells_size cs)) = true ->
  rw_cells segs (write_to_mem m (wa a) bs) X cs.
Proof. intros m a bs X b cs (Ha & Hl & Hb) H Hc. apply rw_cells_frame; auto. eapply chk_sb0_sound; eauto. Qed.

(* [comment removed for export] *)
Lemma rw_cells_frame_h : forall m a bs X b A cs,
  store_ctx a (Z.of_nat (length bs)) X b -> rw_cells segs m A cs ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  rw_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H Hd. apply rw_cells_frame; auto. Qed.

Lemma ro_cells_frame_lit : forall m a bs X b A cs,
  store_ctx a (Z.of_nat (length bs)) X b -> ro_cells segs m A cs ->
  chk_lit b A (Z.of_nat (cells_size cs)) = true ->
  ro_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H Hc. apply ro_cells_frame; auto. eapply chk_lit_sound; eauto. Qed.
Lemma ro_cells_frame_sb : forall m a bs X b c cs,
  store_ctx a (Z.of_nat (length bs)) X b -> ro_cells segs m (X + c) cs ->
  chk_sb b c (Z.of_nat (cells_size cs)) = true ->
  ro_cells segs (write_to_mem m (wa a) bs) (X + c) cs.
Proof. intros m a bs X b c cs (Ha & Hl & Hb) H Hc. apply ro_cells_frame; auto. eapply chk_sb_sound; eauto. Qed.
Lemma ro_cells_frame_sb0 : forall m a bs X b cs,
  store_ctx a (Z.of_nat (length bs)) X b -> ro_cells segs m X cs ->
  chk_sb b 0 (Z.of_nat (cells_size cs)) = true ->
  ro_cells segs (write_to_mem m (wa a) bs) X cs.
Proof. intros m a bs X b cs (Ha & Hl & Hb) H Hc. apply ro_cells_frame; auto. eapply chk_sb0_sound; eauto. Qed.
Lemma ro_cells_frame_h : forall m a bs X b A cs,
  store_ctx a (Z.of_nat (length bs)) X b -> ro_cells segs m A cs ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  ro_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H Hd. apply ro_cells_frame; auto. Qed.

Lemma bytes_at_write_other_lit : forall m a bs X b A cs,
  store_ctx a (Z.of_nat (length bs)) X b -> bytes_at segs m A cs ->
  chk_lit b A (Z.of_nat (length cs)) = true ->
  bytes_at segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H Hc. apply bytes_at_write_other; auto. eapply chk_lit_sound; eauto. Qed.
Lemma bytes_at_write_other_sb : forall m a bs X b c cs,
  store_ctx a (Z.of_nat (length bs)) X b -> bytes_at segs m (X + c) cs ->
  chk_sb b c (Z.of_nat (length cs)) = true ->
  bytes_at segs (write_to_mem m (wa a) bs) (X + c) cs.
Proof. intros m a bs X b c cs (Ha & Hl & Hb) H Hc. apply bytes_at_write_other; auto. eapply chk_sb_sound; eauto. Qed.
Lemma bytes_at_write_other_sb0 : forall m a bs X b cs,
  store_ctx a (Z.of_nat (length bs)) X b -> bytes_at segs m X cs ->
  chk_sb b 0 (Z.of_nat (length cs)) = true ->
  bytes_at segs (write_to_mem m (wa a) bs) X cs.
Proof. intros m a bs X b cs (Ha & Hl & Hb) H Hc. apply bytes_at_write_other; auto. eapply chk_sb0_sound; eauto. Qed.
Lemma bytes_at_write_other_h : forall m a bs X b A cs,
  store_ctx a (Z.of_nat (length bs)) X b -> bytes_at segs m A cs ->
  (A + Z.of_nat (length cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  bytes_at segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H Hd. apply bytes_at_write_other; auto. Qed.

Lemma u8arr_frame_lit : forall m a bs X b A xs,
  store_ctx a (Z.of_nat (length bs)) X b -> u8arr segs m A xs ->
  chk_lit b A (Z.of_nat (length xs)) = true ->
  u8arr segs (write_to_mem m (wa a) bs) A xs.
Proof. intros m a bs X b A xs (Ha & Hl & Hb) H Hc. apply u8arr_frame; auto. eapply chk_lit_sound; eauto. Qed.
Lemma u8arr_frame_sb : forall m a bs X b c xs,
  store_ctx a (Z.of_nat (length bs)) X b -> u8arr segs m (X + c) xs ->
  chk_sb b c (Z.of_nat (length xs)) = true ->
  u8arr segs (write_to_mem m (wa a) bs) (X + c) xs.
Proof. intros m a bs X b c xs (Ha & Hl & Hb) H Hc. apply u8arr_frame; auto. eapply chk_sb_sound; eauto. Qed.
Lemma u8arr_frame_sb0 : forall m a bs X b xs,
  store_ctx a (Z.of_nat (length bs)) X b -> u8arr segs m X xs ->
  chk_sb b 0 (Z.of_nat (length xs)) = true ->
  u8arr segs (write_to_mem m (wa a) bs) X xs.
Proof. intros m a bs X b xs (Ha & Hl & Hb) H Hc. apply u8arr_frame; auto. eapply chk_sb0_sound; eauto. Qed.
Lemma u8arr_frame_h : forall m a bs X b A xs,
  store_ctx a (Z.of_nat (length bs)) X b -> u8arr segs m A xs ->
  (A + Z.of_nat (length xs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  u8arr segs (write_to_mem m (wa a) bs) A xs.
Proof. intros m a bs X b A xs (Ha & Hl & Hb) H Hd. apply u8arr_frame; auto. Qed.

Lemma u32arr_frame_lit : forall m a bs X b A ws,
  store_ctx a (Z.of_nat (length bs)) X b -> u32arr segs m A ws ->
  chk_lit b A (4 * Z.of_nat (length ws)) = true ->
  u32arr segs (write_to_mem m (wa a) bs) A ws.
Proof. intros m a bs X b A ws (Ha & Hl & Hb) H Hc. apply u32arr_frame; auto. eapply chk_lit_sound; eauto. Qed.
Lemma u32arr_frame_sb : forall m a bs X b c ws,
  store_ctx a (Z.of_nat (length bs)) X b -> u32arr segs m (X + c) ws ->
  chk_sb b c (4 * Z.of_nat (length ws)) = true ->
  u32arr segs (write_to_mem m (wa a) bs) (X + c) ws.
Proof. intros m a bs X b c ws (Ha & Hl & Hb) H Hc. apply u32arr_frame; auto. eapply chk_sb_sound; eauto. Qed.
Lemma u32arr_frame_sb0 : forall m a bs X b ws,
  store_ctx a (Z.of_nat (length bs)) X b -> u32arr segs m X ws ->
  chk_sb b 0 (4 * Z.of_nat (length ws)) = true ->
  u32arr segs (write_to_mem m (wa a) bs) X ws.
Proof. intros m a bs X b ws (Ha & Hl & Hb) H Hc. apply u32arr_frame; auto. eapply chk_sb0_sound; eauto. Qed.
Lemma u32arr_frame_h : forall m a bs X b A ws,
  store_ctx a (Z.of_nat (length bs)) X b -> u32arr segs m A ws ->
  (A + 4 * Z.of_nat (length ws) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  u32arr segs (write_to_mem m (wa a) bs) A ws.
Proof. intros m a bs X b A ws (Ha & Hl & Hb) H Hd. apply u32arr_frame; auto. Qed.

Lemma u64arr_frame_lit : forall m a bs X b A ws,
  store_ctx a (Z.of_nat (length bs)) X b -> u64arr segs m A ws ->
  chk_lit b A (8 * Z.of_nat (length ws)) = true ->
  u64arr segs (write_to_mem m (wa a) bs) A ws.
Proof. intros m a bs X b A ws (Ha & Hl & Hb) H Hc. apply u64arr_frame; auto. eapply chk_lit_sound; eauto. Qed.
Lemma u64arr_frame_sb : forall m a bs X b c ws,
  store_ctx a (Z.of_nat (length bs)) X b -> u64arr segs m (X + c) ws ->
  chk_sb b c (8 * Z.of_nat (length ws)) = true ->
  u64arr segs (write_to_mem m (wa a) bs) (X + c) ws.
Proof. intros m a bs X b c ws (Ha & Hl & Hb) H Hc. apply u64arr_frame; auto. eapply chk_sb_sound; eauto. Qed.
Lemma u64arr_frame_sb0 : forall m a bs X b ws,
  store_ctx a (Z.of_nat (length bs)) X b -> u64arr segs m X ws ->
  chk_sb b 0 (8 * Z.of_nat (length ws)) = true ->
  u64arr segs (write_to_mem m (wa a) bs) X ws.
Proof. intros m a bs X b ws (Ha & Hl & Hb) H Hc. apply u64arr_frame; auto. eapply chk_sb0_sound; eauto. Qed.
Lemma u64arr_frame_h : forall m a bs X b A ws,
  store_ctx a (Z.of_nat (length bs)) X b -> u64arr segs m A ws ->
  (A + 8 * Z.of_nat (length ws) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  u64arr segs (write_to_mem m (wa a) bs) A ws.
Proof. intros m a bs X b A ws (Ha & Hl & Hb) H Hd. apply u64arr_frame; auto. Qed.

Lemma u8ro_frame_lit : forall m a bs X b A xs,
  store_ctx a (Z.of_nat (length bs)) X b -> u8ro segs m A xs ->
  chk_lit b A (Z.of_nat (length xs)) = true ->
  u8ro segs (write_to_mem m (wa a) bs) A xs.
Proof. intros m a bs X b A xs (Ha & Hl & Hb) H Hc. apply u8ro_frame; auto. eapply chk_lit_sound; eauto. Qed.
Lemma u8ro_frame_sb : forall m a bs X b c xs,
  store_ctx a (Z.of_nat (length bs)) X b -> u8ro segs m (X + c) xs ->
  chk_sb b c (Z.of_nat (length xs)) = true ->
  u8ro segs (write_to_mem m (wa a) bs) (X + c) xs.
Proof. intros m a bs X b c xs (Ha & Hl & Hb) H Hc. apply u8ro_frame; auto. eapply chk_sb_sound; eauto. Qed.
Lemma u8ro_frame_sb0 : forall m a bs X b xs,
  store_ctx a (Z.of_nat (length bs)) X b -> u8ro segs m X xs ->
  chk_sb b 0 (Z.of_nat (length xs)) = true ->
  u8ro segs (write_to_mem m (wa a) bs) X xs.
Proof. intros m a bs X b xs (Ha & Hl & Hb) H Hc. apply u8ro_frame; auto. eapply chk_sb0_sound; eauto. Qed.
Lemma u8ro_frame_h : forall m a bs X b A xs,
  store_ctx a (Z.of_nat (length bs)) X b -> u8ro segs m A xs ->
  (A + Z.of_nat (length xs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  u8ro segs (write_to_mem m (wa a) bs) A xs.
Proof. intros m a bs X b A xs (Ha & Hl & Hb) H Hd. apply u8ro_frame; auto. Qed.

Lemma stk_write_h : forall m lo hi a bs X b,
  store_ctx a (Z.of_nat (length bs)) X b -> stk segs m lo hi -> stk segs (write_to_mem m (wa a) bs) lo hi.
Proof. intros m lo hi a bs X b (Ha & Hl & Hb) H. apply stk_write; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition call_ctx (m m' : word -> option byte) (X : Z) (B : list ibnd) : Prop :=
  exists W, munch W m m' /\ wmono segs m m' /\ ibs_ok X W B.

Lemma call_ctx_intro : forall W m m' X B,
  munch W m m' -> wmono segs m m' -> ibs_ok X W B -> call_ctx m m' X B.
Proof. intros W m m0 X B MU WM HB. exists W. exact (conj MU (conj WM HB)). Qed.

Lemma bytes_at_transport_lit : forall m m' X B A bs,
  call_ctx m m' X B -> bytes_at segs m A bs -> chks_lit B A (Z.of_nat (length bs)) = true -> bytes_at segs m' A bs.
Proof. intros m m' X B A bs (W & MU & WM & HB) H Hc. eapply bytes_at_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma bytes_at_transport_sb : forall m m' X B c bs,
  call_ctx m m' X B -> bytes_at segs m (X + c) bs -> chks_sb B c (Z.of_nat (length bs)) = true -> bytes_at segs m' (X + c) bs.
Proof. intros m m' X B c bs (W & MU & WM & HB) H Hc. eapply bytes_at_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma bytes_at_transport_sb0 : forall m m' X B bs,
  call_ctx m m' X B -> bytes_at segs m X bs -> chks_sb B 0 (Z.of_nat (length bs)) = true -> bytes_at segs m' X bs.
Proof. intros m m' X B bs (W & MU & WM & HB) H Hc. eapply bytes_at_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

Lemma rw_cells_transport_lit : forall m m' X B A cs,
  call_ctx m m' X B -> rw_cells segs m A cs -> chks_lit B A (Z.of_nat (cells_size cs)) = true -> rw_cells segs m' A cs.
Proof. intros m m' X B A cs (W & MU & WM & HB) H Hc. eapply rw_cells_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma rw_cells_transport_sb : forall m m' X B c cs,
  call_ctx m m' X B -> rw_cells segs m (X + c) cs -> chks_sb B c (Z.of_nat (cells_size cs)) = true -> rw_cells segs m' (X + c) cs.
Proof. intros m m' X B c cs (W & MU & WM & HB) H Hc. eapply rw_cells_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma rw_cells_transport_sb0 : forall m m' X B cs,
  call_ctx m m' X B -> rw_cells segs m X cs -> chks_sb B 0 (Z.of_nat (cells_size cs)) = true -> rw_cells segs m' X cs.
Proof. intros m m' X B cs (W & MU & WM & HB) H Hc. eapply rw_cells_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

Lemma ro_cells_transport_lit : forall m m' X B A cs,
  call_ctx m m' X B -> ro_cells segs m A cs -> chks_lit B A (Z.of_nat (cells_size cs)) = true -> ro_cells segs m' A cs.
Proof. intros m m' X B A cs (W & MU & WM & HB) H Hc. eapply ro_cells_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma ro_cells_transport_sb : forall m m' X B c cs,
  call_ctx m m' X B -> ro_cells segs m (X + c) cs -> chks_sb B c (Z.of_nat (cells_size cs)) = true -> ro_cells segs m' (X + c) cs.
Proof. intros m m' X B c cs (W & MU & WM & HB) H Hc. eapply ro_cells_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma ro_cells_transport_sb0 : forall m m' X B cs,
  call_ctx m m' X B -> ro_cells segs m X cs -> chks_sb B 0 (Z.of_nat (cells_size cs)) = true -> ro_cells segs m' X cs.
Proof. intros m m' X B cs (W & MU & WM & HB) H Hc. eapply ro_cells_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

Lemma u8arr_transport_lit : forall m m' X B A xs,
  call_ctx m m' X B -> u8arr segs m A xs -> chks_lit B A (Z.of_nat (length xs)) = true -> u8arr segs m' A xs.
Proof. intros m m' X B A xs (W & MU & WM & HB) H Hc. eapply u8arr_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma u8arr_transport_sb : forall m m' X B c xs,
  call_ctx m m' X B -> u8arr segs m (X + c) xs -> chks_sb B c (Z.of_nat (length xs)) = true -> u8arr segs m' (X + c) xs.
Proof. intros m m' X B c xs (W & MU & WM & HB) H Hc. eapply u8arr_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma u8arr_transport_sb0 : forall m m' X B xs,
  call_ctx m m' X B -> u8arr segs m X xs -> chks_sb B 0 (Z.of_nat (length xs)) = true -> u8arr segs m' X xs.
Proof. intros m m' X B xs (W & MU & WM & HB) H Hc. eapply u8arr_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

Lemma u32arr_transport_lit : forall m m' X B A ws,
  call_ctx m m' X B -> u32arr segs m A ws -> chks_lit B A (4 * Z.of_nat (length ws)) = true -> u32arr segs m' A ws.
Proof. intros m m' X B A ws (W & MU & WM & HB) H Hc. eapply u32arr_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma u32arr_transport_sb : forall m m' X B c ws,
  call_ctx m m' X B -> u32arr segs m (X + c) ws -> chks_sb B c (4 * Z.of_nat (length ws)) = true -> u32arr segs m' (X + c) ws.
Proof. intros m m' X B c ws (W & MU & WM & HB) H Hc. eapply u32arr_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma u32arr_transport_sb0 : forall m m' X B ws,
  call_ctx m m' X B -> u32arr segs m X ws -> chks_sb B 0 (4 * Z.of_nat (length ws)) = true -> u32arr segs m' X ws.
Proof. intros m m' X B ws (W & MU & WM & HB) H Hc. eapply u32arr_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

Lemma u64arr_transport_lit : forall m m' X B A ws,
  call_ctx m m' X B -> u64arr segs m A ws -> chks_lit B A (8 * Z.of_nat (length ws)) = true -> u64arr segs m' A ws.
Proof. intros m m' X B A ws (W & MU & WM & HB) H Hc. eapply u64arr_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma u64arr_transport_sb : forall m m' X B c ws,
  call_ctx m m' X B -> u64arr segs m (X + c) ws -> chks_sb B c (8 * Z.of_nat (length ws)) = true -> u64arr segs m' (X + c) ws.
Proof. intros m m' X B c ws (W & MU & WM & HB) H Hc. eapply u64arr_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma u64arr_transport_sb0 : forall m m' X B ws,
  call_ctx m m' X B -> u64arr segs m X ws -> chks_sb B 0 (8 * Z.of_nat (length ws)) = true -> u64arr segs m' X ws.
Proof. intros m m' X B ws (W & MU & WM & HB) H Hc. eapply u64arr_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

Lemma u8ro_transport_lit : forall m m' X B A xs,
  call_ctx m m' X B -> u8ro segs m A xs -> chks_lit B A (Z.of_nat (length xs)) = true -> u8ro segs m' A xs.
Proof. intros m m' X B A xs (W & MU & WM & HB) H Hc. eapply u8ro_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma u8ro_transport_sb : forall m m' X B c xs,
  call_ctx m m' X B -> u8ro segs m (X + c) xs -> chks_sb B c (Z.of_nat (length xs)) = true -> u8ro segs m' (X + c) xs.
Proof. intros m m' X B c xs (W & MU & WM & HB) H Hc. eapply u8ro_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma u8ro_transport_sb0 : forall m m' X B xs,
  call_ctx m m' X B -> u8ro segs m X xs -> chks_sb B 0 (Z.of_nat (length xs)) = true -> u8ro segs m' X xs.
Proof. intros m m' X B xs (W & MU & WM & HB) H Hc. eapply u8ro_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

End WithSegs.

Lemma munch_write_h : forall W m0 m a bs X b,
  store_ctx a (Z.of_nat (length bs)) X b -> munch W m0 m -> inside W a (Z.of_nat (length bs)) ->
  munch W m0 (write_to_mem m (wa a) bs).
Proof. intros W m0 m a bs X b (Ha & Hl & Hb) H Hin. apply munch_write; auto. Qed.

(* [comment removed for export] *)
Lemma store_lb_of_bound : forall A sz k n,
  (0 <= A /\ A + sz <= 2^64)%Z -> andb (Z.leb 0 k) (Z.leb (k + n) sz) = true -> (0 <= A + k)%Z.
Proof. intros A sz k n [H1 H2] Hc. apply Bool.andb_true_iff in Hc. destruct Hc as [Hc _]. apply Z.leb_le in Hc. lia. Qed.
Lemma store_ub_of_bound : forall A sz k n,
  (0 <= A /\ A + sz <= 2^64)%Z -> andb (Z.leb 0 k) (Z.leb (k + n) sz) = true -> (A + k + n <= 2^64)%Z.
Proof. intros A sz k n [H1 H2] Hc. apply Bool.andb_true_iff in Hc. destruct Hc as [_ Hc]. apply Z.leb_le in Hc. lia. Qed.

(* [comment removed for export] *)
Record wdesc := WD { wd_l : option Z; wd_h : option Z; wd_lo : option Z; wd_hi : option Z }.
Definition wd_ok (X lo hi : Z) (w : wdesc) : Prop :=
  opt_holds (wd_l w) (fun l => lo = X + l)%Z /\ opt_holds (wd_h w) (fun h => hi = X + h)%Z /\
  opt_holds (wd_lo w) (fun v => lo = v)%Z /\ opt_holds (wd_hi w) (fun v => hi = v)%Z.
Fixpoint wds_ok (X : Z) (W : list ivl) (D : list wdesc) : Prop :=
  match W, D with
  | [], [] => True
  | (lo, hi) :: W', w :: D' => wd_ok X lo hi w /\ wds_ok X W' D'
  | _, _ => False
  end.
(* [comment removed for export] *)
Definition chk_inside1 (w : wdesc) (b : ibnd) (n : Z) : bool :=
  orb (match ib_l b, wd_l w, wd_h w with
       | Some d, Some l, Some h => andb (Z.leb l d) (Z.leb (d + n) h)
       | _, _, _ => false
       end)
      (match ib_L b, ib_U b, wd_lo w, wd_hi w with
       | Some L, Some U, Some lo, Some hi => andb (Z.leb lo L) (Z.leb U hi)
       | _, _, _, _ => false
       end).
Fixpoint chk_inside (D : list wdesc) (b : ibnd) (n : Z) : bool :=
  match D with [] => false | w :: D' => orb (chk_inside1 w b n) (chk_inside D' b n) end.

Lemma chk_inside_sound : forall X a n b W D,
  ib_ok X a (a + n) b -> wds_ok X W D -> chk_inside D b n = true -> inside W a n.
Proof.
  intros X a n [l h L U PQ] W. induction W as [|[lo hi] W IH]; intros [|w D] Hb Hok Hc; cbn in *;
    try discriminate; try contradiction.
  destruct Hok as [Hw HD]. apply Bool.orb_true_iff in Hc. destruct Hc as [Hc|Hc]; [left|right; eauto].
  destruct w as [wl wh wlo whi]. destruct Hb as (Hl & Hh & HL & HU & _). destruct Hw as (H1 & H2 & H3 & H4). cbn in *.
  apply Bool.orb_true_iff in Hc. destruct Hc as [Hc|Hc].
  - destruct l as [d|]; [|discriminate]. destruct wl as [wl|]; [|discriminate]. destruct wh as [wh|]; [|discriminate].
    cbn in *. apply Bool.andb_true_iff in Hc. destruct Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
  - destruct L as [L|]; [|discriminate]. destruct U as [U|]; [|discriminate].
    destruct wlo as [wlo|]; [|discriminate]. destruct whi as [whi|]; [|discriminate].
    cbn in *. apply Bool.andb_true_iff in Hc. destruct Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.

Lemma munch_write_wd : forall W m0 m a bs X b D,
  store_ctx a (Z.of_nat (length bs)) X b -> wds_ok X W D -> munch W m0 m ->
  chk_inside D b (Z.of_nat (length bs)) = true ->
  munch W m0 (write_to_mem m (wa a) bs).
Proof.
  intros W m0 m a bs X b D (Ha & Hl & Hb) HD H Hc. apply munch_write; auto.
  eapply chk_inside_sound; eauto.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Module DietL2.
  Import Ltac2.
  Ltac2 rec is_pos_lit (c : constr) : bool :=
    lazy_match! c with xI ?p => is_pos_lit p | xO ?p => is_pos_lit p | xH => true | _ => false end.
  Ltac2 is_z_lit (c : constr) : bool :=
    lazy_match! c with Z0 => true | Zpos ?p => is_pos_lit p | Zneg ?p => is_pos_lit p | _ => false end.
  Ltac2 size_lit (sz : constr) : constr option :=
    let v := eval cbv beta iota zeta delta
      [cells_size csize length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes u32s u64s
       Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Z.add Pos.add] in $sz in
    if is_z_lit v then Some v else None.
  Ltac2 chunk_of (ty : constr) : (constr * constr) option :=
    lazy_match! ty with
    | rw_cells _ _ ?a ?cs => Some (a, constr:(Z.of_nat (cells_size $cs)))
    | ro_cells _ _ ?a ?cs => Some (a, constr:(Z.of_nat (cells_size $cs)))
    | bytes_at _ _ ?a ?bs => Some (a, constr:(Z.of_nat (@length byte $bs)))
    | u8arr _ _ ?a ?bs => Some (a, constr:(Z.of_nat (@length byte $bs)))
    | u8ro _ _ ?a ?bs => Some (a, constr:(Z.of_nat (@length byte $bs)))
    | u32arr _ _ ?a ?ws => Some (a, constr:((4 * Z.of_nat (@length word $ws))%Z))
    | u64arr _ _ ?a ?ws => Some (a, constr:((8 * Z.of_nat (@length word $ws))%Z))
    | _ => None
    end.
  Ltac2 hull () : unit :=
    let cands := List.map_filter (fun h => let (_, _, ty) := h in
        match chunk_of ty with
        | None => None
        | Some p => let (a, sz) := p in
            if is_z_lit a then match size_lit sz with Some s => Some (a, s) | None => None end else None
        end) (Control.hyps ()) in
    match cands with
    | [] => ltac1:(pose (diet_hull := @None (Z * Z)))
    | c :: rest =>
        let (a0, s0) := c in
        let smin := List.fold_left (fun acc c => let (a, _) := c in Std.eval_vm None constr:(Z.min $acc $a)) a0 rest in
        let emax := List.fold_left (fun acc c => let (a, s) := c in Std.eval_vm None constr:(Z.max $acc ($a + $s)%Z))
                      (Std.eval_vm None constr:(($a0 + $s0)%Z)) rest in
        let v := constr:(@Some (Z * Z) ($smin, $emax)) in
        ltac1:(v |- pose (diet_hull := v)) (Ltac1.of_constr v)
    end.
  Ltac2 hull1 () : unit := Control.enter hull.
End DietL2.
Ltac diet_hull k :=
  ltac2:(DietL2.hull1 ());
  lazymatch goal with D := ?v : option (Z * Z) |- _ => clear D; k v end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac pos_lit_chk p := lazymatch p with xI ?q => pos_lit_chk q | xO ?q => pos_lit_chk q | xH => constr:(tt) end.
Ltac size_lit sz :=
  let v := eval cbv beta iota zeta delta
      [cells_size csize length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes u32s u64s
       Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Z.add Pos.add] in sz in
  lazymatch v with Z0 => v | Zpos ?p => let _ := pos_lit_chk p in v | Zneg ?p => let _ := pos_lit_chk p in v end.

(* [comment removed for export] *)
Ltac len_term bs :=
  let nT := constr:(Z.of_nat (@length byte bs)) in
  match nT with _ => size_lit nT | _ => nT end.

(* [comment removed for export] *)
Ltac zval a :=
  lazymatch a with
  | Z.add ?x ?y => let u := zval x in let v := zval y in eval vm_compute in (u + v)%Z
  | Z.sub ?x ?y => let u := zval x in let v := zval y in eval vm_compute in (u - v)%Z
  | _ => zlit_of a
  end.

(* [comment removed for export] *)
Ltac store_ctx_of_facts full a bs Ha Hl hullprover k :=
  let Hd := fresh "dHd" in let HPQ := fresh "dHPQ" in let SC := fresh "dSC" in
  let nT := constr:(Z.of_nat (@length byte bs)) in
  let n := len_term bs in
  sb_split a ltac:(fun X d pfd =>
    (* [comment removed for export] *)
    try (assert (Hd : dfact (a = (X + d)%Z)) by exact pfd);
    (* [comment removed for export] *)
    let av := match constr:(tt) with _ => let v := zval a in constr:(@Some Z v) | _ => constr:(@None Z) end in
    lazymatch full with
    | true =>
        lazymatch av with
        | Some _ => idtac
        | None => diet_hull ltac:(fun hv =>
                    lazymatch hv with
                    | Some (?smin, ?emax) => try (assert (HPQ : dfact (a + nT <= smin \/ emax <= a)%Z) by (unfold dfact; hullprover))
                    | None => idtac
                    end)
        end
    | false => idtac
    end;
    (* [comment removed for export] *)
    let l := lazymatch goal with _ : dfact (a = (X + d)%Z) |- _ => constr:(@Some Z d) | _ => constr:(@None Z) end in
    let h := lazymatch l with
             | Some _ => match n with
                         | Z.of_nat _ => constr:(@None Z)
                         | _ => let e := eval vm_compute in (d + n)%Z in constr:(@Some Z e)
                         end
             | _ => constr:(@None Z)
             end in
    let U := lazymatch av with
             | Some ?v => match n with
                          | Z.of_nat _ => constr:(@None Z)
                          | _ => let e := eval vm_compute in (v + n)%Z in constr:(@Some Z e)
                          end
             | None => constr:(@None Z)
             end in
    let PQ := lazymatch goal with
              | _ : dfact (a + nT <= ?smin \/ ?emax <= a)%Z |- _ => constr:(@Some (Z * Z) (smin, emax))
              | _ => constr:(@None (Z * Z))
              end in
    let b := constr:(IB l h av U PQ) in
    assert (SC : store_ctx a nT X b);
    [ apply store_ctx_intro; [ exact Ha | exact Hl | ];
      cbv beta iota delta [ib_ok opt_holds ib_l ib_h ib_L ib_U ib_PQ];
      split; [ | split; [ | split; [ | split ] ] ];
      [ (* [comment removed for export] *) first [ exact I | lazymatch goal with |- ?G => lazymatch goal with Hf : dfact G |- _ => exact Hf end end ]
      | (* [comment removed for export] *) first [ exact I
                      | lazymatch goal with Hf : dfact (a = (X + d)%Z) |- _ =>
                          exact (@eq_trans Z (a + n)%Z (X + d + n)%Z (X + (d + n))%Z
                                 (@f_equal Z Z (fun t => (t + n)%Z) a (X + d)%Z Hf)
                                 (@eq_sym Z (X + (d + n))%Z (X + d + n)%Z (Z.add_assoc X d n)))
                        end ]
      | (* [comment removed for export] *) first [ exact I | lazymatch goal with |- (?v <= _)%Z => exact (Z.le_refl v) end ]
      | (* [comment removed for export] *) first [ exact I | lazymatch goal with |- (_ <= ?v)%Z => exact (Z.le_refl v) end ]
      | (* [comment removed for export] *) first [ exact I | lazymatch goal with |- ?G => lazymatch goal with Hf : dfact G |- _ => exact Hf end end ] ]
    | k SC X b;
      try clear SC; try clear HPQ; try clear Hd ]).

(* [comment removed for export] *)
Ltac store_ctx_pose full a bs k kfail :=
  let Ha := fresh "dHa" in let Hl := fresh "dHl" in
  let nT := constr:(Z.of_nat (@length byte bs)) in
  tryif (first [ lazymatch a with
                 | (?A0 + ?k)%Z =>
                     lazymatch goal with
                     | HB : (0 <= A0 /\ A0 + ?sz <= 2 ^ 64)%Z |- _ =>
                         pose proof (store_lb_of_bound A0 sz k nT HB (@eq_refl bool true)) as Ha
                     end
                 end
               | assert (Ha : (0 <= a)%Z) by lia ])
  then (
   tryif (first [ lazymatch a with
                  | (?A0 + ?k)%Z =>
                      lazymatch goal with
                      | HB : (0 <= A0 /\ A0 + ?sz <= 2 ^ 64)%Z |- _ =>
                          pose proof (store_ub_of_bound A0 sz k nT HB (@eq_refl bool true)) as Hl
                      end
                  end
                | assert (Hl : (a + nT <= 2^64)%Z) by (simpl_sizes; slia) ])
   then (store_ctx_of_facts full a bs Ha Hl ltac:(simpl_sizes; slia) k; clear Ha Hl)
   else (clear Ha; kfail))
  else kfail.

(* [comment removed for export] *)
Ltac tr_lit H lem b A2 sz :=
  is_Zlit A2;
  let s := size_lit sz in
  lazymatch eval vm_compute in (chk_lit b A2 s) with true => idtac end;
  apply lem in H; [ | exact (@eq_refl bool true) ].
Ltac tr_lits H lem B A2 sz :=
  is_Zlit A2;
  let s := size_lit sz in
  lazymatch eval vm_compute in (chks_lit B A2 s) with true => idtac end;
  apply lem in H; [ | exact (@eq_refl bool true) ].
(* [comment removed for export] *)
Ltac tr_sb H lem lem0 chk b X A2 sz :=
  let s := size_lit sz in
  lazymatch A2 with
  | Z.add X ?c => is_Zlit c; lazymatch eval vm_compute in (chk b c s) with true => idtac end;
                 apply lem in H; [ | exact (@eq_refl bool true) ]
  | X => lazymatch eval vm_compute in (chk b 0%Z s) with true => idtac end;
         apply lem0 in H; [ | exact (@eq_refl bool true) ]
  end.

Ltac transport_chunks_sc segs m a bs SC X b :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ tr_lit H (bytes_at_write_other_lit segs m a bs X b A2 bs2 SC) b A2 constr:(Z.of_nat (@length byte bs2))
            | tr_sb H (bytes_at_write_other_sb segs m a bs X b) (bytes_at_write_other_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte bs2))
            | apply (bytes_at_write_other_h segs m a bs X b A2 bs2 SC) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lit H (rw_cells_frame_lit segs m a bs X b A2 cs2 SC) b A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (rw_cells_frame_sb segs m a bs X b) (rw_cells_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (rw_cells_frame_h segs m a bs X b A2 cs2 SC) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lit H (ro_cells_frame_lit segs m a bs X b A2 cs2 SC) b A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (ro_cells_frame_sb segs m a bs X b) (ro_cells_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (ro_cells_frame_h segs m a bs X b A2 cs2 SC) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u8arr_frame_lit segs m a bs X b A2 xs SC) b A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8arr_frame_sb segs m a bs X b) (u8arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8arr_frame_h segs m a bs X b A2 xs SC) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?ws |- _ =>
      first [ tr_lit H (u32arr_frame_lit segs m a bs X b A2 ws SC) b A2 constr:((4 * Z.of_nat (@length word ws))%Z)
            | tr_sb H (u32arr_frame_sb segs m a bs X b) (u32arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:((4 * Z.of_nat (@length word ws))%Z)
            | apply (u32arr_frame_h segs m a bs X b A2 ws SC) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?ws |- _ =>
      first [ tr_lit H (u64arr_frame_lit segs m a bs X b A2 ws SC) b A2 constr:((8 * Z.of_nat (@length word ws))%Z)
            | tr_sb H (u64arr_frame_sb segs m a bs X b) (u64arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:((8 * Z.of_nat (@length word ws))%Z)
            | apply (u64arr_frame_h segs m a bs X b A2 ws SC) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u8ro_frame_lit segs m a bs X b A2 xs SC) b A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8ro_frame_sb segs m a bs X b) (u8ro_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8ro_frame_h segs m a bs X b A2 xs SC) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

(* [comment removed for export] *)
Ltac transport_chunks_orig segs m a bs :=
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
  end.
Ltac footprint_after_store_orig segs m a bs :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
Ltac wd_off X e :=
  match e with
  | X => constr:(@Some Z 0%Z)
  | Z.add X ?c => let c' := zlit_of c in constr:(@Some Z c')
  | Z.sub X ?c => let c' := zlit_of c in let v := eval vm_compute in (- c')%Z in constr:(@Some Z v)
  | _ => constr:(@None Z)
  end.
Ltac wd_lit e := match e with _ => let v := zlit_of e in constr:(@Some Z v) | _ => constr:(@None Z) end.
Ltac wdesc_of X W :=
  lazymatch W with
  | nil => constr:(@nil wdesc)
  | cons (?lo, ?hi) ?W' =>
      let l := wd_off X lo in let h := wd_off X hi in
      let vlo := wd_lit lo in let vhi := wd_lit hi in
      let D' := wdesc_of X W' in constr:(@cons wdesc (WD l h vlo vhi) D')
  end.

Ltac footprint_after_store_sc segs m a bs SC X b :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ let D := wdesc_of X Wq in
              let n := size_lit constr:(Z.of_nat (@length byte bs)) in
              lazymatch eval vm_compute in (chk_inside D b n) with true => idtac end;
              let WDH := fresh "dWD" in
              assert (WDH : wds_ok X Wq D) by
                (cbv beta iota delta [wds_ok wd_ok opt_holds wd_l wd_h wd_lo wd_hi];
                 repeat match goal with |- _ /\ _ => split end;
                 first [ exact I | reflexivity | symmetry; apply Z.add_0_r ]);
              apply (munch_write_wd Wq mq m a bs X b D SC WDH) in MU; [ | exact (@eq_refl bool true) ];
              clear WDH
            | apply (munch_write_h Wq mq m a bs X b SC) in MU; [ | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ => apply (stk_write_h segs m loq hiq a bs X b SC) in STq
  end.

(* [comment removed for export] *)
Ltac transport_chunks segs m a bs ::=
  lazymatch goal with
  | SC : store_ctx a _ ?X ?b |- _ => transport_chunks_sc segs m a bs SC X b
  | _ => store_ctx_pose true a bs ltac:(fun SC X b => transport_chunks_sc segs m a bs SC X b)
                                ltac:(transport_chunks_orig segs m a bs)
  end.
Ltac footprint_after_store segs m a bs :=
  lazymatch goal with
  | SC : store_ctx a _ ?X ?b |- _ => footprint_after_store_sc segs m a bs SC X b
  | _ => store_ctx_pose true a bs ltac:(fun SC X b => footprint_after_store_sc segs m a bs SC X b)
                                ltac:(footprint_after_store_orig segs m a bs)
  end.

Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          store_ctx_pose true (A + Z.of_nat kn)%Z (cbytes c')
            ltac:(fun _ _ _ => transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
                               footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c'))
            ltac:(transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
                  footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c'));
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ib_of_call X lo hi PQ :=
  let l := wd_off X lo in let h := wd_off X hi in
  let L := wd_lit lo in let U := wd_lit hi in
  constr:(IB l h L U PQ).

(* [comment removed for export] *)
Ltac ivl_is_lit lo hi := is_zlit_term lo; is_zlit_term hi.

(* [comment removed for export] *)
Ltac ibs_of_call X W hv prover k :=
  lazymatch W with
  | nil => k constr:(@nil ibnd) ltac:(idtac)
  | cons (?lo, ?hi) ?W' =>
      let Hn := fresh "dCPQ" in
      (lazymatch hv with
       | Some (?smin, ?emax) =>
           first [ ivl_is_lit lo hi | assert (Hn : dfact (hi <= smin \/ emax <= lo)%Z) by (unfold dfact; prover) | idtac ]
       | None => idtac
       end);
      let PQ := lazymatch hv with
                | Some (?smin, ?emax) =>
                    lazymatch goal with
                    | _ : dfact (hi <= smin \/ emax <= lo)%Z |- _ => constr:(@Some (Z * Z) (smin, emax))
                    | _ => constr:(@None (Z * Z))
                    end
                | None => constr:(@None (Z * Z))
                end in
      let b := ib_of_call X lo hi PQ in
      ibs_of_call X W' hv prover ltac:(fun B' kc => k constr:(@cons ibnd b B') ltac:(kc; try clear Hn))
  end.

(* [comment removed for export] *)
Ltac base_of_ivls W :=
  lazymatch W with
  | nil => constr:(0%Z)
  | cons (?lo, ?hi) ?W' =>
      match constr:(tt) with
      | _ => let t := match constr:(tt) with _ => is_zlit_term lo end in
             match constr:(tt) with
             | _ => let t' := match constr:(tt) with _ => is_zlit_term hi end in base_of_ivls W'
             | _ => sb_split hi ltac:(fun X d pf => X)
             end
      | _ => sb_split lo ltac:(fun X d pf => X)
      end
  end.

(* [comment removed for export] *)
Ltac call_ctx_pose segs m m' MU WM prover k kfail :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  match constr:(tt) with
  | _ =>
    let X := base_of_ivls W in
    diet_hull ltac:(fun hv =>
      ibs_of_call X W hv prover ltac:(fun B kclear =>
        let CC := fresh "dCC" in
        tryif (assert (CC : call_ctx segs m m' X B);
               [ apply (call_ctx_intro segs W m m' X B MU WM);
                 cbv beta iota delta [ibs_ok ib_ok opt_holds ib_l ib_h ib_L ib_U ib_PQ];
                 repeat match goal with |- _ /\ _ => split end;
                 first [ exact I
                       | lazymatch goal with |- ?G => lazymatch goal with Hf : dfact G |- _ => exact Hf end end
                       | reflexivity | apply Z.le_refl | symmetry; apply Z.add_0_r ]
               | ])
        then (k CC X B; clear CC; kclear)
        else (kclear; kfail)))
  | _ => kfail
  end.

Ltac transport_after_call_orig segs m m' MU WM :=
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
  end.

Ltac transport_after_call_cc segs m m' MU WM CC X B :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ tr_lits H (bytes_at_transport_lit segs m m' X B A2 bs2 CC) B A2 constr:(Z.of_nat (@length byte bs2))
            | tr_sb H (bytes_at_transport_sb segs m m' X B) (bytes_at_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte bs2))
            | apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lits H (rw_cells_transport_lit segs m m' X B A2 cs2 CC) B A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (rw_cells_transport_sb segs m m' X B) (rw_cells_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lits H (ro_cells_transport_lit segs m m' X B A2 cs2 CC) B A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (ro_cells_transport_sb segs m m' X B) (ro_cells_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u8arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8arr_transport_sb segs m m' X B) (u8arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u32arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u32arr_transport_sb segs m m' X B) (u32arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u64arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u64arr_transport_sb segs m m' X B) (u64arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u8ro_transport_lit segs m m' X B A2 xs CC) B A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8ro_transport_sb segs m m' X B) (u8ro_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac transport_after_call segs m m' MU WM :=
  call_ctx_pose segs m m' MU WM ltac:(lia)
    ltac:(fun CC X B => transport_after_call_cc segs m m' MU WM CC X B)
    ltac:(transport_after_call_orig segs m m' MU WM).

Ltac mem_after_store_opt ::=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac   (* [comment removed for export] *)
      end
  | _ => idtac
  end.

Ltac fstep := step.

Ltac fsteps n :=
  lazymatch n with
  | O => idtac
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; fsteps n'
      | _ => idtac
      end
  end.

(* [comment removed for export] *)
Ltac destruct_exs PO :=
  let T := type of PO in let T' := eval hnf in T in
  lazymatch T' with
  | ex _ => let x := fresh "x" in destruct PO as [x PO]; destruct_exs PO
  | _ => idtac
  end.

Ltac destruct_ands PO :=
  lazymatch type of PO with
  | _ /\ _ => let H := fresh "PC" in destruct PO as [H PO]; destruct_ands PO
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac post_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  (* [comment removed for export] *)
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      lazymatch eval vm_compute in (andb (Z.leb 0 n) (Z.ltb n 18446744073709551616)) with
      | true => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (apply bv_eq; vm_compute; reflexivity)
      | false => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end
  end).

Tactic Notation "call" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_call segs m ]
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac carve_frame n ST :=
  lazymatch type of ST with
  | stk ?segs ?m ?lo ?hi =>
      let junk := fresh "junk" in let FR := fresh "FR" in let ST' := fresh "ST" in
      destruct (stk_carve segs m lo hi n ST ltac:(lia)) as [ST' [junk FR]];
      clear ST; rename ST' into ST;
      let z := eval vm_compute in (Z.of_nat n) in
      change (Z.of_nat n) with z in ST, FR;
      (* [comment removed for export] *)
      repeat match type of FR with
      | context [Z.sub (Z.add ?b ?c) ?d] => is_Zlit c; is_Zlit d; let v := eval vm_compute in (c - d)%Z in
           replace (Z.sub (Z.add b c) d) with (Z.add b v) in * by lia
      | context [Z.sub ?b ?d] => is_Zlit d; let v := eval vm_compute in (- d)%Z in
           replace (Z.sub b d) with (Z.add b v) in * by lia
      end
  end.

(* [comment removed for export] *)
Fixpoint mk_CB_cells (sizes : list nat) (bs : list byte) : list cell :=
  match sizes with
  | [] => []
  | s :: sizes' => CB s (firstn s bs) :: mk_CB_cells sizes' (skipn s bs)
  end.

Fixpoint sum_nat (l : list nat) : nat := match l with [] => 0 | x :: l' => x + sum_nat l' end.

Lemma mk_CB_cells_wf : forall sizes bs, length bs = sum_nat sizes -> cells_wf (mk_CB_cells sizes bs).
Proof.
  induction sizes as [|s sizes IH]; intros bs H; cbn; [exact I|].
  cbn in H. split.
  - rewrite firstn_length. lia.
  - apply IH. rewrite skipn_length. lia.
Qed.

Lemma mk_CB_cells_bytes : forall sizes bs, length bs = sum_nat sizes -> cells_bytes (mk_CB_cells sizes bs) = bs.
Proof.
  induction sizes as [|s sizes IH]; intros bs H; cbn in *.
  - destruct bs; [reflexivity| cbn in H; lia].
  - rewrite IH by (rewrite skipn_length; lia). apply firstn_skipn.
Qed.

Lemma mk_CB_cells_size : forall sizes bs, cells_size (mk_CB_cells sizes bs) = sum_nat sizes.
Proof. induction sizes; intros; cbn; [reflexivity|]. rewrite IHsizes. reflexivity. Qed.

Lemma rw_cells_split_CB : forall segs m A pre n junk post sizes,
  rw_cells segs m A (pre ++ CB n junk :: post) -> sum_nat sizes = n ->
  rw_cells segs m A (pre ++ mk_CB_cells sizes junk ++ post).
Proof.
  intros segs m A pre n junk post sizes [[Hwf Hb] Hw] Hs.
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  assert (L : length junk = sum_nat sizes) by lia.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [apply mk_CB_cells_wf; exact L| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite mk_CB_cells_bytes by exact L. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite mk_CB_cells_size, Hs. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_merge : forall segs m A pre mid post,
  rw_cells segs m A (pre ++ mid ++ post) ->
  rw_cells segs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post).
Proof.
  intros segs m A pre mid post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 H23]. apply cells_wf_app in H23. destruct H23 as [H2 H3].
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. cbn. split; [apply cells_bytes_length; exact H2| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes]. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize]. exact Hw.
Qed.

Lemma rw_cells_forget : forall segs m A cs,
  rw_cells segs m A cs -> exists junk, rw_cells segs m A [CB (cells_size cs) junk].
Proof.
  intros segs m A cs H. exists (cells_bytes cs).
  pose proof (rw_cells_merge segs m A [] cs [] ) as M. rewrite app_nil_r in M. cbn [app] in M. apply M. exact H.
Qed.

(* [comment removed for export] *)
Ltac finish :=
  apply evt_done;
  lazymatch goal with |- ?P ?ms => try unfold P end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ reflexivity | ]
  | |- _ = _ => reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
Ltac release_frame FR ST hi :=
  eapply stk_release in FR; [ | exact ST | lia ];
  clear ST; rename FR into ST;
  cbn [cells_size csize Nat.add] in ST;
  lazymatch type of ST with
  | stk ?segs ?m ?lo ?hi' => replace hi' with hi in ST by lia
  end.

(* [comment removed for export] *)
Ltac store_done :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    (* [comment removed for export] *)
    try (lazymatch goal with
    | HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI;
        [ | first [ exact HS
                  | replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
                    first [ exact HS | simpl_sizes; exact HS ] ] ]
    end);
    (* [comment removed for export] *)
    let HBa := fresh "HBarr" in
    try (let X := lazymatch E with Z.add (Z.add ?X _) _ => X | Z.add ?X _ => X | _ => E end in
         first [ lazymatch goal with
                 | H : u32arr segs m X ?xs |- _ => pose proof (u32arr_bound segs m X xs H) as HBa
                 | H : u8arr segs m X ?xs |- _ => pose proof (u8arr_bound segs m X xs H) as HBa
                 | H : u64arr segs m X ?xs |- _ => pose proof (u64arr_bound segs m X xs H) as HBa
                 end
               | lazymatch E with Z.add (Z.add ?X2 _) _ =>
                   lazymatch goal with
                   | H : u32arr segs m X2 ?xs |- _ => pose proof (u32arr_bound segs m X2 xs H) as HBa
                   | H : u8arr segs m X2 ?xs |- _ => pose proof (u8arr_bound segs m X2 xs H) as HBa
                   | H : u64arr segs m X2 ?xs |- _ => pose proof (u64arr_bound segs m X2 xs H) as HBa
                   end
                 end ]);
    store_ctx_pose true E bs
      ltac:(fun _ _ _ => transport_chunks segs m E bs; footprint_after_store segs m E bs)
      ltac:(transport_chunks segs m E bs; footprint_after_store segs m E bs);
    try clear HBa;
    let m' := fresh "m" in
    remember (write_to_mem m (wa E) bs) as m' eqn:Heqm;
    clear Heqm;
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    try clear m
  end.
