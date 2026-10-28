(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition ATP_ELEM_A : Z := 0xb3600.
Definition ATP_OBJ_A : Z := 0xb6bf0.
Definition ATP_ARR_A : Z := 0xb6984.
Definition STR_REPLACE_A : Z := 0x113c28.
Definition STR_FIND_A : Z := 0x114190.
Definition OPNEW_A : Z := 0x167848.
Definition OPDEL_A : Z := 0x10afec.
Definition ARR_DIV10_A : Z := 0x10380.
Definition TPV : Z := 0x6abde8.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition elem_needA (d : nat) : Z := 384 * Z.of_nat d + 64 + RT_STACK.
Definition obj_needA (d : nat) : Z := 320 + elem_needA d.
Definition arr_needA (d : nat) : Z := 96 + elem_needA d.

Definition LVL_C1 : Z := 1 + 64 + 16384 + 2 * DCOST.
Definition elem_costA (d : nat) (L : Z) : Z := Z.of_nat d * LVL_C1 + 2 * L.
Definition obj_costA (d : nat) (L : Z) : Z := (Z.of_nat d + 1) * LVL_C1 + 2 * L.
Definition arr_costA (d : nat) (L : Z) : Z := Z.of_nat d * LVL_C1 + 2 * L.

Lemma mcost_le : forall n, 0 <= n -> mcost n <= 2 * n + 16384 + 2 * DCOST.
Proof. intros n H. unfold mcost. destruct (n <=? 64512); lia. Qed.
Lemma LVL_C1_val : LVL_C1 = 2113601.
Proof. reflexivity. Qed.

Record aenvA : Type := mkAEA {
  ae_lo : Z;  ae_hi : Z;
  ae_DOC : Z;  ae_fD : Z;  ae_kD : nat;
  ae_TAPE : Z;  ae_NT : Z;  ae_SBUF : Z;  ae_NS : Z;  ae_tws : list Z;  ae_sbs : list Z;
  ae_PTR : Z;  ae_p1 : list Z;  ae_PB : Z;  ae_NPB : Z }.

Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Record aenvA_ok (E : aenvA) : Prop := mkAEAok {
  ok_wf : tape_wf (ae_T E) (ae_S E) (ae_sn E) ck_any (ae_n E);
  ok_sbs : Forall (fun c => 0 <= c < 256) (ae_sbs E);
  ok_p1 : Forall (fun c => 0 <= c < 256) (ae_p1 E);
  ok_p1len : zlength (ae_p1 E) < 2^26;

  ok_tape : ae_TAPE E mod 16 = 0 /\ ae_NT E mod 8 = 0 /\ 8 * ae_n E <= ae_NT E /\ 0 < ae_TAPE E /\ ae_TAPE E + ae_NT E <= ae_lo E;
  ok_sbuf : ae_SBUF E mod 16 = 0 /\ ae_NS E mod 8 = 0 /\ ae_sn E <= ae_NS E /\ 0 < ae_SBUF E /\ ae_SBUF E + ae_NS E <= ae_lo E;

  ok_ptr : ae_p1 E <> [] -> 0 < ae_PB E /\ ae_PB E <= ae_PTR E /\ ae_PTR E + zlength (ae_p1 E) <= ae_PB E + ae_NPB E /\ ae_PB E + ae_NPB E <= ae_lo E;
  ok_ptr0 : 0 <= ae_PTR E;

  ok_doc : ae_DOC E mod 8 = 0 /\ ae_fD E <= ae_DOC E /\ ae_DOC E + 16 <= ae_fD E + fs_size (ae_kD E) - 8
           /\ SEGTOP_A <= ae_fD E /\ ae_fD E + fs_size (ae_kD E) <= ae_lo E;

  ok_lo : 0x7fff7f800000 <= ae_lo E;
  ok_hi : ae_lo E <= ae_hi E /\ ae_hi E + 16 <= USTACK_TOP }.

Definition a_live (RT : rt_sig) (Σ : rts RT) (E : aenvA) : Prop :=
  In (ae_TAPE E, ae_NT E) (rt_live RT Σ) /\ In (ae_SBUF E, ae_NS E) (rt_live RT Σ)
  /\ (ae_p1 E = [] \/ In (ae_PB E, ae_NPB E) (rt_live RT Σ))
  /\ In (ae_fD E, ae_kD E) (rt_frames RT Σ)
  /\ rt_sp0 RT Σ - STACK_WIN <= ae_lo E.

Definition AINV_A (E : aenvA) (m : mem) : Prop :=
  bytes_at bsegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E)))
  /\ bytes_at bsegs m (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E))
  /\ bytes_at bsegs m (ae_PTR E) (map (Z_to_bv 8) (ae_p1 E))
  /\ rw_cells bsegs m (ae_DOC E) [C8 (Z_to_bv 64 (ae_TAPE E)); C8 (Z_to_bv 64 (ae_SBUF E))]
  /\ bytes_at bsegs m (shad (ae_DOC E)) [z8; z8].

Definition ainv_rng (E : aenvA) (x : Z) : Prop :=
  (ae_TAPE E <= x < ae_TAPE E + 8 * ae_n E) \/ (ae_SBUF E <= x < ae_SBUF E + ae_sn E)
  \/ (ae_PTR E <= x < ae_PTR E + zlength (ae_p1 E)) \/ (ae_DOC E <= x < ae_DOC E + 16)
  \/ (shad (ae_DOC E) <= x < shad (ae_DOC E) + 2).

Lemma AINV_A_agree : forall E m m', AINV_A E m -> agree_on (ainv_rng E) m m' -> AINV_A E m'.
Proof.
  intros E m m' (H1 & H2 & H3 & H4 & H5) AG. unfold ainv_rng in AG.
  split; [| split; [| split; [| split]]].
  - apply (bytes_at_agree bsegs m m' _ _ H1). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *.
    rewrite u64s_length, length_map in Hx. lia.
  - apply (bytes_at_agree bsegs m m' _ _ H2). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. rewrite length_map in Hx. lia.
  - apply (bytes_at_agree bsegs m m' _ _ H3). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *.
    rewrite length_map in Hx. unfold zlength. lia.
  - apply (rw_cells_agree_nw bsegs m m' _ _ H4). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *.
    cbn [cells_size csize Nat.add] in Hx. lia.
  - apply (bytes_at_agree bsegs m m' _ _ H5). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn [length] in Hx. lia.
Qed.

Lemma ainv_rng_lo : forall E x, aenvA_ok E -> ainv_rng E x -> x < ae_lo E.
Proof.
  intros E x OK Hx. destruct OK as [_ _ _ _ (? & ? & ? & ? & ?) (? & ? & ? & ? & ?) PT _ (? & ? & ? & ? & ?) LO HI].
  unfold ainv_rng, zlength in *.
  assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  unfold shad, SHB, SEGTOP_A, USTACK_TOP in *.
  assert ((ae_DOC E) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia).
  destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; try lia.
  assert (NE : ae_p1 E <> []) by (intros E0; rewrite E0 in Hx; cbn [length] in Hx; lia). specialize (PT NE). lia.
Qed.

Lemma ainv_rng_aclient : forall RT Σ E sp x, a_live RT Σ E -> aenvA_ok E -> ainv_rng E x ->
  aclient (rt_live RT Σ) (rt_frames RT Σ) sp x.
Proof.
  intros RT Σ E sp x (LT & LS & LP & LF & _) OK Hx.
  destruct OK as [_ _ _ _ (? & ? & ? & ? & ?) (? & ? & ? & ? & ?) PT _ (D8 & ? & ? & ? & ?) _ _].
  unfold ainv_rng in Hx. destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]].
  - right; right; left. exists (ae_TAPE E), (ae_NT E). split; [exact LT| lia].
  - right; right; left. exists (ae_SBUF E), (ae_NS E). split; [exact LS| lia].
  - destruct LP as [E0|LP]; [rewrite E0 in Hx; unfold zlength in Hx; cbn [length] in Hx; lia|].
    assert (NE : ae_p1 E <> []) by (intros E0; rewrite E0 in Hx; unfold zlength in Hx; cbn [length] in Hx; lia). specialize (PT NE).
    right; right; left. exists (ae_PB E), (ae_NPB E). split; [exact LP| lia].
  - right; right; right; left. exists (ae_fD E), (ae_kD E). split; [exact LF| lia].
  - right; right; right; right. exists (ae_fD E), (ae_kD E). split; [exact LF|].
    unfold shad in *. pose proof (Z.div_le_mono (ae_fD E) (ae_DOC E) 8 ltac:(lia) ltac:(lia)).
    assert ((ae_DOC E) / 8 + 2 <= (ae_fD E + fs_size (ae_kD E)) / 8); [| lia].
    apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (ae_DOC E) 8 ltac:(lia)). rewrite D8 in *. lia.
Qed.

Lemma AINV_A_pres : forall RT Σ E sp m m', a_live RT Σ E -> aenvA_ok E -> AINV_A E m ->
  rt_pres (rt_live RT Σ) (rt_frames RT Σ) sp m m' -> AINV_A E m'.
Proof.
  intros RT Σ E sp m m' LV OK AI PR. apply (AINV_A_agree E m m' AI). apply (agree_of_pres _ _ _ _ _ _ PR).
  intros x Hx. exact (ainv_rng_aclient RT Σ E sp x LV OK Hx).
Qed.

Lemma AINV_A_pres_fp : forall RT Σ E sp W m m', a_live RT Σ E -> aenvA_ok E -> AINV_A E m ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) sp W m m' -> Forall (fun r => ae_lo E <= fst r) W -> AINV_A E m'.
Proof.
  intros RT Σ E sp W m m' LV OK AI PR HW. apply (AINV_A_agree E m m' AI). apply (agree_of_pres_fp _ _ _ _ _ _ _ PR).
  intros x Hx. split; [exact (ainv_rng_aclient RT Σ E sp x LV OK Hx)|].
  pose proof (ainv_rng_lo E x OK Hx) as XL. clear Hx AI PR LV.
  induction W as [|[l h] W IH]; [exact I|]. inversion HW; subst. cbn [outside fst snd] in *. split; [lia| apply IH; assumption].
Qed.

Lemma AINV_A_pres_ex : forall RT Σ E sp dd n m m', a_live RT Σ E -> aenvA_ok E -> AINV_A E m ->
  rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) sp dd n m m' -> ae_lo E <= dd -> AINV_A E m'.
Proof.
  intros RT Σ E sp dd n m m' LV OK AI PR HD. apply (AINV_A_agree E m m' AI). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR).
  intros x Hx. split; [exact (ainv_rng_aclient RT Σ E sp x LV OK Hx)|]. pose proof (ainv_rng_lo E x OK Hx). lia.
Qed.

Lemma AINV_A_munch : forall E W m m', aenvA_ok E -> AINV_A E m -> munch W m m' -> Forall (fun r => ae_lo E <= fst r) W -> AINV_A E m'.
Proof.
  intros E W m m' OK AI MU HW. apply (AINV_A_agree E m m' AI). apply (agree_of_munch _ _ _ _ MU).
  intros x Hx. pose proof (ainv_rng_lo E x OK Hx) as XL. clear Hx AI MU.
  induction W as [|[l h] W IH]; [exact I|]. inversion HW; subst. cbn [outside fst snd] in *. split; [lia| apply IH; assumption].
Qed.

Lemma a_live_eq : forall RT Σ Σ' E, a_live RT Σ E -> rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> a_live RT Σ' E.
Proof. intros RT Σ Σ' E (A & B & C & D & F) E1 E2 E3. unfold a_live. rewrite E1, E2, E3. tauto. Qed.

Lemma a_live_mono : forall RT Σ Σ' E, a_live RT Σ E ->
  (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ')) -> (forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ')) ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> a_live RT Σ' E.
Proof.
  intros RT Σ Σ' E (A & B & C & D & F) HL HF E3. unfold a_live. rewrite E3.
  split; [auto|]. split; [auto|]. split; [destruct C; auto|]. split; [auto| exact F].
Qed.

Definition ptr_atA (E : aenvA) (P : Z) (ptr : list Z) : Prop :=
  exists pre, ae_p1 E = pre ++ ptr /\ P = ae_PTR E + zlength pre.

Lemma ptr_atA_skip : forall E P ptr k, ptr_atA E P ptr -> (k <= length ptr)%nat -> ptr_atA E (P + Z.of_nat k) (skipn k ptr).
Proof.
  intros E P ptr k (pre & Ep & EP) Hk. exists (pre ++ firstn k ptr). split.
  - rewrite <- app_assoc, firstn_skipn. exact Ep.
  - rewrite EP. unfold zlength. rewrite length_app, length_firstn. lia.
Qed.

Lemma bytes_at_skipn : forall m A (bs : list byte) k,
  bytes_at bsegs m A bs -> (k <= length bs)%nat -> bytes_at bsegs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros m A bs k H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length, Nat.min_l in H by lia. exact H.
Qed.
Lemma bytes_at_firstn : forall m A (bs : list byte) k,
  bytes_at bsegs m A bs -> bytes_at bsegs m A (firstn k bs).
Proof.
  intros m A bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma ptr_atA_facts : forall E P ptr m, aenvA_ok E -> ptr_atA E P ptr -> bytes_at bsegs m (ae_PTR E) (map (Z_to_bv 8) (ae_p1 E)) ->
  bytes_at bsegs m P (map (Z_to_bv 8) ptr) /\ Forall (fun c => 0 <= c < 256) ptr
  /\ ae_PTR E <= P /\ P + zlength ptr = ae_PTR E + zlength (ae_p1 E) /\ zlength ptr < 2^26.
Proof.
  intros E P ptr m OK (pre & Ep & EP) PB. pose proof (ok_p1 E OK) as F. pose proof (ok_p1len E OK) as L.
  rewrite Ep in F, L. rewrite Ep, map_app in PB. apply Forall_app in F. destruct F as [_ F].
  split; [| split; [exact F|]].
  - apply (bytes_at_skipn _ _ _ (length (map (Z_to_bv 8) pre))) in PB; [| rewrite length_app; lia].
    rewrite skipn_app, skipn_all, Nat.sub_diag, length_map in PB. cbn [skipn] in PB. rewrite EP. unfold zlength. exact PB.
  - rewrite EP, Ep. unfold zlength in *. rewrite length_app in *. pose proof (Zle_0_nat (length pre)). lia.
Qed.

Lemma skipn_cons_nth : forall (l : list Z) k, (k < length l)%nat -> skipn k l = nth k l 0 :: skipn (S k) l.
Proof.
  induction l as [|c l IH]; intros [|k] Hk; cbn in Hk |- *; try lia; [reflexivity|]. apply IH. lia.
Qed.
Lemma zlength_nil : zlength (@nil Z) = 0.
Proof. reflexivity. Qed.
Lemma zlength_cons : forall (c : Z) l, zlength (c :: l) = zlength l + 1.
Proof. intros. unfold zlength. cbn [length]. lia. Qed.
Lemma zlength_skipn : forall (l : list Z) k, (k <= length l)%nat -> zlength (skipn k l) = zlength l - Z.of_nat k.
Proof. intros. unfold zlength. rewrite length_skipn. lia. Qed.
Lemma zlength_nonneg : forall (l : list Z), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.
Lemma Forall_nth_Z : forall (P : Z -> Prop) l k, Forall P l -> (k < length l)%nat -> P (nth k l 0).
Proof.
  intros P l k HF Hk. rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hk.
Qed.

Section Stmts.
Variable RT : rt_sig.

Definition lvl_postA (E : aenvA) (Σ : rts RT) (PMc : Model -> Prop) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (out : Z) (m : mem) (cost : Z) : config -> Prop :=
  fun c => exists Σ' : rts RT,
    ASTA RT Σ' PMc (fun ms => exists (v : word) (m' : mem),
         ret_st ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' q (ae_lo E) m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m m'
         /\ (exists jo', rw_cells bsegs m' out [CB 24 jo']) /\ AINV_A E m') c
    /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ - cost <= rt_credit RT Σ'.

Definition lposA (L : list (Z * Z)) : Prop := forall p n, In (p, n) L -> exists n', In (p, n') L /\ 0 < n'.

Definition lvl_pre (E : aenvA) (Σ : rts RT) (m : mem) (q out node i : Z) (jo : list byte) (need cost : Z) (frames : nat) : Prop :=
  rw_cells bsegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] /\ q <= node /\ node + 16 <= ae_hi E /\ node mod 8 = 0
  /\ rw_cells bsegs m out [CB 24 jo] /\ q <= out /\ out + 24 <= ae_hi E /\ out mod 8 = 0
  /\ (node + 16 <= out \/ out + 24 <= node)
  /\ ART RT Σ m /\ mem_inv bsegs m /\ stk bsegs m (ae_lo E) q /\ ae_lo E + need <= q /\ q mod 16 = 0
  /\ (length (rt_frames RT Σ) + frames <= FRAMES_MAX2)%nat /\ cost <= rt_credit RT Σ
  /\ (Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX /\ lposA (rt_live RT Σ)).

Definition lvl_entry (pc : Z) (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 : word) (out node P L : Z)
    (a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) t0 t1 t2 s0 s1 (Z_to_bv 64 out) (Z_to_bv 64 node) (Z_to_bv 64 P) (Z_to_bv 64 L)
          a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Definition atp_elem_cpsA (E : aenvA) (d : nat) : Prop :=
  forall (Σ : rts RT) PMc (ptr : list Z) (i j : Z) (q out node P : Z)
         (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte),
    fdfs_only PMc -> mat_stable PMc -> a_live RT Σ E -> AINV_A E m -> ptr_atA E P ptr ->
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j <= ae_n E - 1 ->
    lvl_pre E Σ m q out node i jo (elem_needA d) (elem_costA d (zlength ptr)) d -> frm0 fc ->
    cps_f (ASTA RT Σ PMc (eq (lvl_entry ATP_ELEM_A ra q gp t0 t1 t2 s0 s1 out node P (zlength ptr)
                                      a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)))
      (lvl_postA E Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m (elem_costA d (zlength ptr))).

Definition atp_obj_cpsA (E : aenvA) (d : nat) : Prop :=
  forall (Σ : rts RT) PMc (ptr : list Z) (i e c : Z) (q out node P : Z)
         (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte),
    fdfs_only PMc -> mat_stable PMc -> a_live RT Σ E -> AINV_A E m -> ptr_atA E P ptr ->
    ty (ae_T E) i = t_obj -> tnext (ae_T E i) = e + 1 -> ae_T E e = tword t_obj_end i ->
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) (i + 1) e c ->
    0 <= i -> e + 1 <= ae_n E - 1 ->
    lvl_pre E Σ m q out node i jo (obj_needA d) (obj_costA d (zlength ptr)) (S d) -> frm0 fc ->
    cps_f (ASTA RT Σ PMc (eq (lvl_entry ATP_OBJ_A ra q gp t0 t1 t2 s0 s1 out node P (zlength ptr)
                                      a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)))
      (lvl_postA E Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m (obj_costA d (zlength ptr))).

Definition atp_arr_cpsA (E : aenvA) (d : nat) : Prop :=
  forall (Σ : rts RT) PMc (ptr : list Z) (i e c : Z) (q out node P : Z)
         (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte),
    fdfs_only PMc -> mat_stable PMc -> a_live RT Σ E -> AINV_A E m -> ptr_atA E P ptr ->
    ty (ae_T E) i = t_arr -> tnext (ae_T E i) = e + 1 -> ae_T E e = tword t_arr_end i ->
    tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d) (i + 1) e c ->
    0 <= i -> e + 1 <= ae_n E - 1 ->
    lvl_pre E Σ m q out node i jo (arr_needA d) (arr_costA d (zlength ptr)) d -> frm0 fc ->
    cps_f (ASTA RT Σ PMc (eq (lvl_entry ATP_ARR_A ra q gp t0 t1 t2 s0 s1 out node P (zlength ptr)
                                      a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)))
      (lvl_postA E Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m (arr_costA d (zlength ptr))).

Lemma lvl_postA_intro : forall E (Σ Σ' : rts RT) PMc (c : config) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q out cost : Z) (m m' : mem)
    (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32) (jo' : list byte),
  ASTA RT Σ' PMc (eq (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                         F' (ret_pc ra) fc' None m' (seg_rom bsegs))) c ->
  ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m m' -> rw_cells bsegs m' out [CB 24 jo'] -> AINV_A E m' ->
  rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - cost <= rt_credit RT Σ' ->
  lvl_postA E Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m cost c.
Proof.
  intros until jo'. intros HC HA MI ST PR OUT AI E1 E2 E3 CR. exists Σ'. split; [| repeat split; assumption].
  eapply ASTA_conseq; [exact HC|]. intros ms <-. exists y10, m'. split; [unfold ret_st; do 16 eexists; reflexivity|].
  split; [exact (conj HA (conj MI ST))|]. split; [exact PR|]. split; [exists jo'; exact OUT| exact AI].
Qed.
End Stmts.

Lemma u64s_read : forall (ws : list word) (i : nat), (i < length ws)%nat ->
  firstn 8 (skipn (8 * i) (u64s ws)) = le8 (nth i ws (Z_to_bv 64 0)).
Proof.
  induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - rewrite Nat.mul_0_r, skipn_O. cbn [u64s]. rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite firstn_all2 by (rewrite length_le8; lia). reflexivity.
  - replace (8 * S i)%nat with (8 + 8 * i)%nat by lia. cbn [u64s nth]. rewrite skipn_app, length_le8.
    replace (8 + 8 * i - 8)%nat with (8 * i)%nat by lia. rewrite skipn_all2 by (rewrite length_le8; lia). cbn [app].
    apply IH. lia.
Qed.

Lemma tape_read : forall m TAPE (tws : list Z) (i : Z),
  bytes_at bsegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) ->
  ov_read_bytes bsegs m (wa (TAPE + 8 * i)) 8 = Some (le8 (Z_to_bv 64 (Tf tws i))).
Proof.
  intros m TAPE tws i HB Hi.
  rewrite (bytes_at_read bsegs m TAPE _ (8 * i) 8 HB); [| lia| rewrite u64s_length, length_map; lia].
  replace (Z.to_nat (8 * i)) with (8 * Z.to_nat i)%nat by lia.
  rewrite u64s_read by (rewrite length_map; lia). f_equal. f_equal.
  unfold Tf. apply (map_nth (Z_to_bv 64)).
Qed.

Lemma zbytes_read1 : forall m A (l : list Z) (k : Z),
  bytes_at bsegs m A (map (Z_to_bv 8) l) -> 0 <= k < zlength l ->
  ov_read_bytes bsegs m (wa (A + k)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat k) l 0)].
Proof.
  intros m A l k HB Hk. unfold zlength in Hk.
  rewrite (bytes_at_read bsegs m A _ k 1 HB); [| lia| rewrite length_map; lia]. f_equal.
  rewrite <- (map_nth (Z_to_bv 8)).
  remember (map (Z_to_bv 8) l) as l' eqn:El.
  assert (HL : (Z.to_nat k < length l')%nat) by (subst l'; rewrite length_map; lia). clear El HB Hk.
  revert l' HL. generalize (Z.to_nat k) as n. clear k.
  induction n as [|n IH]; intros [|c l'] HL; cbn [length] in HL; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma sbuf_read1 : forall m SBUF (sbs : list Z) (o : Z),
  bytes_at bsegs m SBUF (map (Z_to_bv 8) sbs) -> 0 <= o < Z.of_nat (length sbs) ->
  ov_read_bytes bsegs m (wa (SBUF + o)) 1 = Some [Z_to_bv 8 (Tf sbs o)].
Proof. intros m SBUF sbs o HB Ho. unfold Tf. apply zbytes_read1; [exact HB| unfold zlength; lia]. Qed.

Lemma tword_range : forall t v, 0 <= t < 256 -> 0 <= v < 2^56 -> 0 <= tword t v < 2^64.
Proof. intros t v Ht Hv. unfold tword. lia. Qed.
Lemma ttype_range : forall w t, ttype w = t -> (0 <= t)%Z -> (t < 256)%Z -> (0 <= w < 2^64)%Z.
Proof.
  intros w t H Ht0 Ht1. unfold ttype in H.
  pose proof (Z.div_mod w (2^56) ltac:(lia)) as D. pose proof (Z.mod_pos_bound w (2^56) ltac:(lia)) as R. rewrite H in D. lia.
Qed.
Lemma cword_range : forall t nxt cv, 0 <= t < 256 -> 0 <= nxt < 2^32 -> 0 <= cv <= CNT_MAX -> 0 <= cword t nxt cv < 2^64.
Proof. intros t nxt cv Ht Hn Hc. unfold cword. apply tword_range; [lia|]. unfold CNT_MAX in Hc. lia. Qed.
Lemma elem_word_range : forall (T S : Z -> Z) (sn : Z) (d : nat) (i j : Z),
  elem T S sn ck_any d i j -> 0 <= i -> j < 2^32 -> sn < 2^56 -> 0 <= T i < 2^64.
Proof.
  intros T S sn d i j EL Hi Hj Hsn. pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
  assert (SC : scalar T S sn i j -> 0 <= T i < 2^64).
  { intros [[_ [X|[X|X]]]|[[_ [X|[X|X]]]|[_ (o & l & X & (Y1 & Y2 & Y3 & _))]]]; rewrite X;
      try (apply tword_range; [unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl; lia| lia]).
    apply tword_range; [unfold t_str; lia| lia]. }
  destruct d as [|d']; cbn [elem] in EL; fold (elem T S sn ck_any) in EL.
  - destruct EL as [EL|[]]. exact (SC EL).
  - destruct EL as [EL|(e & c & cv & Ej & CK & CS)]; [exact (SC EL)|].
    unfold ck_any in CK.
    destruct CS as [(X & _ & _)|(X & _ & _)]; rewrite X; (apply cword_range; [unfold t_arr, t_obj; lia| lia| exact CK]).
Qed.
Lemma land32_tnext : forall w, (0 <= w)%Z -> Z.land w 4294967295 = tnext w.
Proof. intros w H. change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma mod32_tnext : forall w, (w mod 4294967296)%Z = tnext w.
Proof. intros w. reflexivity. Qed.
Lemma land64_mod : forall x, Z.land x 18446744073709551615 = (x mod 2^64)%Z.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). apply Z.land_ones. lia. Qed.
Lemma Z_to_bv64_eqm : forall a b, (a mod 2^64 = b mod 2^64)%Z -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. exact H. Qed.

Lemma acc_read1 : forall (m : mem) a n x, acc bsegs m a n -> a <= x < a + n ->
  exists b : byte, ov_read_bytes bsegs m (wa (x / 8 + 2147450880)) 1 = Some [b] /\ sh_ok b x.
Proof.
  intros m a n x AC Hx. destruct (AC (x - a) ltac:(lia)) as (b & HB & OK). replace (a + (x - a)) with x in HB, OK by lia.
  exists b. split; [| exact OK]. unfold shad, SHB in HB.
  pose proof (bytes_at_read bsegs m _ _ 0 1 HB ltac:(lia) ltac:(cbn; lia)) as R. rewrite Z.add_0_r in R. exact R.
Qed.

Lemma sh_ok_cases : forall (b : byte) x, sh_ok b x ->
  b = Z_to_bv 8 0 \/ (exists k, b = Z_to_bv 8 k /\ 1 <= k <= 7 /\ x mod 8 < k).
Proof.
  intros b x [H|(H1 & H2)].
  - left. apply bv_eq. rewrite H. reflexivity.
  - right. exists (bv_unsigned b). split; [| lia]. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small; [reflexivity|]. apply bv_unsigned_in_range.
Qed.
Lemma sxb_small7 : forall k, 0 <= k < 128 -> sxb (Z_to_bv 8 k) = Z_to_bv 64 k.
Proof.
  intros k Hk. rewrite sxb_small by lia. destruct (Z.ltb_spec k 128); [reflexivity| lia].
Qed.
Lemma land7_mod : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma shz_stack : forall RT (AF : art_facts RT) Σ m a n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= a -> a + n <= USTACK_TOP ->
  a mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> shz m a n.
Proof.
  intros RT AF Σ m a n HA LO HI A8 N8 N0. pose proof (af_sp0_win RT AF Σ m HA).
  pose proof (shz_of_acc m a n (af_acc_stack RT AF Σ m a n HA LO HI) A8 ltac:(unfold STACK_WIN in *; lia)) as S.
  replace (8 * (n / 8)) with n in S; [exact S|]. pose proof (Z.div_mod n 8 ltac:(lia)). lia.
Qed.

Lemma shz_doc : forall E m, aenvA_ok E -> AINV_A E m -> shz m (ae_DOC E) 16.
Proof.
  intros E m OK (_ & _ & _ & _ & HB). destruct (ok_doc E OK) as (D8 & FL & _ & F0 & _).
  pose proof (shz_of_zero_run m (ae_DOC E) 2 D8 ltac:(unfold SEGTOP_A in *; lia) HB) as S. exact S.
Qed.

Lemma a_u8_small : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Lemma a_u64_small : forall c, (0 <= c < 2^64)%Z -> bv_unsigned (Z_to_bv 64 c) = c.
Proof. intros c H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Lemma a_zx32_small : forall x, (0 <= x < 2^32)%Z -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32. f_equal. rewrite a_u64_small by lia. apply Z.mod_small. lia. Qed.
Lemma a_swrap32_small : forall x, (-2147483648 <= x < 2147483648)%Z -> bv_swrap 32 x = x.
Proof.
  intros x H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma a_sx32_small : forall x, (0 <= x < 2^31)%Z -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold sx32. f_equal. rewrite a_u64_small by lia. apply a_swrap32_small. lia. Qed.
Lemma a_shl3 : forall x, Z.shiftl x 3 = (8 * x)%Z.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma a_shl1 : forall x, Z.shiftl x 1 = (2 * x)%Z.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma a_shr56 : forall w, Z.shiftr w 56 = ttype w.
Proof. intros. unfold ttype. apply Z.shiftr_div_pow2. lia. Qed.
Lemma a_signed_small : forall z, (0 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z H. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. change (18446744073709551616 / 2)%Z with 9223372036854775808%Z.
  rewrite (Z.mod_small z) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma a_shl32_shr32 : forall x, (0 <= x)%Z -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 32 = tnext x.
Proof.
  intros x H. unfold tnext. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  change 18446744073709551616 with (2^32 * 2^32)%Z. rewrite Zmult_mod_distr_r.
  rewrite Z.div_mul by lia. reflexivity.
Qed.

Ltac anorm :=
  cbv beta;
  repeat match goal with
  | |- context [zxb (Z_to_bv 8 ?c)] => rewrite (zxb_small c) by lia
  | |- context [bv_unsigned (Z_to_bv 8 ?c)] => rewrite (a_u8_small c) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?c)] => rewrite (a_u64_small c) by lia
  | |- context [zx32 (Z_to_bv 64 ?c)] => rewrite (a_zx32_small c) by lia
  | |- context [sx32 (Z_to_bv 64 ?c)] => rewrite (a_sx32_small c) by lia
  | |- context [bv_swrap 32 ?x] => rewrite (a_swrap32_small x) by lia
  | |- context [Z.modulo ?x 4294967296] => rewrite (Z.mod_small x 4294967296) by lia
  | |- context [Z.modulo ?x 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by lia
  | |- context [Z.shiftr (Z.modulo (Z.shiftl ?x 32) 18446744073709551616) 32] => rewrite (a_shl32_shr32 x) by lia
  | |- context [Z.shiftr ?w 56] => rewrite (a_shr56 w)
  | |- context [Z.shiftr ?w 3] => rewrite (shr3_div w)
  | |- context [Z.shiftl ?x 3] => rewrite (a_shl3 x)
  | |- context [Z.shiftl ?x 1] => rewrite (a_shl1 x)
  | |- context [Z.land ?x 7] => rewrite (land7_mod x) by lia
  end.
Ltac astep := zstep; anorm.

Ltac atp_st_eq_leaf :=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia | apply Z_to_bv64_eqm; rewrite ?land64_mod; lia]
  | |- _ => reflexivity
  end.
Ltac atp_st_eq_tree :=
  lazymatch goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal; atp_st_eq_tree
  | |- Some _ = Some _ => f_equal; atp_st_eq_leaf
  | |- _ => atp_st_eq_leaf
  end.
Ltac atp_st_eq :=
  cbv beta delta [mkR];
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; atp_st_eq_tree
  end.
Ltac atp_st_eq_goal :=
  cbv beta delta [mkR];
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; atp_st_eq_tree
  | |- _ => reflexivity
  end.
Ltac name_mem mx := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => rename m into mx end.

Ltac if_lia :=
  let K := fresh "Kc" in
  if_cases K; zify_cond K; rewrite ?land64_mod, ?a_signed_small in K by lia; try (exfalso; lia); [try clear K].

Definition keepA (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change (keepA T) in H end.
Ltac unhide H := unfold keepA in H.

Ltac chk0 H x := shz_pose H x; zstep; rewrite ?shr3_div; zstep; zstep; shz_norm.

Definition shb_cells (m : mem) : Prop :=
  ro_cells bsegs m 1501040 [C8 (Z_to_bv 64 1539000)] /\ ro_cells bsegs m 1539000 [C8 (Z_to_bv 64 2147450880)].
Lemma shb_cells_of_art : forall RT (AF : art_facts RT) Σ m, ART RT Σ m -> shb_cells m.
Proof. intros RT AF Σ m HA. destruct (af_client_consts RT AF Σ m HA) as (G1 & G2 & _). exact (conj G1 G2). Qed.

Definition ATP_ROOT_STACK_A : Z := 458752.
Definition ATP_ROOT_COST_A (L : Z) : Z := 1024 * LVL_C1 + 2 * L.
Definition ATP_ROOT_FRAMES_A : nat := 1024.
Lemma ATP_ROOT_STACK_A_eq : ATP_ROOT_STACK_A = obj_needA 1023.
Proof. reflexivity. Qed.
Lemma ATP_ROOT_COST_A_eq : forall L, ATP_ROOT_COST_A L = obj_costA 1023 L.
Proof. intros L. unfold ATP_ROOT_COST_A, obj_costA. lia. Qed.
Lemma arr_le_obj_needA : forall d, arr_needA d <= obj_needA d.
Proof. intros d. unfold arr_needA, obj_needA. lia. Qed.
Lemma arr_le_obj_costA : forall d L, 0 <= L -> arr_costA d L <= obj_costA d L.
Proof. intros d L HL. unfold arr_costA, obj_costA, LVL_C1, DCOST. lia. Qed.
