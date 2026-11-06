(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow R_sizeclass.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow R_sizeclass.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_leaves.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_poison.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_setshadow.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_glue_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_sec_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_tlsgetaddr.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_intalloc.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_frame.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_trans.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts0.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_sep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freelift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_geo0.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CONSTS_LITS : list (Z * Z) :=
  [ (863992, 864016); (864016, 864017); (0xcce18, 0xcce20); (0xcce28, 0xcce30); (0x165fe0, 0x165fe8); (0x1680f8, 0x168100);
    (0x16816c, 0x16816d); (0xd5da0, 0xd5da1); (0xd5da4, 0xd5da8); (0x609480, 0x609488); (0x62a880, 0x62a888);
    (0xcce38, 0xcce58); (0xd6538, 0xd6540); (0xd7220, 0xd7238); (0xcce58, 0xcce60); (0xcecb0, 0xcecb8); (0xd5d9c, 0xd5d9d);
    (0x1680e0, 0x1680e8); (839224, 839232); (877880, 877888); (839312, 839320); (877888, 877892);
    (0x16815d, 0x16815e); (0x168164, 0x168165); (0xcce30, 0xcce38); (0xcce60, 0xcce68); (0xceca8, 0xcecb0); (0xd3d55, 0xd3d56);
    (0xd723c, 0xd7240); (0x16808a, 0x16808b); (0xcdab0, 0xcdab8); (0xcdab8, 0xcdac0); (0xcdad0, 0xcdad8); (0xcd9a0, 0xcd9a8); (0xd7219, 0xd721a);
    (0xceb70, 0xceb78); (0xcec58, 0xcec60); (0xceb48, 0xceb50); (0x168163, 0x168164); (0xd3cf8, 0xd3d00); (0xd3d00, 0xd3d04);
    (0x1587a2, 0x1587a3); (0xd3d64, 0xd3d68); (0xd3d6c, 0xd3d70); (0xd3d8d, 0xd3d8e); (0x6094e8, 0x6094ec); (0xcda90, 0xcda98);
    (0x168000, 0x168008); (0x168008, 0x168010); (0xd31f0, 0xd3208); (0xd3d68, 0xd3d6c);
    (0xceb80, 0xceb98); (0xd3df0, 0xd3df8); (0xcc8c0, 0xcc8d8); (0xccd30, 0xccd38); (0xcce08, 0xcce18); (0xcda98, 0xcdaa8); (0xcdaa8, 0xcdab0);
    (0xcdac0, 0xcdad0); (0xcdb00, 0xcdb10); (0xceb40, 0xceb48); (0xceba0, 0xcebb8); (0xd3d50, 0xd3d54); (0x1680bc, 0x1680bd);
    (0x1683e0, 0x1683e1); (0xceb60, 0xceb70); (0x168166, 0x168168);
    (* [comment removed for export] *)
    (0xcce78, 0xcce80); (0x168143, 0x168144); (0x16815c, 0x16815d); (0x629798, 0x6297a0) ].

(* [comment removed for export] *)
Local Lemma In_CONSTS_LITS_b : forall e : Z * Z,
  existsb (fun p => andb (Z.eqb (fst p) (fst e)) (Z.eqb (snd p) (snd e))) CONSTS_LITS = true -> In e CONSTS_LITS.
Proof.
  intros [x y] H. apply existsb_exists in H. destruct H as ([a b] & Hin & Hb). apply andb_true_iff in Hb.
  destruct Hb as [H1 H2]. cbn [fst snd] in H1, H2. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst a b. exact Hin.
Qed.

Lemma consts_rngs_kind : forall L r, In r (consts_rngs L) ->
  In r CONSTS_LITS \/ (l_T L <= fst r /\ snd r <= l_T L + 0x30) \/ r = (l_T L + 0xc60, l_T L + 0xc60 + 1)
  \/ (l_TCX L <= fst r /\ snd r <= l_TCX L + 0x10000).
Proof.
  intros L r Hr. unfold consts_rngs in Hr. unfold_consts.
  (* [comment removed for export] *)
  repeat (destruct Hr as [<-|Hr]; [first [solve [left; lazymatch goal with |- In ?e _ =>
                                                   lazymatch e with context [L] => fail | _ => idtac end end;
                                                 apply In_CONSTS_LITS_b; vm_compute; reflexivity]
                                         | solve [right; left; cbn [fst snd]; lia] | solve [right; right; left; reflexivity]
                                         | solve [right; right; right; cbn [fst snd]; lia]] |]).
  destruct Hr.
Qed.

Lemma dsjb_all : forall V l, forallb (fun r => dsjb V (fst r) (snd r - fst r)) l = true ->
  Forall (fun r => disjoint_from V (fst r) (snd r - fst r)) l.
Proof.
  intros V l H. apply Forall_forall. intros r Hr. exact (dsjb_sound _ _ _ (proj1 (forallb_forall _ _) H r Hr)).
Qed.
Lemma dsjb_all' : forall V l, forallb (fun r => dsjb V (fst r) (snd r)) l = true -> Forall (fun r => disjoint_from V (fst r) (snd r)) l.
Proof.
  intros V l H. apply Forall_forall. intros r Hr. exact (dsjb_sound _ _ _ (proj1 (forallb_forall _ _) H r Hr)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DEP_LITS : list (Z * Z) :=
  [(0x1b8418, 0x5b8418 + 4 - 0x1b8418); (0x5b8428, 8); (0x1a8408, 8); (0x1a8418, 0x1a8420 + 4 - 0x1a8418)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ris_of_whole : forall SB (W : list ivl) (DC : list Z), (forall a n, RIS_of SB <= a -> a + n <= RIS_of SB + 4096 -> disjoint_from W a n) ->
  forall c a n, 1 <= c <= 31 -> ~ In c DC -> rinfo (RIS_of SB) c <= a -> a + n <= rinfo (RIS_of SB) c + 120 -> disjoint_from W a n.
Proof. intros SB W DC H c a n Hc _ H1 H2. apply H; unfold rinfo in *; lia. Qed.

Section FKit.
Variables (Σ : rtsA) (m : mem) (W : list ivl) (D : list (Z * nat)) (DS : list nat) (TZ IZ : list ivl) (usp : Z) (DC : list Z).
Hypothesis HG : geo_ok Σ.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Hypothesis HW_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from IZ a n -> disjoint_from W a n.
Hypothesis HW_T : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from TZ a n -> disjoint_from W a n.
Hypothesis HW_grant : forall i b gn a n, nth_error (startup_grants L) i = Some (b, gn) -> (i = 1 \/ i = 3 \/ i = 4 \/ i = 5)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
(* [comment removed for export] *)
Hypothesis HW_ris : forall c a n, 1 <= c <= 31 -> ~ In c DC -> rinfo (RIS_of SB) c <= a -> a + n <= rinfo (RIS_of SB) c + 120 ->
  disjoint_from W a n.
Hypothesis HW_fa : forall c a n, 1 <= c <= 31 -> ~ In c DC -> fa SB c <= a -> a + n <= fa SB c + kFaCap -> disjoint_from W a n.
Hypothesis HW_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
  p_abeg SB c i <= a -> a + n <= p_abeg SB c i + ClassSize c -> disjoint_from W a n.
Hypothesis HW_shad_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
  shad (p_abeg SB c i) <= a -> a + n <= shad (p_abeg SB c i + ClassSize c) -> disjoint_from W a n.
Hypothesis HW_shad_reg : forall c a n, 1 <= c <= 31 -> ~ In c DC -> shad (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) <= a ->
  a + n <= shad (rb SB c + 2 ^ 32) -> disjoint_from W a n.
Hypothesis HW_shad_app : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= l_PRB L \/ l_PRB L + 0x2000011000 <= lo) ->
  (forall k s, nth_error (sec Σ) k = Some s -> In k DS -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo) ->
  shad lo <= a -> a + n <= shad hi -> disjoint_from W a n.
Hypothesis HW_secmap : forall k s a n, nth_error (sec Σ) k = Some s -> ~ In k DS -> s_mb s <= a -> a + n <= s_mb s + smsz (s_n s) ->
  disjoint_from W a n.

Lemma fk_aceil : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47.
Proof. pose proof (g_aceil Σ HG) as (X & Y & _). lia. Qed.

Lemma fk_prb : 0 < l_PRB L /\ l_PRB L + 0x2000011000 <= l_ACEIL L /\ SEGTOP_A <= l_PRB L /\ l_PRB L <= SB
  /\ SB + 2 ^ 37 + 4096 <= l_PRB L + 0x2000011000.
Proof.
  pose proof (g_prb Σ HG) as (P1 & P2 & P3).
  pose proof (g_grant Σ HG (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _ & G5).
  unfold SEGTOP_A in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma fk_slot : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  rb SB c <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))
  /\ ClassSize c * Z.of_nat (length (r_st (pr Σ c))) <= r_muser (pr Σ c) <= kUserCap /\ 32 <= ClassSize c.
Proof.
  intros c i st Hc Hn. pose proof HG as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & _ & W3 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm).
  pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
  assert (Hx : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
  { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
    replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
    apply Z.mul_le_mono_nonneg_r; lia. }
  assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
  unfold p_abeg, rb in *. repeat split; lia.
Qed.

Lemma kv_reg : forall c, 1 <= c <= 31 -> ~ In c DC -> reg_avoid W SB c (pr Σ c).
Proof.
  intros c Hc HDC. pose proof fk_prb as (P0 & P1 & P2 & P3 & P4). pose proof HG as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm32).
  assert (Hau : 0 <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) by (apply Z.mul_nonneg_nonneg; lia).
  unfold reg_avoid. split; [|split].
  - apply (HW_ris c); [exact Hc | exact HDC | lia | lia].
  - apply (HW_fa c); [exact Hc | exact HDC | lia | unfold kFaCap in *; lia].
  - apply (HW_shad_reg c); [exact Hc | exact HDC | lia|].
    pose proof (div8_add (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c))))
                  ltac:(unfold rb; lia) ltac:(lia)) as X.
    assert ((rb SB c + r_muser (pr Σ c)) / 8 <= (rb SB c + 2 ^ 32) / 8) by (apply Z.div_le_mono; unfold kUserCap in *; lia).
    pose proof (Z.div_pos (r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) 8 ltac:(lia) ltac:(lia)).
    replace (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c))) + (r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c)))))
      with (rb SB c + r_muser (pr Σ c)) in X by ring.
    unfold shad. lia.
Qed.

Lemma kv_pclass : forall c, 1 <= c <= 31 -> disjoint_from TZ (pc_addr T c) 80 -> pclass_avoid W T c.
Proof. intros c Hc HZ. unfold pclass_avoid. apply HW_T; [unfold pc_addr; lia | unfold pc_addr; lia | exact HZ]. Qed.

(* [comment removed for export] *)
Lemma fk_shad_le : forall a x y, 0 <= a -> 0 <= x -> 0 <= y -> shad a + x / 8 + y / 8 <= shad (a + x + y).
Proof. intros a x y Ha Hx Hy. unfold shad. pose proof (div8_add3 a x y Ha Hx Hy). pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). lia. Qed.

Lemma fk_shad_le2 : forall a x, 0 <= a -> 0 <= x -> shad a + x / 8 <= shad (a + x).
Proof. intros a x Ha Hx. unfold shad. pose proof (div8_add a x Ha Hx). lia. Qed.

Lemma fk_shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

(* [comment removed for export] *)
Lemma kv_pchunk_gen : forall c i st st', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
  (forall n, st' = CkAlloc n \/ st' = CkQuar n -> rz_size n + n <= ClassSize c /\ 0 <= n) -> pchunk_avoid W SB c i st'.
Proof.
  intros c i st st' Hc Hn HD Hfit. pose proof (fk_slot c i st Hc Hn) as (S1 & S2 & S3 & S4). pose proof fk_prb as (P0 & _ & _ & P3 & _).
  unfold pchunk_avoid. set (AB := p_abeg SB c i) in *. set (S := ClassSize c) in *.
  assert (HAB : 0 <= AB) by (unfold rb in S1; lia).
  assert (HS0 : 0 <= S / 8) by (apply Z.div_pos; lia).
  assert (HSE : shad AB + S / 8 <= shad (AB + S)) by exact (fk_shad_le2 AB S HAB ltac:(lia)).
  assert (SHS : forall a k, shad AB <= a -> a + k <= shad (AB + S) -> disjoint_from W a k) by (intros a k H1 H2; exact (HW_shad_slot c i st a k Hc Hn HD H1 H2)).
  assert (SL : forall a k, AB <= a -> a + k <= AB + S -> disjoint_from W a k) by (intros a k H1 H2; exact (HW_slot c i st a k Hc Hn HD H1 H2)).
  clear HD. destruct st' as [|n|n|].
  - apply SHS; lia.
  - destruct (Hfit n (or_introl eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
    pose proof (fl_ushadow_len n F2) as U. assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
    assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia).
    split; [apply SL; lia|].
    split; [intros _; apply SL; lia|].
    pose proof (fk_shad_le AB (rz_size n) (ru8 n) HAB ltac:(lia) Hu) as E1.
    pose proof (fk_shad_mono (AB + rz_size n + ru8 n) (AB + S) ltac:(lia)) as E2.
    split.
    + rewrite length_app, Nat2Z.inj_add, farun_lenZ, U by lia.
      apply SHS; lia.
    + pose proof (fk_shad_le2 (AB + rz_size n + ru8 n) (S - rz_size n - ru8 n) ltac:(lia) ltac:(lia)) as E3.
      replace (AB + rz_size n + ru8 n + (S - rz_size n - ru8 n)) with (AB + S) in E3 by ring.
      pose proof (fk_shad_mono AB (AB + rz_size n + ru8 n) ltac:(lia)) as E4.
      assert (0 <= (S - rz_size n - ru8 n) / 8) by (apply Z.div_pos; lia).
      apply SHS; lia.
  - destruct (Hfit n (or_intror eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
    assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
    assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia). assert (Hu8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
    assert (Hd8 : 0 <= (S - rz_size n - ru8 n) / 8) by (apply Z.div_pos; lia).
    split; [apply SL; lia|].
    split; [intros _; apply SL; lia|].
    rewrite !length_app, !Nat2Z.inj_add, !farun_lenZ, fdrun_lenZ by lia.
    pose proof (div8_add3 (rz_size n) (ru8 n) (S - rz_size n - ru8 n) ltac:(lia) Hu ltac:(lia)) as X.
    replace (rz_size n + ru8 n + (S - rz_size n - ru8 n)) with S in X by ring.
    apply SHS; lia.
  - apply SHS; lia.
Qed.

Lemma kv_pchunk : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D -> pchunk_avoid W SB c i st.
Proof.
  intros c i st Hc Hn HD. apply (kv_pchunk_gen c i st st Hc Hn HD).
  intros n Hs. pose proof HG as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
  pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. destruct Hs as [->| ->]; cbv beta iota in X; lia.
Qed.

(* [comment removed for export] *)
Lemma fk_map : forall k s, nth_error (sec Σ) k = Some s ->
  64513 <= s_n s /\ 0 < s_mb s /\ s_mb s + smsz (s_n s) <= l_ACEIL L /\ (s_mb s + smsz (s_n s) <= 0x10000 \/ SEGTOP_A <= s_mb s)
  /\ apart (s_mb s) (smsz (s_n s)) (l_PRB L) 0x2000011000 /\ apart (s_mb s) (smsz (s_n s)) (l_FSB L) 0xb09000
  /\ Forall (fun g => apart (s_mb s) (smsz (s_n s)) (fst g) (snd g)) (startup_grants L)
  /\ 6144 + ru8 (s_n s) <= smsz (s_n s) /\ s_n s <= ru8 (s_n s)
  /\ (forall k' s', nth_error (sec Σ) k' = Some s' -> k' <> k -> apart (s_mb s) (smsz (s_n s)) (s_mb s') (smsz (s_n s'))).
Proof.
  intros k s Hk. pose proof HG as (_ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & HSP & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (Hn & (G1 & G2 & G3 & G4 & G5) & Hp & Hf & HGs).
  assert (Hroom : 6144 + ru8 (s_n s) <= smsz (s_n s)).
  { unfold smsz, pg_up, needed, rounded, ru8. rewrite (rz_size_big (s_n s)) by lia. rewrite Z.max_l by lia. rewrite Z.max_l by lia.
    assert (8 * ((s_n s + 7) / 8) + 2048 + 2048 <= (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) / 4096 * 4096); [|lia].
    pose proof (Z.mod_pos_bound (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
    pose proof (Z.div_mod (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia. }
  assert (Hu : s_n s <= ru8 (s_n s)) by (unfold ru8; pose proof (Z.div_mod (s_n s + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (s_n s + 7) 8 ltac:(lia)); lia).
  split; [lia|]. split; [exact G1|]. split; [exact G3|]. split; [exact G5|]. split; [exact Hp|]. split; [exact Hf|]. split; [exact HGs|].
  split; [exact Hroom|]. split; [exact Hu|]. intros k' s' Hk' Hne. exact (HSP k k' s s' Hk Hk' (fun E => Hne (eq_sym E))).
Qed.

Lemma kv_schunk : forall k s, nth_error (sec Σ) k = Some s -> ~ In k DS -> schunk_avoid W s.
Proof.
  intros k s Hk HD. pose proof (fk_map k s Hk) as (Hn & G1 & G3 & G5 & Hp & _ & _ & Hroom & Hu & HSP). pose proof fk_aceil as (_ & X).
  assert (HDS : forall k' s', nth_error (sec Σ) k' = Some s' -> In k' DS -> s_mb s + smsz (s_n s) <= s_mb s' \/ s_mb s' + smsz (s_n s') <= s_mb s).
  { intros k' s' Hk' Hin. assert (k' <> k) by (intros ->; exact (HD Hin)). pose proof (HSP k' s' Hk' H) as Ha. unfold apart in Ha. lia. }
  assert (Hoff : s_mb s + smsz (s_n s) <= l_PRB L \/ l_PRB L + 0x2000011000 <= s_mb s) by (unfold apart in Hp; lia).
  assert (SH : forall a n, shad (s_mb s) <= a -> a + n <= shad (s_mb s + smsz (s_n s)) -> disjoint_from W a n).
  { intros a n H1 H2. apply (HW_shad_app (s_mb s) (s_mb s + smsz (s_n s))); [lia | lia | exact Hoff | exact HDS | exact H1 | exact H2]. }
  assert (Hu8 : 0 <= ru8 (s_n s)) by lia.
  unfold schunk_avoid.
  split; [apply (HW_secmap k s); [exact Hk | exact HD | lia | lia]|].
  split; [apply (HW_secmap k s); [exact Hk | exact HD | lia | lia]|].
  split; [apply (HW_secmap k s); [exact Hk | exact HD | lia | destruct (s_quar s); lia]|].
  pose proof (fk_shad_le2 (s_mb s) 6144 ltac:(lia) ltac:(lia)) as E1. change (6144 / 8) with 768 in E1.
  pose proof (fk_shad_le2 (s_mb s + 6144) (ru8 (s_n s)) ltac:(lia) Hu8) as E2.
  pose proof (fk_shad_le2 (s_mb s + 6144 + ru8 (s_n s)) (smsz (s_n s) - 6144 - ru8 (s_n s)) ltac:(lia) ltac:(lia)) as E3.
  replace (s_mb s + 6144 + ru8 (s_n s) + (smsz (s_n s) - 6144 - ru8 (s_n s))) with (s_mb s + smsz (s_n s)) in E3 by ring.
  assert (0 <= (smsz (s_n s) - 6144 - ru8 (s_n s)) / 8) by (apply Z.div_pos; lia). assert (0 <= ru8 (s_n s) / 8) by (apply Z.div_pos; lia).
  pose proof (fk_shad_mono (s_mb s + 6144 + ru8 (s_n s)) (s_mb s + smsz (s_n s)) ltac:(lia)) as E4.
  pose proof (fk_shad_mono (s_mb s) (s_mb s + 6144) ltac:(lia)) as E5.
  pose proof (fk_shad_mono (s_mb s + 6144) (s_mb s + 6144 + ru8 (s_n s)) ltac:(lia)) as E6.
  replace (s_mb s + 4096 + 2048) with (s_mb s + 6144) by ring.
  split; [change ((4096 + 2048) / 8) with 768; apply SH; [lia | rewrite Z.max_r by lia; lia]|].
  split.
  - apply SH; [lia|]. destruct (s_quar s); [rewrite fdrun_lenZ by (apply Z.div_pos; lia) | rewrite (fl_ushadow_len (s_n s)) by lia]; lia.
  - apply SH; [lia | ]. replace (smsz (s_n s) - 4096 - 2048 - ru8 (s_n s)) with (smsz (s_n s) - 6144 - ru8 (s_n s)) by ring.
    rewrite Z.max_r by (apply Z.div_pos; lia). lia.
Qed.

Lemma kv_sec : Forall (fun r => disjoint_from IZ (fst r) (snd r)) sec_lits -> sec_avoid W Σ.
Proof.
  intros HZ. split.
  - apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
      unfold sec_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold i_sec_chunks, i_sec_nres, i_sec_mutex, i_sec_page,
      i_sec_range, i_sec_sorted, i_sec_bylog, i_gstat_alloc, INST, g_instance, SEGTOP_A; lia|]); destruct Hr.
  - pose proof HG as (_ & _ & HS & _). destruct HS as (_ & Hn & _).
    apply (HW_grant 1 (l_PAB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma kv_quar : disjoint_from TZ (qcacheT T) 32 -> Forall (fun r => disjoint_from IZ (fst r) (snd r)) [(i_q_global, 32); (i_q_cmutex, 4)] ->
  (forall i, nth_error (r_st (pr Σ 24)) i = Some CkBatch -> ~ In (24, i) D) ->
  Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) (ql Σ ++ qg Σ) ->
  quar_avoid W Σ.
Proof.
  intros HZ HI HB HBt. split; [apply HW_T; [unfold qcacheT; lia | unfold qcacheT; lia | exact HZ]|].
  split.
  - apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HI r Hr)];
      destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; unfold i_q_global, i_q_cmutex, INST, g_instance, SEGTOP_A; lia.
  - 
    apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HBt b Hb) as (i & Hi & E). rewrite E.
    pose proof (fk_slot 24 i CkBatch ltac:(lia) Hi) as (S1 & S2 & S3 & S4). change (ClassSize 24) with 8192 in *.
    apply (HW_slot 24 i CkBatch); [lia | exact Hi | exact (HB i Hi) | lia | change (ClassSize 24) with 8192; lia].
Qed.

Lemma kv_dep : Forall (fun r => disjoint_from IZ (fst r) (snd r)) DEP_LITS ->
  (forall i b gn a n, nth_error (startup_grants L) i = Some (b, gn) -> (i = 6 \/ i = 7)%nat -> b <= a -> a + n <= b + gn -> disjoint_from W a n) ->
  dep_avoid W L.
Proof.
  intros HZ HD. split.
  - apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
      unfold DEP_LITS in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold SEGTOP_A; lia|]); destruct Hr.
  - split; [apply (HD 6%nat (l_DNB L) 0x100000); [reflexivity | lia | lia | lia]|].
    apply (HD 7%nat (l_SSB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma kv_ia : Forall (fun r => disjoint_from IZ (fst r) (snd r)) ia_lits -> dsjl W ia_lits.
Proof.
  intros HZ. apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
    unfold ia_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold g_ia_word, IAP, SEGTOP_A; lia|]); destruct Hr.
Qed.

Lemma fk_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 -> disjoint_from W a n.
Proof. intros a n H1 H2. exact (HW_grant 5 (l_FSB L) 0xb09000 a n eq_refl ltac:(lia) H1 H2). Qed.

(* [comment removed for export] *)
Lemma fk_fsb_off : l_FSB L + 0xb09000 <= l_PRB L \/ l_PRB L + 0x2000011000 <= l_FSB L.
Proof. pose proof (g_apart Σ HG 0 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in X. lia. Qed.

Lemma fk_fsb_maps : forall k s, nth_error (sec Σ) k = Some s -> l_FSB L + 0xb09000 <= s_mb s \/ s_mb s + smsz (s_n s) <= l_FSB L.
Proof. intros k s Hk. pose proof (fk_map k s Hk) as (_ & _ & _ & _ & _ & Hf & _). unfold apart in Hf. lia. Qed.

Lemma kv_fs_cls : forall k, (k = 0 \/ k = 2 \/ k = 3 \/ k = 6 \/ k = 7)%nat -> fs_cls_avoid W (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof.
  intros k Hk. pose proof HG as (_ & _ & _ & HF). destruct HF as (F0 & F2 & F4 & _).
  assert (Hwf : flags_ok (Z.of_nat k) (fss_flags (fs_of Σ k))) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; [exact (proj1 F0) | exact (proj1 F2) | exact (proj1 (proj1 F4)) | exact (proj1 (proj1 (proj2 F4))) | exact (proj1 (proj2 (proj2 F4)))]).
  destruct Hwf as [Hlen _].
  assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 3 \/ Z.of_nat k = 6 \/ Z.of_nat k = 7) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
  pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  pose proof fk_aceil as (_ & X). pose proof (fl_flags_range _ Hc) as (R1 & R2). pose proof fk_fsb_off as Off.
  unfold fs_cls_avoid. split; [apply fk_fsb; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; lia|]. split.
  - rewrite Hlen. apply fk_fsb; unfold fl_base; lia.
  - intros p Hp _. pose proof (frame_addr_range (l_FSB L) (Z.of_nat k) p Hc Hp) as (A1 & A2). unfold kFakeStackSize in A2.
    assert (Hfz : 0 < fsz (Z.of_nat k)) by (unfold fsz; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
    split; [apply fk_fsb; lia|].
    pose proof (fk_shad_le2 (frame_addr (l_FSB L) (Z.of_nat k) p) (fsz (Z.of_nat k)) ltac:(lia) ltac:(lia)) as E.
    apply (HW_shad_app (frame_addr (l_FSB L) (Z.of_nat k) p) (frame_addr (l_FSB L) (Z.of_nat k) p + fsz (Z.of_nat k))); [lia | lia | lia | | lia | lia].
    intros k' s' Hk' _. pose proof (fk_fsb_maps k' s' Hk'). lia.
Qed.

Lemma kv_fs : Forall (fun r => disjoint_from IZ (fst r) (snd r)) fs_lits -> disjoint_from TZ (T + 48) 16 -> fs_avoid W Σ.
Proof.
  intros HZ HT. pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
  unfold fs_avoid. split; [apply fk_fsb; lia|].
  split; [exact (kv_fs_cls 0%nat ltac:(lia))|]. split; [exact (kv_fs_cls 2%nat ltac:(lia))|]. split; [exact (conj (kv_fs_cls 3%nat ltac:(lia)) (conj (kv_fs_cls 6%nat ltac:(lia)) (kv_fs_cls 7%nat ltac:(lia))))|].
  split.
  { apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
      unfold fs_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold tpA, g_real_tls_get_addr, g_dtv_ptr, g_dtv1,
      g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; lia|]);
      destruct Hr. }
  split; [apply (HW_grant 4 (l_DTV L) 4096); [reflexivity | lia | lia | lia]|].
  split; [apply HW_T; [lia | lia | exact HT]|].
  apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (g_frame Σ HG f k Hin) as (X1 & X2 & X3). apply fk_fsb; lia.
Qed.

Lemma kv_shadow : shadow_avoid W L.
Proof.
  pose proof fk_aceil as (X1 & X2). pose proof fk_prb as (P0 & P1 & P2 & _).
  split.
  - pose proof (fk_shad_le2 (l_ACEIL L) (2 ^ 47 - l_ACEIL L) ltac:(unfold SHB in *; lia) ltac:(lia)) as E.
    replace (l_ACEIL L + (2 ^ 47 - l_ACEIL L)) with (2 ^ 47) in E by ring.
    assert (0 <= (2 ^ 47 - l_ACEIL L) / 8) by (apply Z.div_pos; lia).
    apply (HW_shad_app (l_ACEIL L) (2 ^ 47)); [unfold SHB in *; lia | lia | lia | | lia | rewrite Z.max_r by (apply Z.div_pos; lia); lia].
    intros k s Hk _. pose proof (fk_map k s Hk) as (_ & _ & G3 & _). lia.
  - apply Forall_forall. intros r Hr.
    assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0x62adb8) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
    apply (HW_shad_app 0x10000 SEGTOP_A); [lia | unfold SEGTOP_A; lia | unfold SEGTOP_A in *; lia | | apply fk_shad_mono; lia | ].
    + intros k s Hk _. pose proof (fk_map k s Hk) as (Hn & G1 & _ & G5 & _ & _ & _ & Hroom & Hu & _). unfold SEGTOP_A in *. lia.
    + assert ((snd r - 1) / 8 < 808448) by (apply Z.div_lt_upper_bound; lia).
      assert (shad (snd r - 1) + 1 <= shad SEGTOP_A) by (unfold shad, SEGTOP_A; change (0x62b000 / 8) with 808448; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma kv_consts : Forall (fun r => disjoint_from IZ (fst r) (snd r - fst r)) CONSTS_LITS -> disjoint_from TZ T 0x30 ->
  forall x, in_rngs (consts_rngs L) x -> x <> T + 0xc60 -> outside W x.
Proof.
  intros HZ HTZ x Hx Hne. unfold in_rngs in Hx. apply Exists_exists in Hx as (r & Hr & Hrx). cbv beta in Hrx.
  destruct (consts_rngs_kind L r Hr) as [Hl|[(H1 & H2)|[Er|(H1 & H2)]]].
  - pose proof (proj1 (Forall_forall _ _) HZ r Hl) as Dr.
    assert (Hrng : 0x10000 <= fst r /\ snd r <= SEGTOP_A) by (unfold CONSTS_LITS in Hl; repeat (destruct Hl as [<-|Hl]; [cbn; unfold SEGTOP_A; lia|]); destruct Hl).
    apply (disjoint_outside W (fst r) (snd r - fst r)); [apply HW_img; [lia | lia | exact Dr] | lia].
  - apply (disjoint_outside W x 1); [apply HW_T; [lia | lia | exact (dsj_sub TZ T 0x30 x 1 HTZ ltac:(lia) ltac:(lia))] | lia].
  - rewrite Er in Hrx. cbn [fst snd] in Hrx. lia.
  - apply (disjoint_outside W x 1); [|lia].
    apply (HW_grant 3 (l_TCX L) 0x10000); [reflexivity | lia | lia | lia].
Qed.

(* [comment removed for export] *)
Hypothesis HW_stack : forall a n, usp <= a -> a + n <= USTACK_TOP -> disjoint_from W a n.

Lemma kv_client : Forall (fun r => disjoint_from IZ (fst r) (snd r - fst r)) CLIENT_STATIC ->
  forall (L' : list (Z * Z)), (forall p n, In (p, n) L' ->
      (exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) /\ p = p_ubeg SB c i n /\ ~ In (c, i) D)
      \/ (exists k s, nth_error (sec Σ) k = Some s /\ s_quar s = false /\ s_n s = n /\ p = s_ubeg s /\ ~ In k DS)) ->
  forall x, aclient L' (frames Σ) usp x -> outside W x.
Proof.
  intros HCS L' HL' x Hx. destruct Hx as [H|[H|[H|[H|H]]]].
  - apply (disjoint_outside W x 1); [apply HW_stack; lia | lia].
  - destruct H as ((lo & hi & Hin & Hlh) & _). pose proof (proj1 (Forall_forall _ _) HCS (lo, hi) Hin) as Dr. cbn [fst snd] in Dr.
    apply (disjoint_outside W lo (hi - lo)); [|lia].
    apply HW_img; [| | exact Dr]; unfold CLIENT_STATIC in Hin; destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold SEGTOP_A; lia.
  - destruct H as (p & n & Hin & Hpx). apply (disjoint_outside W p n); [|lia].
    destruct (HL' p n Hin) as [(c & i & Hc & Hn & -> & HD)|(k & s & Hk & Hq & Hn' & -> & HD)].
    + pose proof (fk_slot c i _ Hc Hn) as (S1 & S2 & S3 & S4).
      assert (Hfit : rz_size n + n <= ClassSize c /\ 0 <= n).
      { pose proof HG as (_ & HR & _). destruct HR as (HR & _).
        pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
        pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
      pose proof (fl_rz_facts n) as (R1 & R2).
      apply (HW_slot c i (CkAlloc n)); [exact Hc | exact Hn | exact HD | unfold p_ubeg; lia | unfold p_ubeg; lia].
    + pose proof (fk_map k s Hk) as (_ & _ & _ & _ & _ & _ & _ & Hroom & Hu & _).
      apply (HW_secmap k s); [exact Hk | exact HD | unfold s_ubeg; lia | unfold s_ubeg; rewrite <- Hn'; lia].
  - destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W f (fs_size k - 8)); [|lia].
    destruct (g_frame Σ HG f k Hin) as (Y1 & Y2 & Y3). apply fk_fsb; lia.
  - destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W (shad f) (shad (f + fs_size k) - shad f)); [|lia].
    destruct (g_frame Σ HG f k Hin) as (Y1 & Y2 & Y3). pose proof fk_fsb_off as Off.
    pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _ & G3 & _).
    pose proof fk_aceil as (_ & X).
    apply (HW_shad_app f (f + fs_size k)); [lia | lia | lia | | lia | lia].
    intros k' s' Hk' _. pose proof (fk_fsb_maps k' s' Hk'). lia.
Qed.

End FKit.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface D_defs D_kit R_sizeclass R_cache_defs R_prim_defs
  R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc
  RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CONSTS_LITS : list (Z * Z) :=
  [ (809720, 809744); (809744, 809745); (0xbfa38, 0xbfa40); (0xbfa48, 0xbfa50); (0x158be0, 0x158be8); (0x15acf8, 0x15ad00);
    (0x15ad6c, 0x15ad6d); (0xc89a0, 0xc89a1); (0xc89a4, 0xc89a8); (0x5fc080, 0x5fc088); (0x61d480, 0x61d488);
    (0xbfa58, 0xbfa78); (0xc9138, 0xc9140); (0xc9e20, 0xc9e38); (0xbfa78, 0xbfa80); (0xc18d0, 0xc18d8); (0xc899c, 0xc899d);
    (0x15ace0, 0x15ace8); (784984, 784992); (823608, 823616); (785072, 785080); (823616, 823620);
    (0x15ad5d, 0x15ad5e); (0x15ad64, 0x15ad65); (0xbfa50, 0xbfa58); (0xbfa80, 0xbfa88); (0xc18c8, 0xc18d0); (0xc6955, 0xc6956);
    (0xc9e3c, 0xc9e40); (0x15ac8a, 0x15ac8b); (0xc06d0, 0xc06d8); (0xc06d8, 0xc06e0); (0xc06f0, 0xc06f8); (0xc05c0, 0xc05c8); (0xc9e19, 0xc9e1a);
    (0xc1790, 0xc1798); (0xc1878, 0xc1880); (0xc1768, 0xc1770); (0x15ad63, 0x15ad64); (0xc68f8, 0xc6900); (0xc6900, 0xc6904);
    (0x14b3a2, 0x14b3a3); (0xc6964, 0xc6968); (0xc696c, 0xc6970); (0xc698d, 0xc698e); (0x5fc0e8, 0x5fc0ec); (0xc06b0, 0xc06b8);
    (0x15ac00, 0x15ac08); (0x15ac08, 0x15ac10); (0xc5df0, 0xc5e08); (0xc6968, 0xc696c);
    (0xc17a0, 0xc17b8); (0xc69f0, 0xc69f8); (0xbf4e0, 0xbf4f8); (0xbf950, 0xbf958); (0xbfa28, 0xbfa38); (0xc06b8, 0xc06c8); (0xc06c8, 0xc06d0);
    (0xc06e0, 0xc06f0); (0xc0720, 0xc0730); (0xc1760, 0xc1768); (0xc17c0, 0xc17d8); (0xc6950, 0xc6954); (0x15acbc, 0x15acbd);
    (0x15afe0, 0x15afe1); (0xc1780, 0xc1790); (0x15ad66, 0x15ad68);
    (* [comment removed for export] *)
    (0xbfa98, 0xbfaa0); (0x15ad43, 0x15ad44); (0x15ad5c, 0x15ad5d); (0x61c398, 0x61c3a0) ].

(* [comment removed for export] *)
Local Lemma In_CONSTS_LITS_b : forall e : Z * Z,
  existsb (fun p => andb (Z.eqb (fst p) (fst e)) (Z.eqb (snd p) (snd e))) CONSTS_LITS = true -> In e CONSTS_LITS.
Proof.
  intros [x y] H. apply existsb_exists in H. destruct H as ([a b] & Hin & Hb). apply andb_true_iff in Hb.
  destruct Hb as [H1 H2]. cbn [fst snd] in H1, H2. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst a b. exact Hin.
Qed.

Lemma consts_rngs_kind : forall L r, In r (consts_rngs L) ->
  In r CONSTS_LITS \/ (l_T L <= fst r /\ snd r <= l_T L + 0x30) \/ r = (l_T L + 0xc60, l_T L + 0xc60 + 1)
  \/ (l_TCX L <= fst r /\ snd r <= l_TCX L + 0x10000).
Proof.
  intros L r Hr. unfold consts_rngs in Hr. unfold_consts.
  (* [comment removed for export] *)
  repeat (destruct Hr as [<-|Hr]; [first [solve [left; lazymatch goal with |- In ?e _ =>
                                                   lazymatch e with context [L] => fail | _ => idtac end end;
                                                 apply In_CONSTS_LITS_b; vm_compute; reflexivity]
                                         | solve [right; left; cbn [fst snd]; lia] | solve [right; right; left; reflexivity]
                                         | solve [right; right; right; cbn [fst snd]; lia]] |]).
  destruct Hr.
Qed.

Lemma dsjb_all : forall V l, forallb (fun r => dsjb V (fst r) (snd r - fst r)) l = true ->
  Forall (fun r => disjoint_from V (fst r) (snd r - fst r)) l.
Proof.
  intros V l H. apply Forall_forall. intros r Hr. exact (dsjb_sound _ _ _ (proj1 (forallb_forall _ _) H r Hr)).
Qed.
Lemma dsjb_all' : forall V l, forallb (fun r => dsjb V (fst r) (snd r)) l = true -> Forall (fun r => disjoint_from V (fst r) (snd r)) l.
Proof.
  intros V l H. apply Forall_forall. intros r Hr. exact (dsjb_sound _ _ _ (proj1 (forallb_forall _ _) H r Hr)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DEP_LITS : list (Z * Z) :=
  [(0x1ab018, 0x5ab018 + 4 - 0x1ab018); (0x5ab028, 8); (0x19b008, 8); (0x19b018, 0x19b020 + 4 - 0x19b018)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ris_of_whole : forall SB (W : list ivl) (DC : list Z), (forall a n, RIS_of SB <= a -> a + n <= RIS_of SB + 4096 -> disjoint_from W a n) ->
  forall c a n, 1 <= c <= 31 -> ~ In c DC -> rinfo (RIS_of SB) c <= a -> a + n <= rinfo (RIS_of SB) c + 120 -> disjoint_from W a n.
Proof. intros SB W DC H c a n Hc _ H1 H2. apply H; unfold rinfo in *; lia. Qed.

Section FKit.
Variables (Σ : rtsA) (m : mem) (W : list ivl) (D : list (Z * nat)) (DS : list nat) (TZ IZ : list ivl) (usp : Z) (DC : list Z).
Hypothesis HG : geo_ok Σ.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Hypothesis HW_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from IZ a n -> disjoint_from W a n.
Hypothesis HW_T : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from TZ a n -> disjoint_from W a n.
Hypothesis HW_grant : forall i b gn a n, nth_error (startup_grants L) i = Some (b, gn) -> (i = 1 \/ i = 3 \/ i = 4 \/ i = 5)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
(* [comment removed for export] *)
Hypothesis HW_ris : forall c a n, 1 <= c <= 31 -> ~ In c DC -> rinfo (RIS_of SB) c <= a -> a + n <= rinfo (RIS_of SB) c + 120 ->
  disjoint_from W a n.
Hypothesis HW_fa : forall c a n, 1 <= c <= 31 -> ~ In c DC -> fa SB c <= a -> a + n <= fa SB c + kFaCap -> disjoint_from W a n.
Hypothesis HW_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
  p_abeg SB c i <= a -> a + n <= p_abeg SB c i + ClassSize c -> disjoint_from W a n.
Hypothesis HW_shad_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
  shad (p_abeg SB c i) <= a -> a + n <= shad (p_abeg SB c i + ClassSize c) -> disjoint_from W a n.
Hypothesis HW_shad_reg : forall c a n, 1 <= c <= 31 -> ~ In c DC -> shad (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) <= a ->
  a + n <= shad (rb SB c + 2 ^ 32) -> disjoint_from W a n.
Hypothesis HW_shad_app : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= l_PRB L \/ l_PRB L + 0x2000011000 <= lo) ->
  (forall k s, nth_error (sec Σ) k = Some s -> In k DS -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo) ->
  shad lo <= a -> a + n <= shad hi -> disjoint_from W a n.
Hypothesis HW_secmap : forall k s a n, nth_error (sec Σ) k = Some s -> ~ In k DS -> s_mb s <= a -> a + n <= s_mb s + smsz (s_n s) ->
  disjoint_from W a n.

Lemma fk_aceil : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47.
Proof. pose proof (g_aceil Σ HG) as (X & Y & _). lia. Qed.

Lemma fk_prb : 0 < l_PRB L /\ l_PRB L + 0x2000011000 <= l_ACEIL L /\ SEGTOP_A <= l_PRB L /\ l_PRB L <= SB
  /\ SB + 2 ^ 37 + 4096 <= l_PRB L + 0x2000011000.
Proof.
  pose proof (g_prb Σ HG) as (P1 & P2 & P3).
  pose proof (g_grant Σ HG (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _ & G5).
  unfold SEGTOP_A in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma fk_slot : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  rb SB c <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))
  /\ ClassSize c * Z.of_nat (length (r_st (pr Σ c))) <= r_muser (pr Σ c) <= kUserCap /\ 32 <= ClassSize c.
Proof.
  intros c i st Hc Hn. pose proof HG as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & _ & W3 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm).
  pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
  assert (Hx : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
  { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
    replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
    apply Z.mul_le_mono_nonneg_r; lia. }
  assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
  unfold p_abeg, rb in *. repeat split; lia.
Qed.

Lemma kv_reg : forall c, 1 <= c <= 31 -> ~ In c DC -> reg_avoid W SB c (pr Σ c).
Proof.
  intros c Hc HDC. pose proof fk_prb as (P0 & P1 & P2 & P3 & P4). pose proof HG as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm32).
  assert (Hau : 0 <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) by (apply Z.mul_nonneg_nonneg; lia).
  unfold reg_avoid. split; [|split].
  - apply (HW_ris c); [exact Hc | exact HDC | lia | lia].
  - apply (HW_fa c); [exact Hc | exact HDC | lia | unfold kFaCap in *; lia].
  - apply (HW_shad_reg c); [exact Hc | exact HDC | lia|].
    pose proof (div8_add (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c))))
                  ltac:(unfold rb; lia) ltac:(lia)) as X.
    assert ((rb SB c + r_muser (pr Σ c)) / 8 <= (rb SB c + 2 ^ 32) / 8) by (apply Z.div_le_mono; unfold kUserCap in *; lia).
    pose proof (Z.div_pos (r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) 8 ltac:(lia) ltac:(lia)).
    replace (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c))) + (r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c)))))
      with (rb SB c + r_muser (pr Σ c)) in X by ring.
    unfold shad. lia.
Qed.

Lemma kv_pclass : forall c, 1 <= c <= 31 -> disjoint_from TZ (pc_addr T c) 80 -> pclass_avoid W T c.
Proof. intros c Hc HZ. unfold pclass_avoid. apply HW_T; [unfold pc_addr; lia | unfold pc_addr; lia | exact HZ]. Qed.

(* [comment removed for export] *)
Lemma fk_shad_le : forall a x y, 0 <= a -> 0 <= x -> 0 <= y -> shad a + x / 8 + y / 8 <= shad (a + x + y).
Proof. intros a x y Ha Hx Hy. unfold shad. pose proof (div8_add3 a x y Ha Hx Hy). pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). lia. Qed.

Lemma fk_shad_le2 : forall a x, 0 <= a -> 0 <= x -> shad a + x / 8 <= shad (a + x).
Proof. intros a x Ha Hx. unfold shad. pose proof (div8_add a x Ha Hx). lia. Qed.

Lemma fk_shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

(* [comment removed for export] *)
Lemma kv_pchunk_gen : forall c i st st', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
  (forall n, st' = CkAlloc n \/ st' = CkQuar n -> rz_size n + n <= ClassSize c /\ 0 <= n) -> pchunk_avoid W SB c i st'.
Proof.
  intros c i st st' Hc Hn HD Hfit. pose proof (fk_slot c i st Hc Hn) as (S1 & S2 & S3 & S4). pose proof fk_prb as (P0 & _ & _ & P3 & _).
  unfold pchunk_avoid. set (AB := p_abeg SB c i) in *. set (S := ClassSize c) in *.
  assert (HAB : 0 <= AB) by (unfold rb in S1; lia).
  assert (HS0 : 0 <= S / 8) by (apply Z.div_pos; lia).
  assert (HSE : shad AB + S / 8 <= shad (AB + S)) by exact (fk_shad_le2 AB S HAB ltac:(lia)).
  assert (SHS : forall a k, shad AB <= a -> a + k <= shad (AB + S) -> disjoint_from W a k) by (intros a k H1 H2; exact (HW_shad_slot c i st a k Hc Hn HD H1 H2)).
  assert (SL : forall a k, AB <= a -> a + k <= AB + S -> disjoint_from W a k) by (intros a k H1 H2; exact (HW_slot c i st a k Hc Hn HD H1 H2)).
  clear HD. destruct st' as [|n|n|].
  - apply SHS; lia.
  - destruct (Hfit n (or_introl eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
    pose proof (fl_ushadow_len n F2) as U. assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
    assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia).
    split; [apply SL; lia|].
    split; [intros _; apply SL; lia|].
    pose proof (fk_shad_le AB (rz_size n) (ru8 n) HAB ltac:(lia) Hu) as E1.
    pose proof (fk_shad_mono (AB + rz_size n + ru8 n) (AB + S) ltac:(lia)) as E2.
    split.
    + rewrite length_app, Nat2Z.inj_add, farun_lenZ, U by lia.
      apply SHS; lia.
    + pose proof (fk_shad_le2 (AB + rz_size n + ru8 n) (S - rz_size n - ru8 n) ltac:(lia) ltac:(lia)) as E3.
      replace (AB + rz_size n + ru8 n + (S - rz_size n - ru8 n)) with (AB + S) in E3 by ring.
      pose proof (fk_shad_mono AB (AB + rz_size n + ru8 n) ltac:(lia)) as E4.
      assert (0 <= (S - rz_size n - ru8 n) / 8) by (apply Z.div_pos; lia).
      apply SHS; lia.
  - destruct (Hfit n (or_intror eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
    assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
    assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia). assert (Hu8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
    assert (Hd8 : 0 <= (S - rz_size n - ru8 n) / 8) by (apply Z.div_pos; lia).
    split; [apply SL; lia|].
    split; [intros _; apply SL; lia|].
    rewrite !length_app, !Nat2Z.inj_add, !farun_lenZ, fdrun_lenZ by lia.
    pose proof (div8_add3 (rz_size n) (ru8 n) (S - rz_size n - ru8 n) ltac:(lia) Hu ltac:(lia)) as X.
    replace (rz_size n + ru8 n + (S - rz_size n - ru8 n)) with S in X by ring.
    apply SHS; lia.
  - apply SHS; lia.
Qed.

Lemma kv_pchunk : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D -> pchunk_avoid W SB c i st.
Proof.
  intros c i st Hc Hn HD. apply (kv_pchunk_gen c i st st Hc Hn HD).
  intros n Hs. pose proof HG as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
  pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. destruct Hs as [->| ->]; cbv beta iota in X; lia.
Qed.

(* [comment removed for export] *)
Lemma fk_map : forall k s, nth_error (sec Σ) k = Some s ->
  64513 <= s_n s /\ 0 < s_mb s /\ s_mb s + smsz (s_n s) <= l_ACEIL L /\ (s_mb s + smsz (s_n s) <= 0x10000 \/ SEGTOP_A <= s_mb s)
  /\ apart (s_mb s) (smsz (s_n s)) (l_PRB L) 0x2000011000 /\ apart (s_mb s) (smsz (s_n s)) (l_FSB L) 0xb09000
  /\ Forall (fun g => apart (s_mb s) (smsz (s_n s)) (fst g) (snd g)) (startup_grants L)
  /\ 6144 + ru8 (s_n s) <= smsz (s_n s) /\ s_n s <= ru8 (s_n s)
  /\ (forall k' s', nth_error (sec Σ) k' = Some s' -> k' <> k -> apart (s_mb s) (smsz (s_n s)) (s_mb s') (smsz (s_n s'))).
Proof.
  intros k s Hk. pose proof HG as (_ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & HSP & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (Hn & (G1 & G2 & G3 & G4 & G5) & Hp & Hf & HGs).
  assert (Hroom : 6144 + ru8 (s_n s) <= smsz (s_n s)).
  { unfold smsz, pg_up, needed, rounded, ru8. rewrite (rz_size_big (s_n s)) by lia. rewrite Z.max_l by lia. rewrite Z.max_l by lia.
    assert (8 * ((s_n s + 7) / 8) + 2048 + 2048 <= (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) / 4096 * 4096); [|lia].
    pose proof (Z.mod_pos_bound (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
    pose proof (Z.div_mod (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia. }
  assert (Hu : s_n s <= ru8 (s_n s)) by (unfold ru8; pose proof (Z.div_mod (s_n s + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (s_n s + 7) 8 ltac:(lia)); lia).
  split; [lia|]. split; [exact G1|]. split; [exact G3|]. split; [exact G5|]. split; [exact Hp|]. split; [exact Hf|]. split; [exact HGs|].
  split; [exact Hroom|]. split; [exact Hu|]. intros k' s' Hk' Hne. exact (HSP k k' s s' Hk Hk' (fun E => Hne (eq_sym E))).
Qed.

Lemma kv_schunk : forall k s, nth_error (sec Σ) k = Some s -> ~ In k DS -> schunk_avoid W s.
Proof.
  intros k s Hk HD. pose proof (fk_map k s Hk) as (Hn & G1 & G3 & G5 & Hp & _ & _ & Hroom & Hu & HSP). pose proof fk_aceil as (_ & X).
  assert (HDS : forall k' s', nth_error (sec Σ) k' = Some s' -> In k' DS -> s_mb s + smsz (s_n s) <= s_mb s' \/ s_mb s' + smsz (s_n s') <= s_mb s).
  { intros k' s' Hk' Hin. assert (k' <> k) by (intros ->; exact (HD Hin)). pose proof (HSP k' s' Hk' H) as Ha. unfold apart in Ha. lia. }
  assert (Hoff : s_mb s + smsz (s_n s) <= l_PRB L \/ l_PRB L + 0x2000011000 <= s_mb s) by (unfold apart in Hp; lia).
  assert (SH : forall a n, shad (s_mb s) <= a -> a + n <= shad (s_mb s + smsz (s_n s)) -> disjoint_from W a n).
  { intros a n H1 H2. apply (HW_shad_app (s_mb s) (s_mb s + smsz (s_n s))); [lia | lia | exact Hoff | exact HDS | exact H1 | exact H2]. }
  assert (Hu8 : 0 <= ru8 (s_n s)) by lia.
  unfold schunk_avoid.
  split; [apply (HW_secmap k s); [exact Hk | exact HD | lia | lia]|].
  split; [apply (HW_secmap k s); [exact Hk | exact HD | lia | lia]|].
  split; [apply (HW_secmap k s); [exact Hk | exact HD | lia | destruct (s_quar s); lia]|].
  pose proof (fk_shad_le2 (s_mb s) 6144 ltac:(lia) ltac:(lia)) as E1. change (6144 / 8) with 768 in E1.
  pose proof (fk_shad_le2 (s_mb s + 6144) (ru8 (s_n s)) ltac:(lia) Hu8) as E2.
  pose proof (fk_shad_le2 (s_mb s + 6144 + ru8 (s_n s)) (smsz (s_n s) - 6144 - ru8 (s_n s)) ltac:(lia) ltac:(lia)) as E3.
  replace (s_mb s + 6144 + ru8 (s_n s) + (smsz (s_n s) - 6144 - ru8 (s_n s))) with (s_mb s + smsz (s_n s)) in E3 by ring.
  assert (0 <= (smsz (s_n s) - 6144 - ru8 (s_n s)) / 8) by (apply Z.div_pos; lia). assert (0 <= ru8 (s_n s) / 8) by (apply Z.div_pos; lia).
  pose proof (fk_shad_mono (s_mb s + 6144 + ru8 (s_n s)) (s_mb s + smsz (s_n s)) ltac:(lia)) as E4.
  pose proof (fk_shad_mono (s_mb s) (s_mb s + 6144) ltac:(lia)) as E5.
  pose proof (fk_shad_mono (s_mb s + 6144) (s_mb s + 6144 + ru8 (s_n s)) ltac:(lia)) as E6.
  replace (s_mb s + 4096 + 2048) with (s_mb s + 6144) by ring.
  split; [change ((4096 + 2048) / 8) with 768; apply SH; [lia | rewrite Z.max_r by lia; lia]|].
  split.
  - apply SH; [lia|]. destruct (s_quar s); [rewrite fdrun_lenZ by (apply Z.div_pos; lia) | rewrite (fl_ushadow_len (s_n s)) by lia]; lia.
  - apply SH; [lia | ]. replace (smsz (s_n s) - 4096 - 2048 - ru8 (s_n s)) with (smsz (s_n s) - 6144 - ru8 (s_n s)) by ring.
    rewrite Z.max_r by (apply Z.div_pos; lia). lia.
Qed.

Lemma kv_sec : Forall (fun r => disjoint_from IZ (fst r) (snd r)) sec_lits -> sec_avoid W Σ.
Proof.
  intros HZ. split.
  - apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
      unfold sec_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold i_sec_chunks, i_sec_nres, i_sec_mutex, i_sec_page,
      i_sec_range, i_sec_sorted, i_sec_bylog, i_gstat_alloc, INST, g_instance, SEGTOP_A; lia|]); destruct Hr.
  - pose proof HG as (_ & _ & HS & _). destruct HS as (_ & Hn & _).
    apply (HW_grant 1 (l_PAB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma kv_quar : disjoint_from TZ (qcacheT T) 32 -> Forall (fun r => disjoint_from IZ (fst r) (snd r)) [(i_q_global, 32); (i_q_cmutex, 4)] ->
  (forall i, nth_error (r_st (pr Σ 24)) i = Some CkBatch -> ~ In (24, i) D) ->
  Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) (ql Σ ++ qg Σ) ->
  quar_avoid W Σ.
Proof.
  intros HZ HI HB HBt. split; [apply HW_T; [unfold qcacheT; lia | unfold qcacheT; lia | exact HZ]|].
  split.
  - apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HI r Hr)];
      destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; unfold i_q_global, i_q_cmutex, INST, g_instance, SEGTOP_A; lia.
  - 
    apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HBt b Hb) as (i & Hi & E). rewrite E.
    pose proof (fk_slot 24 i CkBatch ltac:(lia) Hi) as (S1 & S2 & S3 & S4). change (ClassSize 24) with 8192 in *.
    apply (HW_slot 24 i CkBatch); [lia | exact Hi | exact (HB i Hi) | lia | change (ClassSize 24) with 8192; lia].
Qed.

Lemma kv_dep : Forall (fun r => disjoint_from IZ (fst r) (snd r)) DEP_LITS ->
  (forall i b gn a n, nth_error (startup_grants L) i = Some (b, gn) -> (i = 6 \/ i = 7)%nat -> b <= a -> a + n <= b + gn -> disjoint_from W a n) ->
  dep_avoid W L.
Proof.
  intros HZ HD. split.
  - apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
      unfold DEP_LITS in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold SEGTOP_A; lia|]); destruct Hr.
  - split; [apply (HD 6%nat (l_DNB L) 0x100000); [reflexivity | lia | lia | lia]|].
    apply (HD 7%nat (l_SSB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma kv_ia : Forall (fun r => disjoint_from IZ (fst r) (snd r)) ia_lits -> dsjl W ia_lits.
Proof.
  intros HZ. apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
    unfold ia_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold g_ia_word, IAP, SEGTOP_A; lia|]); destruct Hr.
Qed.

Lemma fk_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 -> disjoint_from W a n.
Proof. intros a n H1 H2. exact (HW_grant 5 (l_FSB L) 0xb09000 a n eq_refl ltac:(lia) H1 H2). Qed.

(* [comment removed for export] *)
Lemma fk_fsb_off : l_FSB L + 0xb09000 <= l_PRB L \/ l_PRB L + 0x2000011000 <= l_FSB L.
Proof. pose proof (g_apart Σ HG 0 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in X. lia. Qed.

Lemma fk_fsb_maps : forall k s, nth_error (sec Σ) k = Some s -> l_FSB L + 0xb09000 <= s_mb s \/ s_mb s + smsz (s_n s) <= l_FSB L.
Proof. intros k s Hk. pose proof (fk_map k s Hk) as (_ & _ & _ & _ & _ & Hf & _). unfold apart in Hf. lia. Qed.

Lemma kv_fs_cls : forall k, (k = 0 \/ k = 2 \/ k = 3 \/ k = 6 \/ k = 7)%nat -> fs_cls_avoid W (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof.
  intros k Hk. pose proof HG as (_ & _ & _ & HF). destruct HF as (F0 & F2 & F4 & _).
  assert (Hwf : flags_ok (Z.of_nat k) (fss_flags (fs_of Σ k))) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; [exact (proj1 F0) | exact (proj1 F2) | exact (proj1 (proj1 F4)) | exact (proj1 (proj1 (proj2 F4))) | exact (proj1 (proj2 (proj2 F4)))]).
  destruct Hwf as [Hlen _].
  assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 3 \/ Z.of_nat k = 6 \/ Z.of_nat k = 7) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
  pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  pose proof fk_aceil as (_ & X). pose proof (fl_flags_range _ Hc) as (R1 & R2). pose proof fk_fsb_off as Off.
  unfold fs_cls_avoid. split; [apply fk_fsb; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; lia|]. split.
  - rewrite Hlen. apply fk_fsb; unfold fl_base; lia.
  - intros p Hp _. pose proof (frame_addr_range (l_FSB L) (Z.of_nat k) p Hc Hp) as (A1 & A2). unfold kFakeStackSize in A2.
    assert (Hfz : 0 < fsz (Z.of_nat k)) by (unfold fsz; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
    split; [apply fk_fsb; lia|].
    pose proof (fk_shad_le2 (frame_addr (l_FSB L) (Z.of_nat k) p) (fsz (Z.of_nat k)) ltac:(lia) ltac:(lia)) as E.
    apply (HW_shad_app (frame_addr (l_FSB L) (Z.of_nat k) p) (frame_addr (l_FSB L) (Z.of_nat k) p + fsz (Z.of_nat k))); [lia | lia | lia | | lia | lia].
    intros k' s' Hk' _. pose proof (fk_fsb_maps k' s' Hk'). lia.
Qed.

Lemma kv_fs : Forall (fun r => disjoint_from IZ (fst r) (snd r)) fs_lits -> disjoint_from TZ (T + 48) 16 -> fs_avoid W Σ.
Proof.
  intros HZ HT. pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
  unfold fs_avoid. split; [apply fk_fsb; lia|].
  split; [exact (kv_fs_cls 0%nat ltac:(lia))|]. split; [exact (kv_fs_cls 2%nat ltac:(lia))|]. split; [exact (conj (kv_fs_cls 3%nat ltac:(lia)) (conj (kv_fs_cls 6%nat ltac:(lia)) (kv_fs_cls 7%nat ltac:(lia))))|].
  split.
  { apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
      unfold fs_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold tpA, g_real_tls_get_addr, g_dtv_ptr, g_dtv1,
      g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; lia|]);
      destruct Hr. }
  split; [apply (HW_grant 4 (l_DTV L) 4096); [reflexivity | lia | lia | lia]|].
  split; [apply HW_T; [lia | lia | exact HT]|].
  apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (g_frame Σ HG f k Hin) as (X1 & X2 & X3). apply fk_fsb; lia.
Qed.

Lemma kv_shadow : shadow_avoid W L.
Proof.
  pose proof fk_aceil as (X1 & X2). pose proof fk_prb as (P0 & P1 & P2 & _).
  split.
  - pose proof (fk_shad_le2 (l_ACEIL L) (2 ^ 47 - l_ACEIL L) ltac:(unfold SHB in *; lia) ltac:(lia)) as E.
    replace (l_ACEIL L + (2 ^ 47 - l_ACEIL L)) with (2 ^ 47) in E by ring.
    assert (0 <= (2 ^ 47 - l_ACEIL L) / 8) by (apply Z.div_pos; lia).
    apply (HW_shad_app (l_ACEIL L) (2 ^ 47)); [unfold SHB in *; lia | lia | lia | | lia | rewrite Z.max_r by (apply Z.div_pos; lia); lia].
    intros k s Hk _. pose proof (fk_map k s Hk) as (_ & _ & G3 & _). lia.
  - apply Forall_forall. intros r Hr.
    assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0x61d9b8) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
    apply (HW_shad_app 0x10000 SEGTOP_A); [lia | unfold SEGTOP_A; lia | unfold SEGTOP_A in *; lia | | apply fk_shad_mono; lia | ].
    + intros k s Hk _. pose proof (fk_map k s Hk) as (Hn & G1 & _ & G5 & _ & _ & _ & Hroom & Hu & _). unfold SEGTOP_A in *. lia.
    + assert ((snd r - 1) / 8 < 801792) by (apply Z.div_lt_upper_bound; lia).
      assert (shad (snd r - 1) + 1 <= shad SEGTOP_A) by (unfold shad, SEGTOP_A; change (0x61e000 / 8) with 801792; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma kv_consts : Forall (fun r => disjoint_from IZ (fst r) (snd r - fst r)) CONSTS_LITS -> disjoint_from TZ T 0x30 ->
  forall x, in_rngs (consts_rngs L) x -> x <> T + 0xc60 -> outside W x.
Proof.
  intros HZ HTZ x Hx Hne. unfold in_rngs in Hx. apply Exists_exists in Hx as (r & Hr & Hrx). cbv beta in Hrx.
  destruct (consts_rngs_kind L r Hr) as [Hl|[(H1 & H2)|[Er|(H1 & H2)]]].
  - pose proof (proj1 (Forall_forall _ _) HZ r Hl) as Dr.
    assert (Hrng : 0x10000 <= fst r /\ snd r <= SEGTOP_A) by (unfold CONSTS_LITS in Hl; repeat (destruct Hl as [<-|Hl]; [cbn; unfold SEGTOP_A; lia|]); destruct Hl).
    apply (disjoint_outside W (fst r) (snd r - fst r)); [apply HW_img; [lia | lia | exact Dr] | lia].
  - apply (disjoint_outside W x 1); [apply HW_T; [lia | lia | exact (dsj_sub TZ T 0x30 x 1 HTZ ltac:(lia) ltac:(lia))] | lia].
  - rewrite Er in Hrx. cbn [fst snd] in Hrx. lia.
  - apply (disjoint_outside W x 1); [|lia].
    apply (HW_grant 3 (l_TCX L) 0x10000); [reflexivity | lia | lia | lia].
Qed.

(* [comment removed for export] *)
Hypothesis HW_stack : forall a n, usp <= a -> a + n <= USTACK_TOP -> disjoint_from W a n.

Lemma kv_client : Forall (fun r => disjoint_from IZ (fst r) (snd r - fst r)) CLIENT_STATIC ->
  forall (L' : list (Z * Z)), (forall p n, In (p, n) L' ->
      (exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) /\ p = p_ubeg SB c i n /\ ~ In (c, i) D)
      \/ (exists k s, nth_error (sec Σ) k = Some s /\ s_quar s = false /\ s_n s = n /\ p = s_ubeg s /\ ~ In k DS)) ->
  forall x, aclient L' (frames Σ) usp x -> outside W x.
Proof.
  intros HCS L' HL' x Hx. destruct Hx as [H|[H|[H|[H|H]]]].
  - apply (disjoint_outside W x 1); [apply HW_stack; lia | lia].
  - destruct H as ((lo & hi & Hin & Hlh) & _). pose proof (proj1 (Forall_forall _ _) HCS (lo, hi) Hin) as Dr. cbn [fst snd] in Dr.
    apply (disjoint_outside W lo (hi - lo)); [|lia].
    apply HW_img; [| | exact Dr]; unfold CLIENT_STATIC in Hin; destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold SEGTOP_A; lia.
  - destruct H as (p & n & Hin & Hpx). apply (disjoint_outside W p n); [|lia].
    destruct (HL' p n Hin) as [(c & i & Hc & Hn & -> & HD)|(k & s & Hk & Hq & Hn' & -> & HD)].
    + pose proof (fk_slot c i _ Hc Hn) as (S1 & S2 & S3 & S4).
      assert (Hfit : rz_size n + n <= ClassSize c /\ 0 <= n).
      { pose proof HG as (_ & HR & _). destruct HR as (HR & _).
        pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
        pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
      pose proof (fl_rz_facts n) as (R1 & R2).
      apply (HW_slot c i (CkAlloc n)); [exact Hc | exact Hn | exact HD | unfold p_ubeg; lia | unfold p_ubeg; lia].
    + pose proof (fk_map k s Hk) as (_ & _ & _ & _ & _ & _ & _ & Hroom & Hu & _).
      apply (HW_secmap k s); [exact Hk | exact HD | unfold s_ubeg; lia | unfold s_ubeg; rewrite <- Hn'; lia].
  - destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W f (fs_size k - 8)); [|lia].
    destruct (g_frame Σ HG f k Hin) as (Y1 & Y2 & Y3). apply fk_fsb; lia.
  - destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W (shad f) (shad (f + fs_size k) - shad f)); [|lia].
    destruct (g_frame Σ HG f k Hin) as (Y1 & Y2 & Y3). pose proof fk_fsb_off as Off.
    pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _ & G3 & _).
    pose proof fk_aceil as (_ & X).
    apply (HW_shad_app f (f + fs_size k)); [lia | lia | lia | | lia | lia].
    intros k' s' Hk' _. pose proof (fk_fsb_maps k' s' Hk'). lia.
Qed.

End FKit.
