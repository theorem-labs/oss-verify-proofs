(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface RtB_Annot BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_MILB LbB_Own LbB_ContStmt LbB_ContV4R.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_V4WVotS LbB_V4W32S.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition le4s (xs : list Z) : list byte := flat_map (fun x => word_to_le_bytes 4 (Z_to_bv 64 x)) xs.

Lemma le4s_length : forall xs, length (le4s xs) = (4 * length xs)%nat.
Proof.
  induction xs as [|x xs IH]; [reflexivity|]. unfold le4s in *. cbn [flat_map length]. rewrite length_app, IH.
  rewrite CatExec.length_N_to_le_bytes. lia.
Qed.

Lemma Znth_cons_succ : forall x xs i, 0 <= i -> Znth (i + 1) (x :: xs) = Znth i xs.
Proof. intros x xs i Hi. unfold Znth. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity. Qed.
Lemma Znth_cons_0 : forall x xs, Znth 0 (x :: xs) = x.
Proof. reflexivity. Qed.
Lemma Zlen_cons : forall (x : Z) xs, Zlen (x :: xs) = Zlen xs + 1.
Proof. intros. unfold Zlen. cbn [length]. lia. Qed.
Lemma Zlen_app1 : forall (xs : list Z) x, Zlen (xs ++ [x]) = Zlen xs + 1.
Proof. intros. unfold Zlen. rewrite length_app. cbn [length]. lia. Qed.
Lemma Znth_app1_lt : forall xs x i, 0 <= i < Zlen xs -> Znth i (xs ++ [x]) = Znth i xs.
Proof. intros xs x i Hi. unfold Znth, Zlen in *. rewrite app_nth1 by lia. reflexivity. Qed.
Lemma Znth_app1_eq : forall xs x, Znth (Zlen xs) (xs ++ [x]) = x.
Proof. intros xs x. unfold Znth, Zlen. rewrite Nat2Z.id, app_nth2, Nat.sub_diag by lia. reflexivity. Qed.

Lemma bytes_at_le4s : forall m xs a,
  (forall i, 0 <= i < Zlen xs -> fldA m (a + 4 * i) 4 (Znth i xs)) -> 0 <= a -> a + 4 * Zlen xs < 2 ^ 64 ->
  bytes_at asegs m a (le4s xs).
Proof.
  intros m xs. induction xs as [|x xs IH]; intros a HF Ha Han.
  - apply bytes_at_nil. unfold Zlen in Han. cbn [length Z.of_nat] in Han. lia.
  - pose proof (Zlen_cons x xs) as ZC. assert (ZL : 0 <= Zlen xs) by (unfold Zlen; lia).
    unfold le4s. cbn [flat_map]. fold (le4s xs). apply bytes_at_app. split.
    + apply bytes_at_of_rdn; [lia | rewrite CatExec.length_N_to_le_bytes; rewrite Zlen_cons in Han; lia |].
      rewrite CatExec.length_N_to_le_bytes. pose proof (HF 0 ltac:(rewrite Zlen_cons; lia)) as F0.
      rewrite Z.add_0_r in F0. unfold fldA, fld in F0. rewrite Znth_cons_0 in F0. exact F0.
    + rewrite CatExec.length_N_to_le_bytes. rewrite Zlen_cons in Han. apply IH; [| lia | lia].
      intros i Hi. pose proof (HF (i + 1) ltac:(rewrite Zlen_cons; lia)) as Fi. rewrite Znth_cons_succ in Fi by lia.
      replace (a + 4 * (i + 1)) with (a + Z.of_nat 4 + 4 * i) in Fi by lia. exact Fi.
Qed.

Lemma le4s_slice : forall xs i, 0 <= i < Zlen xs ->
  firstn 4 (skipn (Z.to_nat (4 * i)) (le4s xs)) = word_to_le_bytes 4 (Z_to_bv 64 (Znth i xs)).
Proof.
  induction xs as [|x xs IH]; intros i Hi; [unfold Zlen in Hi; cbn in Hi; lia|].
  unfold le4s. cbn [flat_map]. fold (le4s xs).
  destruct (Z.eq_dec i 0) as [->|Hne].
  - replace (Z.to_nat (4 * 0)) with 0%nat by reflexivity. rewrite skipn_O. rewrite Znth_cons_0.
    rewrite firstn_app, CatExec.length_N_to_le_bytes, Nat.sub_diag. cbn [firstn].
    rewrite app_nil_r. apply firstn_all2. rewrite CatExec.length_N_to_le_bytes. lia.
  - rewrite Zlen_cons in Hi. replace (Z.to_nat (4 * i)) with (4 + Z.to_nat (4 * (i - 1)))%nat by lia.
    rewrite skipn_app, CatExec.length_N_to_le_bytes. replace (4 + Z.to_nat (4 * (i - 1)) - 4)%nat with (Z.to_nat (4 * (i - 1))) by lia.
    rewrite skipn_all2 by (rewrite CatExec.length_N_to_le_bytes; lia). cbn [app].
    replace i with ((i - 1) + 1) at 2 by lia. rewrite Znth_cons_succ by lia. apply IH. lia.
Qed.

Lemma fld_of_le4s : forall m a xs i, bytes_at asegs m a (le4s xs) -> 0 <= i < Zlen xs -> fldA m (a + 4 * i) 4 (Znth i xs).
Proof.
  intros m a xs i HB Hi. unfold fldA, fld.
  pose proof (bytes_at_rdn asegs m a (le4s xs) (Z.to_nat (4 * i)) 4 HB) as R.
  rewrite le4s_length in R. unfold Zlen in Hi. specialize (R ltac:(lia)).
  rewrite Z2Nat.id in R by lia. unfold wa in R. rewrite le4s_slice in R by (unfold Zlen; lia). exact R.
Qed.

Lemma fld_of_rw_cells8 : forall m a z, rw_cells asegs m a [C8 (Z_to_bv 64 z)] -> 0 <= a -> fldA m a 8 z.
Proof.
  intros m a z Hc Ha. unfold fldA, fld.
  pose proof (rw_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- rdn_of_ov. exact RD.
Qed.
Lemma fld_of_rw_cells4 : forall m a z, rw_cells asegs m a [C4 (Z_to_bv 64 z)] -> 0 <= a -> fldA m a 4 z.
Proof.
  intros m a z Hc Ha. unfold fldA, fld.
  pose proof (rw_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- rdn_of_ov. exact RD.
Qed.

Lemma rw_cells_split3 : forall m a w0 w1 w2, rw_cells asegs m a [C8 w0; C8 w1; C8 w2] ->
  rw_cells asegs m a [C8 w0] /\ rw_cells asegs m (a + 8) [C8 w1] /\ rw_cells asegs m (a + 16) [C8 w2].
Proof.
  intros m a w0 w1 w2 H. change [C8 w0; C8 w1; C8 w2] with ([C8 w0] ++ [C8 w1] ++ [C8 w2]) in H.
  apply rw_cells_app in H. destruct H as [H0 H]. cbn [cells_size csize] in H.
  apply rw_cells_app in H. destruct H as [H1 H2]. cbn [cells_size csize] in H2.
  split; [exact H0|]. split; [replace (a + 8) with (a + Z.of_nat (8 + 0)) by lia; exact H1|].
  replace (a + 16) with (a + Z.of_nat (8 + 0) + Z.of_nat (8 + 0)) by lia. exact H2.
Qed.

Lemma v4_seg_rom_hi : forall x : word, AIMG_TOP <= bv_unsigned x -> PropExec.seg_rom asegs x = None.
Proof.
  intros x Hx. unfold PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1%Z. unfold AIMG_TOP in Hx.
  change AsanUbsan.M.loaded_segments with asegs. rewrite BakeStackRep.find_segment_asegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x91000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x91000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x17e000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x17e000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x186000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x186000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x6e8000); cbn [andb]; try lia; reflexivity.
Qed.

Lemma v4_cells_size_map_C8' : forall (ws : list word), Z.of_nat (cells_size (map (fun w => C8 w) ws)) = 8 * Z.of_nat (length ws).
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IH. lia. Qed.

Lemma mdef_of_rw_cells_hi : forall m A cs, rw_cells asegs m A cs -> AIMG_TOP <= A -> mdef m A (Z.of_nat (cells_size cs)).
Proof.
  intros m A cs [[Hwf HB] _] Ha i Hi. pose proof HB as (B0 & B1 & B).
  rewrite (cells_bytes_length cs Hwf) in B1, B.
  specialize (B (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B by lia.
  destruct (nth_error (cells_bytes cs) (Z.to_nat i)) as [b|] eqn:Eb;
    [|apply nth_error_None in Eb; rewrite (cells_bytes_length cs Hwf) in Eb; lia].
  unfold mrd in B. change (wa (A + i)) with (Z_to_bv 64 (A + i)) in B.
  destruct (m (Z_to_bv 64 (A + i))) as [b'|] eqn:E; [discriminate|].
  change (BLPropExec.seg_rom asegs (Z_to_bv 64 (A + i))) with (PropExec.seg_rom asegs (Z_to_bv 64 (A + i))) in B.
  rewrite v4_seg_rom_hi in B by (change (Z_to_bv 64 (A + i)) with (wa (A + i)); rewrite wa_unsigned; unfold AIMG_TOP in *; lia).
  discriminate.
Qed.

Lemma v4_vec32_new : forall LB' m' v A xs x cap',
  rw_cells asegs m' v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (Zlen xs + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))] ->
  bytes_at asegs m' A (le4s xs) -> rw_cells asegs m' (A + 4 * Zlen xs) [C4 (Z_to_bv 64 x)] ->
  0 <= x < 2 ^ 32 -> (forall i, 0 <= i < Zlen xs -> 0 <= Znth i xs < 2 ^ 32) ->
  0 < A -> A mod 16 = 0 -> Zlen xs + 1 <= cap' -> A + 4 * cap' <= 2 ^ 47 -> In (A, 4 * cap') (lbl LB') ->
  (v + 24 <= A \/ A + 4 * cap' <= v) -> AIMG_TOP <= v -> v + 24 <= 2 ^ 47 ->
  vec32A LB' m' v A (xs ++ [x]) cap'.
Proof.
  intros LB' m' v A xs x cap' HC HB HX Hx Hxs A0 A16 Hc Hhi HIn Hd Hv0 Hv1.
  pose proof (rw_cells_split3 _ _ _ _ _ HC) as (C0 & C8' & C16).
  pose proof (mdef_of_rw_cells_hi _ _ _ HC Hv0) as MD. cbn [cells_size csize] in MD.
  unfold vec32A, vec32. rewrite Zlen_app1. unfold AIMG_TOP in Hv0.
  assert (ZL : 0 <= Zlen xs) by (unfold Zlen; lia).
  split; [lia|]. split; [lia|]. split; [exact MD|]. split; [lia|].
  split; [right; split; [lia|]; split; [exact A16|]; split; [lia|]; split; [lia|]; split; [exact HIn | exact Hd]|].
  split; [apply fld_of_rw_cells8; [exact C0 | lia]|].
  split; [apply fld_of_rw_cells8; [exact C8' | lia]|].
  split; [apply fld_of_rw_cells8; [exact C16 | lia]|].
  intros i Hi. destruct (Z.eq_dec i (Zlen xs)) as [->|Hne].
  - rewrite Znth_app1_eq. split; [exact Hx|]. apply fld_of_rw_cells4; [exact HX | lia].
  - rewrite Znth_app1_lt by lia. split; [apply Hxs; lia|]. apply fld_of_le4s; [exact HB | lia].
Qed.

Lemma nodup_id_same : forall (LB : list block) p A0 n0 A n, List.NoDup (map blk_id LB) -> In (p, A0, n0) LB -> In (p, A, n) LB ->
  (p, A0, n0) = (p, A, n).
Proof.
  induction LB as [|b0 LB IH]; intros p A0 n0 A n ND H1 H2; [destruct H1|].
  cbn [map] in ND. apply NoDup_cons_iff in ND as [NI ND].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - rewrite E1 in E2. exact E2.
  - exfalso. apply NI. rewrite E1. cbn [blk_id fst]. apply in_map_iff. exists (p, A, n). split; [reflexivity | exact H2].
  - exfalso. apply NI. rewrite E2. cbn [blk_id fst]. apply in_map_iff. exists (p, A0, n0). split; [reflexivity | exact H1].
  - exact (IH p A0 n0 A n ND H1 H2).
Qed.

Section LBR.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma lb_remove_keep : forall p LB bb, List.NoDup (map blk_id LB) -> In bb LB -> blk_id bb <> p -> In bb (as_lb_remove H p LB).
  Proof.
    pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    intros p LB. induction LB as [|b0 LB IH]; intros bb ND Hin Hne; [destruct Hin|].
    cbn [map] in ND. apply NoDup_cons_iff in ND as [NI ND].
    destruct (Z.eq_dec (blk_id b0) p) as [E|E].
    - destruct b0 as [[p0 A0] n0]. cbn [blk_id fst] in E. subst p0. rewrite L1 by exact NI.
      destruct Hin as [<-|Hin]; [cbn in Hne; lia | exact Hin].
    - rewrite (L2 p b0 LB E). destruct Hin as [<-|Hin]; [left; reflexivity | right; apply IH; assumption].
  Qed.

  Lemma xpres_of_apres_rm : forall s LB LBx SP X m0 m m' p A n,
    as_RHEAP H s LBx m0 -> In (p, A, n) LBx -> (forall bb, In bb LB -> In bb LBx) ->
    apres H (as_lb_remove H p LBx) SP m m' ->
    (forall a, A <= a < A + n -> rin_ivs X a) -> (forall a, sh A <= a < sh A + nsh n -> rin_ivs X a) ->
    xpres H LB SP X m m'.
  Proof.
    intros s LB LBx SP X m0 m m' p A n RH IN SUB AP HX1 HX2 a Ha [Hc Hx].
    pose proof (ah_nodup H HH _ _ _ RH) as ND.
    apply AP; [exact Ha|]. unfold aclient_addr in *.
    destruct Hc as [Hc|[Hc|[(bb & Hb & Hr)|[(bb & Hb & Hr)|Hc]]]]; [left; exact Hc | right; left; exact Hc | | | right; right; right; right; exact Hc].
    - right; right; left. exists bb. split; [|exact Hr]. apply lb_remove_keep; [exact ND | apply SUB; exact Hb |].
      intros E. destruct bb as [[p0 A0] n0]. cbn [blk_id blk_addr blk_size fst snd] in E, Hr. subst p0.
      assert (EQ : (p, A0, n0) = (p, A, n)).
      { eapply nodup_id_same; eauto. }
      inversion EQ; subst. apply Hx. apply HX1. lia.
    - right; right; right; left. exists bb. split; [|exact Hr]. apply lb_remove_keep; [exact ND | apply SUB; exact Hb |].
      intros E. destruct bb as [[p0 A0] n0]. cbn [blk_id blk_addr blk_size fst snd] in E, Hr. subst p0.
      assert (EQ : (p, A0, n0) = (p, A, n)).
      { eapply nodup_id_same; eauto. }
      inversion EQ; subst. apply Hx. apply HX2. lia.
  Qed.
End LBR.

Lemma v4_sh_hull : forall b n, 0 <= b -> b mod 8 = 0 -> 0 <= n ->
  sh (hull_lo b) <= sh b /\ sh b + nsh n <= sh (hull_hi (b + n)).
Proof.
  intros b n Hb H8 Hn. pose proof (hull_lo_le b Hb) as (L1 & L2 & L3). pose proof (hull_hi_ge (b + n) ltac:(lia)) as (K1 & K2 & K3).
  split; [apply sh_mono; lia|].
  unfold sh, nsh. Z.div_mod_to_equations. lia.
Qed.

Lemma v4_sh_apart : forall a n b k, 0 <= a -> 0 <= b -> a mod 8 = 0 -> b mod 8 = 0 -> 0 <= n -> 0 <= k ->
  (a + n <= b \/ b + k <= a) -> (sh a + nsh n <= sh b \/ sh b + nsh k <= sh a).
Proof. intros a n b k Ha Hb Ha8 Hb8 Hn Hk D. unfold sh, nsh. Z.div_mod_to_equations. lia. Qed.

Lemma v4_app_sh : forall a n b k, 0 <= b -> 0 <= k -> b + k <= 2 ^ 47 ->
  ((0 <= a /\ a + n <= 0x7fff7000) \/ 0x10007fff8000 <= a) ->
  a + n <= sh b \/ sh b + nsh k <= a.
Proof. intros a n b k Hb Hk Hbk Ha. unfold sh, nsh, ASHADOW_BASE. Z.div_mod_to_equations. lia. Qed.

Lemma v4_mod16_sub96 : forall z, z mod 16 = 0 -> (z - 96) mod 16 = 0.
Proof. intros z Hz. Z.div_mod_to_equations. lia. Qed.

Lemma v4_mod4_even : forall z k, z mod 4 = 0 -> k mod 4 = 0 -> (z + k) mod 2 = 0.
Proof. intros z k Hz Hk. Z.div_mod_to_equations. lia. Qed.

Lemma v4_mod16_8 : forall z, z mod 16 = 0 -> z mod 8 = 0.
Proof. intros z Hz. Z.div_mod_to_equations. lia. Qed.

Lemma v4_mod16_16le : forall z, 0 < z -> z mod 16 = 0 -> 16 <= z.
Proof. intros z H0 Hz. Z.div_mod_to_equations. lia. Qed.

Lemma v4_nsh24 : nsh 24 = 3.
Proof. reflexivity. Qed.

Lemma v4_src_shk : forall m src, accessible m src 4 -> src mod 4 = 0 -> 0 <= src ->
  exists k, LbB_Kit.shk m src k /\ (k = 0 \/ src mod 8 + 4 <= k < 8).
Proof.
  intros m src (A0 & A1 & AC) H4 H0.
  destruct (AC src ltac:(lia)) as (v0 & V0 & M0 & B0).
  destruct (AC (src + 3) ltac:(lia)) as (v1 & V1 & M1 & B1).
  assert (SH : sh (src + 3) = sh src) by (unfold sh; f_equal; Z.div_mod_to_equations; lia).
  rewrite SH, M0 in M1. assert (E : b8 v0 = b8 v1) by congruence.
  assert (E' : v0 = v1).
  { apply (f_equal (@bv_unsigned 8)) in E. unfold b8 in E. rewrite !Z_to_bv_unsigned in E.
    rewrite !bv_wrap_small in E by (unfold bv_modulus; cbn; lia). exact E. }
  subst v1. exists v0. split.
  - pose proof (shk_of_mrd m src (b8 v0) H0 M0) as K. unfold b8 in K. rewrite Z_to_bv_unsigned, bv_wrap_small in K by (unfold bv_modulus; cbn; lia).
    exact K.
  - unfold byte_ok in B1. clear - B1 V0 H4. Z.div_mod_to_equations. lia.
Qed.

Lemma bytes_of_CB : forall m A n bs, rw_cells asegs m A [CB n bs] -> bytes_at asegs m A bs.
Proof. intros m A n bs [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Lemma v4_new_granule : forall cap, 1 <= cap -> 4 * cap < 8 * (4 * vgrow cap / 8).
Proof.
  intros cap Hc. destruct (Z_le_gt_dec cap 1) as [L|L].
  - rewrite vgrow_le1 by lia. replace cap with 1 by lia. reflexivity.
  - rewrite vgrow_ge2 by lia. replace (4 * (2 * cap)) with (cap * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Definition vot_runs (E : Z) : Prop :=
  v4_B1 E /\ vot_B3a E /\ vot_B3ak E /\ vot_B3b E /\ vot_B3bk E /\ vot_B5 E /\ vot_B7 E /\ vot_B9D E /\ vot_B9N E
  /\ vot_B11 E /\ v4_ret_ok (E + 532).

Lemma vot_runs_100040 : vot_runs (v4_entry VOT_SLOW_CREF).
Proof.
  exact (conj v4_B1_fe724 (conj vot_B3a_100040 (conj vot_B3ak_100040 (conj vot_B3b_100040 (conj vot_B3bk_100040
    (conj vot_B5_100040 (conj vot_B7_100040 (conj vot_B9D_100040 (conj vot_B9N_100040 (conj vot_B11_100040
    v4_ret_ok_100040)))))))))).
Qed.

Lemma vot_runs_fb3d4 : vot_runs (v4_entry VOT_SLOW_RREF).
Proof.
  exact (conj v4_B1_fa4fc (conj vot_B3a_fb3d4 (conj vot_B3ak_fb3d4 (conj vot_B3b_fb3d4 (conj vot_B3bk_fb3d4
    (conj vot_B5_fb3d4 (conj vot_B7_fb3d4 (conj vot_B9D_fb3d4 (conj vot_B9N_fb3d4 (conj vot_B11_fb3d4
    v4_ret_ok_fb3d4)))))))))).
Qed.
Section V4S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable c : v4_consts.
  Hypothesis RUNS : vot_runs (v4_entry c).
  Hypothesis DRA : v4_del_ra c = v4_entry c + 488.

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
            (v b cap src x : Z) (xs : list Z) (pid : bptr) (lo B shi spz : Z).
  Hypothesis SPZ : bv_unsigned sp = spz.
  Hypothesis SPR : 2 ^ 45 <= spz - 112 /\ spz <= 2 ^ 47 /\ spz mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis TRO : trace_ok (as_TR H) APC0_FREE [v4_del_ra c].
  Hypothesis VBAND : (0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47).
  Hypothesis OBJ : obj_win H LB LF spz lo v 24.
  Hypothesis V8 : v mod 8 = 0.
  Hypothesis XSL : Zlen xs = cap.
  Hypothesis VEC : vec32A LB m v b xs cap.
  Hypothesis OLD : v4_oldblk LB b cap pid.
  Hypothesis OLDSH : 0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * cap)).
  Hypothesis GROW : 4 * v4_newcap cap <= 2 ^ 26.
  Hypothesis XR : 0 <= x < 2 ^ 31.
  Hypothesis SRC : src4_keep H LB spz m src x.
  Hypothesis SRCR : src mod 4 = 0 /\ 0 <= src /\ src + 4 <= 2 ^ 47.
  Hypothesis RH0 : as_RHEAP H s LB m.
  Hypothesis AOK : as_alloc_ok H s LB (4 * v4_newcap cap).
  Hypothesis CM : as_Cm H (4 * v4_newcap cap) + as_Cf H (4 * cap) <= as_AL H s.
  Hypothesis RA0 : as_rauxv_ok H m B.
  Hypothesis SPB : spz <= B.
  Hypothesis ST0 : stk asegs m lo spz.
  Hypothesis LOR : aceil <= lo /\ lo <= spz - V4_STACK.
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis AC0 : ACONST m.
  Hypothesis RF0 : as_RFS H LF m.
  Hypothesis S00 : stack0 m lo shi.
  Hypothesis SHI : spz <= shi.
  Hypothesis ADV0 : addressable m v 24.
  Hypothesis VWR : wr_at asegs m v 24.
  Hypothesis OWN : lb_own LB m.
  Hypothesis E0R : 0 <= v4_entry c < 0x200000 /\ v4_entry c mod 4 = 0.

  Let E0 := v4_entry c.
  Let cap' := v4_newcap cap.
  Let Q := v4slow_post H c ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap x xs pid lo B shi m mo.
  Let FRAME : list cell := map (fun w => C8 w) [Z_to_bv 64 v; s7; s6; s5; s4; s3; s2; s1; s0; ra].

  Lemma spz_sp : sp = Z_to_bv 64 spz.
  Proof. rewrite <- SPZ. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Definition v4_B5at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    vot_B5_pre R mk v (spz - 112) b cap A cap' (bv_unsigned s10) (bv_unsigned s9) (bv_unsigned s8) v cap' (4 * cap)
      ASHADOW_BASE (sh (v + 8)) (A + 4 * cap') src (v + 8) (E0 + 408).

  Definition v4_B7at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    vot_B7_pre R mk v (spz - 112) b cap A cap' (bv_unsigned s10) (bv_unsigned s9) (bv_unsigned s8) v cap' (4 * cap)
      ASHADOW_BASE (sh (v + 8)) (A + 4 * cap') src (v + 8) (E0 + 408).

  Definition v4_B9at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    vot_B9_pre R mk A (spz - 112) v src cap b cap' (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
      (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) (bv_unsigned s6) (bv_unsigned s7).

  Definition v4_B11at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    vot_B11_pre R mk A (spz - 112) v cap (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
      (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) (bv_unsigned s6) (bv_unsigned s7).

  Definition v4_mid (sk : as_St H) (mk : mem) (pid' : bptr) (A : Z) (Xk : list (Z * Z)) : Prop :=
    mem_inv asegs mk /\ stk asegs mk lo spz /\ (exists e, rw_cells asegs mk (errno_addr tp) [C4 e]) /\ as_rauxv_ok H mk B
    /\ ACONST mk /\ as_RFS H LF mk /\ stack0 mk lo shi /\ as_RHEAP H sk ((pid', A, 4 * cap') :: LB) mk
    /\ rw_cells asegs mk (spz - 80) FRAME /\ xpres H LB spz Xk m mk /\ as_AL H sk >= as_AL H s - as_Cm H (4 * cap')
    /\ lb_own ((pid', A, 4 * cap') :: LB) mk.

  Definition v4_wk (A : Z) (Xk : list (Z * Z)) (iv : Z * Z) : Prop :=
    (aceil <= fst iv /\ snd iv <= spz - 80)
    \/ (A <= fst iv /\ snd iv <= A + 4 * cap')
    \/ (sh A <= fst iv /\ snd iv <= sh A + nsh (4 * cap'))
    \/ ((forall a, fst iv <= a < snd iv -> rin_ivs Xk a) /\ aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv
        /\ stack0_ok iv /\ (snd iv <= spz - 80 \/ spz <= fst iv) /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)).

  Lemma v4_cls : forall s' LBx p A n SP m0 a,
    as_RHEAP H s' ((p, A, n) :: LBx) m0 -> ~ In p (map blk_id LBx) -> aceil <= SP -> aclient_addr H LBx SP a ->
    SP <= a \/ (a < aceil /\ ~ (A <= a < A + n) /\ ~ (sh A <= a < sh A + nsh n)).
  Proof.
    intros s' LBx p A n SP m0 a RH NI HSP Hc.
    pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    unfold blk_addr, blk_size in R0, R16, Rn, RI, RC, RF, RAPP. cbn [fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    pose proof aceil_facts as ACF.
    assert (SHA : sh A + nsh n <= sh aceil).
    { unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
    assert (SHB : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; acb; Z.div_mod_to_equations; lia).
    unfold AIMG_TOP in RI.
    assert (SHL : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    acb.
    unfold aclient_addr in Hc.
    destruct Hc as [Hc|[Hc|[(b0 & Hb & Hr)|[(b0 & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
    - left. exact Hc.
    - right. unfold aimg_client in Hc. destruct Hc as [Hc|[Hc|[Hc|Hc]]]; (split; [lia | split; lia]).
    - right. assert (Hb' : In b0 ((p, A, n) :: LBx)) by (right; exact Hb).
      assert (Hid : blk_id b0 <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
      pose proof (ah_disj H HH _ _ _ (p, A, n) b0 RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b0 RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
      destruct b0 as [[pb Ab] nb]. unfold blk_addr, blk_size in *. cbn [fst snd] in *.
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in QAPP, HI2.
      destruct D as [D|D]; destruct QAPP as [QAPP|QAPP]; split; try lia; split; lia.
    - right. assert (Hb' : In b0 ((p, A, n) :: LBx)) by (right; exact Hb).
      assert (Hid : blk_id b0 <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
      pose proof (ah_disj H HH _ _ _ (p, A, n) b0 RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b0 RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      unfold blk_addr, blk_size in D, Hr, Q0, Q16, Qn, QI, QC, QF, QAPP. cbn [fst snd] in D.
      destruct b0 as [[pb Ab] nb]. cbn [fst snd] in *.
      unfold aapp, aapp_lo, aapp_hi in RAPP, QAPP. acb.
      unfold nsh, sh, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      Z.div_mod_to_equations.
      destruct D as [D|D]; split; try lia; split; lia.
    - right. assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in F4, HI2. unfold AFS_SIZE in *.
      destruct RF as [RF|RF]; destruct F4 as [F4|F4]; split; try lia; split; lia.
    - right. unfold aapp, aapp_lo, aapp_hi in RAPP, F4. acb.
      unfold sh, nsh, AFS_SIZE, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      Z.div_mod_to_equations.
      destruct RF as [RF|RF]; split; try lia; split; lia.
    - right. assert (SA0 : 0x7fff8000 <= sh aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in RAPP, Hc. destruct RAPP as [RP|RP]; split; try lia; split; lia.
  Qed.

  Lemma v4_xpres_mixed : forall s' p A n SP X m0 m1 m2 W,
    as_RHEAP H s' ((p, A, n) :: LB) m0 -> ~ In p (map blk_id LB) -> aceil <= SP ->
    munch W m1 m2 -> wmono asegs m1 m2 ->
    Forall (fun iv : Z * Z => (A <= fst iv /\ snd iv <= A + n) \/ (sh A <= fst iv /\ snd iv <= sh A + nsh n)
                              \/ (aceil <= fst iv /\ snd iv <= SP) \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
    xpres H LB SP X m1 m2.
  Proof.
    intros s' p A n SP X m0 m1 m2 W RH NI HSP MU WM FW a Ha [Hc Hx].
    pose proof (v4_cls s' LB p A n SP m0 a RH NI HSP Hc) as CLS.
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[l h] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as H1. cbn in H1.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      destruct H1 as [[H1 H2]|[[H1 H2]|[[H1 H2]|H1]]].
      - destruct CLS as [C|(C1 & C2 & C3)]; [pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (_ & _ & _ & _ & RC & _); cbn in RC|]; lia.
      - destruct CLS as [C|(C1 & C2 & C3)].
        + assert (sh A + nsh n <= sh aceil).
          { pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & _ & Rn & _ & RC & _). cbn in *.
            unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
          assert (sh aceil < aceil) by (apply sh_below_aceil; acb; unfold AAPP_HI; lia). lia.
        + lia.
      - destruct CLS as [C|(C1 & C2 & C3)]; lia.
      - intros K. apply Hx. apply H1. exact K. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  Lemma v4_mid_munch : forall sk mk mk' pid' A Xk W,
    v4_mid sk mk pid' A Xk -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    munch W mk mk' -> wmono asegs mk mk' -> mem_inv asegs mk' -> Forall (v4_wk A Xk) W ->
    v4_mid sk mk' pid' A Xk.
  Proof.
    intros sk mk mk' pid' A Xk W (MI & ST & (e & ERR) & RA & AC & RF & S0 & RH & FR & XP & AL & OW) ABR NI MU WM MI' FW.
    destruct SPR as (SPL & SPH & SP16). destruct LOR as [LO1 LO2].
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof ABR as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
    pose proof (ah_fsb H HH _ _ _ RH) as (FS1 & FS2 & FS3 & FS4).
    assert (SHAb : sh A + nsh (4 * cap') <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHAl : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHAC : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHIT : sh AIMG_TOP <= sh A) by (unfold sh, AIMG_TOP; Z.div_mod_to_equations; lia).
    assert (VSPZ : AIMG_TOP <= lo) by (unfold AIMG_TOP; lia).
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.

    assert (W1 : Forall (aclient_write_ok H ((pid', A, 4 * cap') :: LB)) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold v4_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & Hw & _)]]].
      - left. cbn. lia.
      - right; right; left. exists (pid', A, 4 * cap'). split; [left; reflexivity | cbn; lia].
      - right; right; right; left. exists (pid', A, 4 * cap'). split; [left; reflexivity | cbn; lia].
      - unfold aclient_write_ok in *.
        destruct Hw as [K|[K|[(b' & Hb & K)|[(b' & Hb & K)|K]]]]; [left; exact K | right; left; exact K | | | right; right; right; right; exact K].
        + right; right; left. exists b'. split; [right; exact Hb | exact K].
        + right; right; right; left. exists b'. split; [right; exact Hb | exact K]. }
    assert (W2 : Forall (afs_write_ok H LF) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold v4_wk in Hw. cbn [fst snd] in Hw.
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in FS4, BAPP. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & Hw & _)]]]; [left; cbn; unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; lia | | | exact Hw].
      - left. cbn. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. split; [destruct BF; lia | lia].
      - left. cbn. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. split; [destruct FS4; lia | lia]. }
    assert (W3 : Forall aconst_ok W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold v4_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & Hw & _)]]]; [| | | exact Hw].
      - apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia].
      - eapply (aconst_ok_app A (4 * cap')); [exact BAPP | lia | lia].
      - apply aconst_ok_high; [lia | right; left; lia]. }
    assert (W4 : Forall stack0_ok W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold v4_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & Hw & _)]]]; [| | | exact Hw].
      - left. cbn. unfold AHI_LO. lia.
      - eapply (stack0_ok_aapp A (4 * cap')); [exact BAPP | lia | lia].
      - right. cbn. lia. }
    destruct (client_frame H HH sk _ LF B W mk mk' RH RF AC RA MU WM W1 W2 W3) as (RH' & RF' & AC' & RA').
    split; [exact MI'|]. split; [eapply BakeStackRep.stk_high_transport; [exact ST | exact WM | exact VSPZ]|].
    split.
    { exists e. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. subst tp. rewrite u64_of_Z by (unfold ATP; lia).
      eapply disjoint_from_of_Forall; [exact FW|]. intros l h Hw. unfold v4_wk in Hw. cbn [fst snd cells_size csize Z.of_nat] in *.
      unfold ATP in *. destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & _ & _ & Hw)]]]; lia. }
    split; [exact RA'|]. split; [exact AC'|]. split; [exact RF'|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact W4]|].
    split; [exact RH'|].
    split.
    { eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      eapply disjoint_from_of_Forall; [exact FW|]. intros l h Hw. unfold v4_wk in Hw. cbn [fst snd] in Hw.
      unfold FRAME. rewrite v4_cells_size_map_C8'. cbn [length].
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & _ & Hw & _)]]]; lia. }
    split; [|split; [exact AL | exact (lb_own_wmono _ _ _ OW WM)]].
    eapply (xpres_trans H); [exact XP|].
    eapply (v4_xpres_mixed sk pid' A (4 * cap') spz Xk mk mk mk' W RH NI ltac:(lia) MU WM).
    eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold v4_wk in Hw. cbn [fst snd] in *.
    destruct Hw as [Hw|[Hw|[Hw|(Hw & _)]]].
    - right; right; left. lia.
    - left. exact Hw.
    - right; left. exact Hw.
    - right; right; right. exact Hw.
  Qed.

  Lemma v4_vec_facts :
    fldA m v 8 b /\ fldA m (v + 8) 8 (b + 4 * cap) /\ fldA m (v + 16) 8 (b + 4 * cap)
    /\ (forall i, 0 <= i < cap -> 0 <= Znth i xs < 2 ^ 32 /\ fldA m (b + 4 * i) 4 (Znth i xs))
    /\ 0 <= cap /\ ((b = 0 /\ cap = 0) \/ (1 <= cap /\ In (pid, b, 4 * cap) LB /\ ablock_range H b (4 * cap))).
  Proof.
    destruct VEC as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2 & FE). rewrite XSL in F1, FE, Hlen.
    split; [exact F0|]. split; [exact F1|]. split; [exact F2|]. split; [exact FE|]. split; [lia|].
    destruct OLD as [[-> ->]|(Hc & HIn)]; [left; split; reflexivity|].
    right. split; [lia|]. split; [exact HIn|]. exact (ah_blocks H HH _ _ _ _ RH0 HIn).
  Qed.

  Lemma v4_s_end : forall (msF1 : machine_state) (mo1 : Model) (s1' : as_St H) (m1 : mem) (R1 : bvmap 5 word) (pid' : bptr) (A : Z) (e1 : word),
    as_VIS H s1' msF1 = MS R1 F (Z_to_bv 64 (E0 + 488)) fc None m1 (seg_rom asegs) -> rfull R1 ->
    v4_B11at R1 m1 A -> getr R1 3 = gp -> getr R1 4 = tp ->
    getr R1 24 = s8 -> getr R1 25 = s9 -> getr R1 26 = s10 -> getr R1 27 = s11 ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    rw_cells asegs m1 (spz - 80) FRAME ->
    mem_inv asegs m1 -> stk asegs m1 lo spz -> rw_cells asegs m1 (errno_addr tp) [C4 e1] -> as_rauxv_ok H m1 B ->
    xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap)) m m1 ->
    ablock_range H A (4 * cap') -> as_RHEAP H s1' (v4_newLB H LB b pid pid' A (4 * cap')) m1 ->
    vec32A (v4_newLB H LB b pid pid' A (4 * cap')) m1 v A (xs ++ [x]) cap' ->
    SHAD m1 A (cc_gen (4 * cap') (4 * (cap + 1))) -> addressable m1 v 24 ->
    wr_at asegs m1 v 24 -> lb_own (v4_newLB H LB b pid pid' A (4 * cap')) m1 ->
    as_RFS H LF m1 -> ACONST m1 -> stack0 m1 lo shi ->
    as_AL H s1' >= as_AL H s - (as_Cm H (4 * cap') + as_Cf H (4 * cap)) ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 s1' m1 R1 pid' A e1 VIS1 HF1 B11P G3 G4 G24 G25 G26 G27 KR1 MP1 FR1 MI1 ST1 ERR1 RA1 XP1 ABR RH1 VEC1 SH1
      ADV1 WV1 OW1 RF1 AC1 S01 AL1.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & B11 & RET).
    destruct (B11 R1 F fc m1 A (spz - 112) v cap (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
                (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) (bv_unsigned s6) (bv_unsigned s7) B11P)
      as (R' & M' & Hms & EM & K1 & K2 & K8 & K9 & K10 & K18 & K19 & K20 & K21 & K22 & K23 & KK).
    subst M'.
    assert (HF' : rfull R') by exact (msteps_full asegs _ _ Hms HF1).
    assert (K3 : getr R' 3 = gp) by (rewrite (KK 3%bv ltac:(inb)); exact G3).
    assert (K4 : getr R' 4 = tp) by (rewrite (KK 4%bv ltac:(inb)); exact G4).
    assert (K24 : getr R' 24 = s8) by (rewrite (KK 24%bv ltac:(inb)); exact G24).
    assert (K25 : getr R' 25 = s9) by (rewrite (KK 25%bv ltac:(inb)); exact G25).
    assert (K26 : getr R' 26 = s10) by (rewrite (KK 26%bv ltac:(inb)); exact G26).
    assert (K27 : getr R' 27 = s11) by (rewrite (KK 27%bv ltac:(inb)); exact G27).
    eapply (sr_evt H HH) with
      (P := fun ms => ms = MS (mkR ra sp gp tp (getr R' 5) (getr R' 6) (getr R' 7) s0 s1 (Z_to_bv 64 (A + 4 * (cap + 1)))
                                   (getr R' 11) (getr R' 12) (getr R' 13) (getr R' 14) (getr R' 15) (getr R' 16) (getr R' 17)
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (getr R' 28) (getr R' 29) (getr R' 30) (getr R' 31))
                              F (ret_pc ra) fc None m1 (seg_rom asegs));
      [exact KR1 | exact VIS1 | |].
    { eapply evt_of_msteps; [exact Hms|]. rewrite (rfull_eq R' HF'). apply RET.
      rewrite K1, K2, K3, K4, K8, K9, K10, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27. unfold wz.
      rewrite !Z_to_bv_bv_unsigned. replace (spz - 112 + 112) with spz by lia.
      replace (A + 4 * cap + 4) with (A + 4 * (cap + 1)) by lia. rewrite <- spz_sp. reflexivity. }
    intros msF2 mo2 KR2 MP2 HP. cbv beta in HP.
    exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14), (getr R' 15), (getr R' 16),
      (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), m1, e1, s1', pid', A.
    cbn [cfg_ms cfg_model]. rewrite SPZ.
    split; [exact HP|]. split; [exact KR2|]. split; [eapply (ah_mpres_trans H HH); eassumption|].
    split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact RA1|]. split; [exact XP1|].
    split; [exact ABR|]. split; [exact RH1|]. split; [exact VEC1|]. split; [exact SH1|]. split; [exact ADV1|].
    split; [exact WV1|]. split; [exact OW1|].
    split; [exact RF1|]. split; [exact AC1|]. split; [exact S01|]. exact AL1.
  Qed.
  Lemma v4_capb : 0 <= cap -> cap + 1 <= cap' /\ 4 * cap' <= 2 ^ 26.
  Proof.
    intros C0. split; [|exact GROW]. unfold cap', v4_newcap.
    destruct (Z_le_gt_dec cap 1) as [L|L]; [rewrite vgrow_le1 by lia | rewrite vgrow_ge2 by lia]; lia.
  Qed.

  Lemma v4_E0_even : forall k, 0 <= k < 0x1000 -> k mod 4 = 0 -> 0 <= E0 + k < 2 ^ 64 /\ (E0 + k) mod 2 = 0.
  Proof.
    intros k Hk H4. destruct E0R as [R0 R4]. split; [unfold E0; lia|]. unfold E0. exact (v4_mod4_even _ _ R4 H4).
  Qed.

  Lemma v4_old_facts : 0 < cap ->
    In (pid, b, 4 * cap) LB /\ ablock_range H b (4 * cap) /\ (v + 24 <= b \/ b + 4 * cap <= v) /\ b <> 0.
  Proof.
    intros Hc. pose proof v4_vec_facts as (_ & _ & _ & _ & _ & OB).
    destruct OB as [[_ C]|(_ & HIn & ABR)]; [lia|].
    destruct VEC as (_ & _ & _ & _ & Hb & _). destruct Hb as [[_ C]|(_ & _ & _ & _ & _ & D)]; [lia|].
    split; [exact HIn|]. split; [exact ABR|]. split; [exact D|]. destruct ABR as (B0 & _). lia.
  Qed.

  Lemma v4_blk_shad : forall sk mk LBx p A n, as_RHEAP H sk LBx mk -> In (p, A, n) LBx ->
    exists sbs, SHAD mk A sbs /\ Z.of_nat (length sbs) = nsh n.
  Proof.
    intros sk mk LBx p A n RH HIn.
    pose proof (ah_blk_shvis H HH _ _ _ _ _ _ RH HIn) as SV. unfold shvis in SV.
    pose proof (ah_blocks H HH _ _ _ _ RH HIn) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    cbn [blk_addr blk_size fst snd] in B0, B16, Bn, BI, BC, BF, BAPP.
    pose proof (v4_mod16_8 A B16) as B8.
    destruct (v4_sh_hull A n ltac:(lia) B8 Bn) as [HL1 HL2].
    assert (NS : 0 <= nsh n) by (unfold nsh; apply Z.div_pos; lia).
    destruct (stk_split asegs mk _ (sh A) _ SV ltac:(lia)) as [_ SV2].
    destruct (stk_split asegs mk _ (sh A + nsh n) _ SV2 ltac:(lia)) as [SV3 _].
    destruct (stk_carve asegs mk (sh A) (sh A + nsh n) (Z.to_nat (nsh n)) SV3 ltac:(lia)) as [_ (junk & RC)].
    rewrite Z2Nat.id in RC by lia. replace (sh A + nsh n - nsh n) with (sh A) in RC by lia.
    exists junk. split.
    - eapply SHAD_of_rw_cells; [lia | exact B8 | exact RC].
    - destruct RC as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _]. rewrite Hl, Z2Nat.id by lia. reflexivity.
  Qed.

  Lemma v4_hdr_fresh : forall sk mk pid' A n,
    as_RHEAP H sk ((pid', A, n) :: LB) mk -> ~ In pid' (map blk_id LB) -> 0 < n -> v + 24 <= A \/ A + n <= v.
  Proof.
    intros sk mk pid' A n RH NI Hn.
    destruct OBJ as (CL & _).
    pose proof (ah_blocks H HH _ _ _ (pid', A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    destruct LOR as [LO1 LO2]. unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    assert (SPC : aceil <= spz) by lia.
    destruct (Z_le_gt_dec (v + 24) A) as [D|D]; [left; exact D|].
    destruct (Z_le_gt_dec (A + n) v) as [D'|D']; [right; exact D'|].
    exfalso.
    assert (Ha : v <= Z.max v A < v + 24) by lia.
    pose proof (aclient_range_addr H LB spz v 24 (Z.max v A) CL Ha) as Hc.
    destruct (v4_cls sk LB pid' A n spz mk (Z.max v A) RH NI SPC Hc) as [C|(C1 & C2 & C3)]; [lia|].
    apply C2. lia.
  Qed.

  Lemma v4_band_of_aapp : forall A n, aapp A n -> (0 <= A /\ A + n <= 0x7fff7000) \/ 0x10007fff8000 <= A.
  Proof. intros A n HA. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in HA. destruct HA; [left|right]; lia. Qed.

  Lemma v4_xc_hdr : 0 < cap -> xclient_range H LB spz (v4_oldx b (4 * cap)) v 24.
  Proof.
    intros Hc. destruct (v4_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    destruct OBJ as (CL & _).
    split; [exact CL|].
    unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
    assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
    pose proof (v4_app_sh v 24 b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) VB) as D2.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.

  Lemma v4_xc_hdrsh : 0 < cap -> xclient_range H LB spz (v4_oldx b (4 * cap)) (sh v) 3.
  Proof.
    intros Hc. destruct (v4_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    destruct OBJ as (_ & CLS & _). rewrite v4_nsh24 in CLS.
    split; [exact CLS|].
    unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
    assert (VB : v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    pose proof (v4_app_sh b (4 * cap) v 24 ltac:(lia) ltac:(lia) VB (v4_band_of_aapp _ _ BAPP)) as D1. rewrite v4_nsh24 in D1.
    pose proof (v4_sh_apart v 24 b (4 * cap) ltac:(lia) ltac:(lia) V8 (v4_mod16_8 b B16) ltac:(lia) ltac:(lia) D) as D2.
    rewrite v4_nsh24 in D2.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.

  Definition v4_X0 : list (Z * Z) := if b =? 0 then [] else [(sh b, sh b + nsh (4 * cap))].
  Definition v4_X1 : list (Z * Z) := (v, v + 24) :: v4_X0.

  Lemma v4_xc_old : 0 < cap -> xclient_range H LB spz v4_X0 b (4 * cap).
  Proof.
    intros Hc. destruct (v4_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    split; [eapply (aclient_range_block H); [exact HIn | lia | lia]|].
    unfold v4_X0. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
    pose proof (v4_app_sh b (4 * cap) b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (v4_band_of_aapp _ _ BAPP)) as D2.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.

  Lemma v4_X1_sub : forall a, rin_ivs v4_X1 a -> rin_ivs ((v, v + 24) :: v4_oldx b (4 * cap)) a.
  Proof.
    intros a Ha. unfold v4_X1, v4_X0, v4_oldx in Ha |- *. destruct (b =? 0); cbn [rin_ivs fst snd] in Ha |- *; tauto.
  Qed.

  Lemma v4_dj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
  Proof.
    induction W as [|[l h] W IH]; intros a n a' n' D H1 H2; [exact I|]. cbn in D |- *. destruct D as [D1 D2].
    split; [lia | exact (IH a n a' n' D2 H1 H2)].
  Qed.

  Lemma v4_wr_sub : forall mk a n a' n', wr_at asegs mk a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs mk a' n'.
  Proof.
    intros mk a n a' n' (W0 & W1 & W) H1 H2 H3. split; [lia|]. split; [lia|].
    intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
  Qed.

  Lemma v4_CB0 : forall mk a, 0 <= a <= 2 ^ 64 -> rw_cells asegs mk a [CB 0 []].
  Proof.
    intros mk a Ha. split; [split|].
    - cbn. split; [reflexivity | exact I].
    - cbn [cells_bytes cbytes app]. apply bytes_at_nil. lia.
    - cbn [cells_size csize Nat.add Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia.
  Qed.

  Lemma v4_shvis0 : forall mk, shvis mk 0 0.
  Proof.
    intros mk. unfold shvis. change (sh (hull_lo 0)) with 2147450880. change (sh (hull_hi 0)) with 2147450880.
    split; [lia|]. split; [lia|]. intros a Ha. lia.
  Qed.

  Lemma v4_shk4 : forall mk A, addressable mk A 4 -> LbB_Kit.shk mk A 4.
  Proof.
    intros mk A [_ SH]. pose proof SH as (SA0 & _).
    destruct (shk_of_SHAD mk A (shadow_of 4) A SH ltac:(change (Z.of_nat (length (shadow_of 4))) with 1; lia)) as (bb & Hb & K).
    rewrite Z.sub_diag in Hb. change (nth_error (shadow_of 4) (Z.to_nat (0 / 8))) with (Some (b8 4)) in Hb. injection Hb as <-. exact K.
  Qed.

  Lemma v4_acl_sub : forall LBx SP A n A' n', aclient_range H LBx SP A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
    aclient_range H LBx SP A' n'.
  Proof.
    intros LBx SP A n A' n' K H1 H2 H3. unfold aclient_range in *.
    destruct K as [K|[K|[(bb & Hb & K1 & K2)|[(bb & Hb & K1 & K2)|[K|[K|K]]]]]].
    - left. lia.
    - right; left. intros a Ha. apply K. lia.
    - right; right; left. exists bb. split; [exact Hb | lia].
    - right; right; right; left. exists bb. split; [exact Hb | lia].
    - right; right; right; right; left. lia.
    - right; right; right; right; right; left. lia.
    - right; right; right; right; right; right. lia.
  Qed.

  Lemma v4_xcl_sub : forall X A n A' n', xclient_range H LB spz X A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
    xclient_range H LB spz X A' n'.
  Proof.
    intros X A n A' n' [K KX] H1 H2 H3. split; [exact (v4_acl_sub _ _ _ _ _ _ K H1 H2 H3)|].
    eapply Forall_impl; [|exact KX]. intros [l h] Hlh. cbn [fst snd] in *. lia.
  Qed.

  Lemma v4_fld_xpres : forall X mk a k z, xpres H LB spz X m mk -> xclient_range H LB spz X a (Z.of_nat k) ->
    0 <= a -> a + Z.of_nat k < 2 ^ 64 -> fldA m a k z -> fldA mk a k z.
  Proof.
    intros X mk a k z XP XC H0 H1 Hf. unfold fldA in *. eapply fld_agree; [exact H0 | exact H1 | exact Hf |].
    intros a' Ha'. hnf in Ha'.
    destruct (XP a' ltac:(lia) (xclient_range_addr H LB spz X a (Z.of_nat k) a' XC Ha')) as [E _]. exact E.
  Qed.

  Lemma v4_SHAD_xpres : forall X mk A' sbs, xpres H LB spz X m mk -> SHAD m A' sbs ->
    xclient_range H LB spz X (sh A') (Z.of_nat (length sbs)) -> SHAD mk A' sbs.
  Proof.
    intros X mk A' sbs XP (S0 & S8 & [UB UW]) XC. split; [exact S0|]. split; [exact S8|].
    split; [eapply (xpres_bytes_at H); [exact XP | exact UB | exact XC] | eapply (xpres_wr_at H); [exact XP | exact UW | exact XC]].
  Qed.

  Lemma apres_of_xpres_nil : forall mk, xpres H LB spz [] m mk -> apres H LB spz m mk.
  Proof. intros mk XP a Ha Hc. apply XP; [exact Ha|]. split; [exact Hc | intros K; exact K]. Qed.

  Lemma v4_mid_weaken : forall sk mk pid' A X X', v4_mid sk mk pid' A X -> (forall a, rin_ivs X a -> rin_ivs X' a) ->
    v4_mid sk mk pid' A X'.
  Proof.
    intros sk mk pid' A X X' (MI & ST & ERR & RA & AC & RF & S0 & RH & FR & XP & AL & OW) HX.
    repeat (split; [assumption|]). split; [eapply (xpres_weaken H); [exact XP | lia | intros bb Hb; exact Hb | exact HX]|].
    split; assumption.
  Qed.

  Lemma v4_wk_hdr : forall A Xk, (forall a, v <= a < v + 24 -> rin_ivs Xk a) -> v4_wk A Xk (v, v + 24).
  Proof.
    intros A Xk HX. right; right; right. cbn [fst snd].
    destruct OBJ as (_ & _ & WO & FW & CO & SD).
    pose proof LOR as [LO1 LO2]. unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    assert (SHC : 0x7fff7000 < sh aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    split; [exact HX|]. split; [exact WO|]. split; [exact FW|]. split; [exact CO|].
    split; [unfold stack0_ok; cbn [fst snd]; destruct VBAND; [right | left]; unfold AHI_LO; lia|].
    split; [lia|]. right. unfold ATP. destruct VBAND; lia.
  Qed.

  Lemma v4_wk_oldsh : 0 < cap -> forall A Xk, (forall a, sh b <= a < sh b + nsh (4 * cap) -> rin_ivs Xk a) ->
    v4_wk A Xk (sh b, sh b + nsh (4 * cap)).
  Proof.
    intros Hc A Xk HX. destruct (v4_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    pose proof (v4_app_sh (as_FSB H) AFS_SIZE b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (v4_band_of_aapp _ _ FS4)) as DF.
    pose proof (sh_nsh_high b (4 * cap) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHH. unfold AHI_LO in SHH.
    assert (SHL : 0x7fff8000 <= sh b) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    right; right; right. cbn [fst snd].
    split; [exact HX|].
    split; [right; right; right; left; exists (pid, b, 4 * cap); split; [exact HIn | cbn [blk_addr blk_size fst snd]; lia]|].
    split; [left; cbn [fst snd]; split; [lia | unfold ATLS_PRIV_HI, ATP; lia]|].
    split; [apply aconst_ok_high; [apply sh_mono; unfold AIMG_TOP in *; lia | right; left; lia]|].
    split; [apply stack0_ok_sh; lia|].
    split; [lia|]. right. unfold ATP. lia.
  Qed.

  Lemma v4_hdr_X0 : forall mk, xpres H LB spz v4_X0 m mk ->
    fldA mk v 8 b /\ fldA mk (v + 8) 8 (b + 4 * cap) /\ fldA mk (v + 16) 8 (b + 4 * cap) /\ addressable mk v 24
    /\ wr_at asegs mk v 24.
  Proof.
    intros mk XP.
    pose proof v4_vec_facts as (F0 & F1 & F2 & _ & C0 & OB).
    assert (VB2 : 0 <= v /\ v + 24 < 2 ^ 64) by (destruct VBAND; lia).
    assert (XCH : xclient_range H LB spz v4_X0 v 24).
    { destruct OBJ as (CL & _). split; [exact CL|]. unfold v4_X0. destruct (Z.eqb_spec b 0) as [E|NE]; [apply Forall_nil|].
      destruct OB as [[E _]|(Hc & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [contradiction|].
      pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
      assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
      pose proof (v4_app_sh v 24 b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) VB) as D.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    assert (XCS : xclient_range H LB spz v4_X0 (sh v) 3).
    { destruct OBJ as (_ & CLS & _). rewrite v4_nsh24 in CLS. split; [exact CLS|]. unfold v4_X0.
      destruct (Z.eqb_spec b 0) as [E|NE]; [apply Forall_nil|].
      destruct OB as [[E _]|(Hc & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [contradiction|].
      assert (D : v + 24 <= b \/ b + 4 * cap <= v) by (destruct (v4_old_facts ltac:(lia)) as (_ & _ & D & _); exact D).
      pose proof (v4_sh_apart v 24 b (4 * cap) ltac:(lia) ltac:(lia) V8 (v4_mod16_8 b B16) ltac:(lia) ltac:(lia) D) as D2.
      rewrite v4_nsh24 in D2.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    split; [eapply v4_fld_xpres; [exact XP | eapply v4_xcl_sub; [exact XCH | lia | cbn; lia | lia] | lia | cbn; lia | exact F0]|].
    split; [eapply v4_fld_xpres; [exact XP | eapply v4_xcl_sub; [exact XCH | lia | cbn; lia | lia] | lia | cbn; lia | exact F1]|].
    split; [eapply v4_fld_xpres; [exact XP | eapply v4_xcl_sub; [exact XCH | lia | cbn; lia | lia] | lia | cbn; lia | exact F2]|].
    split.
    - destruct ADV0 as [AN SV]. split; [exact AN|]. eapply v4_SHAD_xpres; [exact XP | exact SV |].
      rewrite shadow_of_length by lia. rewrite v4_nsh24. exact XCS.
    - eapply (xpres_wr_at H); [exact XP | exact VWR | exact XCH].
  Qed.

  Let HANN : annotate_gen_stmt := annotate_gen_ok.

  Lemma v4_s9 : forall (msF8 : machine_state) (mo8 : Model) (sk8 : as_St H) (m8 : mem) (R8 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk8 msF8 = MS R8 F (Z_to_bv 64 (E0 + 408)) fc None m8 (seg_rom asegs) -> rfull R8 ->
    v4_B9at R8 m8 A -> getr R8 3 = gp -> getr R8 4 = tp ->
    getr R8 24 = s8 -> getr R8 25 = s9 -> getr R8 26 = s10 -> getr R8 27 = s11 ->
    as_AKREL H sk8 (mkCfg msF8 mo8) -> as_MPRES H mo mo8 ->
    v4_mid sk8 m8 pid' A v4_X1 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m8 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))] ->
    bytes_at asegs m8 A (le4s xs) -> rw_cells asegs m8 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m8 A (cc_gen (4 * cap') (4 * (cap + 1))) -> addressable m8 v 24 ->
    as_SR H Q (mkCfg msF8 mo8).
  Proof.
    intros msF8 mo8 sk8 m8 R8 pid' A VIS8 HF8 B9P G3 G4 G24 G25 G26 G27 KR8 MP8 MID ABR NI HDR BUF XC SHA ADV8.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & _ & B9D & B9N & _ & _).
    pose proof MID as (MI8 & ST8 & (e8 & ERR8) & RA8 & AC8 & RF8 & S08 & RH8 & FR8 & XP8 & AL8 & OW8).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v4_vec_facts as (F0 & F1 & F2 & FE & C0 & OB).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB : 0x6e8000 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    pose proof B9P as P. unfold v4_B9at, vot_B9_pre in P.
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                   & PSP & PA & PV & PC & PN & PB & _ & _ & _ & PAN & _ & _ & _ & _ & PCN & _ & _).
    assert (FL : forall mk (w : word) k a, rw_cells asegs mk (spz - 80) FRAME -> cell_at FRAME k = Some (C8 w) ->
              a = spz - 80 + Z.of_nat k -> fldA mk a 8 (bv_unsigned w)).
    { intros mk w k a FR CA Ea. subst a. unfold fldA, fld. rewrite Z_to_bv_bv_unsigned. rewrite <- rdn_of_ov.
      exact (rw_cells_read asegs mk _ _ k _ FR CA). }
    assert (B11F : forall R mk, getr R 2 = wz (spz - 112) -> getr R 8 = wz (A + 4 * cap + 4) ->
              rw_cells asegs mk (spz - 80) FRAME -> v4_B11at R mk A).
    { intros R mk R2 R8' FR. unfold v4_B11at, vot_B11_pre.
      split; [exact R2|]. split; [exact R8'|].
      split; [eapply (FL mk ra 72%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s0 64%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s1 56%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s2 48%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s3 40%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s4 32%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s5 24%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s6 16%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s7 8%nat); [exact FR | reflexivity | lia]|].
      lia. }
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47 /\ (b = 0 -> cap = 0) /\ (b <> 0 -> 16 <= b)).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia|].
      split; [lia|]. split; [lia|]. split; [intros E; lia|]. intros _. exact (v4_mod16_16le b O0 O16). }
    destruct OB0 as (OB1 & OB2 & OB3 & OB4).
    assert (HNEW : v + 24 <= A \/ A + 4 * cap' <= v) by (eapply v4_hdr_fresh; [exact RH8 | exact NI | lia]).
    assert (VEC9 : forall m9 LB9, rw_cells asegs m9 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))] ->
              bytes_at asegs m9 A (le4s xs) -> rw_cells asegs m9 (A + 4 * cap) [C4 (Z_to_bv 64 x)] -> In (A, 4 * cap') (lbl LB9) ->
              vec32A LB9 m9 v A (xs ++ [x]) cap').
    { intros m9 LB9 H1 H2 H3 H4. apply v4_vec32_new; [rewrite XSL; exact H1 | exact H2 | rewrite XSL; exact H3 | lia
        | intros i Hi; rewrite XSL in Hi; exact (proj1 (FE i Hi)) | lia | exact A16 | rewrite XSL; lia | lia | exact H4 | exact HNEW
        | unfold AIMG_TOP; lia | lia]. }
    destruct (Z.eq_dec b 0) as [Z0|NZ].
    -
      destruct (B9N R8 F fc m8 A (spz - 112) v src cap b cap' (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
                  (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) (bv_unsigned s6) (bv_unsigned s7) B9P Z0)
        as (R9 & M9 & Hms & EM9 & K2 & K8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & KK).
      subst M9.
      pose proof (msteps_full asegs _ _ Hms HF8) as HF9. cbn [ms_regs] in HF9.
      eapply (sr_blk H HH); [exact KR8 | exact VIS8 | exact HF8 | exact Hms |].
      intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R9 HF9) in VIS1.
      eapply (v4_s_end msF1 mo1 sk8 m8 R9 pid' A e8 VIS1 HF9).
      + exact (B11F R9 m8 K2 K8 FR8).
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 24%bv ltac:(inb)). exact G24.
      + rewrite (KK 25%bv ltac:(inb)). exact G25.
      + rewrite (KK 26%bv ltac:(inb)). exact G26.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR1.
      + eapply (ah_mpres_trans H HH); [exact MP8 | exact MP1].
      + exact FR8.
      + exact MI8.
      + exact ST8.
      + exact ERR8.
      + exact RA8.
      + eapply (xpres_weaken H); [exact XP8 | lia | intros bb Hb; exact Hb | exact v4_X1_sub].
      + exact ABR.
      + unfold v4_newLB. rewrite Z0. cbn [Z.eqb]. exact RH8.
      + apply VEC9; [exact HDR | exact BUF | exact XC | ]. unfold v4_newLB. apply (lbl_in _ pid'). left. reflexivity.
      + exact SHA.
      + exact ADV8.
      + exact (proj2 HDR).
      + unfold v4_newLB. rewrite Z0. cbn [Z.eqb]. exact OW8.
      + exact RF8.
      + exact AC8.
      + exact S08.
      + assert (CF0 : 0 <= as_Cf H (4 * cap)) by (pose proof (ah_costs H HH) as (_ & _ & CF & _); apply CF; lia). lia.
    -
      assert (Hc : 0 < cap) by (destruct OB as [[E1 _]|(Hc & _)]; [contradiction | lia]).
      destruct (v4_old_facts Hc) as (HIn & (O0 & O16 & On & OI & OC & OF & OAP) & OD & _).
      destruct (B9D R8 F fc m8 A (spz - 112) v src cap b cap' (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
                  (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) (bv_unsigned s6) (bv_unsigned s7) B9P NZ)
        as (R9 & M9 & Hms & EM9 & K1 & K2w & K8 & _ & K10 & _ & _ & _ & _ & _ & _ & _ & KK).
      subst M9.
      assert (K2 : getr R9 2 = Z_to_bv 64 (spz - 112)) by exact K2w.
      pose proof (msteps_full asegs _ _ Hms HF8) as HF9. cbn [ms_regs] in HF9.
      eapply (sr_blk H HH); [exact KR8 | exact VIS8 | exact HF8 | exact Hms |].
      intros msF9 mo9 KR9 MP9 VIS9.
      assert (K4 : getr R9 4 = tp) by (rewrite (KK 4%bv ltac:(inb)); exact G4).
      assert (HINx : In (pid, b, 4 * cap) ((pid', A, 4 * cap') :: LB)) by (right; exact HIn).
      destruct (rw_cells_of_own _ m8 (pid, b, 4 * cap) OW8 HINx ltac:(cbn [blk_addr blk_size fst snd]; exact OI) ltac:(cbn [blk_addr blk_size fst snd]; lia)) as (obs & OC8).
      cbn [blk_addr blk_size fst snd] in OC8.
      destruct (v4_blk_shad sk8 m8 _ pid b (4 * cap) RH8 HINx) as (sbs & SHB & SHL).
      assert (CFB : as_Cf H (4 * cap) <= as_AL H sk8) by (pose proof CM as CM'; change (v4_newcap cap) with cap' in CM'; lia).
      assert (SP112 : (spz - 112) mod 16 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
      destruct (v4_E0_even 488 ltac:(lia) eq_refl) as [ER1 ER2].
      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (p := pid) (A := b) (n := 4 * cap) (LB := (pid', A, 4 * cap') :: LB) (lo := lo) (B := B)
          (errv := e8) (CH := []) (bs := obs) (sbs := sbs);
          [ exact VIS9 | exact RH8 | exact KR9 | exact HINx | exact CFB | exact OC8 | exact SHB | exact SHL
          | exact RA8 | rewrite K2, u64_of_Z by lia; lia
          | rewrite K2, u64_of_Z by lia; exact (proj1 (stk_split asegs m8 lo (spz - 112) spz ST8 ltac:(lia)))
          | exact LO1 | rewrite K2, u64_of_Z by lia; unfold AFREE_STACK; lia
          | rewrite K4; exact ERR8 | exact MI8 | rewrite K4; exact TPV | rewrite K2, u64_of_Z by lia; exact SP112 | exact AC8
          | rewrite K8; unfold wz; rewrite u64_of_Z by lia; apply (ah_chain_nil H HH); left; lia
          | rewrite K1; cbn [map]; unfold wz; rewrite u64_of_Z by lia; rewrite <- DRA; exact TRO
          | exact K10 ]. }
      intros c2 POST. destruct c2 as [msF2 mo2].
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m9 & s9'
                        & VIS2 & KR2 & MP2 & MI9 & ST9 & ERR9 & RA9 & AP9 & RH9 & AC9 & AL9).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite K1 in VIS2. unfold wz in VIS2. rewrite (ret_pc_even (v4_entry c + 488) ER1 ER2) in VIS2.
      rewrite K2, u64_of_Z in ST9, AP9 by lia. rewrite K4 in ERR9.

      assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 4 * cap); split; [reflexivity | exact HIn]).
      pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
      assert (RMx : as_lb_remove H pid ((pid', A, 4 * cap') :: LB) = (pid', A, 4 * cap') :: as_lb_remove H pid LB).
      { apply L2. cbn [blk_id fst]. exact NEQ. }
      rewrite RMx in AP9, RH9.

      assert (XPF0 : xpres H LB (spz - 112) (v4_oldx b (4 * cap)) m8 m9).
      { eapply (xpres_of_apres_rm H HH sk8 LB ((pid', A, 4 * cap') :: LB) (spz - 112) _ m8 m8 m9 pid b (4 * cap) RH8 HINx);
          [intros bb Hb; right; exact Hb | rewrite RMx; exact AP9 | |].
        - intros a Ha. unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. left. cbn [fst snd]. lia.
        - intros a Ha. unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. right. left. cbn [fst snd]. lia. }
      assert (XPF : xpres H LB spz (v4_oldx b (4 * cap)) m8 m9)
        by (eapply (xpres_weaken H); [exact XPF0 | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]).
      assert (HDR9 : rw_cells asegs m9 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))]).
      { eapply (xpres_rw_cells H); [exact XPF | exact HDR | exact (v4_xc_hdr Hc)]. }
      assert (FR9 : rw_cells asegs m9 (spz - 80) FRAME) by (eapply (apres_rw_cells H); [exact AP9 | exact FR8 | left; lia]).
      assert (INA : In (pid', A, 4 * cap') ((pid', A, 4 * cap') :: as_lb_remove H pid LB)) by (left; reflexivity).
      eapply (v4_s_end msF2 mo2 s9' m9 _ pid' A e8 VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
      + apply B11F; [exact K2w | exact K8 | exact FR9].
      + exact (eq_trans (KK 3%bv ltac:(inb)) G3).
      + exact K4.
      + exact (eq_trans (KK 24%bv ltac:(inb)) G24).
      + exact (eq_trans (KK 25%bv ltac:(inb)) G25).
      + exact (eq_trans (KK 26%bv ltac:(inb)) G26).
      + exact (eq_trans (KK 27%bv ltac:(inb)) G27).
      + exact KR2.
      + eapply (ah_mpres_trans H HH); [exact MP8 | eapply (ah_mpres_trans H HH); [exact MP9 | exact MP2]].
      + exact FR9.
      + exact MI9.
      + eapply (stk_merge asegs); [exact ST9 | | lia].
        eapply (apres_stk H); [exact AP9 | exact (proj2 (stk_split asegs m8 lo (spz - 112) spz ST8 ltac:(lia))) | lia].
      + exact ERR9.
      + exact RA9.
      + eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP8 | lia | intros bb Hb; exact Hb | exact v4_X1_sub] |].
        eapply (xpres_weaken H); [exact XPF | lia | intros bb Hb; exact Hb | intros a Ha; right; exact Ha].
      + exact ABR.
      + unfold v4_newLB. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. exact RH9.
      + apply VEC9; [exact HDR9 | | |].
        * eapply (apres_bytes_at H); [exact AP9 | exact BUF |]. rewrite le4s_length. eapply (aclient_range_block H); [exact INA | lia |].
          unfold Zlen in XSL. lia.
        * eapply (apres_rw_cells H); [exact AP9 | exact XC |]. cbn [cells_size csize]. eapply (aclient_range_block H); [exact INA | lia | lia].
        * unfold v4_newLB. apply (lbl_in _ pid'). left. reflexivity.
      + eapply (apres_SHAD H); [exact AP9 | exact SHA |]. rewrite cc_gen_length by lia. eapply (aclient_range_block_sh H). exact INA.
      + destruct ADV8 as [AN (SA0 & SA8 & [UB UW])]. split; [exact AN|]. split; [exact SA0|]. split; [exact SA8|].
        assert (XCS : xclient_range H LB spz (v4_oldx b (4 * cap)) (sh v) (Z.of_nat (length (shadow_of 24)))).
        { rewrite shadow_of_length by lia. rewrite v4_nsh24. exact (v4_xc_hdrsh Hc). }
        split; [eapply (xpres_bytes_at H); [exact XPF | exact UB | exact XCS] | eapply (xpres_wr_at H); [exact XPF | exact UW | exact XCS]].
      + exact (proj2 HDR9).
      + unfold v4_newLB. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
        eapply (lb_own_apres H); [| exact AP9 | intros bb Hb; exact Hb].
        eapply lb_own_incl; [| exact OW8]. intros bb [Hb|Hb]; [left; exact Hb | right; exact (L3 _ _ _ Hb)].
      + exact (RFS_via_apres H HH LF _ _ m8 m9 RF8 AP9).
      + exact AC9.
      + eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP9) | exact S08 | apply Forall_nil].
      + lia.
  Qed.

  Lemma v4_s8 : forall (msF7 : machine_state) (mo7 : Model) (sk7 : as_St H) (m7 : mem) (R7 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk7 msF7 = MS R7 F (Z_to_bv 64 AANNOTATE_CC) fc None m7 (seg_rom asegs) -> rfull R7 ->
    getr R7 1 = Z_to_bv 64 (E0 + 408) -> getr R7 10 = Z_to_bv 64 A -> getr R7 11 = Z_to_bv 64 (A + 4 * cap') ->
    getr R7 12 = Z_to_bv 64 (A + 4 * cap') -> getr R7 13 = Z_to_bv 64 (A + 4 * cap + 4) ->
    v4_B9at R7 m7 A -> getr R7 3 = gp -> getr R7 4 = tp ->
    getr R7 24 = s8 -> getr R7 25 = s9 -> getr R7 26 = s10 -> getr R7 27 = s11 ->
    as_AKREL H sk7 (mkCfg msF7 mo7) -> as_MPRES H mo mo7 ->
    v4_mid sk7 m7 pid' A v4_X1 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m7 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))] ->
    bytes_at asegs m7 A (le4s xs) -> rw_cells asegs m7 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m7 A (cc_gen (4 * cap') (4 * cap')) -> addressable m7 v 24 ->
    as_SR H Q (mkCfg msF7 mo7).
  Proof.
    intros msF7 mo7 sk7 m7 R7 pid' A VIS7 HF7 G1 G10 G11 G12 G13 B9P G3 G4 G24 G25 G26 G27 KR7 MP7 MID ABR NI HDR BUF XC SHA
      ADV7.
    pose proof MID as (MI7 & ST7 & _ & _ & AC7 & _ & _ & RH7 & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v4_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
    assert (HNEW : v + 24 <= A \/ A + 4 * cap' <= v) by (eapply v4_hdr_fresh; [exact RH7 | exact NI | lia]).
    unfold v4_B9at, vot_B9_pre in B9P.
    destruct B9P as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & FV0 & FV8 & FV16 & FS0 & FS8 & FS16 & FS24 & FS32
                     & FRa & FR0 & FR1 & FR2 & FR3 & FR4 & FR5 & FR6 & FR7 & RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & WS & SHV
                     & RG7 & RG8 & RG9 & RG10 & RG11 & RG12 & RG13 & RG14 & RG15).
    rewrite (rfull_eq R7 HF7) in VIS7.
    eapply (ahh_evt_then H HH); [exact KR7 | exact VIS7 | |].
    { eapply HANN with (beg := A) (len := 4 * cap') (oldmid := 4 * cap') (newmid := 4 * cap + 4) (lo := lo).
      - exact G10.
      - exact G11.
      - exact G12.
      - rewrite G13. f_equal. lia.
      - exact (v4_mod16_8 A A16).
      - lia.
      - lia.
      - lia.
      - exact AAP.
      - unfold AAPP_HI; lia.
      - exact SHA.
      - rewrite G2. unfold wz. rewrite u64_of_Z by lia. exact (proj1 (stk_split asegs m7 lo (spz - 112) spz ST7 ltac:(lia))).
      - exact LO1.
      - rewrite G2. unfold wz. rewrite u64_of_Z by lia. unfold AINTRIN_STACK. lia.
      - exact MI7.
      - exact AC7.
      - unfold in_app_mem. destruct (v4_band_of_aapp _ _ AAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia. }
    intros msF8 mo8 KR8 MP8 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m8
                      & VIS8 & MU8 & WM8 & MI8 & ST8 & SH8 & AC8).
    rewrite G2 in MU8, ST8. unfold wz in MU8, ST8. rewrite u64_of_Z in MU8, ST8 by lia. unfold AINTRIN_STACK in MU8.
    rewrite G1 in VIS8. destruct (v4_E0_even 408 ltac:(lia) eq_refl) as [ER1 ER2].
    rewrite (ret_pc_even (E0 + 408) ER1 ER2) in VIS8.
    assert (W8 : Forall (v4_wk A v4_X1) [(sh A, sh A + nsh (4 * cap')); (spz - 112 - 4096, spz - 112)]).
    { apply Forall_cons; [right; right; left; cbn [fst snd]; lia|].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (DSV : disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 112 - 4096, spz - 112)] v 24).
    { pose proof (v4_app_sh v 24 A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) VB) as D. destruct OBJ as (_ & _ & _ & _ & _ & SD).
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSA : disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 112 - 4096, spz - 112)] A (4 * cap')).
    { pose proof (v4_app_sh A (4 * cap') A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) (v4_band_of_aapp _ _ AAP)) as D.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSS : disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 112 - 4096, spz - 112)] (sh v) (nsh 24)).
    { pose proof (v4_sh_apart v 24 A (4 * cap') ltac:(lia) ltac:(lia) V8 (v4_mod16_8 A A16) ltac:(lia) ltac:(lia) HNEW) as D.
      pose proof (sh_nsh_high v 24 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; destruct VBAND; lia)) as D2. unfold AHI_LO in D2.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSP : forall a, spz - 112 <= a <= spz - 8 ->
                  disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 112 - 4096, spz - 112)] a 8).
    { intros a Ha. pose proof (sh_nsh_high A (4 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as D2.
      unfold AHI_LO in D2. cbn. split; [lia | split; [lia | exact I]]. }
    assert (FMU : forall a z, fldA m7 a 8 z -> disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 112 - 4096, spz - 112)] a 8 ->
                  0 <= a -> a + 8 < 2 ^ 64 -> fldA m8 a 8 z).
    { intros a z Fa D Ha0 Ha1. unfold fldA in Fa |- *. eapply fld_agree; [exact Ha0 | exact Ha1 | exact Fa |].
      intros y Hy. red in Hy. apply MU8. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia]. }
    assert (ADV8 : addressable m8 v 24) by (eapply addressable_transport; [exact ADV7 | exact MU8 | exact WM8 | exact DSS]).
    eapply (v4_s9 msF8 mo8 sk7 m8 _ pid' A VIS8 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold v4_B9at, vot_B9_pre.
      split; [exact G2|]. split; [exact G8|]. split; [exact G9|]. split; [exact G18|]. split; [exact G19|].
      split; [exact G20|]. split; [exact G21|]. split; [exact G22|]. split; [exact G23|].
      split; [eapply FMU; [exact FV0 | eapply v4_dj_sub; [exact DSV | lia | lia] | lia | lia]|].
      split; [eapply FMU; [exact FV8 | eapply v4_dj_sub; [exact DSV | lia | lia] | lia | lia]|].
      split; [eapply FMU; [exact FV16 | eapply v4_dj_sub; [exact DSV | lia | lia] | lia | lia]|].
      split; [eapply FMU; [exact FS0 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS8 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS16 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS24 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS32 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FRa | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR0 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR1 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR2 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR3 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR4 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR5 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR6 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR7 | apply DSP; lia | lia | lia]|].
      split; [exact RG1|]. split; [exact RG2|]. split; [exact RG3|]. split; [exact RG4|]. split; [exact RG5|].
      split; [exact RG6|].
      split; [exact (wr_at_wmono _ _ _ _ WS WM8)|].
      split; [eapply sh0_of_addressable; [exact ADV8 | change (8 * (24 / 8)) with 24; lia]|].
      split; [exact RG7|]. split; [exact RG8|]. split; [exact RG9|]. split; [exact RG10|]. split; [exact RG11|].
      split; [exact RG12|]. split; [exact RG13|]. split; [exact RG14|]. exact RG15.
    - exact G3.
    - exact G4.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR8.
    - eapply (ah_mpres_trans H HH); [exact MP7 | exact MP8].
    - eapply v4_mid_munch; [exact MID | exact ABR | exact NI | exact MU8 | exact WM8 | exact MI8 | exact W8].
    - exact ABR.
    - exact NI.
    - eapply rw_cells_transport; [exact HDR | exact MU8 | exact WM8 | exact DSV].
    - eapply bytes_at_transport; [exact BUF | exact MU8 |]. eapply v4_dj_sub; [exact DSA | lia | rewrite le4s_length; unfold Zlen in XSL; lia].
    - eapply rw_cells_transport; [exact XC | exact MU8 | exact WM8 |]. cbn [cells_size csize Nat.add Z.of_nat].
      eapply v4_dj_sub; [exact DSA | lia | lia].
    - replace (4 * (cap + 1)) with (4 * cap + 4) by lia. exact SH8.
    - exact ADV8.
  Qed.

  Lemma v4_s7 : forall (msF6 : machine_state) (mo6 : Model) (sk6 : as_St H) (m6 : mem) (R6 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk6 msF6 = MS R6 F (Z_to_bv 64 970144) fc None m6 (seg_rom asegs) -> rfull R6 ->
    v4_B7at R6 m6 A -> getr R6 3 = gp -> getr R6 4 = tp -> getr R6 27 = s11 ->
    as_AKREL H sk6 (mkCfg msF6 mo6) -> as_MPRES H mo mo6 ->
    v4_mid sk6 m6 pid' A v4_X0 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    bytes_at asegs m6 A (le4s xs) -> rw_cells asegs m6 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m6 A (cc_gen (4 * cap') (4 * cap')) ->
    as_SR H Q (mkCfg msF6 mo6).
  Proof.
    intros msF6 mo6 sk6 m6 R6 pid' A VIS6 HF6 B7P G3 G4 G27 KR6 MP6 MID ABR NI BUF XC SHA.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & B7 & _).
    pose proof MID as (MI6 & ST6 & _ & _ & _ & _ & _ & RH6 & FR6 & XP6 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v4_vec_facts as (_ & _ & _ & _ & C0 & OB).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (HNEW : v + 24 <= A \/ A + 4 * cap' <= v) by (eapply v4_hdr_fresh; [exact RH6 | exact NI | lia]).
    destruct (v4_hdr_X0 m6 XP6) as (_ & _ & _ & ADV6 & WV6).
    unfold v4_B7at in B7P.
    destruct (B7 R6 F fc m6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B7P)
      as (R7 & M7 & Hms & MU7 & WM7 & P0 & P24 & PV16 & P16 & PV8 & P8 & PV0 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13
          & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & KK).
    pose proof (msteps_full asegs _ _ Hms HF6) as HF7. cbn [ms_regs] in HF7.
    assert (MI7 : mem_inv asegs M7) by exact (msteps_mem_inv asegs _ _ Hms MI6).
    eapply (sr_blk H HH); [exact KR6 | exact VIS6 | exact HF6 | exact Hms |].
    intros msF7 mo7 KR7 MP7 VIS7. rewrite <- (rfull_eq R7 HF7) in VIS7.
    assert (MID7 : v4_mid sk6 M7 pid' A v4_X1).
    { eapply v4_mid_munch; [eapply v4_mid_weaken; [exact MID | intros a Ha; right; exact Ha] | exact ABR | exact NI
                           | exact MU7 | exact WM7 | exact MI7 |].
      apply Forall_cons; [left; cbn [fst snd]; lia|].
      apply Forall_cons; [apply v4_wk_hdr; intros a Ha; left; cbn [fst snd]; lia | apply Forall_nil]. }
    pose proof MID7 as (_ & ST7 & _ & _ & _ & _ & _ & _ & FR7 & _).
    assert (CONS8 : forall mk a w cs, rw_cells asegs mk a (C8 w :: cs) ->
                    rw_cells asegs mk a [C8 w] /\ rw_cells asegs mk (a + 8) cs).
    { intros mk a w cs Hc. change (C8 w :: cs) with ([C8 w] ++ cs) in Hc. apply rw_cells_app in Hc. exact Hc. }
    assert (JOIN8 : forall mk a w cs, rw_cells asegs mk a [C8 w] -> rw_cells asegs mk (a + 8) cs ->
                    rw_cells asegs mk a (C8 w :: cs)).
    { intros mk a w cs H1 H2. change (C8 w :: cs) with ([C8 w] ++ cs). apply rw_cells_app. split; [exact H1 | exact H2]. }
    assert (FW : forall mk a a' (w : word), rw_cells asegs mk a [C8 w] -> a' = a -> 0 <= a -> fldA mk a' 8 (bv_unsigned w)).
    { intros mk a a' w Hc -> Ha. apply fld_of_rw_cells8; [rewrite Z_to_bv_bv_unsigned; exact Hc | exact Ha]. }
    assert (C8F : forall mk a a' z z', fldA mk a' 8 z' -> a = a' -> z = z' -> wr_at asegs mk a 8 ->
                  rw_cells asegs mk a [C8 (Z_to_bv 64 z)]).
    { intros mk a a' z z' HF -> -> HW. pose proof HW as (HW0 & HW1 & _). split; [|exact HW].
      split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply bytes_at_of_rdn; [lia | rewrite length_le8; lia | rewrite length_le8; exact HF]. }
    unfold FRAME in FR7. cbn [map] in FR7.
    destruct (CONS8 _ _ _ _ FR7) as (FVv & FR7a). destruct (CONS8 _ _ _ _ FR7a) as (F7 & FR7b).
    destruct (CONS8 _ _ _ _ FR7b) as (F6 & FR7c). destruct (CONS8 _ _ _ _ FR7c) as (F5 & FR7d).
    destruct (CONS8 _ _ _ _ FR7d) as (F4 & FR7e). destruct (CONS8 _ _ _ _ FR7e) as (F3 & FR7f).
    destruct (CONS8 _ _ _ _ FR7f) as (F2 & FR7g). destruct (CONS8 _ _ _ _ FR7g) as (F1 & FR7h).
    destruct (CONS8 _ _ _ _ FR7h) as (F0 & Fra).
    assert (ADV7 : addressable M7 v 24).
    { eapply addressable_transport; [exact ADV6 | exact MU7 | exact WM7 |].
      pose proof (v4_app_sh v 24 v 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VBAND; [left|right]; lia)) as D.
      pose proof (v4_app_sh (spz - 112) 32 v 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(right; lia)) as D2.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (WV7 : wr_at asegs M7 v 24) by exact (wr_at_wmono _ _ _ _ WV6 WM7).
    assert (B9P : v4_B9at R7 M7 A).
    { unfold v4_B9at, vot_B9_pre.
      split; [exact K2|]. split; [exact K8|]. split; [exact K9|]. split; [exact K18|]. split; [exact K19|].
      split; [exact K20|]. split; [exact K21|]. split; [exact K22|]. split; [exact K23|].
      split; [exact PV0|]. split; [exact PV8|]. split; [exact PV16|].
      split; [exact P0|]. split; [exact P8|]. split; [exact P16|]. split; [exact P24|].
      split; [replace (spz - 112 + 32) with (spz - 80) by lia; exact (fld_of_rw_cells8 _ _ _ FVv ltac:(lia))|].
      split; [eapply FW; [exact Fra | lia | lia]|].
      split; [eapply FW; [exact F0 | lia | lia]|].
      split; [eapply FW; [exact F1 | lia | lia]|].
      split; [eapply FW; [exact F2 | lia | lia]|].
      split; [eapply FW; [exact F3 | lia | lia]|].
      split; [eapply FW; [exact F4 | lia | lia]|].
      split; [eapply FW; [exact F5 | lia | lia]|].
      split; [eapply FW; [exact F6 | lia | lia]|].
      split; [eapply FW; [exact F7 | lia | lia]|].
      split; [lia|]. split; [lia|]. split; [destruct VBAND; lia|]. split; [lia|]. split; [lia|].
      split; [destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1; lia | lia]|].
      split; [eapply wr_at_of_stk_win; [exact ST7 | lia | lia]|].
      split; [eapply sh0_of_addressable; [exact ADV7 | change (8 * (24 / 8)) with 24; lia]|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [destruct VBAND; lia|].
      split; [destruct VBAND; lia|]. split; [lia|].
      destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    assert (HDR7 : rw_cells asegs M7 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1)));
                                         C8 (Z_to_bv 64 (A + 4 * cap'))]).
    { apply JOIN8; [eapply C8F; [exact PV0 | lia | lia | eapply v4_wr_sub; [exact WV7 | lia | lia | lia]]|].
      apply JOIN8; [eapply C8F; [exact PV8 | lia | lia | eapply v4_wr_sub; [exact WV7 | lia | lia | lia]]|].
      eapply C8F; [exact PV16 | lia | lia | eapply v4_wr_sub; [exact WV7 | lia | lia | lia]]. }
    assert (DV : disjoint_from [(spz - 112, spz - 112 + 32); (v, v + 24)] A (4 * cap')) by (cbn; split; [lia | split; [lia | exact I]]).
    eapply (v4_s8 msF7 mo7 sk6 M7 R7 pid' A VIS7 HF7).
    - exact K1.
    - exact K10.
    - exact K11.
    - exact K12.
    - rewrite K13. unfold wz. f_equal. lia.
    - exact B9P.
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - rewrite K24. unfold wz. apply Z_to_bv_bv_unsigned.
    - rewrite K25. unfold wz. apply Z_to_bv_bv_unsigned.
    - rewrite K26. unfold wz. apply Z_to_bv_bv_unsigned.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR7.
    - eapply (ah_mpres_trans H HH); [exact MP6 | exact MP7].
    - exact MID7.
    - exact ABR.
    - exact NI.
    - exact HDR7.
    - eapply bytes_at_transport; [exact BUF | exact MU7 |]. eapply v4_dj_sub; [exact DV | lia | rewrite le4s_length; unfold Zlen in XSL; lia].
    - eapply rw_cells_transport; [exact XC | exact MU7 | exact WM7 |]. cbn [cells_size csize Nat.add Z.of_nat].
      eapply v4_dj_sub; [exact DV | lia | lia].
    - eapply SHAD_transport; [exact SHA | exact MU7 | exact WM7 |]. rewrite cc_gen_length by lia.
      pose proof (v4_app_sh v 24 A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VBAND; [left|right]; lia)) as D.
      pose proof (v4_app_sh (spz - 112) 32 A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(right; lia)) as D2.
      cbn. split; [lia | split; [lia | exact I]].
    - exact ADV7.
  Qed.

  Lemma v4_s6 : forall (msF5 : machine_state) (mo5 : Model) (sk5 : as_St H) (m5 : mem) (R5 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    as_VIS H sk5 msF5 = MS R5 F (Z_to_bv 64 AASAN_MEMCPY) fc None m5 (seg_rom asegs) -> rfull R5 ->
    getr R5 1 = Z_to_bv 64 970144 -> getr R5 10 = Z_to_bv 64 A -> getr R5 11 = Z_to_bv 64 b ->
    getr R5 12 = Z_to_bv 64 (4 * cap) ->
    v4_B7at R5 m5 A -> getr R5 3 = gp -> getr R5 4 = tp -> getr R5 27 = s11 ->
    as_AKREL H sk5 (mkCfg msF5 mo5) -> as_MPRES H mo mo5 ->
    v4_mid sk5 m5 pid' A v4_X0 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m5 A [CB (Z.to_nat (4 * cap)) jA] -> rw_cells asegs m5 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m5 A (cc_gen (4 * cap') (4 * cap')) -> (0 < cap -> SHAD m5 b (cc_gen (4 * cap) (4 * cap))) ->
    as_SR H Q (mkCfg msF5 mo5).
  Proof.
    intros msF5 mo5 sk5 m5 R5 pid' A jA VIS5 HF5 G1 G10 G11 G12 B7A G3 G4 G27 KR5 MP5 MID ABR NI CBA XC SHA OSH.
    pose proof MID as (MI5 & ST5 & _ & _ & AC5 & _ & _ & RH5 & _ & XP5 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v4_vec_facts as (_ & _ & _ & FE & C0 & OB).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof B7A as (P2 & P8 & P9 & P18 & P19 & P22 & P23 & P24 & P25 & P20 & P21 & P26 & FV0 & FV8 & FV16 & FS0 & FS8 & FS16
                       & FS24 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & WH & VD & WV & WS & HS0 & HS1 & HS2 & HS3 & HS4 & HS5
                       & HS6 & HS7 & HS8 & HS9 & HS10 & HS11 & Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & N9 & N10 & N11 & N12 & N13 & N14
                       & N15 & N16 & N17 & N18 & N19 & N20).
    assert (G2 : getr R5 2 = Z_to_bv 64 (spz - 112 - 96)) by exact P2.
    assert (OBB : (b = 0 /\ cap = 0) \/ (0 < cap /\ In (pid, b, 4 * cap) LB /\ ablock_range H b (4 * cap))).
    { destruct OB as [E|(Hc & HIn & ABb)]; [left; exact E | right; split; [lia|]; split; assumption]. }
    assert (OB0 : 0 <= b /\ b + 4 * cap <= aceil).
    { destruct OBB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }

    assert (SRCB : bytes_at asegs m5 b (le4s xs)).
    { destruct OBB as [[E1 E2]|(Hc & HIn & ABb)].
      - assert (XN : xs = []) by (apply length_zero_iff_nil; unfold Zlen in XSL; lia). rewrite XN. apply bytes_at_nil. lia.
      - eapply (xpres_bytes_at H); [exact XP5 | |].
        + apply bytes_at_le4s; [intros i Hi; rewrite XSL in Hi; exact (proj2 (FE i Hi)) | lia | rewrite XSL; lia].
        + rewrite le4s_length. replace (Z.of_nat (4 * length xs)) with (4 * cap) by (unfold Zlen in XSL; lia). exact (v4_xc_old Hc). }
    assert (ADA : addressable m5 A (4 * cap')) by (split; [lia | rewrite <- cc_gen_full; exact SHA]).
    rewrite (rfull_eq R5 HF5) in VIS5.
    eapply (ahh_evt_then H HH); [exact KR5 | exact VIS5 | |].
    { eapply (ah_memcpy H HH) with (src := le4s xs) (junk := jA) (lo := lo); rewrite ?G10, ?G11, ?G12, ?G2; rewrite ?u64_of_Z by lia.
      - exact SRCB.
      - rewrite le4s_length. unfold Zlen in XSL. lia.
      - exact CBA.
      - destruct OBB as [[E1 E2]|(Hc & HIn & ABb)]; [left; lia|].
        assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 4 * cap); split; [reflexivity | exact HIn]).
        pose proof (ah_disj H HH _ _ _ (pid', A, 4 * cap') (pid, b, 4 * cap) RH5 (or_introl eq_refl) (or_intror HIn) NEQ) as D.
        cbn [blk_addr blk_size fst snd] in D. lia.
      - destruct OBB as [[E1 E2]|(Hc & HIn & ABb)].
        + replace (4 * cap) with 0 by lia. apply accessible_nil. unfold AAPP_HI. lia.
        + eapply (addressable_accessible m5 b (4 * cap)); [split; [lia | rewrite <- cc_gen_full; exact (OSH Hc)] | lia | lia | unfold AAPP_HI; lia].
      - eapply addressable_accessible; [exact ADA | lia | lia | unfold AAPP_HI; lia].
      - destruct OBB as [[E1 E2]|(Hc & HIn & ABb)].
        + rewrite E1, E2. replace (0 + 4 * 0) with 0 by lia. apply v4_shvis0.
        + exact (ah_blk_shvis H HH _ _ _ _ _ _ RH5 (or_intror HIn)).
      - eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ RH5 (or_introl eq_refl)) | lia | lia | lia | lia | lia].
      - exact (proj1 (stk_split asegs m5 lo (spz - 112 - 96) spz ST5 ltac:(lia))).
      - exact LO1.
      - unfold AINTRIN_STACK; lia.
      - exact MI5.
      - exact AC5.
      - lia.
      - destruct OBB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))].
        + left. unfold ASHADOW_BASE. lia.
        + unfold in_app_mem. destruct (v4_band_of_aapp _ _ OAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia.
      - unfold in_app_mem. destruct (v4_band_of_aapp _ _ AAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia.
      - eapply aconst_ok_app; [exact AAP | lia | lia].
      - left; lia.
      - left; lia. }
    intros msF6 mo6 KR6 MP6 POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m6
                      & VIS6 & MU6 & WM6 & MI6 & ST6 & CB6 & SB6 & AC6).
    rewrite G10, G12, G2, ?u64_of_Z in MU6 by lia. rewrite G10, G12, ?u64_of_Z in CB6 by lia. rewrite G2, u64_of_Z in ST6 by lia.
    unfold AINTRIN_STACK in MU6.
    rewrite G1 in VIS6. rewrite (ret_pc_even 970144 ltac:(lia) eq_refl) in VIS6.
    assert (W6 : Forall (v4_wk A v4_X0) [(A, A + 4 * cap); (spz - 112 - 96 - 4096, spz - 112 - 96)]).
    { apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (MID6 : v4_mid sk5 m6 pid' A v4_X0)
      by (eapply v4_mid_munch; [exact MID | exact ABR | exact NI | exact MU6 | exact WM6 | exact MI6 | exact W6]).
    pose proof MID6 as (_ & _ & _ & _ & _ & _ & S06 & _ & _ & XP6 & _ & _).
    destruct (v4_hdr_X0 m6 XP6) as (FV0' & FV8' & FV16' & ADV6 & _).
    assert (FT : forall a z, fldA m5 a 8 z -> spz - 112 - 96 <= a -> a + 8 <= spz -> fldA m6 a 8 z).
    { intros a z Hf Ha Hk. unfold fldA in Hf |- *. eapply fld_agree; [lia | change (Z.of_nat 8) with 8; lia | exact Hf |].
      intros y Hy. red in Hy. change (Z.of_nat 8) with 8 in Hy. apply MU6. rewrite u64_of_Z by lia.
      cbn [outside]. split; [lia | split; [lia | exact I]]. }
    eapply (v4_s7 msF6 mo6 sk5 m6 _ pid' A VIS6 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold v4_B7at, vot_B7_pre.
      refine (conj P2 (conj P8 (conj P9 (conj P18 (conj P19 (conj P22 (conj P23 (conj P24 (conj P25 (conj P20 (conj P21
        (conj P26 _)))))))))))).
      refine (conj FV0' (conj FV8' (conj FV16' _))).
      do 4 (split; [eapply FT; [eassumption | lia | lia] |]).
      refine (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (conj N7 (conj N8 _)))))))).
      refine (conj (wr_at_transport asegs _ _ _ _ WH WM6) (conj VD (conj (wr_at_transport asegs _ _ _ _ WV WM6)
        (conj (wr_at_transport asegs _ _ _ _ WS WM6) _)))).
      do 12 (split; [eapply FT; [eassumption | lia | lia] |]).
      split; [eapply sh0_of_stack0; [exact S06 | lia] |].
      split; [eapply sh0_of_addressable; [exact ADV6 | change (8 * (24 / 8)) with 24; lia] |].
      split; [eapply sh0_of_addressable; [exact ADV6 | change (8 * (24 / 8)) with 24; lia] |].
      split; [eapply sh0_of_stack0; [exact S06 | lia] |].
      split; [eapply sh0_of_addressable; [exact ADV6 | change (8 * (24 / 8)) with 24; lia] |].
      split; [eapply sh0_of_stack0; [exact S06 | lia] |].
      split; [eapply sh0_of_stack0; [exact S06 | lia] |].
      exact (conj N9 (conj N10 (conj N11 (conj N12 (conj N13 (conj N14 (conj N15 (conj N16 (conj N17 (conj N18 (conj N19
        N20))))))))))).
    - exact G3.
    - exact G4.
    - exact G27.
    - exact KR6.
    - eapply (ah_mpres_trans H HH); [exact MP5 | exact MP6].
    - exact MID6.
    - exact ABR.
    - exact NI.
    - exact (bytes_of_CB _ _ _ _ CB6).
    - eapply rw_cells_transport; [exact XC | exact MU6 | exact WM6 |]. cbn. split; [lia | split; [lia | exact I]].
    - eapply SHAD_transport; [exact SHA | exact MU6 | exact WM6 |]. rewrite cc_gen_length by lia.
      pose proof (v4_app_sh A (4 * cap) A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct (v4_band_of_aapp _ _ AAP); [left|right]; lia)) as D.
      pose proof (sh_nsh_high A (4 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as D2. unfold AHI_LO in D2.
      cbn. split; [lia | split; [lia | exact I]].
  Qed.

  Lemma v4_s5 : forall (msF4 : machine_state) (mo4 : Model) (sk4 : as_St H) (m4 : mem) (R4 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    0 < cap ->
    as_VIS H sk4 msF4 = MS R4 F (Z_to_bv 64 970008) fc None m4 (seg_rom asegs) -> rfull R4 ->
    v4_B5at R4 m4 A -> getr R4 3 = gp -> getr R4 4 = tp -> getr R4 27 = s11 ->
    as_AKREL H sk4 (mkCfg msF4 mo4) -> as_MPRES H mo mo4 ->
    v4_mid sk4 m4 pid' A v4_X0 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m4 A [CB (Z.to_nat (4 * cap)) jA] -> rw_cells asegs m4 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m4 A (cc_gen (4 * cap') (4 * cap')) -> SHAD m4 b (cc_gen (4 * cap) (4 * cap)) ->
    as_SR H Q (mkCfg msF4 mo4).
  Proof.
    intros msF4 mo4 sk4 m4 R4 pid' A jA Hc VIS4 HF4 B5A G3 G4 G27 KR4 MP4 MID ABR NI CBA XC SHA OSH.
    pose proof RUNS as (_ & _ & _ & _ & _ & B5 & _).
    pose proof MID as (_ & _ & _ & _ & _ & _ & S04 & _ & _ & XP4 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    destruct (v4_hdr_X0 m4 XP4) as (_ & _ & _ & ADV4 & _).
    destruct (B5 R4 F fc m4 v (spz - 112) b cap A cap' (bv_unsigned s10) (bv_unsigned s9) (bv_unsigned s8) v cap' (4 * cap)
                 ASHADOW_BASE (sh (v + 8)) (A + 4 * cap') src (v + 8) (E0 + 408) B5A)
      as (R5 & M5 & Hms & EM5 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25
          & K26 & KK).
    subst M5.
    pose proof (msteps_full asegs _ _ Hms HF4) as HF5. cbn [ms_regs] in HF5.
    eapply (sr_blk H HH); [exact KR4 | exact VIS4 | exact HF4 | exact Hms |].
    intros msF5 mo5 KR5 MP5 VIS5. rewrite <- (rfull_eq R5 HF5) in VIS5.
    eapply (v4_s6 msF5 mo5 sk4 m4 R5 pid' A jA VIS5 HF5).
    - exact K1.
    - exact K10.
    - exact K11.
    - exact K12.
    - pose proof B5A as BP. unfold v4_B5at, vot_B5_pre in BP. decompose [and] BP. clear BP.
      unfold v4_B7at, vot_B7_pre.
      repeat match goal with |- _ /\ _ => split end.
      all: try assumption.
      all: first [ eapply sh0_of_stack0; [exact S04 | lia]
                      | eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia] ].
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR5.
    - eapply (ah_mpres_trans H HH); [exact MP4 | exact MP5].
    - exact MID.
    - exact ABR.
    - exact NI.
    - exact CBA.
    - exact XC.
    - exact SHA.
    - intros _. exact OSH.
  Qed.

  Lemma v4_s4 : forall (msF3 : machine_state) (mo3 : Model) (sk3 : as_St H) (m3 : mem) (R3 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    0 < cap ->
    as_VIS H sk3 msF3 = MS R3 F (Z_to_bv 64 AANNOTATE_CC) fc None m3 (seg_rom asegs) -> rfull R3 ->
    getr R3 1 = Z_to_bv 64 970008 -> getr R3 10 = Z_to_bv 64 b -> getr R3 11 = Z_to_bv 64 (b + 4 * cap) ->
    getr R3 12 = Z_to_bv 64 (b + 4 * cap) -> getr R3 13 = Z_to_bv 64 (b + 4 * cap) ->
    v4_B5at R3 m3 A -> getr R3 3 = gp -> getr R3 4 = tp -> getr R3 27 = s11 ->
    as_AKREL H sk3 (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
    v4_mid sk3 m3 pid' A [] -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m3 A [CB (Z.to_nat (4 * cap)) jA] -> rw_cells asegs m3 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m3 A (cc_gen (4 * cap') (4 * cap')) ->
    as_SR H Q (mkCfg msF3 mo3).
  Proof.
    intros msF3 mo3 sk3 m3 R3 pid' A jA Hc VIS3 HF3 G1 G10 G11 G12 G13 B5 G3 G4 G27 KR3 MP3 MID ABR NI CBA XC SHA.
    pose proof B5 as (G2 & G8 & G9 & G18 & G19 & G22 & G23 & G24 & G25 & F0 & F8 & F16 & FS0 & FS8 & FS16 & FS24
                      & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & WH & P26 & WV & WS
                      & K0 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & Z8 & ZV8 & ZV
                      & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54 & P55).
    pose proof MID as (MI3 & ST3 & _ & _ & AC3 & _ & _ & RH3 & _ & XP3 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v4_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    destruct (v4_old_facts Hc) as (HIn & (O0 & O16 & On & OI & OC & OF & OAP) & OD & NZ).
    assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 4 * cap); split; [reflexivity | exact HIn]).
    pose proof (ah_disj H HH _ _ _ (pid', A, 4 * cap') (pid, b, 4 * cap) RH3 (or_introl eq_refl) (or_intror HIn) NEQ) as DAB.
    cbn [blk_addr blk_size fst snd] in DAB.
    assert (OSH3 : SHAD m3 b (cc_gen (4 * cap) (4 * cap))).
    { eapply v4_SHAD_xpres; [exact XP3 | exact (OLDSH Hc) |]. rewrite cc_gen_length by lia.
      split; [eapply (aclient_range_block_sh H); exact HIn | apply Forall_nil]. }
    rewrite (rfull_eq R3 HF3) in VIS3.
    eapply (ahh_evt_then H HH); [exact KR3 | exact VIS3 | |].
    { eapply HANN with (beg := b) (len := 4 * cap) (oldmid := 4 * cap) (newmid := 4 * cap) (lo := lo).
      - exact G10.
      - exact G11.
      - exact G12.
      - exact G13.
      - exact (v4_mod16_8 b O16).
      - lia.
      - lia.
      - lia.
      - exact OAP.
      - unfold AAPP_HI; lia.
      - exact OSH3.
      - rewrite G2, u64_of_Z by lia. exact (proj1 (stk_split asegs m3 lo (spz - 112 - 96) spz ST3 ltac:(lia))).
      - exact LO1.
      - rewrite G2, u64_of_Z by lia. unfold AINTRIN_STACK. lia.
      - exact MI3.
      - exact AC3.
      - unfold in_app_mem. destruct (v4_band_of_aapp _ _ OAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia. }
    intros msF4 mo4 KR4 MP4 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4
                      & VIS4 & MU4 & WM4 & MI4 & ST4 & SH4 & AC4).
    rewrite G2, u64_of_Z in MU4, ST4 by lia. unfold AINTRIN_STACK in MU4.
    rewrite G1 in VIS4. rewrite (ret_pc_even 970008 ltac:(lia) eq_refl) in VIS4.
    assert (W4 : Forall (v4_wk A v4_X0) [(sh b, sh b + nsh (4 * cap)); (spz - 112 - 96 - 4096, spz - 112 - 96)]).
    { apply Forall_cons; [|apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]].
      apply (v4_wk_oldsh Hc). intros a Ha. unfold v4_X0. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. left. cbn [fst snd]. lia. }
    pose proof (v4_app_sh A (4 * cap') b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (v4_band_of_aapp _ _ AAP)) as DAS.
    pose proof (v4_sh_apart A (4 * cap') b (4 * cap) ltac:(lia) ltac:(lia) (v4_mod16_8 A A16) (v4_mod16_8 b O16) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as DSS.
    pose proof (sh_nsh_high A (4 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHA2. unfold AHI_LO in SHA2.
    pose proof (sh_nsh_high b (4 * cap) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHB2. unfold AHI_LO in SHB2.
    assert (MID4 : v4_mid sk3 m4 pid' A v4_X0).
    { eapply v4_mid_munch; [eapply v4_mid_weaken; [exact MID | intros a Ha; destruct Ha] | exact ABR | exact NI
                           | exact MU4 | exact WM4 | exact MI4 | exact W4]. }
    pose proof MID4 as (_ & _ & _ & _ & _ & _ & S04 & _ & _ & XP4 & _ & _).
    destruct (v4_hdr_X0 m4 XP4) as (F0' & F8' & F16' & ADV4 & WV4).
    assert (FLDT : forall a k z, spz - 112 - 96 <= a -> a + Z.of_nat k <= spz -> fldA m3 a k z -> fldA m4 a k z).
    { intros a k z Ha Hk Hf. unfold fldA in *. eapply fld_agree; [lia | lia | exact Hf |].
      intros a' Ha'. hnf in Ha'. apply MU4. rewrite u64_of_Z by lia. cbn [outside]. split; [lia | split; [lia | exact I]]. }
    clear F0 F8 F16.
    repeat match goal with
           | Hf : fldA m3 ?a ?k ?z |- _ =>
               let Hn := fresh "T" in
               assert (Hn : fldA m4 a k z) by (apply FLDT; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Hf]); clear Hf
           end.
    pose proof (wr_at_transport asegs _ _ _ _ WH WM4) as WH'.
    pose proof (wr_at_transport asegs _ _ _ _ WS WM4) as WS'.
    assert (Z8' : LbB_Kit.sh0 m4 (spz - 112 + 8)) by (eapply sh0_of_stack0; [exact S04 | lia]).
    assert (ZV8' : LbB_Kit.sh0 m4 (v + 8)) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZV' : LbB_Kit.sh0 m4 v) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
    eapply (v4_s5 msF4 mo4 sk3 m4 _ pid' A jA Hc VIS4 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold v4_B5at, vot_B5_pre.
      split; [exact G2|]. split; [exact G8|]. split; [exact G9|]. split; [exact G18|]. split; [exact G19|].
      split; [exact G22|]. split; [exact G23|]. split; [exact G24|]. split; [exact G25|].
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
    - exact G3.
    - exact G4.
    - exact G27.
    - exact KR4.
    - eapply (ah_mpres_trans H HH); [exact MP3 | exact MP4].
    - exact MID4.
    - exact ABR.
    - exact NI.
    - eapply rw_cells_transport; [exact CBA | exact MU4 | exact WM4 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
      cbn. split; [lia | split; [lia | exact I]].
    - eapply rw_cells_transport; [exact XC | exact MU4 | exact WM4 |]. cbn. split; [lia | split; [lia | exact I]].
    - eapply SHAD_transport; [exact SHA | exact MU4 | exact WM4 |]. rewrite cc_gen_length by lia.
      cbn. split; [lia | split; [lia | exact I]].
    - exact SH4.
  Qed.

  Lemma v4_s3 : forall (msF2 : machine_state) (mo2 : Model) (sk2 : as_St H) (m2 : mem) (R2 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jall : list byte),
    as_VIS H sk2 msF2 = MS R2 F (Z_to_bv 64 (E0 + 200)) fc None m2 (seg_rom asegs) -> rfull R2 ->
    getr R2 2 = Z_to_bv 64 (spz - 112) -> getr R2 3 = gp -> getr R2 4 = tp -> getr R2 8 = Z_to_bv 64 (v + 8) ->
    getr R2 9 = Z_to_bv 64 src -> getr R2 10 = Z_to_bv 64 A -> getr R2 18 = Z_to_bv 64 (4 * cap') ->
    getr R2 19 = Z_to_bv 64 (sh (v + 8)) -> getr R2 20 = Z_to_bv 64 ASHADOW_BASE -> getr R2 21 = Z_to_bv 64 (4 * cap) ->
    getr R2 22 = Z_to_bv 64 cap' -> getr R2 23 = Z_to_bv 64 v ->
    getr R2 24 = s8 -> getr R2 25 = s9 -> getr R2 26 = s10 -> getr R2 27 = s11 ->
    as_AKREL H sk2 (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
    v4_mid sk2 m2 pid' A [] -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m2 A [CB (Z.to_nat (4 * cap')) jall] -> addressable m2 A (4 * cap') ->
    as_SR H Q (mkCfg msF2 mo2).
  Proof.
    intros msF2 mo2 sk2 m2 R2 pid' A jall VIS2 HF2 G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR2 MP2 MID ABR NI
      CBall ADD2.
    pose proof RUNS as (_ & B3a & B3ak & B3b & B3bk & _).
    pose proof MID as (MI2 & ST2 & _ & _ & AC2 & _ & S02 & RH2 & FR2 & XP2 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof (v4_band_of_aapp _ _ AAP) as ABND.
    pose proof v4_vec_facts as (_ & _ & _ & _ & C0 & OB).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof OBJ as (_ & _ & _ & _ & _ & SD).
    pose proof SRCR as (SR4 & SR0 & SR47).
    assert (VB2 : 1048576 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    assert (HNEW : v + 24 <= A \/ A + 4 * cap' <= v) by (eapply v4_hdr_fresh; [exact RH2 | exact NI | lia]).
    assert (XP2' : xpres H LB spz v4_X0 m m2)
      by (eapply (xpres_weaken H); [exact XP2 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
    destruct (v4_hdr_X0 m2 XP2') as (F0 & F8 & F16 & ADV2 & WV2).
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    assert (SRCF : src + 4 <= spz - 112 \/ spz <= src).
    { destruct (Z_le_gt_dec (src + 4) (spz - 112)) as [L1|L1]; [left; exact L1|].
      destruct (Z_le_gt_dec spz src) as [L2|L2]; [right; exact L2|]. exfalso.
      assert (SA : spz - 112 <= src /\ src + 4 <= spz) by (Z.div_mod_to_equations; lia).
      assert (WS0 : wr_at asegs m src 4) by (eapply wr_at_of_stk_win; [exact ST0 | lia | lia]).
      assert (BL : forall z, length (word_to_le_bytes 4 (Z_to_bv 64 z)) = 4%nat) by (intros z; reflexivity).
      pose proof (wr_at_store_ok asegs m src 4 0 4%nat WS0 ltac:(lia) ltac:(lia)) as SO. rewrite Z.add_0_r in SO.
      assert (KEY : forall y, nth_error (word_to_le_bytes 4 (Z_to_bv 64 x)) 0 = nth_error (word_to_le_bytes 4 (Z_to_bv 64 y)) 0).
      { intros y.
        assert (MIW : mem_inv asegs (write_to_mem m (wa src) (word_to_le_bytes 4 (Z_to_bv 64 y)))).
        { apply mem_inv_store; [exact MI0 | rewrite BL; exact SO]. }
        assert (MUW : munch [(src, src + 4)] m (write_to_mem m (wa src) (word_to_le_bytes 4 (Z_to_bv 64 y)))).
        { apply munch_write; [apply munch_refl | lia | rewrite BL; lia | cbn [inside]; left; rewrite BL; lia]. }
        assert (WMW : wmono asegs m (write_to_mem m (wa src) (word_to_le_bytes 4 (Z_to_bv 64 y)))).
        { apply wmono_write. apply wmono_refl. }
        assert (ACW : ACONST (write_to_mem m (wa src) (word_to_le_bytes 4 (Z_to_bv 64 y)))).
        { eapply ACONST_frame; [exact AC0 | exact MUW | exact WMW |]. apply Forall_cons; [|apply Forall_nil].
          apply aconst_ok_high; [|right; left; lia].
          pose proof (sh_below_aceil AIMG_TOP ltac:(unfold AIMG_TOP, AAPP_HI; lia)) as SBA. lia. }
        assert (APW : apres H LB spz m (write_to_mem m (wa src) (word_to_le_bytes 4 (Z_to_bv 64 y)))).
        { eapply (apres_of_munch H HH); [exact RH0 | exact MUW | exact WMW |].
          apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
        destruct (SRC _ ACW MIW APW) as [FX _].
        unfold fldA, fld in FX.
        assert (BX : bytes_at asegs (write_to_mem m (wa src) (word_to_le_bytes 4 (Z_to_bv 64 y))) src
                       (word_to_le_bytes 4 (Z_to_bv 64 x))).
        { apply bytes_at_of_rdn; [lia | rewrite BL; lia | rewrite BL; exact FX]. }
        destruct BX as (_ & _ & BX). specialize (BX 0%nat ltac:(rewrite BL; lia)).
        rewrite <- BX. unfold mrd. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
        rewrite write_to_mem_spec by (try rewrite BL; lia).
        rewrite wa_unsigned by lia. rewrite BL, Z.leb_refl, Z.sub_diag.
        destruct (Z.ltb_spec0 src (src + Z.of_nat 4)) as [_|NL]; [|exfalso; lia]. cbn [andb]. change (Z.to_nat 0) with 0%nat.
        destruct (nth_error (word_to_le_bytes 4 (Z_to_bv 64 y)) 0) eqn:EN0; [reflexivity|].
        apply nth_error_None in EN0. rewrite BL in EN0. lia. }
      pose proof (KEY 0) as K0. pose proof (KEY 1) as K1. rewrite K0 in K1.
      apply (f_equal (option_map bv_unsigned)) in K1. vm_compute in K1. discriminate K1. }
    destruct (SRC m2 AC2 MI2 (apres_of_xpres_nil m2 XP2)) as [FS ACS].
    destruct (v4_src_shk m2 src ACS SR4 SR0) as (k & SK & KR).
    destruct (rw_cells_CB_split asegs m2 A (Z.to_nat (4 * cap')) (Z.to_nat (4 * cap)) jall CBall ltac:(lia)) as [CBA _].
    pose proof (proj2 CBall) as WA. cbn [cells_size csize] in WA. rewrite Nat.add_0_r, Z2Nat.id in WA by lia.
    assert (WSL : wr_at asegs m2 (A + 4 * cap) 4) by (eapply v4_wr_sub; [exact WA | lia | lia | lia]).
    assert (WSB : wr_at asegs m2 (spz - 112) 32) by (eapply wr_at_of_stk_win; [exact ST2 | lia | lia]).
    assert (WHF : wr_at asegs m2 (spz - 112 - 96) 96) by (eapply wr_at_of_stk_win; [exact ST2 | lia | lia]).
    assert (FV : fldA m2 (spz - 112 + 32) 8 v).
    { unfold fldA, fld. pose proof (rw_cells_read asegs m2 (spz - 80) FRAME 0%nat _ FR2 eq_refl) as RD.
      replace (spz - 80 + Z.of_nat 0) with (spz - 112 + 32) in RD by lia. rewrite <- rdn_of_ov. exact RD. }
    assert (ZV : LbB_Kit.sh0 m2 v) by (eapply sh0_of_addressable; [exact ADV2 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZV8 : LbB_Kit.sh0 m2 (v + 8)) by (eapply sh0_of_addressable; [exact ADV2 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZV16 : LbB_Kit.sh0 m2 (v + 16)) by (eapply sh0_of_addressable; [exact ADV2 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZSB : LbB_Kit.sh0 m2 (spz - 112 + 8)) by (eapply sh0_of_stack0; [exact S02 | lia]).
    assert (SHA0 : SHAD m2 A (cc_gen (4 * cap') (4 * cap'))) by (rewrite cc_gen_full; exact (proj2 ADD2)).
    pose proof (sh_nsh_high A (4 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHA2. unfold AHI_LO in SHA2.
    pose proof (v4_app_sh (A + 4 * cap) 4 A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct ABND; [left|right]; lia)) as DAS.
    pose proof (msteps_full asegs) as MSF.
    destruct OB as [[E1 E2]|(Hc & HIn & ABb)].
    -
      assert (C1 : cap' = 1) by (unfold cap', v4_newcap; rewrite E2; reflexivity).
      assert (BM4 : b mod 4 = 0) by (rewrite E1; reflexivity).
      assert (SK4 : LbB_Kit.shk m2 (A + 4 * cap) 4).
      { rewrite E2. replace (A + 4 * 0) with A by lia. apply v4_shk4. pose proof ADD2 as ADD2'. rewrite C1 in ADD2'. exact ADD2'. }
      pose proof (B3b R2 F fc m2 A (spz - 112) v src cap b x cap') as B3b'.
      pose proof (B3bk R2 F fc m2 A (spz - 112) v src cap b x cap' k) as B3bk'.
      match type of B3b' with _ -> ?P => assert (EX : P) end.
      { destruct KR as [K0|KR'].
        - apply B3b'. subst k. unfold vot_B3b_pre.
          repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
        - assert (SR8 : src mod 8 = 0) by (clear - SR4 KR'; Z.div_mod_to_equations; lia).
          apply B3bk'. unfold vot_B3bk_pre.
          repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
      destruct EX as (R3 & M3 & Hms & MU3 & WM3 & W0 & W1 & W2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & S16 & XA & S24 & S8 & S0
                      & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & KK).
      pose proof (MSF _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
      assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
      assert (MID3 : v4_mid sk2 M3 pid' A []).
      { eapply v4_mid_munch; [exact MID | exact ABR | exact NI | exact MU3 | exact WM3 | exact MI3 |].
        apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_nil]. }
      pose proof MID3 as (_ & _ & _ & _ & _ & _ & S03 & _ & _ & XP3 & _ & _).
      assert (XP3' : xpres H LB spz v4_X0 m M3)
        by (eapply (xpres_weaken H); [exact XP3 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
      destruct (v4_hdr_X0 M3 XP3') as (F0' & F8' & F16' & ADV3 & WV3).
      rewrite G26 in W0. rewrite G25 in W1. rewrite G24 in W2.
      assert (W0' : fldA M3 (spz - 112 - 96) 8 (bv_unsigned s10)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W0).
      assert (W1' : fldA M3 (spz - 112 - 88) 8 (bv_unsigned s9)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W1).
      assert (W2' : fldA M3 (spz - 112 - 80) 8 (bv_unsigned s8)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W2).
      pose proof (wr_at_transport asegs _ _ _ _ WHF WM3) as WHF3.
      pose proof (wr_at_transport asegs _ _ _ _ WSB WM3) as WSB3.
      assert (ZS0 : LbB_Kit.sh0 M3 (spz - 112)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZS8 : LbB_Kit.sh0 M3 (spz - 112 + 8)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZS16 : LbB_Kit.sh0 M3 (spz - 112 + 16)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZS24 : LbB_Kit.sh0 M3 (spz - 112 + 24)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZV3 : LbB_Kit.sh0 M3 v) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZV83 : LbB_Kit.sh0 M3 (v + 8)) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZV163 : LbB_Kit.sh0 M3 (v + 16)) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (XC3 : rw_cells asegs M3 (A + 4 * cap) [C4 (Z_to_bv 64 x)]).
      { pose proof (wr_at_transport asegs _ _ _ _ WSL WM3) as WSL3. pose proof WSL3 as (WL0 & WL1 & _).
        split; [|exact WSL3]. split; [clear - WL0; cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        apply bytes_at_of_rdn; [lia | rewrite length_le4; lia | rewrite length_le4; exact XA]. }
      assert (SHA3 : SHAD M3 A (cc_gen (4 * cap') (4 * cap'))).
      { eapply SHAD_transport; [exact SHA0 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia.
        cbn. split; [lia | split; [lia | exact I]]. }
      eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
      intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
      eapply (v4_s6 msF3 mo3 sk2 M3 R3 pid' A [] VIS3 HF3).
      + exact K1.
      + exact K10.
      + exact K11.
      + exact K12.
      + unfold v4_B7at, vot_B7_pre.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR3.
      + eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
      + eapply (v4_mid_weaken _ _ _ _ [] v4_X0); [exact MID3 | intros a Ha; destruct Ha].
      + exact ABR.
      + exact NI.
      + rewrite E2. change (Z.to_nat (4 * 0)) with 0%nat. apply v4_CB0. lia.
      + exact XC3.
      + exact SHA3.
      + intros Hc. lia.
    -
      pose proof ABb as (O0 & O16 & On & OI & OC & OF & OAP).
      assert (B16 : 16 <= b) by exact (v4_mod16_16le b O0 O16).
      assert (BM4 : b mod 4 = 0) by (clear - O16; Z.div_mod_to_equations; lia).
      assert (SH0 : LbB_Kit.sh0 m2 (A + 4 * cap)).
      { eapply sh0_of_addressable; [exact ADD2|]. pose proof (v4_new_granule cap ltac:(lia)) as NG.
        change (vgrow cap) with cap' in NG. lia. }
      pose proof (B3a R2 F fc m2 A (spz - 112) v src cap b x cap') as B3a'.
      pose proof (B3ak R2 F fc m2 A (spz - 112) v src cap b x cap' k) as B3ak'.
      match type of B3a' with _ -> ?P => assert (EX : P) end.
      { destruct KR as [K0|KR'].
        - apply B3a'. subst k. unfold vot_B3a_pre.
          repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
        - assert (SR8 : src mod 8 = 0) by (clear - SR4 KR'; Z.div_mod_to_equations; lia).
          apply B3ak'. unfold vot_B3ak_pre.
          repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
      destruct EX as (R3 & M3 & Hms & MU3 & WM3 & W0 & W1 & W2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & S16 & XA & S24 & S8 & S0
                      & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & KK).
      pose proof (MSF _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
      assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
      assert (MID3 : v4_mid sk2 M3 pid' A []).
      { eapply v4_mid_munch; [exact MID | exact ABR | exact NI | exact MU3 | exact WM3 | exact MI3 |].
        apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_nil]. }
      pose proof MID3 as (_ & _ & _ & _ & _ & _ & S03 & _ & _ & XP3 & _ & _).
      assert (XP3' : xpres H LB spz v4_X0 m M3)
        by (eapply (xpres_weaken H); [exact XP3 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
      destruct (v4_hdr_X0 M3 XP3') as (F0' & F8' & F16' & ADV3 & WV3).
      rewrite G26 in W0. rewrite G25 in W1. rewrite G24 in W2.
      assert (W0' : fldA M3 (spz - 112 - 96) 8 (bv_unsigned s10)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W0).
      assert (W1' : fldA M3 (spz - 112 - 88) 8 (bv_unsigned s9)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W1).
      assert (W2' : fldA M3 (spz - 112 - 80) 8 (bv_unsigned s8)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W2).
      pose proof (wr_at_transport asegs _ _ _ _ WHF WM3) as WHF3.
      pose proof (wr_at_transport asegs _ _ _ _ WSB WM3) as WSB3.
      assert (ZS8 : LbB_Kit.sh0 M3 (spz - 112 + 8)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZV3 : LbB_Kit.sh0 M3 v) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZV83 : LbB_Kit.sh0 M3 (v + 8)) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (XC3 : rw_cells asegs M3 (A + 4 * cap) [C4 (Z_to_bv 64 x)]).
      { pose proof (wr_at_transport asegs _ _ _ _ WSL WM3) as WSL3. pose proof WSL3 as (WL0 & WL1 & _).
        split; [|exact WSL3]. split; [clear - WL0; cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        apply bytes_at_of_rdn; [lia | rewrite length_le4; lia | rewrite length_le4; exact XA]. }
      assert (SHA3 : SHAD M3 A (cc_gen (4 * cap') (4 * cap'))).
      { eapply SHAD_transport; [exact SHA0 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia.
        cbn. split; [lia | split; [lia | exact I]]. }
      eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
      intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
      eapply (v4_s4 msF3 mo3 sk2 M3 R3 pid' A (firstn (Z.to_nat (4 * cap)) jall) ltac:(lia) VIS3 HF3).
      + exact K1.
      + exact K10.
      + exact K11.
      + rewrite K12. unfold wz. f_equal. lia.
      + rewrite K13. unfold wz. f_equal. lia.
      + unfold v4_B5at, vot_B5_pre.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR3.
      + eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
      + exact MID3.
      + exact ABR.
      + exact NI.
      + eapply rw_cells_transport; [exact CBA | exact MU3 | exact WM3 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        cbn. split; [lia | split; [lia | exact I]].
      + exact XC3.
      + exact SHA3.
  Qed.

  Lemma v4_sn : forall (msF1 : machine_state) (mo1 : Model) (m1 : mem) (R1 : bvmap 5 word) (e1 : word),
    as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs) -> rfull R1 ->
    getr R1 1 = Z_to_bv 64 (E0 + 200) -> getr R1 2 = Z_to_bv 64 (spz - 112) -> getr R1 3 = gp -> getr R1 4 = tp ->
    getr R1 8 = Z_to_bv 64 (v + 8) -> getr R1 9 = Z_to_bv 64 src -> getr R1 10 = Z_to_bv 64 (4 * cap') ->
    getr R1 18 = Z_to_bv 64 (4 * cap') -> getr R1 19 = Z_to_bv 64 (sh (v + 8)) -> getr R1 20 = Z_to_bv 64 ASHADOW_BASE ->
    getr R1 21 = Z_to_bv 64 (4 * cap) -> getr R1 22 = Z_to_bv 64 cap' -> getr R1 23 = Z_to_bv 64 v ->
    getr R1 24 = s8 -> getr R1 25 = s9 -> getr R1 26 = s10 -> getr R1 27 = s11 ->
    as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    mem_inv asegs m1 -> stk asegs m1 lo spz -> rw_cells asegs m1 (errno_addr tp) [C4 e1] -> as_rauxv_ok H m1 B ->
    ACONST m1 -> as_RFS H LF m1 -> stack0 m1 lo shi -> as_RHEAP H s LB m1 -> rw_cells asegs m1 (spz - 80) FRAME ->
    xpres H LB spz [] m m1 -> lb_own LB m1 ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 m1 R1 e1 VIS1 HF1 G1 G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR1 MP1
      MI1 ST1 ERR1 RA1 AC1 RF1 S01 RH1 FR1 XP1 OW1.
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof v4_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (SP112 : (spz - 112) mod 16 = 0).
    { replace (spz - 112) with (spz + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact SP16. }
    assert (CMB : as_Cm H (4 * cap') <= as_AL H s).
    { pose proof CM as CM'. change (v4_newcap cap) with cap' in CM'.
      assert (CF0 : 0 <= as_Cf H (4 * cap)) by (pose proof (ah_costs H HH) as (_ & _ & CF & _); apply CF; lia). lia. }
    rewrite (rfull_eq R1 HF1) in VIS1.
    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH) with (n := 4 * cap') (LB := LB) (lo := lo) (B := B) (errv := e1);
        [ exact VIS1 | exact RH1 | exact KR1 | exact AOK | exact CMB | exact RA1 | rewrite G2, u64_of_Z by lia; lia
        | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo (spz - 112) spz ST1 ltac:(lia)))
        | exact LO1 | rewrite G2, u64_of_Z by lia; unfold AOPNEW_STACK, AMALLOC_STACK; lia
        | rewrite G4; exact ERR1 | exact MI1 | rewrite G4; exact TPV | rewrite G2, u64_of_Z by lia; exact SP112
        | exact AC1 | exact G10 | lia ]. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & A & junk & p
                      & sk2 & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RAX2 & AP2 & ABR & RH2 & CB2 & ADDR & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite G1 in VIS2. destruct (v4_E0_even 200 ltac:(lia) eq_refl) as [ER1 ER2].
    rewrite (ret_pc_even (E0 + 200) ER1 ER2) in VIS2.
    rewrite G2, u64_of_Z in AP2, ST2 by lia. rewrite G4 in ERR2.
    pose proof (ah_nodup H HH _ _ _ RH2) as ND. cbn [map] in ND. apply NoDup_cons_iff in ND as [NI _].
    cbn [blk_id fst] in NI.
    eapply (v4_s3 msF2 mo2 sk2 m2 _ p A junk VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - exact G2.
    - exact G3.
    - exact G4.
    - exact G8.
    - exact G9.
    - reflexivity.
    - exact G18.
    - exact G19.
    - exact G20.
    - exact G21.
    - exact G22.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR2.
    - eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
    - split; [exact MI2|].
      split; [eapply (stk_merge asegs); [exact ST2 | | lia];
              eapply (apres_stk H); [exact AP2 | exact (proj2 (stk_split asegs m1 lo (spz - 112) spz ST1 ltac:(lia))) | lia]|].
      split; [exists errv2; exact ERR2|].
      split; [exact RAX2|]. split; [exact AC2|].
      split; [exact (RFS_via_apres H HH LF LB _ m1 m2 RF1 AP2)|].
      split; [eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]|].
      split; [exact RH2|].
      split; [eapply (apres_rw_cells H); [exact AP2 | exact FR1 | left; lia]|].
      split; [eapply (xpres_trans H); [exact XP1 |];
              eapply (xpres_weaken H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]|].
      split; [exact AL2|].
      apply lb_own_cons; [exact (own_of_rw_cells _ _ _ _ CB2 ltac:(lia)) | exact (lb_own_apres H _ _ _ _ _ OW1 AP2 (fun bb Hb => Hb))].
    - exact ABR.
    - exact NI.
    - exact CB2.
    - exact ADDR.
  Qed.

  Lemma v4_main : forall (msF : machine_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 E0) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv VIS KR ERR.
    pose proof RUNS as (B1 & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof v4_vec_facts as (F0 & F1 & F2 & _ & C0 & OB).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (GZ : gz m v 24) by (intros i Hi; eapply sh0_of_addressable; [exact ADV0 | change (8 * (24 / 8)) with 24; lia]).
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    assert (VSD : v + 24 <= spz - 112 \/ spz <= v) by (destruct OBJ as (_ & _ & _ & _ & _ & SD); lia).
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R0 eqn:HR0.
    assert (HF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
    destruct (B1 R0 F fc m v b cap src spz lo ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity)
                 ltac:(rewrite HR0; exact spz_sp) AC0 F0 F1 F2 GZ ST0 ltac:(lia) ltac:(lia) SPH
                 ltac:(destruct VBAND; lia) ltac:(destruct VBAND; lia) VSD (proj1 OB0) (proj2 OB0) ltac:(lia))
      as (R1 & M1 & Hms & MU1 & WM1 & FR1 & K1 & K2 & K10 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & KK).
    assert (FRM : rw_cells asegs M1 (spz - 80) FRAME) by (rewrite HR0 in FR1; exact FR1).
    pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    destruct (stack_window_ok H LB LF (spz - 112) spz ltac:(lia) FS2) as (SW1 & SW2 & SW3).
    destruct (client_frame H HH s LB LF B [(spz - 112, spz)] m M1 RH0 RF0 AC0 RA0 MU1 WM1
                ltac:(apply Forall_cons; [exact SW1 | apply Forall_nil]) ltac:(apply Forall_cons; [exact SW2 | apply Forall_nil])
                ltac:(apply Forall_cons; [exact SW3 | apply Forall_nil]))
      as (RH1 & RF1 & AC1 & RA1).
    assert (ST1 : stk asegs M1 lo spz) by (apply (stk_high_transport m M1 lo spz ST0 WM1); unfold AIMG_TOP; lia).
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. split; [lia | exact I]. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S00 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (XP1 : xpres H LB spz [] m M1).
    { eapply (xpres_of_munch H s LB spz [] [(spz - 112, spz)] m m M1); [exact HH | exact RH0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (OW1 : lb_own LB M1) by exact (lb_own_wmono _ _ _ OWN WM1).
    eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R1 HF1) in VIS1.
    eapply (v4_sn msF1 mo1 M1 R1 errv VIS1 HF1).
    - exact K1.
    - exact K2.
    - rewrite (KK 3%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 4%bv ltac:(inb)), HR0. reflexivity.
    - exact K8.
    - exact K9.
    - exact K10.
    - exact K18.
    - exact K19.
    - exact K20.
    - exact K21.
    - exact K22.
    - exact K23.
    - rewrite (KK 24%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 25%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 26%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 27%bv ltac:(inb)), HR0. reflexivity.
    - exact KR1.
    - exact MP1.
    - exact MI1.
    - exact ST1.
    - exact ERR1.
    - exact RA1.
    - exact AC1.
    - exact RF1.
    - exact S01.
    - exact RH1.
    - exact FRM.
    - exact XP1.
    - exact OW1.
  Qed.
End V4S.

Definition v32_runs (E : Z) : Prop :=
  v4_B1 E /\ v32_B3a E /\ v32_B3ak E /\ v32_B3b E /\ v32_B3bk E /\ v32_B5 E /\ v32_B7 E /\ v32_B9D E /\ v32_B9N E
  /\ v32_B11 E /\ v4_ret_ok (E + 528).

Lemma v32_runs_f871c : v32_runs (v4_entry V32_SLOW_CREF).
Proof.
  exact (conj v4_B1_f871c (conj v32_B3a_f871c (conj v32_B3ak_f871c (conj v32_B3b_f871c (conj v32_B3bk_f871c
    (conj v32_B5_f871c (conj v32_B7_f871c (conj v32_B9D_f871c (conj v32_B9N_f871c (conj v32_B11_f871c
    v4_ret_ok_f871c)))))))))).
Qed.

Lemma v32_runs_f898c : v32_runs (v4_entry V32_SLOW_RREF).
Proof.
  exact (conj v4_B1_f898c (conj v32_B3a_f898c (conj v32_B3ak_f898c (conj v32_B3b_f898c (conj v32_B3bk_f898c
    (conj v32_B5_f898c (conj v32_B7_f898c (conj v32_B9D_f898c (conj v32_B9N_f898c (conj v32_B11_f898c
    v4_ret_ok_f898c)))))))))).
Qed.
Section V4S32.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable c : v4_consts.
  Hypothesis RUNS : v32_runs (v4_entry c).
  Hypothesis DRA : v4_del_ra c = v4_entry c + 484.

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
            (v b cap src x : Z) (xs : list Z) (pid : bptr) (lo B shi spz : Z).
  Hypothesis SPZ : bv_unsigned sp = spz.
  Hypothesis SPR : 2 ^ 45 <= spz - 112 /\ spz <= 2 ^ 47 /\ spz mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis TRO : trace_ok (as_TR H) APC0_FREE [v4_del_ra c].
  Hypothesis VBAND : (0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47).
  Hypothesis OBJ : obj_win H LB LF spz lo v 24.
  Hypothesis V8 : v mod 8 = 0.
  Hypothesis XSL : Zlen xs = cap.
  Hypothesis VEC : vec32A LB m v b xs cap.
  Hypothesis OLD : v4_oldblk LB b cap pid.
  Hypothesis OLDSH : 0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * cap)).
  Hypothesis GROW : 4 * v4_newcap cap <= 2 ^ 26.
  Hypothesis XR : 0 <= x < 2 ^ 32.
  Hypothesis SRC : src4_keep H LB spz m src x.
  Hypothesis SRCR : src mod 4 = 0 /\ 0 <= src /\ src + 4 <= 2 ^ 47.
  Hypothesis RH0 : as_RHEAP H s LB m.
  Hypothesis AOK : as_alloc_ok H s LB (4 * v4_newcap cap).
  Hypothesis CM : as_Cm H (4 * v4_newcap cap) + as_Cf H (4 * cap) <= as_AL H s.
  Hypothesis RA0 : as_rauxv_ok H m B.
  Hypothesis SPB : spz <= B.
  Hypothesis ST0 : stk asegs m lo spz.
  Hypothesis LOR : aceil <= lo /\ lo <= spz - V4_STACK.
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis AC0 : ACONST m.
  Hypothesis RF0 : as_RFS H LF m.
  Hypothesis S00 : stack0 m lo shi.
  Hypothesis SHI : spz <= shi.
  Hypothesis ADV0 : addressable m v 24.
  Hypothesis VWR : wr_at asegs m v 24.
  Hypothesis OWN : lb_own LB m.
  Hypothesis E0R : 0 <= v4_entry c < 0x200000 /\ v4_entry c mod 4 = 0.

  Let E0 := v4_entry c.
  Let cap' := v4_newcap cap.
  Let Q := v4slow_post H c ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap x xs pid lo B shi m mo.
  Let FRAME : list cell := map (fun w => C8 w) [Z_to_bv 64 v; s7; s6; s5; s4; s3; s2; s1; s0; ra].

  Lemma spz_sp32 : sp = Z_to_bv 64 spz.
  Proof. rewrite <- SPZ. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Definition v32c_B5at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    v32_B5_pre R mk v (spz - 112) b cap A cap' (bv_unsigned s8) v cap' (4 * cap) ASHADOW_BASE (sh (v + 8))
      (A + 4 * cap') src (v + 8) (E0 + 404).

  Definition v32c_B7at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    v32_B7_pre R mk v (spz - 112) b cap A cap' (bv_unsigned s8) v cap' (4 * cap) ASHADOW_BASE (sh (v + 8))
      (A + 4 * cap') src (v + 8) (E0 + 404).

  Definition v32c_B9at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    v32_B9_pre E0 R mk A (spz - 112) v src cap b cap' (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
      (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) (bv_unsigned s6) (bv_unsigned s7).

  Definition v32c_B11at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    v32_B11_pre R mk A (spz - 112) v cap (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
      (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) (bv_unsigned s6) (bv_unsigned s7).

  Definition v32c_mid (sk : as_St H) (mk : mem) (pid' : bptr) (A : Z) (Xk : list (Z * Z)) : Prop :=
    mem_inv asegs mk /\ stk asegs mk lo spz /\ (exists e, rw_cells asegs mk (errno_addr tp) [C4 e]) /\ as_rauxv_ok H mk B
    /\ ACONST mk /\ as_RFS H LF mk /\ stack0 mk lo shi /\ as_RHEAP H sk ((pid', A, 4 * cap') :: LB) mk
    /\ rw_cells asegs mk (spz - 80) FRAME /\ xpres H LB spz Xk m mk /\ as_AL H sk >= as_AL H s - as_Cm H (4 * cap')
    /\ lb_own ((pid', A, 4 * cap') :: LB) mk.

  Definition v32c_wk (A : Z) (Xk : list (Z * Z)) (iv : Z * Z) : Prop :=
    (aceil <= fst iv /\ snd iv <= spz - 80)
    \/ (A <= fst iv /\ snd iv <= A + 4 * cap')
    \/ (sh A <= fst iv /\ snd iv <= sh A + nsh (4 * cap'))
    \/ ((forall a, fst iv <= a < snd iv -> rin_ivs Xk a) /\ aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv
        /\ stack0_ok iv /\ (snd iv <= spz - 80 \/ spz <= fst iv) /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)).

  Lemma v32c_cls : forall s' LBx p A n SP m0 a,
    as_RHEAP H s' ((p, A, n) :: LBx) m0 -> ~ In p (map blk_id LBx) -> aceil <= SP -> aclient_addr H LBx SP a ->
    SP <= a \/ (a < aceil /\ ~ (A <= a < A + n) /\ ~ (sh A <= a < sh A + nsh n)).
  Proof.
    intros s' LBx p A n SP m0 a RH NI HSP Hc.
    pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    unfold blk_addr, blk_size in R0, R16, Rn, RI, RC, RF, RAPP. cbn [fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    pose proof aceil_facts as ACF.
    assert (SHA : sh A + nsh n <= sh aceil).
    { unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
    assert (SHB : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; acb; Z.div_mod_to_equations; lia).
    unfold AIMG_TOP in RI.
    assert (SHL : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    acb.
    unfold aclient_addr in Hc.
    destruct Hc as [Hc|[Hc|[(b0 & Hb & Hr)|[(b0 & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
    - left. exact Hc.
    - right. unfold aimg_client in Hc. destruct Hc as [Hc|[Hc|[Hc|Hc]]]; (split; [lia | split; lia]).
    - right. assert (Hb' : In b0 ((p, A, n) :: LBx)) by (right; exact Hb).
      assert (Hid : blk_id b0 <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
      pose proof (ah_disj H HH _ _ _ (p, A, n) b0 RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b0 RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
      destruct b0 as [[pb Ab] nb]. unfold blk_addr, blk_size in *. cbn [fst snd] in *.
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in QAPP, HI2.
      destruct D as [D|D]; destruct QAPP as [QAPP|QAPP]; split; try lia; split; lia.
    - right. assert (Hb' : In b0 ((p, A, n) :: LBx)) by (right; exact Hb).
      assert (Hid : blk_id b0 <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
      pose proof (ah_disj H HH _ _ _ (p, A, n) b0 RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b0 RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      unfold blk_addr, blk_size in D, Hr, Q0, Q16, Qn, QI, QC, QF, QAPP. cbn [fst snd] in D.
      destruct b0 as [[pb Ab] nb]. cbn [fst snd] in *.
      unfold aapp, aapp_lo, aapp_hi in RAPP, QAPP. acb.
      unfold nsh, sh, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      Z.div_mod_to_equations.
      destruct D as [D|D]; split; try lia; split; lia.
    - right. assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in F4, HI2. unfold AFS_SIZE in *.
      destruct RF as [RF|RF]; destruct F4 as [F4|F4]; split; try lia; split; lia.
    - right. unfold aapp, aapp_lo, aapp_hi in RAPP, F4. acb.
      unfold sh, nsh, AFS_SIZE, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      Z.div_mod_to_equations.
      destruct RF as [RF|RF]; split; try lia; split; lia.
    - right. assert (SA0 : 0x7fff8000 <= sh aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in RAPP, Hc. destruct RAPP as [RP|RP]; split; try lia; split; lia.
  Qed.

  Lemma v32c_xpres_mixed : forall s' p A n SP X m0 m1 m2 W,
    as_RHEAP H s' ((p, A, n) :: LB) m0 -> ~ In p (map blk_id LB) -> aceil <= SP ->
    munch W m1 m2 -> wmono asegs m1 m2 ->
    Forall (fun iv : Z * Z => (A <= fst iv /\ snd iv <= A + n) \/ (sh A <= fst iv /\ snd iv <= sh A + nsh n)
                              \/ (aceil <= fst iv /\ snd iv <= SP) \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
    xpres H LB SP X m1 m2.
  Proof.
    intros s' p A n SP X m0 m1 m2 W RH NI HSP MU WM FW a Ha [Hc Hx].
    pose proof (v32c_cls s' LB p A n SP m0 a RH NI HSP Hc) as CLS.
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[l h] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as H1. cbn in H1.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      destruct H1 as [[H1 H2]|[[H1 H2]|[[H1 H2]|H1]]].
      - destruct CLS as [C|(C1 & C2 & C3)]; [pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (_ & _ & _ & _ & RC & _); cbn in RC|]; lia.
      - destruct CLS as [C|(C1 & C2 & C3)].
        + assert (sh A + nsh n <= sh aceil).
          { pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & _ & Rn & _ & RC & _). cbn in *.
            unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
          assert (sh aceil < aceil) by (apply sh_below_aceil; acb; unfold AAPP_HI; lia). lia.
        + lia.
      - destruct CLS as [C|(C1 & C2 & C3)]; lia.
      - intros K. apply Hx. apply H1. exact K. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  Lemma v32c_mid_munch : forall sk mk mk' pid' A Xk W,
    v32c_mid sk mk pid' A Xk -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    munch W mk mk' -> wmono asegs mk mk' -> mem_inv asegs mk' -> Forall (v32c_wk A Xk) W ->
    v32c_mid sk mk' pid' A Xk.
  Proof.
    intros sk mk mk' pid' A Xk W (MI & ST & (e & ERR) & RA & AC & RF & S0 & RH & FR & XP & AL & OW) ABR NI MU WM MI' FW.
    destruct SPR as (SPL & SPH & SP16). destruct LOR as [LO1 LO2].
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof ABR as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
    pose proof (ah_fsb H HH _ _ _ RH) as (FS1 & FS2 & FS3 & FS4).
    assert (SHAb : sh A + nsh (4 * cap') <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHAl : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHAC : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHIT : sh AIMG_TOP <= sh A) by (unfold sh, AIMG_TOP; Z.div_mod_to_equations; lia).
    assert (VSPZ : AIMG_TOP <= lo) by (unfold AIMG_TOP; lia).
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.

    assert (W1 : Forall (aclient_write_ok H ((pid', A, 4 * cap') :: LB)) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold v32c_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & Hw & _)]]].
      - left. cbn. lia.
      - right; right; left. exists (pid', A, 4 * cap'). split; [left; reflexivity | cbn; lia].
      - right; right; right; left. exists (pid', A, 4 * cap'). split; [left; reflexivity | cbn; lia].
      - unfold aclient_write_ok in *.
        destruct Hw as [K|[K|[(b' & Hb & K)|[(b' & Hb & K)|K]]]]; [left; exact K | right; left; exact K | | | right; right; right; right; exact K].
        + right; right; left. exists b'. split; [right; exact Hb | exact K].
        + right; right; right; left. exists b'. split; [right; exact Hb | exact K]. }
    assert (W2 : Forall (afs_write_ok H LF) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold v32c_wk in Hw. cbn [fst snd] in Hw.
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in FS4, BAPP. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & Hw & _)]]]; [left; cbn; unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; lia | | | exact Hw].
      - left. cbn. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. split; [destruct BF; lia | lia].
      - left. cbn. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. split; [destruct FS4; lia | lia]. }
    assert (W3 : Forall aconst_ok W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold v32c_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & Hw & _)]]]; [| | | exact Hw].
      - apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia].
      - eapply (aconst_ok_app A (4 * cap')); [exact BAPP | lia | lia].
      - apply aconst_ok_high; [lia | right; left; lia]. }
    assert (W4 : Forall stack0_ok W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold v32c_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & Hw & _)]]]; [| | | exact Hw].
      - left. cbn. unfold AHI_LO. lia.
      - eapply (stack0_ok_aapp A (4 * cap')); [exact BAPP | lia | lia].
      - right. cbn. lia. }
    destruct (client_frame H HH sk _ LF B W mk mk' RH RF AC RA MU WM W1 W2 W3) as (RH' & RF' & AC' & RA').
    split; [exact MI'|]. split; [eapply BakeStackRep.stk_high_transport; [exact ST | exact WM | exact VSPZ]|].
    split.
    { exists e. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. subst tp. rewrite u64_of_Z by (unfold ATP; lia).
      eapply disjoint_from_of_Forall; [exact FW|]. intros l h Hw. unfold v32c_wk in Hw. cbn [fst snd cells_size csize Z.of_nat] in *.
      unfold ATP in *. destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & _ & _ & Hw)]]]; lia. }
    split; [exact RA'|]. split; [exact AC'|]. split; [exact RF'|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact W4]|].
    split; [exact RH'|].
    split.
    { eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      eapply disjoint_from_of_Forall; [exact FW|]. intros l h Hw. unfold v32c_wk in Hw. cbn [fst snd] in Hw.
      unfold FRAME. rewrite v4_cells_size_map_C8'. cbn [length].
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & _ & Hw & _)]]]; lia. }
    split; [|split; [exact AL | exact (lb_own_wmono _ _ _ OW WM)]].
    eapply (xpres_trans H); [exact XP|].
    eapply (v32c_xpres_mixed sk pid' A (4 * cap') spz Xk mk mk mk' W RH NI ltac:(lia) MU WM).
    eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold v32c_wk in Hw. cbn [fst snd] in *.
    destruct Hw as [Hw|[Hw|[Hw|(Hw & _)]]].
    - right; right; left. lia.
    - left. exact Hw.
    - right; left. exact Hw.
    - right; right; right. exact Hw.
  Qed.

  Lemma v32c_vec_facts :
    fldA m v 8 b /\ fldA m (v + 8) 8 (b + 4 * cap) /\ fldA m (v + 16) 8 (b + 4 * cap)
    /\ (forall i, 0 <= i < cap -> 0 <= Znth i xs < 2 ^ 32 /\ fldA m (b + 4 * i) 4 (Znth i xs))
    /\ 0 <= cap /\ ((b = 0 /\ cap = 0) \/ (1 <= cap /\ In (pid, b, 4 * cap) LB /\ ablock_range H b (4 * cap))).
  Proof.
    destruct VEC as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2 & FE). rewrite XSL in F1, FE, Hlen.
    split; [exact F0|]. split; [exact F1|]. split; [exact F2|]. split; [exact FE|]. split; [lia|].
    destruct OLD as [[-> ->]|(Hc & HIn)]; [left; split; reflexivity|].
    right. split; [lia|]. split; [exact HIn|]. exact (ah_blocks H HH _ _ _ _ RH0 HIn).
  Qed.

  Lemma v32c_s_end : forall (msF1 : machine_state) (mo1 : Model) (s1' : as_St H) (m1 : mem) (R1 : bvmap 5 word) (pid' : bptr) (A : Z) (e1 : word),
    as_VIS H s1' msF1 = MS R1 F (Z_to_bv 64 (E0 + 484)) fc None m1 (seg_rom asegs) -> rfull R1 ->
    v32c_B11at R1 m1 A -> getr R1 3 = gp -> getr R1 4 = tp ->
    getr R1 24 = s8 -> getr R1 25 = s9 -> getr R1 26 = s10 -> getr R1 27 = s11 ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    rw_cells asegs m1 (spz - 80) FRAME ->
    mem_inv asegs m1 -> stk asegs m1 lo spz -> rw_cells asegs m1 (errno_addr tp) [C4 e1] -> as_rauxv_ok H m1 B ->
    xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap)) m m1 ->
    ablock_range H A (4 * cap') -> as_RHEAP H s1' (v4_newLB H LB b pid pid' A (4 * cap')) m1 ->
    vec32A (v4_newLB H LB b pid pid' A (4 * cap')) m1 v A (xs ++ [x]) cap' ->
    SHAD m1 A (cc_gen (4 * cap') (4 * (cap + 1))) -> addressable m1 v 24 ->
    wr_at asegs m1 v 24 -> lb_own (v4_newLB H LB b pid pid' A (4 * cap')) m1 ->
    as_RFS H LF m1 -> ACONST m1 -> stack0 m1 lo shi ->
    as_AL H s1' >= as_AL H s - (as_Cm H (4 * cap') + as_Cf H (4 * cap)) ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 s1' m1 R1 pid' A e1 VIS1 HF1 B11P G3 G4 G24 G25 G26 G27 KR1 MP1 FR1 MI1 ST1 ERR1 RA1 XP1 ABR RH1 VEC1 SH1
      ADV1 WV1 OW1 RF1 AC1 S01 AL1.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & B11 & RET).
    destruct (B11 R1 F fc m1 A (spz - 112) v cap (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
                (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) (bv_unsigned s6) (bv_unsigned s7) B11P)
      as (R' & M' & Hms & EM & K1 & K2 & K8 & K9 & K10 & K18 & K19 & K20 & K21 & K22 & K23 & KK).
    subst M'.
    assert (HF' : rfull R') by exact (msteps_full asegs _ _ Hms HF1).
    assert (K3 : getr R' 3 = gp) by (rewrite (KK 3%bv ltac:(inb)); exact G3).
    assert (K4 : getr R' 4 = tp) by (rewrite (KK 4%bv ltac:(inb)); exact G4).
    assert (K24 : getr R' 24 = s8) by (rewrite (KK 24%bv ltac:(inb)); exact G24).
    assert (K25 : getr R' 25 = s9) by (rewrite (KK 25%bv ltac:(inb)); exact G25).
    assert (K26 : getr R' 26 = s10) by (rewrite (KK 26%bv ltac:(inb)); exact G26).
    assert (K27 : getr R' 27 = s11) by (rewrite (KK 27%bv ltac:(inb)); exact G27).
    eapply (sr_evt H HH) with
      (P := fun ms => ms = MS (mkR ra sp gp tp (getr R' 5) (getr R' 6) (getr R' 7) s0 s1 (Z_to_bv 64 (A + 4 * (cap + 1)))
                                   (getr R' 11) (getr R' 12) (getr R' 13) (getr R' 14) (getr R' 15) (getr R' 16) (getr R' 17)
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (getr R' 28) (getr R' 29) (getr R' 30) (getr R' 31))
                              F (ret_pc ra) fc None m1 (seg_rom asegs));
      [exact KR1 | exact VIS1 | |].
    { eapply evt_of_msteps; [exact Hms|]. rewrite (rfull_eq R' HF'). apply RET.
      rewrite K1, K2, K3, K4, K8, K9, K10, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27. unfold wz.
      rewrite !Z_to_bv_bv_unsigned. replace (spz - 112 + 112) with spz by lia.
      replace (A + 4 * cap + 4) with (A + 4 * (cap + 1)) by lia. rewrite <- spz_sp32. reflexivity. }
    intros msF2 mo2 KR2 MP2 HP. cbv beta in HP.
    exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14), (getr R' 15), (getr R' 16),
      (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), m1, e1, s1', pid', A.
    cbn [cfg_ms cfg_model]. rewrite SPZ.
    split; [exact HP|]. split; [exact KR2|]. split; [eapply (ah_mpres_trans H HH); eassumption|].
    split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact RA1|]. split; [exact XP1|].
    split; [exact ABR|]. split; [exact RH1|]. split; [exact VEC1|]. split; [exact SH1|]. split; [exact ADV1|].
    split; [exact WV1|]. split; [exact OW1|].
    split; [exact RF1|]. split; [exact AC1|]. split; [exact S01|]. exact AL1.
  Qed.
  Lemma v32c_capb : 0 <= cap -> cap + 1 <= cap' /\ 4 * cap' <= 2 ^ 26.
  Proof.
    intros C0. split; [|exact GROW]. unfold cap', v4_newcap.
    destruct (Z_le_gt_dec cap 1) as [L|L]; [rewrite vgrow_le1 by lia | rewrite vgrow_ge2 by lia]; lia.
  Qed.

  Lemma v32c_E0_even : forall k, 0 <= k < 0x1000 -> k mod 4 = 0 -> 0 <= E0 + k < 2 ^ 64 /\ (E0 + k) mod 2 = 0.
  Proof.
    intros k Hk H4. destruct E0R as [R0 R4]. split; [unfold E0; lia|]. unfold E0. exact (v4_mod4_even _ _ R4 H4).
  Qed.

  Lemma v32c_old_facts : 0 < cap ->
    In (pid, b, 4 * cap) LB /\ ablock_range H b (4 * cap) /\ (v + 24 <= b \/ b + 4 * cap <= v) /\ b <> 0.
  Proof.
    intros Hc. pose proof v32c_vec_facts as (_ & _ & _ & _ & _ & OB).
    destruct OB as [[_ C]|(_ & HIn & ABR)]; [lia|].
    destruct VEC as (_ & _ & _ & _ & Hb & _). destruct Hb as [[_ C]|(_ & _ & _ & _ & _ & D)]; [lia|].
    split; [exact HIn|]. split; [exact ABR|]. split; [exact D|]. destruct ABR as (B0 & _). lia.
  Qed.

  Lemma v32c_blk_shad : forall sk mk LBx p A n, as_RHEAP H sk LBx mk -> In (p, A, n) LBx ->
    exists sbs, SHAD mk A sbs /\ Z.of_nat (length sbs) = nsh n.
  Proof.
    intros sk mk LBx p A n RH HIn.
    pose proof (ah_blk_shvis H HH _ _ _ _ _ _ RH HIn) as SV. unfold shvis in SV.
    pose proof (ah_blocks H HH _ _ _ _ RH HIn) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    cbn [blk_addr blk_size fst snd] in B0, B16, Bn, BI, BC, BF, BAPP.
    pose proof (v4_mod16_8 A B16) as B8.
    destruct (v4_sh_hull A n ltac:(lia) B8 Bn) as [HL1 HL2].
    assert (NS : 0 <= nsh n) by (unfold nsh; apply Z.div_pos; lia).
    destruct (stk_split asegs mk _ (sh A) _ SV ltac:(lia)) as [_ SV2].
    destruct (stk_split asegs mk _ (sh A + nsh n) _ SV2 ltac:(lia)) as [SV3 _].
    destruct (stk_carve asegs mk (sh A) (sh A + nsh n) (Z.to_nat (nsh n)) SV3 ltac:(lia)) as [_ (junk & RC)].
    rewrite Z2Nat.id in RC by lia. replace (sh A + nsh n - nsh n) with (sh A) in RC by lia.
    exists junk. split.
    - eapply SHAD_of_rw_cells; [lia | exact B8 | exact RC].
    - destruct RC as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _]. rewrite Hl, Z2Nat.id by lia. reflexivity.
  Qed.

  Lemma v32c_hdr_fresh : forall sk mk pid' A n,
    as_RHEAP H sk ((pid', A, n) :: LB) mk -> ~ In pid' (map blk_id LB) -> 0 < n -> v + 24 <= A \/ A + n <= v.
  Proof.
    intros sk mk pid' A n RH NI Hn.
    destruct OBJ as (CL & _).
    pose proof (ah_blocks H HH _ _ _ (pid', A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    destruct LOR as [LO1 LO2]. unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    assert (SPC : aceil <= spz) by lia.
    destruct (Z_le_gt_dec (v + 24) A) as [D|D]; [left; exact D|].
    destruct (Z_le_gt_dec (A + n) v) as [D'|D']; [right; exact D'|].
    exfalso.
    assert (Ha : v <= Z.max v A < v + 24) by lia.
    pose proof (aclient_range_addr H LB spz v 24 (Z.max v A) CL Ha) as Hc.
    destruct (v32c_cls sk LB pid' A n spz mk (Z.max v A) RH NI SPC Hc) as [C|(C1 & C2 & C3)]; [lia|].
    apply C2. lia.
  Qed.

  Lemma v32c_band_of_aapp : forall A n, aapp A n -> (0 <= A /\ A + n <= 0x7fff7000) \/ 0x10007fff8000 <= A.
  Proof. intros A n HA. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in HA. destruct HA; [left|right]; lia. Qed.

  Lemma v32c_xc_hdr : 0 < cap -> xclient_range H LB spz (v4_oldx b (4 * cap)) v 24.
  Proof.
    intros Hc. destruct (v32c_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    destruct OBJ as (CL & _).
    split; [exact CL|].
    unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
    assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
    pose proof (v4_app_sh v 24 b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) VB) as D2.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.

  Lemma v32c_xc_hdrsh : 0 < cap -> xclient_range H LB spz (v4_oldx b (4 * cap)) (sh v) 3.
  Proof.
    intros Hc. destruct (v32c_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    destruct OBJ as (_ & CLS & _). rewrite v4_nsh24 in CLS.
    split; [exact CLS|].
    unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
    assert (VB : v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    pose proof (v4_app_sh b (4 * cap) v 24 ltac:(lia) ltac:(lia) VB (v32c_band_of_aapp _ _ BAPP)) as D1. rewrite v4_nsh24 in D1.
    pose proof (v4_sh_apart v 24 b (4 * cap) ltac:(lia) ltac:(lia) V8 (v4_mod16_8 b B16) ltac:(lia) ltac:(lia) D) as D2.
    rewrite v4_nsh24 in D2.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.

  Definition v32c_X0 : list (Z * Z) := if b =? 0 then [] else [(sh b, sh b + nsh (4 * cap))].
  Definition v32c_X1 : list (Z * Z) := (v, v + 24) :: v32c_X0.

  Lemma v32c_xc_old : 0 < cap -> xclient_range H LB spz v32c_X0 b (4 * cap).
  Proof.
    intros Hc. destruct (v32c_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    split; [eapply (aclient_range_block H); [exact HIn | lia | lia]|].
    unfold v32c_X0. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
    pose proof (v4_app_sh b (4 * cap) b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (v32c_band_of_aapp _ _ BAPP)) as D2.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.

  Lemma v32c_X1_sub : forall a, rin_ivs v32c_X1 a -> rin_ivs ((v, v + 24) :: v4_oldx b (4 * cap)) a.
  Proof.
    intros a Ha. unfold v32c_X1, v32c_X0, v4_oldx in Ha |- *. destruct (b =? 0); cbn [rin_ivs fst snd] in Ha |- *; tauto.
  Qed.

  Lemma v32c_dj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
  Proof.
    induction W as [|[l h] W IH]; intros a n a' n' D H1 H2; [exact I|]. cbn in D |- *. destruct D as [D1 D2].
    split; [lia | exact (IH a n a' n' D2 H1 H2)].
  Qed.

  Lemma v32c_wr_sub : forall mk a n a' n', wr_at asegs mk a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs mk a' n'.
  Proof.
    intros mk a n a' n' (W0 & W1 & W) H1 H2 H3. split; [lia|]. split; [lia|].
    intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
  Qed.

  Lemma v32c_CB0 : forall mk a, 0 <= a <= 2 ^ 64 -> rw_cells asegs mk a [CB 0 []].
  Proof.
    intros mk a Ha. split; [split|].
    - cbn. split; [reflexivity | exact I].
    - cbn [cells_bytes cbytes app]. apply bytes_at_nil. lia.
    - cbn [cells_size csize Nat.add Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia.
  Qed.

  Lemma v32c_shvis0 : forall mk, shvis mk 0 0.
  Proof.
    intros mk. unfold shvis. change (sh (hull_lo 0)) with 2147450880. change (sh (hull_hi 0)) with 2147450880.
    split; [lia|]. split; [lia|]. intros a Ha. lia.
  Qed.

  Lemma v32c_shk4 : forall mk A, addressable mk A 4 -> LbB_Kit.shk mk A 4.
  Proof.
    intros mk A [_ SH]. pose proof SH as (SA0 & _).
    destruct (shk_of_SHAD mk A (shadow_of 4) A SH ltac:(change (Z.of_nat (length (shadow_of 4))) with 1; lia)) as (bb & Hb & K).
    rewrite Z.sub_diag in Hb. change (nth_error (shadow_of 4) (Z.to_nat (0 / 8))) with (Some (b8 4)) in Hb. injection Hb as <-. exact K.
  Qed.

  Lemma v32c_acl_sub : forall LBx SP A n A' n', aclient_range H LBx SP A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
    aclient_range H LBx SP A' n'.
  Proof.
    intros LBx SP A n A' n' K H1 H2 H3. unfold aclient_range in *.
    destruct K as [K|[K|[(bb & Hb & K1 & K2)|[(bb & Hb & K1 & K2)|[K|[K|K]]]]]].
    - left. lia.
    - right; left. intros a Ha. apply K. lia.
    - right; right; left. exists bb. split; [exact Hb | lia].
    - right; right; right; left. exists bb. split; [exact Hb | lia].
    - right; right; right; right; left. lia.
    - right; right; right; right; right; left. lia.
    - right; right; right; right; right; right. lia.
  Qed.

  Lemma v32c_xcl_sub : forall X A n A' n', xclient_range H LB spz X A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
    xclient_range H LB spz X A' n'.
  Proof.
    intros X A n A' n' [K KX] H1 H2 H3. split; [exact (v32c_acl_sub _ _ _ _ _ _ K H1 H2 H3)|].
    eapply Forall_impl; [|exact KX]. intros [l h] Hlh. cbn [fst snd] in *. lia.
  Qed.

  Lemma v32c_fld_xpres : forall X mk a k z, xpres H LB spz X m mk -> xclient_range H LB spz X a (Z.of_nat k) ->
    0 <= a -> a + Z.of_nat k < 2 ^ 64 -> fldA m a k z -> fldA mk a k z.
  Proof.
    intros X mk a k z XP XC H0 H1 Hf. unfold fldA in *. eapply fld_agree; [exact H0 | exact H1 | exact Hf |].
    intros a' Ha'. hnf in Ha'.
    destruct (XP a' ltac:(lia) (xclient_range_addr H LB spz X a (Z.of_nat k) a' XC Ha')) as [E _]. exact E.
  Qed.

  Lemma v32c_SHAD_xpres : forall X mk A' sbs, xpres H LB spz X m mk -> SHAD m A' sbs ->
    xclient_range H LB spz X (sh A') (Z.of_nat (length sbs)) -> SHAD mk A' sbs.
  Proof.
    intros X mk A' sbs XP (S0 & S8 & [UB UW]) XC. split; [exact S0|]. split; [exact S8|].
    split; [eapply (xpres_bytes_at H); [exact XP | exact UB | exact XC] | eapply (xpres_wr_at H); [exact XP | exact UW | exact XC]].
  Qed.

  Lemma apres_of_xpres_nil32 : forall mk, xpres H LB spz [] m mk -> apres H LB spz m mk.
  Proof. intros mk XP a Ha Hc. apply XP; [exact Ha|]. split; [exact Hc | intros K; exact K]. Qed.

  Lemma v32c_mid_weaken : forall sk mk pid' A X X', v32c_mid sk mk pid' A X -> (forall a, rin_ivs X a -> rin_ivs X' a) ->
    v32c_mid sk mk pid' A X'.
  Proof.
    intros sk mk pid' A X X' (MI & ST & ERR & RA & AC & RF & S0 & RH & FR & XP & AL & OW) HX.
    repeat (split; [assumption|]). split; [eapply (xpres_weaken H); [exact XP | lia | intros bb Hb; exact Hb | exact HX]|].
    split; assumption.
  Qed.

  Lemma v32c_wk_hdr : forall A Xk, (forall a, v <= a < v + 24 -> rin_ivs Xk a) -> v32c_wk A Xk (v, v + 24).
  Proof.
    intros A Xk HX. right; right; right. cbn [fst snd].
    destruct OBJ as (_ & _ & WO & FW & CO & SD).
    pose proof LOR as [LO1 LO2]. unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    assert (SHC : 0x7fff7000 < sh aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    split; [exact HX|]. split; [exact WO|]. split; [exact FW|]. split; [exact CO|].
    split; [unfold stack0_ok; cbn [fst snd]; destruct VBAND; [right | left]; unfold AHI_LO; lia|].
    split; [lia|]. right. unfold ATP. destruct VBAND; lia.
  Qed.

  Lemma v32c_wk_oldsh : 0 < cap -> forall A Xk, (forall a, sh b <= a < sh b + nsh (4 * cap) -> rin_ivs Xk a) ->
    v32c_wk A Xk (sh b, sh b + nsh (4 * cap)).
  Proof.
    intros Hc A Xk HX. destruct (v32c_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    pose proof (v4_app_sh (as_FSB H) AFS_SIZE b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (v32c_band_of_aapp _ _ FS4)) as DF.
    pose proof (sh_nsh_high b (4 * cap) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHH. unfold AHI_LO in SHH.
    assert (SHL : 0x7fff8000 <= sh b) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    right; right; right. cbn [fst snd].
    split; [exact HX|].
    split; [right; right; right; left; exists (pid, b, 4 * cap); split; [exact HIn | cbn [blk_addr blk_size fst snd]; lia]|].
    split; [left; cbn [fst snd]; split; [lia | unfold ATLS_PRIV_HI, ATP; lia]|].
    split; [apply aconst_ok_high; [apply sh_mono; unfold AIMG_TOP in *; lia | right; left; lia]|].
    split; [apply stack0_ok_sh; lia|].
    split; [lia|]. right. unfold ATP. lia.
  Qed.

  Lemma v32c_hdr_X0 : forall mk, xpres H LB spz v32c_X0 m mk ->
    fldA mk v 8 b /\ fldA mk (v + 8) 8 (b + 4 * cap) /\ fldA mk (v + 16) 8 (b + 4 * cap) /\ addressable mk v 24
    /\ wr_at asegs mk v 24.
  Proof.
    intros mk XP.
    pose proof v32c_vec_facts as (F0 & F1 & F2 & _ & C0 & OB).
    assert (VB2 : 0 <= v /\ v + 24 < 2 ^ 64) by (destruct VBAND; lia).
    assert (XCH : xclient_range H LB spz v32c_X0 v 24).
    { destruct OBJ as (CL & _). split; [exact CL|]. unfold v32c_X0. destruct (Z.eqb_spec b 0) as [E|NE]; [apply Forall_nil|].
      destruct OB as [[E _]|(Hc & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [contradiction|].
      pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
      assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
      pose proof (v4_app_sh v 24 b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) VB) as D.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    assert (XCS : xclient_range H LB spz v32c_X0 (sh v) 3).
    { destruct OBJ as (_ & CLS & _). rewrite v4_nsh24 in CLS. split; [exact CLS|]. unfold v32c_X0.
      destruct (Z.eqb_spec b 0) as [E|NE]; [apply Forall_nil|].
      destruct OB as [[E _]|(Hc & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [contradiction|].
      assert (D : v + 24 <= b \/ b + 4 * cap <= v) by (destruct (v32c_old_facts ltac:(lia)) as (_ & _ & D & _); exact D).
      pose proof (v4_sh_apart v 24 b (4 * cap) ltac:(lia) ltac:(lia) V8 (v4_mod16_8 b B16) ltac:(lia) ltac:(lia) D) as D2.
      rewrite v4_nsh24 in D2.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    split; [eapply v32c_fld_xpres; [exact XP | eapply v32c_xcl_sub; [exact XCH | lia | cbn; lia | lia] | lia | cbn; lia | exact F0]|].
    split; [eapply v32c_fld_xpres; [exact XP | eapply v32c_xcl_sub; [exact XCH | lia | cbn; lia | lia] | lia | cbn; lia | exact F1]|].
    split; [eapply v32c_fld_xpres; [exact XP | eapply v32c_xcl_sub; [exact XCH | lia | cbn; lia | lia] | lia | cbn; lia | exact F2]|].
    split.
    - destruct ADV0 as [AN SV]. split; [exact AN|]. eapply v32c_SHAD_xpres; [exact XP | exact SV |].
      rewrite shadow_of_length by lia. rewrite v4_nsh24. exact XCS.
    - eapply (xpres_wr_at H); [exact XP | exact VWR | exact XCH].
  Qed.

  Let HANN : annotate_gen_stmt := annotate_gen_ok.

  Lemma v32c_s9 : forall (msF8 : machine_state) (mo8 : Model) (sk8 : as_St H) (m8 : mem) (R8 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk8 msF8 = MS R8 F (Z_to_bv 64 958128) fc None m8 (seg_rom asegs) -> rfull R8 ->
    v32c_B9at R8 m8 A -> getr R8 3 = gp -> getr R8 4 = tp ->
    getr R8 24 = s8 -> getr R8 25 = s9 -> getr R8 26 = s10 -> getr R8 27 = s11 ->
    as_AKREL H sk8 (mkCfg msF8 mo8) -> as_MPRES H mo mo8 ->
    v32c_mid sk8 m8 pid' A v32c_X1 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m8 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))] ->
    bytes_at asegs m8 A (le4s xs) -> rw_cells asegs m8 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m8 A (cc_gen (4 * cap') (4 * (cap + 1))) -> addressable m8 v 24 ->
    as_SR H Q (mkCfg msF8 mo8).
  Proof.
    intros msF8 mo8 sk8 m8 R8 pid' A VIS8 HF8 B9P G3 G4 G24 G25 G26 G27 KR8 MP8 MID ABR NI HDR BUF XC SHA ADV8.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & _ & B9D & B9N & _ & _).
    pose proof MID as (MI8 & ST8 & (e8 & ERR8) & RA8 & AC8 & RF8 & S08 & RH8 & FR8 & XP8 & AL8 & OW8).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v32c_vec_facts as (F0 & F1 & F2 & FE & C0 & OB).
    destruct (v32c_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB : 0x6e8000 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    pose proof B9P as P. unfold v32c_B9at, v32_B9_pre in P.
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                   & PSP & PA & PV & PC & PN & PB & _ & _ & _ & _ & _ & PAN & _ & _ & _ & _ & PCN & _ & _).
    assert (FL : forall mk (w : word) k a, rw_cells asegs mk (spz - 80) FRAME -> cell_at FRAME k = Some (C8 w) ->
              a = spz - 80 + Z.of_nat k -> fldA mk a 8 (bv_unsigned w)).
    { intros mk w k a FR CA Ea. subst a. unfold fldA, fld. rewrite Z_to_bv_bv_unsigned. rewrite <- rdn_of_ov.
      exact (rw_cells_read asegs mk _ _ k _ FR CA). }
    assert (B11F : forall R mk, getr R 2 = wz (spz - 112) -> getr R 8 = wz (A + 4 * cap + 4) ->
              rw_cells asegs mk (spz - 80) FRAME -> v32c_B11at R mk A).
    { intros R mk R2 R8' FR. unfold v32c_B11at, v32_B11_pre.
      split; [exact R2|]. split; [exact R8'|].
      split; [eapply (FL mk ra 72%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s0 64%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s1 56%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s2 48%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s3 40%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s4 32%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s5 24%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s6 16%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s7 8%nat); [exact FR | reflexivity | lia]|].
      lia. }
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47 /\ (b = 0 -> cap = 0) /\ (b <> 0 -> 16 <= b)).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia|].
      split; [lia|]. split; [lia|]. split; [intros E; lia|]. intros _. exact (v4_mod16_16le b O0 O16). }
    destruct OB0 as (OB1 & OB2 & OB3 & OB4).
    assert (HNEW : v + 24 <= A \/ A + 4 * cap' <= v) by (eapply v32c_hdr_fresh; [exact RH8 | exact NI | lia]).
    assert (VEC9 : forall m9 LB9, rw_cells asegs m9 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))] ->
              bytes_at asegs m9 A (le4s xs) -> rw_cells asegs m9 (A + 4 * cap) [C4 (Z_to_bv 64 x)] -> In (A, 4 * cap') (lbl LB9) ->
              vec32A LB9 m9 v A (xs ++ [x]) cap').
    { intros m9 LB9 H1 H2 H3 H4. apply v4_vec32_new; [rewrite XSL; exact H1 | exact H2 | rewrite XSL; exact H3 | lia
        | intros i Hi; rewrite XSL in Hi; exact (proj1 (FE i Hi)) | lia | exact A16 | rewrite XSL; lia | lia | exact H4 | exact HNEW
        | unfold AIMG_TOP; lia | lia]. }
    destruct (Z.eq_dec b 0) as [Z0|NZ].
    -
      destruct (B9N R8 F fc m8 A (spz - 112) v src cap b cap' (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
                  (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) (bv_unsigned s6) (bv_unsigned s7) B9P Z0)
        as (R9 & M9 & Hms & EM9 & _ & K2 & K8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & KK).
      subst M9.
      pose proof (msteps_full asegs _ _ Hms HF8) as HF9. cbn [ms_regs] in HF9.
      eapply (sr_blk H HH); [exact KR8 | exact VIS8 | exact HF8 | exact Hms |].
      intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R9 HF9) in VIS1.
      eapply (v32c_s_end msF1 mo1 sk8 m8 R9 pid' A e8 VIS1 HF9).
      + exact (B11F R9 m8 K2 K8 FR8).
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 24%bv ltac:(inb)). exact G24.
      + rewrite (KK 25%bv ltac:(inb)). exact G25.
      + rewrite (KK 26%bv ltac:(inb)). exact G26.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR1.
      + eapply (ah_mpres_trans H HH); [exact MP8 | exact MP1].
      + exact FR8.
      + exact MI8.
      + exact ST8.
      + exact ERR8.
      + exact RA8.
      + eapply (xpres_weaken H); [exact XP8 | lia | intros bb Hb; exact Hb | exact v32c_X1_sub].
      + exact ABR.
      + unfold v4_newLB. rewrite Z0. cbn [Z.eqb]. exact RH8.
      + apply VEC9; [exact HDR | exact BUF | exact XC | ]. unfold v4_newLB. apply (lbl_in _ pid'). left. reflexivity.
      + exact SHA.
      + exact ADV8.
      + exact (proj2 HDR).
      + unfold v4_newLB. rewrite Z0. cbn [Z.eqb]. exact OW8.
      + exact RF8.
      + exact AC8.
      + exact S08.
      + assert (CF0 : 0 <= as_Cf H (4 * cap)) by (pose proof (ah_costs H HH) as (_ & _ & CF & _); apply CF; lia). lia.
    -
      assert (Hc : 0 < cap) by (destruct OB as [[E1 _]|(Hc & _)]; [contradiction | lia]).
      destruct (v32c_old_facts Hc) as (HIn & (O0 & O16 & On & OI & OC & OF & OAP) & OD & _).
      destruct (B9D R8 F fc m8 A (spz - 112) v src cap b cap' (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
                  (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) (bv_unsigned s6) (bv_unsigned s7) B9P NZ)
        as (R9 & M9 & Hms & EM9 & K1 & K2w & K8 & _ & K10 & _ & _ & _ & _ & _ & _ & _ & KK).
      subst M9.
      assert (K2 : getr R9 2 = Z_to_bv 64 (spz - 112)) by exact K2w.
      pose proof (msteps_full asegs _ _ Hms HF8) as HF9. cbn [ms_regs] in HF9.
      eapply (sr_blk H HH); [exact KR8 | exact VIS8 | exact HF8 | exact Hms |].
      intros msF9 mo9 KR9 MP9 VIS9.
      assert (K4 : getr R9 4 = tp) by (rewrite (KK 4%bv ltac:(inb)); exact G4).
      assert (HINx : In (pid, b, 4 * cap) ((pid', A, 4 * cap') :: LB)) by (right; exact HIn).
      destruct (rw_cells_of_own _ m8 (pid, b, 4 * cap) OW8 HINx ltac:(cbn [blk_addr blk_size fst snd]; exact OI) ltac:(cbn [blk_addr blk_size fst snd]; lia)) as (obs & OC8).
      cbn [blk_addr blk_size fst snd] in OC8.
      destruct (v32c_blk_shad sk8 m8 _ pid b (4 * cap) RH8 HINx) as (sbs & SHB & SHL).
      assert (CFB : as_Cf H (4 * cap) <= as_AL H sk8) by (pose proof CM as CM'; change (v4_newcap cap) with cap' in CM'; lia).
      assert (SP112 : (spz - 112) mod 16 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
      destruct (v32c_E0_even 484 ltac:(lia) eq_refl) as [ER1 ER2].
      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (p := pid) (A := b) (n := 4 * cap) (LB := (pid', A, 4 * cap') :: LB) (lo := lo) (B := B)
          (errv := e8) (CH := []) (bs := obs) (sbs := sbs);
          [ exact VIS9 | exact RH8 | exact KR9 | exact HINx | exact CFB | exact OC8 | exact SHB | exact SHL
          | exact RA8 | rewrite K2, u64_of_Z by lia; lia
          | rewrite K2, u64_of_Z by lia; exact (proj1 (stk_split asegs m8 lo (spz - 112) spz ST8 ltac:(lia)))
          | exact LO1 | rewrite K2, u64_of_Z by lia; unfold AFREE_STACK; lia
          | rewrite K4; exact ERR8 | exact MI8 | rewrite K4; exact TPV | rewrite K2, u64_of_Z by lia; exact SP112 | exact AC8
          | rewrite K8; unfold wz; rewrite u64_of_Z by lia; apply (ah_chain_nil H HH); left; lia
          | rewrite K1; cbn [map]; unfold wz; rewrite u64_of_Z by lia; rewrite <- DRA; exact TRO
          | exact K10 ]. }
      intros c2 POST. destruct c2 as [msF2 mo2].
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m9 & s9'
                        & VIS2 & KR2 & MP2 & MI9 & ST9 & ERR9 & RA9 & AP9 & RH9 & AC9 & AL9).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite K1 in VIS2. unfold wz in VIS2. rewrite (ret_pc_even (v4_entry c + 484) ER1 ER2) in VIS2.
      rewrite K2, u64_of_Z in ST9, AP9 by lia. rewrite K4 in ERR9.

      assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 4 * cap); split; [reflexivity | exact HIn]).
      pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
      assert (RMx : as_lb_remove H pid ((pid', A, 4 * cap') :: LB) = (pid', A, 4 * cap') :: as_lb_remove H pid LB).
      { apply L2. cbn [blk_id fst]. exact NEQ. }
      rewrite RMx in AP9, RH9.

      assert (XPF0 : xpres H LB (spz - 112) (v4_oldx b (4 * cap)) m8 m9).
      { eapply (xpres_of_apres_rm H HH sk8 LB ((pid', A, 4 * cap') :: LB) (spz - 112) _ m8 m8 m9 pid b (4 * cap) RH8 HINx);
          [intros bb Hb; right; exact Hb | rewrite RMx; exact AP9 | |].
        - intros a Ha. unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. left. cbn [fst snd]. lia.
        - intros a Ha. unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. right. left. cbn [fst snd]. lia. }
      assert (XPF : xpres H LB spz (v4_oldx b (4 * cap)) m8 m9)
        by (eapply (xpres_weaken H); [exact XPF0 | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]).
      assert (HDR9 : rw_cells asegs m9 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))]).
      { eapply (xpres_rw_cells H); [exact XPF | exact HDR | exact (v32c_xc_hdr Hc)]. }
      assert (FR9 : rw_cells asegs m9 (spz - 80) FRAME) by (eapply (apres_rw_cells H); [exact AP9 | exact FR8 | left; lia]).
      assert (INA : In (pid', A, 4 * cap') ((pid', A, 4 * cap') :: as_lb_remove H pid LB)) by (left; reflexivity).
      eapply (v32c_s_end msF2 mo2 s9' m9 _ pid' A e8 VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
      + apply B11F; [exact K2w | exact K8 | exact FR9].
      + exact (eq_trans (KK 3%bv ltac:(inb)) G3).
      + exact K4.
      + exact (eq_trans (KK 24%bv ltac:(inb)) G24).
      + exact (eq_trans (KK 25%bv ltac:(inb)) G25).
      + exact (eq_trans (KK 26%bv ltac:(inb)) G26).
      + exact (eq_trans (KK 27%bv ltac:(inb)) G27).
      + exact KR2.
      + eapply (ah_mpres_trans H HH); [exact MP8 | eapply (ah_mpres_trans H HH); [exact MP9 | exact MP2]].
      + exact FR9.
      + exact MI9.
      + eapply (stk_merge asegs); [exact ST9 | | lia].
        eapply (apres_stk H); [exact AP9 | exact (proj2 (stk_split asegs m8 lo (spz - 112) spz ST8 ltac:(lia))) | lia].
      + exact ERR9.
      + exact RA9.
      + eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP8 | lia | intros bb Hb; exact Hb | exact v32c_X1_sub] |].
        eapply (xpres_weaken H); [exact XPF | lia | intros bb Hb; exact Hb | intros a Ha; right; exact Ha].
      + exact ABR.
      + unfold v4_newLB. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. exact RH9.
      + apply VEC9; [exact HDR9 | | |].
        * eapply (apres_bytes_at H); [exact AP9 | exact BUF |]. rewrite le4s_length. eapply (aclient_range_block H); [exact INA | lia |].
          unfold Zlen in XSL. lia.
        * eapply (apres_rw_cells H); [exact AP9 | exact XC |]. cbn [cells_size csize]. eapply (aclient_range_block H); [exact INA | lia | lia].
        * unfold v4_newLB. apply (lbl_in _ pid'). left. reflexivity.
      + eapply (apres_SHAD H); [exact AP9 | exact SHA |]. rewrite cc_gen_length by lia. eapply (aclient_range_block_sh H). exact INA.
      + destruct ADV8 as [AN (SA0 & SA8 & [UB UW])]. split; [exact AN|]. split; [exact SA0|]. split; [exact SA8|].
        assert (XCS : xclient_range H LB spz (v4_oldx b (4 * cap)) (sh v) (Z.of_nat (length (shadow_of 24)))).
        { rewrite shadow_of_length by lia. rewrite v4_nsh24. exact (v32c_xc_hdrsh Hc). }
        split; [eapply (xpres_bytes_at H); [exact XPF | exact UB | exact XCS] | eapply (xpres_wr_at H); [exact XPF | exact UW | exact XCS]].
      + exact (proj2 HDR9).
      + unfold v4_newLB. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
        eapply (lb_own_apres H); [| exact AP9 | intros bb Hb; exact Hb].
        eapply lb_own_incl; [| exact OW8]. intros bb [Hb|Hb]; [left; exact Hb | right; exact (L3 _ _ _ Hb)].
      + exact (RFS_via_apres H HH LF _ _ m8 m9 RF8 AP9).
      + exact AC9.
      + eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP9) | exact S08 | apply Forall_nil].
      + lia.
  Qed.

  Lemma v32c_s8 : forall (msF7 : machine_state) (mo7 : Model) (sk7 : as_St H) (m7 : mem) (R7 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk7 msF7 = MS R7 F (Z_to_bv 64 AANNOTATE_CC) fc None m7 (seg_rom asegs) -> rfull R7 ->
    getr R7 1 = Z_to_bv 64 958128 -> getr R7 10 = Z_to_bv 64 A -> getr R7 11 = Z_to_bv 64 (A + 4 * cap') ->
    getr R7 12 = Z_to_bv 64 (A + 4 * cap') -> getr R7 13 = Z_to_bv 64 (A + 4 * cap + 4) ->
    v32c_B9at R7 m7 A -> getr R7 3 = gp -> getr R7 4 = tp ->
    getr R7 24 = s8 -> getr R7 25 = s9 -> getr R7 26 = s10 -> getr R7 27 = s11 ->
    as_AKREL H sk7 (mkCfg msF7 mo7) -> as_MPRES H mo mo7 ->
    v32c_mid sk7 m7 pid' A v32c_X1 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m7 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))] ->
    bytes_at asegs m7 A (le4s xs) -> rw_cells asegs m7 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m7 A (cc_gen (4 * cap') (4 * cap')) -> addressable m7 v 24 ->
    as_SR H Q (mkCfg msF7 mo7).
  Proof.
    intros msF7 mo7 sk7 m7 R7 pid' A VIS7 HF7 G1 G10 G11 G12 G13 B9P G3 G4 G24 G25 G26 G27 KR7 MP7 MID ABR NI HDR BUF XC SHA
      ADV7.
    pose proof MID as (MI7 & ST7 & _ & _ & AC7 & _ & _ & RH7 & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v32c_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (v32c_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
    assert (HNEW : v + 24 <= A \/ A + 4 * cap' <= v) by (eapply v32c_hdr_fresh; [exact RH7 | exact NI | lia]).
    unfold v32c_B9at, v32_B9_pre in B9P.
    destruct B9P as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & FV0 & FV8 & FV16 & FS0 & FS8 & FS16 & FS24 & FS32
                     & FRa & FR0 & FR1 & FR2 & FR3 & FR4 & FR5 & FR6 & FR7 & RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & WS
                     & FE & FW8 & SHV & RG7 & RG8 & RG9 & RG10 & RG11 & RG12 & RG13 & RG14 & RG15).
    rewrite (rfull_eq R7 HF7) in VIS7.
    eapply (ahh_evt_then H HH); [exact KR7 | exact VIS7 | |].
    { eapply HANN with (beg := A) (len := 4 * cap') (oldmid := 4 * cap') (newmid := 4 * cap + 4) (lo := lo).
      - exact G10.
      - exact G11.
      - exact G12.
      - rewrite G13. f_equal. lia.
      - exact (v4_mod16_8 A A16).
      - lia.
      - lia.
      - lia.
      - exact AAP.
      - unfold AAPP_HI; lia.
      - exact SHA.
      - rewrite G2. unfold wz. rewrite u64_of_Z by lia.
        exact (proj1 (stk_split asegs m7 lo (spz - 112 - 16) spz ST7 ltac:(lia))).
      - exact LO1.
      - rewrite G2. unfold wz. rewrite u64_of_Z by lia. unfold AINTRIN_STACK. lia.
      - exact MI7.
      - exact AC7.
      - unfold in_app_mem. destruct (v32c_band_of_aapp _ _ AAP) as [K|K]; [left | right];
          unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia. }
    intros msF8 mo8 KR8 MP8 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m8
                      & VIS8 & MU8 & WM8 & MI8 & ST8 & SH8 & AC8).
    rewrite G2 in MU8, ST8. unfold wz in MU8, ST8. rewrite u64_of_Z in MU8, ST8 by lia. unfold AINTRIN_STACK in MU8.
    rewrite G1 in VIS8. rewrite (ret_pc_even 958128 ltac:(lia) ltac:(reflexivity)) in VIS8.
    assert (W8 : Forall (v32c_wk A v32c_X1) [(sh A, sh A + nsh (4 * cap')); (spz - 112 - 16 - 4096, spz - 112 - 16)]).
    { apply Forall_cons; [right; right; left; cbn [fst snd]; lia|].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (DSV : disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 112 - 16 - 4096, spz - 112 - 16)] v 24).
    { pose proof (v4_app_sh v 24 A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) VB) as D. destruct OBJ as (_ & _ & _ & _ & _ & SD).
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSA : disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 112 - 16 - 4096, spz - 112 - 16)] A (4 * cap')).
    { pose proof (v4_app_sh A (4 * cap') A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) (v32c_band_of_aapp _ _ AAP)) as D.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSS : disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 112 - 16 - 4096, spz - 112 - 16)] (sh v) (nsh 24)).
    { pose proof (v4_sh_apart v 24 A (4 * cap') ltac:(lia) ltac:(lia) V8 (v4_mod16_8 A A16) ltac:(lia) ltac:(lia) HNEW) as D.
      pose proof (sh_nsh_high v 24 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; destruct VBAND; lia)) as D2. unfold AHI_LO in D2.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSP : forall a, spz - 112 - 16 <= a <= spz - 8 ->
                  disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 112 - 16 - 4096, spz - 112 - 16)] a 8).
    { intros a Ha. pose proof (sh_nsh_high A (4 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as D2.
      unfold AHI_LO in D2. cbn. split; [lia | split; [lia | exact I]]. }
    assert (FMU : forall a z, fldA m7 a 8 z ->
                  disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 112 - 16 - 4096, spz - 112 - 16)] a 8 ->
                  0 <= a -> a + 8 < 2 ^ 64 -> fldA m8 a 8 z).
    { intros a z Fa D Ha0 Ha1. unfold fldA in Fa |- *. eapply fld_agree; [exact Ha0 | exact Ha1 | exact Fa |].
      intros y Hy. red in Hy. apply MU8. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia]. }
    assert (ADV8 : addressable m8 v 24) by (eapply addressable_transport; [exact ADV7 | exact MU8 | exact WM8 | exact DSS]).
    eapply (v32c_s9 msF8 mo8 sk7 m8 _ pid' A VIS8 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold v32c_B9at, v32_B9_pre.
      split; [exact G2|]. split; [exact G8|]. split; [exact G9|]. split; [exact G18|]. split; [exact G19|].
      split; [exact G20|]. split; [exact G21|]. split; [exact G22|]. split; [exact G23|].
      split; [eapply FMU; [exact FV0 | eapply v32c_dj_sub; [exact DSV | lia | lia] | lia | lia]|].
      split; [eapply FMU; [exact FV8 | eapply v32c_dj_sub; [exact DSV | lia | lia] | lia | lia]|].
      split; [eapply FMU; [exact FV16 | eapply v32c_dj_sub; [exact DSV | lia | lia] | lia | lia]|].
      split; [eapply FMU; [exact FS0 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS8 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS16 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS24 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS32 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FRa | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR0 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR1 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR2 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR3 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR4 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR5 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR6 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR7 | apply DSP; lia | lia | lia]|].
      split; [exact RG1|]. split; [exact RG2|]. split; [exact RG3|]. split; [exact RG4|]. split; [exact RG5|].
      split; [exact RG6|].
      split; [exact (wr_at_wmono _ _ _ _ WS WM8)|].
      split; [eapply FMU; [exact FE | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FW8 | apply DSP; lia | lia | lia]|].
      split; [eapply sh0_of_addressable; [exact ADV8 | change (8 * (24 / 8)) with 24; lia]|].
      split; [exact RG7|]. split; [exact RG8|]. split; [exact RG9|]. split; [exact RG10|]. split; [exact RG11|].
      split; [exact RG12|]. split; [exact RG13|]. split; [exact RG14|]. exact RG15.
    - exact G3.
    - exact G4.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR8.
    - eapply (ah_mpres_trans H HH); [exact MP7 | exact MP8].
    - eapply v32c_mid_munch; [exact MID | exact ABR | exact NI | exact MU8 | exact WM8 | exact MI8 | exact W8].
    - exact ABR.
    - exact NI.
    - eapply rw_cells_transport; [exact HDR | exact MU8 | exact WM8 | exact DSV].
    - eapply bytes_at_transport; [exact BUF | exact MU8 |].
      eapply v32c_dj_sub; [exact DSA | lia | rewrite le4s_length; unfold Zlen in XSL; lia].
    - eapply rw_cells_transport; [exact XC | exact MU8 | exact WM8 |]. cbn [cells_size csize Nat.add Z.of_nat].
      eapply v32c_dj_sub; [exact DSA | lia | lia].
    - replace (4 * (cap + 1)) with (4 * cap + 4) by lia. exact SH8.
    - exact ADV8.
  Qed.

  Lemma v32c_s7 : forall (msF6 : machine_state) (mo6 : Model) (sk6 : as_St H) (m6 : mem) (R6 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk6 msF6 = MS R6 F (Z_to_bv 64 956436) fc None m6 (seg_rom asegs) -> rfull R6 ->
    v32c_B7at R6 m6 A -> getr R6 3 = gp -> getr R6 4 = tp -> getr R6 25 = s9 -> getr R6 26 = s10 -> getr R6 27 = s11 ->
    as_AKREL H sk6 (mkCfg msF6 mo6) -> as_MPRES H mo mo6 ->
    v32c_mid sk6 m6 pid' A v32c_X0 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    bytes_at asegs m6 A (le4s xs) -> rw_cells asegs m6 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m6 A (cc_gen (4 * cap') (4 * cap')) ->
    as_SR H Q (mkCfg msF6 mo6).
  Proof.
    intros msF6 mo6 sk6 m6 R6 pid' A VIS6 HF6 B7P G3 G4 G25 G26 G27 KR6 MP6 MID ABR NI BUF XC SHA.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & B7 & _).
    pose proof MID as (MI6 & ST6 & _ & _ & _ & _ & _ & RH6 & FR6 & XP6 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v32c_vec_facts as (_ & _ & _ & _ & C0 & OB).
    destruct (v32c_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (HNEW : v + 24 <= A \/ A + 4 * cap' <= v) by (eapply v32c_hdr_fresh; [exact RH6 | exact NI | lia]).
    destruct (v32c_hdr_X0 m6 XP6) as (_ & _ & _ & ADV6 & WV6).
    unfold v32c_B7at in B7P.
    destruct (B7 R6 F fc m6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B7P)
      as (R7 & M7 & Hms & MU7 & WM7 & PW & PH8 & PH9 & P0 & P24 & PV16 & P16 & PV8 & P8 & PV0 & K1 & K2 & K8 & K9 & K10
          & K11 & K12 & K13 & K14 & K15 & K16 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & KK).
    pose proof (msteps_full asegs _ _ Hms HF6) as HF7. cbn [ms_regs] in HF7.
    assert (MI7 : mem_inv asegs M7) by exact (msteps_mem_inv asegs _ _ Hms MI6).
    eapply (sr_blk H HH); [exact KR6 | exact VIS6 | exact HF6 | exact Hms |].
    intros msF7 mo7 KR7 MP7 VIS7. rewrite <- (rfull_eq R7 HF7) in VIS7.
    assert (MID7 : v32c_mid sk6 M7 pid' A v32c_X1).
    { eapply v32c_mid_munch; [eapply v32c_mid_weaken; [exact MID | intros a Ha; right; exact Ha] | exact ABR | exact NI
                             | exact MU7 | exact WM7 | exact MI7 |].
      apply Forall_cons; [left; cbn [fst snd]; lia|].
      apply Forall_cons; [apply v32c_wk_hdr; intros a Ha; left; cbn [fst snd]; lia | apply Forall_nil]. }
    pose proof MID7 as (_ & ST7 & _ & _ & _ & _ & _ & _ & FR7 & _).
    assert (CONS8 : forall mk a w cs, rw_cells asegs mk a (C8 w :: cs) ->
                    rw_cells asegs mk a [C8 w] /\ rw_cells asegs mk (a + 8) cs).
    { intros mk a w cs Hc. change (C8 w :: cs) with ([C8 w] ++ cs) in Hc. apply rw_cells_app in Hc. exact Hc. }
    assert (JOIN8 : forall mk a w cs, rw_cells asegs mk a [C8 w] -> rw_cells asegs mk (a + 8) cs ->
                    rw_cells asegs mk a (C8 w :: cs)).
    { intros mk a w cs H1 H2. change (C8 w :: cs) with ([C8 w] ++ cs). apply rw_cells_app. split; [exact H1 | exact H2]. }
    assert (FW : forall mk a a' (w : word), rw_cells asegs mk a [C8 w] -> a' = a -> 0 <= a -> fldA mk a' 8 (bv_unsigned w)).
    { intros mk a a' w Hc -> Ha. apply fld_of_rw_cells8; [rewrite Z_to_bv_bv_unsigned; exact Hc | exact Ha]. }
    assert (C8F : forall mk a a' z z', fldA mk a' 8 z' -> a = a' -> z = z' -> wr_at asegs mk a 8 ->
                  rw_cells asegs mk a [C8 (Z_to_bv 64 z)]).
    { intros mk a a' z z' HF -> -> HW. pose proof HW as (HW0 & HW1 & _). split; [|exact HW].
      split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply bytes_at_of_rdn; [lia | rewrite length_le8; lia | rewrite length_le8; exact HF]. }
    unfold FRAME in FR7. cbn [map] in FR7.
    destruct (CONS8 _ _ _ _ FR7) as (FVv & FR7a). destruct (CONS8 _ _ _ _ FR7a) as (F7 & FR7b).
    destruct (CONS8 _ _ _ _ FR7b) as (F6 & FR7c). destruct (CONS8 _ _ _ _ FR7c) as (F5 & FR7d).
    destruct (CONS8 _ _ _ _ FR7d) as (F4 & FR7e). destruct (CONS8 _ _ _ _ FR7e) as (F3 & FR7f).
    destruct (CONS8 _ _ _ _ FR7f) as (F2 & FR7g). destruct (CONS8 _ _ _ _ FR7g) as (F1 & FR7h).
    destruct (CONS8 _ _ _ _ FR7h) as (F0 & Fra).
    assert (ADV7 : addressable M7 v 24).
    { eapply addressable_transport; [exact ADV6 | exact MU7 | exact WM7 |].
      pose proof (v4_app_sh v 24 v 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VBAND; [left|right]; lia)) as D.
      pose proof (v4_app_sh (spz - 112 - 24) 56 v 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(right; lia)) as D2.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (WV7 : wr_at asegs M7 v 24) by exact (wr_at_wmono _ _ _ _ WV6 WM7).
    assert (B9P : v32c_B9at R7 M7 A).
    { unfold v32c_B9at, v32_B9_pre.
      split; [exact K2|]. split; [exact K8|]. split; [exact K9|]. split; [exact K18|]. split; [exact K19|].
      split; [exact K20|]. split; [exact K21|]. split; [exact K22|]. split; [exact K23|].
      split; [exact PV0|]. split; [exact PV8|]. split; [exact PV16|].
      split; [exact P0|]. split; [exact P8|]. split; [exact P16|]. split; [exact P24|].
      split; [replace (spz - 112 + 32) with (spz - 80) by lia; exact (fld_of_rw_cells8 _ _ _ FVv ltac:(lia))|].
      split; [eapply FW; [exact Fra | lia | lia]|].
      split; [eapply FW; [exact F0 | lia | lia]|].
      split; [eapply FW; [exact F1 | lia | lia]|].
      split; [eapply FW; [exact F2 | lia | lia]|].
      split; [eapply FW; [exact F3 | lia | lia]|].
      split; [eapply FW; [exact F4 | lia | lia]|].
      split; [eapply FW; [exact F5 | lia | lia]|].
      split; [eapply FW; [exact F6 | lia | lia]|].
      split; [eapply FW; [exact F7 | lia | lia]|].
      split; [lia|]. split; [lia|]. split; [destruct VBAND; lia|]. split; [lia|]. split; [lia|].
      split; [destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1; lia | lia]|].
      split; [eapply wr_at_of_stk_win; [exact ST7 | lia | lia]|].
      split; [exact PH9|]. split; [exact PH8|].
      split; [eapply sh0_of_addressable; [exact ADV7 | change (8 * (24 / 8)) with 24; lia]|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [destruct VBAND; lia|].
      split; [destruct VBAND; lia|]. split; [lia|].
      destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    assert (HDR7 : rw_cells asegs M7 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1)));
                                         C8 (Z_to_bv 64 (A + 4 * cap'))]).
    { apply JOIN8; [eapply C8F; [exact PV0 | lia | lia | eapply v32c_wr_sub; [exact WV7 | lia | lia | lia]]|].
      apply JOIN8; [eapply C8F; [exact PV8 | lia | lia | eapply v32c_wr_sub; [exact WV7 | lia | lia | lia]]|].
      eapply C8F; [exact PV16 | lia | lia | eapply v32c_wr_sub; [exact WV7 | lia | lia | lia]]. }
    assert (DV : disjoint_from [(spz - 112 - 24, spz - 112 + 32); (v, v + 24)] A (4 * cap'))
      by (cbn; split; [lia | split; [lia | exact I]]).
    eapply (v32c_s8 msF7 mo7 sk6 M7 R7 pid' A VIS7 HF7).
    - exact K1.
    - exact K10.
    - exact K11.
    - exact K12.
    - rewrite K13. unfold wz. f_equal. Z.div_mod_to_equations. lia.
    - exact B9P.
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - rewrite K24. unfold wz. apply Z_to_bv_bv_unsigned.
    - rewrite (KK 25%bv ltac:(inb)). exact G25.
    - rewrite (KK 26%bv ltac:(inb)). exact G26.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR7.
    - eapply (ah_mpres_trans H HH); [exact MP6 | exact MP7].
    - exact MID7.
    - exact ABR.
    - exact NI.
    - exact HDR7.
    - eapply bytes_at_transport; [exact BUF | exact MU7 |].
      eapply v32c_dj_sub; [exact DV | lia | rewrite le4s_length; unfold Zlen in XSL; lia].
    - eapply rw_cells_transport; [exact XC | exact MU7 | exact WM7 |]. cbn [cells_size csize Nat.add Z.of_nat].
      eapply v32c_dj_sub; [exact DV | lia | lia].
    - eapply SHAD_transport; [exact SHA | exact MU7 | exact WM7 |]. rewrite cc_gen_length by lia.
      pose proof (v4_app_sh v 24 A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VBAND; [left|right]; lia)) as D.
      pose proof (v4_app_sh (spz - 112 - 24) 56 A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(right; lia)) as D2.
      cbn. split; [lia | split; [lia | exact I]].
    - exact ADV7.
  Qed.

  Lemma v32c_s6 : forall (msF5 : machine_state) (mo5 : Model) (sk5 : as_St H) (m5 : mem) (R5 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    as_VIS H sk5 msF5 = MS R5 F (Z_to_bv 64 AASAN_MEMCPY) fc None m5 (seg_rom asegs) -> rfull R5 ->
    getr R5 1 = Z_to_bv 64 956436 -> getr R5 10 = Z_to_bv 64 A -> getr R5 11 = Z_to_bv 64 b ->
    getr R5 12 = Z_to_bv 64 (4 * cap) ->
    v32c_B7at R5 m5 A -> getr R5 3 = gp -> getr R5 4 = tp -> getr R5 25 = s9 -> getr R5 26 = s10 -> getr R5 27 = s11 ->
    as_AKREL H sk5 (mkCfg msF5 mo5) -> as_MPRES H mo mo5 ->
    v32c_mid sk5 m5 pid' A v32c_X0 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m5 A [CB (Z.to_nat (4 * cap)) jA] -> rw_cells asegs m5 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m5 A (cc_gen (4 * cap') (4 * cap')) -> (0 < cap -> SHAD m5 b (cc_gen (4 * cap) (4 * cap))) ->
    as_SR H Q (mkCfg msF5 mo5).
  Proof.
    intros msF5 mo5 sk5 m5 R5 pid' A jA VIS5 HF5 G1 G10 G11 G12 B7A G3 G4 G25 G26 G27 KR5 MP5 MID ABR NI CBA XC SHA OSH.
    pose proof MID as (MI5 & ST5 & _ & _ & AC5 & _ & _ & RH5 & _ & XP5 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v32c_vec_facts as (_ & _ & _ & FE & C0 & OB).
    destruct (v32c_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof B7A as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & PAC & FV0 & FV8 & FV16 & FS0 & FS8 & FS16
                       & FS24 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & WH & VD & WV & WS & HS0 & HS1 & HS2 & HS3 & HS4 & HS5
                       & HS6 & HS7 & HS8 & HS9 & Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & N9 & N10 & N11 & N12 & N13 & N14
                       & N15 & N16 & N17 & N18 & N19 & N20 & N21).
    assert (G2 : getr R5 2 = Z_to_bv 64 (spz - 112 - 80)) by exact P2.
    assert (OBB : (b = 0 /\ cap = 0) \/ (0 < cap /\ In (pid, b, 4 * cap) LB /\ ablock_range H b (4 * cap))).
    { destruct OB as [E|(Hc & HIn & ABb)]; [left; exact E | right; split; [lia|]; split; assumption]. }
    assert (OB0 : 0 <= b /\ b + 4 * cap <= aceil).
    { destruct OBB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }

    assert (SRCB : bytes_at asegs m5 b (le4s xs)).
    { destruct OBB as [[E1 E2]|(Hc & HIn & ABb)].
      - assert (XN : xs = []) by (apply length_zero_iff_nil; unfold Zlen in XSL; lia). rewrite XN. apply bytes_at_nil. lia.
      - eapply (xpres_bytes_at H); [exact XP5 | |].
        + apply bytes_at_le4s; [intros i Hi; rewrite XSL in Hi; exact (proj2 (FE i Hi)) | lia | rewrite XSL; lia].
        + rewrite le4s_length. replace (Z.of_nat (4 * length xs)) with (4 * cap) by (unfold Zlen in XSL; lia). exact (v32c_xc_old Hc). }
    assert (ADA : addressable m5 A (4 * cap')) by (split; [lia | rewrite <- cc_gen_full; exact SHA]).
    rewrite (rfull_eq R5 HF5) in VIS5.
    eapply (ahh_evt_then H HH); [exact KR5 | exact VIS5 | |].
    { eapply (ah_memcpy H HH) with (src := le4s xs) (junk := jA) (lo := lo); rewrite ?G10, ?G11, ?G12, ?G2; rewrite ?u64_of_Z by lia.
      - exact SRCB.
      - rewrite le4s_length. unfold Zlen in XSL. lia.
      - exact CBA.
      - destruct OBB as [[E1 E2]|(Hc & HIn & ABb)]; [left; lia|].
        assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 4 * cap); split; [reflexivity | exact HIn]).
        pose proof (ah_disj H HH _ _ _ (pid', A, 4 * cap') (pid, b, 4 * cap) RH5 (or_introl eq_refl) (or_intror HIn) NEQ) as D.
        cbn [blk_addr blk_size fst snd] in D. lia.
      - destruct OBB as [[E1 E2]|(Hc & HIn & ABb)].
        + replace (4 * cap) with 0 by lia. apply accessible_nil. unfold AAPP_HI. lia.
        + eapply (addressable_accessible m5 b (4 * cap)); [split; [lia | rewrite <- cc_gen_full; exact (OSH Hc)] | lia | lia | unfold AAPP_HI; lia].
      - eapply addressable_accessible; [exact ADA | lia | lia | unfold AAPP_HI; lia].
      - destruct OBB as [[E1 E2]|(Hc & HIn & ABb)].
        + rewrite E1, E2. replace (0 + 4 * 0) with 0 by lia. apply v32c_shvis0.
        + exact (ah_blk_shvis H HH _ _ _ _ _ _ RH5 (or_intror HIn)).
      - eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ RH5 (or_introl eq_refl)) | lia | lia | lia | lia | lia].
      - exact (proj1 (stk_split asegs m5 lo (spz - 112 - 80) spz ST5 ltac:(lia))).
      - exact LO1.
      - unfold AINTRIN_STACK; lia.
      - exact MI5.
      - exact AC5.
      - lia.
      - destruct OBB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))].
        + left. unfold ASHADOW_BASE. lia.
        + unfold in_app_mem. destruct (v32c_band_of_aapp _ _ OAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia.
      - unfold in_app_mem. destruct (v32c_band_of_aapp _ _ AAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia.
      - eapply aconst_ok_app; [exact AAP | lia | lia].
      - left; lia.
      - left; lia. }
    intros msF6 mo6 KR6 MP6 POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m6
                      & VIS6 & MU6 & WM6 & MI6 & ST6 & CB6 & SB6 & AC6).
    rewrite G10, G12, G2, ?u64_of_Z in MU6 by lia. rewrite G10, G12, ?u64_of_Z in CB6 by lia. rewrite G2, u64_of_Z in ST6 by lia.
    unfold AINTRIN_STACK in MU6.
    rewrite G1 in VIS6. rewrite (ret_pc_even 956436 ltac:(lia) eq_refl) in VIS6.
    assert (W6 : Forall (v32c_wk A v32c_X0) [(A, A + 4 * cap); (spz - 112 - 80 - 4096, spz - 112 - 80)]).
    { apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (MID6 : v32c_mid sk5 m6 pid' A v32c_X0)
      by (eapply v32c_mid_munch; [exact MID | exact ABR | exact NI | exact MU6 | exact WM6 | exact MI6 | exact W6]).
    pose proof MID6 as (_ & _ & _ & _ & _ & _ & S06 & _ & _ & XP6 & _ & _).
    destruct (v32c_hdr_X0 m6 XP6) as (FV0' & FV8' & FV16' & ADV6 & _).
    assert (FT : forall a z, fldA m5 a 8 z -> spz - 112 - 80 <= a -> a + 8 <= spz -> fldA m6 a 8 z).
    { intros a z Hf Ha Hk. unfold fldA in Hf |- *. eapply fld_agree; [lia | change (Z.of_nat 8) with 8; lia | exact Hf |].
      intros y Hy. red in Hy. change (Z.of_nat 8) with 8 in Hy. apply MU6. rewrite u64_of_Z by lia.
      cbn [outside]. split; [lia | split; [lia | exact I]]. }
    eapply (v32c_s7 msF6 mo6 sk5 m6 _ pid' A VIS6 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold v32c_B7at, v32_B7_pre.
      refine (conj P2 (conj P8 (conj P9 (conj P18 (conj P19 (conj P20 (conj P21 (conj P22 (conj P23 (conj P24
        (conj AC6 _))))))))))).
      refine (conj FV0' (conj FV8' (conj FV16' _))).
      do 4 (split; [eapply FT; [eassumption | lia | lia] |]).
      refine (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (conj N7 (conj N8 _)))))))).
      refine (conj (wr_at_transport asegs _ _ _ _ WH WM6) (conj VD (conj (wr_at_transport asegs _ _ _ _ WV WM6)
        (conj (wr_at_transport asegs _ _ _ _ WS WM6) _)))).
      do 10 (split; [eapply FT; [eassumption | lia | lia] |]).
      split; [eapply sh0_of_stack0; [exact S06 | lia] |].
      split; [eapply sh0_of_addressable; [exact ADV6 | change (8 * (24 / 8)) with 24; lia] |].
      split; [eapply sh0_of_addressable; [exact ADV6 | change (8 * (24 / 8)) with 24; lia] |].
      split; [eapply sh0_of_stack0; [exact S06 | lia] |].
      split; [eapply sh0_of_addressable; [exact ADV6 | change (8 * (24 / 8)) with 24; lia] |].
      split; [eapply sh0_of_stack0; [exact S06 | lia] |].
      split; [eapply sh0_of_stack0; [exact S06 | lia] |].
      exact (conj N9 (conj N10 (conj N11 (conj N12 (conj N13 (conj N14 (conj N15 (conj N16 (conj N17 (conj N18 (conj N19
        (conj N20 N21)))))))))))).
    - exact G3.
    - exact G4.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR6.
    - eapply (ah_mpres_trans H HH); [exact MP5 | exact MP6].
    - exact MID6.
    - exact ABR.
    - exact NI.
    - exact (bytes_of_CB _ _ _ _ CB6).
    - eapply rw_cells_transport; [exact XC | exact MU6 | exact WM6 |]. cbn. split; [lia | split; [lia | exact I]].
    - eapply SHAD_transport; [exact SHA | exact MU6 | exact WM6 |]. rewrite cc_gen_length by lia.
      pose proof (v4_app_sh A (4 * cap) A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct (v32c_band_of_aapp _ _ AAP); [left|right]; lia)) as D.
      pose proof (sh_nsh_high A (4 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as D2. unfold AHI_LO in D2.
      cbn. split; [lia | split; [lia | exact I]].
  Qed.

  Lemma v32c_s5 : forall (msF4 : machine_state) (mo4 : Model) (sk4 : as_St H) (m4 : mem) (R4 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    0 < cap ->
    as_VIS H sk4 msF4 = MS R4 F (Z_to_bv 64 954568) fc None m4 (seg_rom asegs) -> rfull R4 ->
    v32c_B5at R4 m4 A -> getr R4 3 = gp -> getr R4 4 = tp -> getr R4 25 = s9 -> getr R4 26 = s10 -> getr R4 27 = s11 ->
    as_AKREL H sk4 (mkCfg msF4 mo4) -> as_MPRES H mo mo4 ->
    v32c_mid sk4 m4 pid' A v32c_X0 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m4 A [CB (Z.to_nat (4 * cap)) jA] -> rw_cells asegs m4 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m4 A (cc_gen (4 * cap') (4 * cap')) -> SHAD m4 b (cc_gen (4 * cap) (4 * cap)) ->
    as_SR H Q (mkCfg msF4 mo4).
  Proof.
    intros msF4 mo4 sk4 m4 R4 pid' A jA Hc VIS4 HF4 B5A G3 G4 G25 G26 G27 KR4 MP4 MID ABR NI CBA XC SHA OSH.
    pose proof RUNS as (_ & _ & _ & _ & _ & B5 & _).
    pose proof MID as (_ & _ & _ & _ & AC4 & _ & S04 & _ & _ & XP4 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    destruct (v32c_hdr_X0 m4 XP4) as (_ & _ & _ & ADV4 & _).
    destruct (B5 R4 F fc m4 v (spz - 112) b cap A cap' (bv_unsigned s8) v cap' (4 * cap)
                 ASHADOW_BASE (sh (v + 8)) (A + 4 * cap') src (v + 8) (E0 + 404) B5A)
      as (R5 & M5 & Hms & EM5 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & KK).
    subst M5.
    assert (DA : forall z, z = 4 * cap + (A + -4 * (4 * cap / 4)) -> Z_to_bv 64 z = Z_to_bv 64 A).
    { intros z ->. f_equal. Z.div_mod_to_equations. lia. }
    pose proof (msteps_full asegs _ _ Hms HF4) as HF5. cbn [ms_regs] in HF5.
    eapply (sr_blk H HH); [exact KR4 | exact VIS4 | exact HF4 | exact Hms |].
    intros msF5 mo5 KR5 MP5 VIS5. rewrite <- (rfull_eq R5 HF5) in VIS5.
    eapply (v32c_s6 msF5 mo5 sk4 m4 R5 pid' A jA VIS5 HF5).
    - exact K1.
    - rewrite K10. unfold wz. apply DA. reflexivity.
    - exact K11.
    - exact K12.
    - pose proof B5A as (P2 & P8 & P9 & P21 & FV0 & FV8 & FV16 & FS0 & FS8 & FS16 & FS24 & N1 & N2 & N3 & N4 & N5 & N6 & N7
                        & N8 & WH & VD & WV & WS & WC0 & WC1 & HS0 & HS1 & HS2 & HS3 & HS4 & HS5 & HS6 & HS7 & HS8 & HS9
                        & Z0 & Z1 & Z2 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19 & N20).
      unfold v32c_B7at, v32_B7_pre.
      repeat match goal with |- _ /\ _ => split end.
      all: try assumption.
      all: first [ exact AC4
                      | rewrite K20; unfold wz; apply DA; reflexivity
                      | eapply sh0_of_stack0; [exact S04 | lia]
                      | eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]
                      | eapply v32c_wr_sub; [exact WH | lia | lia | lia]
                      | destruct VBAND; lia
                      | lia ].
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - rewrite (KK 25%bv ltac:(inb)). exact G25.
    - rewrite (KK 26%bv ltac:(inb)). exact G26.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR5.
    - eapply (ah_mpres_trans H HH); [exact MP4 | exact MP5].
    - exact MID.
    - exact ABR.
    - exact NI.
    - exact CBA.
    - exact XC.
    - exact SHA.
    - intros _. exact OSH.
  Qed.

  Lemma v32c_s4 : forall (msF3 : machine_state) (mo3 : Model) (sk3 : as_St H) (m3 : mem) (R3 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    0 < cap ->
    as_VIS H sk3 msF3 = MS R3 F (Z_to_bv 64 AANNOTATE_CC) fc None m3 (seg_rom asegs) -> rfull R3 ->
    getr R3 1 = Z_to_bv 64 954568 -> getr R3 10 = Z_to_bv 64 b -> getr R3 11 = Z_to_bv 64 (b + 4 * cap) ->
    getr R3 12 = Z_to_bv 64 (b + 4 * cap) -> getr R3 13 = Z_to_bv 64 (b + 4 * cap) ->
    v32c_B5at R3 m3 A -> getr R3 3 = gp -> getr R3 4 = tp -> getr R3 25 = s9 -> getr R3 26 = s10 -> getr R3 27 = s11 ->
    as_AKREL H sk3 (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
    v32c_mid sk3 m3 pid' A [] -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m3 A [CB (Z.to_nat (4 * cap)) jA] -> rw_cells asegs m3 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m3 A (cc_gen (4 * cap') (4 * cap')) ->
    as_SR H Q (mkCfg msF3 mo3).
  Proof.
    intros msF3 mo3 sk3 m3 R3 pid' A jA Hc VIS3 HF3 G1 G10 G11 G12 G13 B5 G3 G4 G25 G26 G27 KR3 MP3 MID ABR NI CBA XC SHA.
    pose proof B5 as B5r. unfold v32c_B5at, v32_B5_pre in B5r. destruct B5r as (G2 & G8 & G9 & G21 & B5r).
    repeat match type of B5r with _ /\ _ => let Hn := fresh "BF" in destruct B5r as [Hn B5r] end.
    pose proof MID as (MI3 & ST3 & _ & _ & AC3 & _ & _ & RH3 & _ & XP3 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v32c_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (v32c_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    destruct (v32c_old_facts Hc) as (HIn & (O0 & O16 & On & OI & OC & OF & OAP) & OD & NZ).
    assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 4 * cap); split; [reflexivity | exact HIn]).
    pose proof (ah_disj H HH _ _ _ (pid', A, 4 * cap') (pid, b, 4 * cap) RH3 (or_introl eq_refl) (or_intror HIn) NEQ) as DAB.
    cbn [blk_addr blk_size fst snd] in DAB.
    assert (OSH3 : SHAD m3 b (cc_gen (4 * cap) (4 * cap))).
    { eapply v32c_SHAD_xpres; [exact XP3 | exact (OLDSH Hc) |]. rewrite cc_gen_length by lia.
      split; [eapply (aclient_range_block_sh H); exact HIn | apply Forall_nil]. }
    rewrite (rfull_eq R3 HF3) in VIS3.
    eapply (ahh_evt_then H HH); [exact KR3 | exact VIS3 | |].
    { eapply HANN with (beg := b) (len := 4 * cap) (oldmid := 4 * cap) (newmid := 4 * cap) (lo := lo).
      - exact G10.
      - exact G11.
      - exact G12.
      - exact G13.
      - exact (v4_mod16_8 b O16).
      - lia.
      - lia.
      - lia.
      - exact OAP.
      - unfold AAPP_HI; lia.
      - exact OSH3.
      - rewrite G2, u64_of_Z by lia. exact (proj1 (stk_split asegs m3 lo (spz - 112 - 96) spz ST3 ltac:(lia))).
      - exact LO1.
      - rewrite G2, u64_of_Z by lia. unfold AINTRIN_STACK. lia.
      - exact MI3.
      - exact AC3.
      - unfold in_app_mem. destruct (v32c_band_of_aapp _ _ OAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia. }
    intros msF4 mo4 KR4 MP4 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4
                      & VIS4 & MU4 & WM4 & MI4 & ST4 & SH4 & AC4).
    rewrite G2, u64_of_Z in MU4, ST4 by lia. unfold AINTRIN_STACK in MU4.
    rewrite G1 in VIS4. rewrite (ret_pc_even 954568 ltac:(lia) eq_refl) in VIS4.
    assert (W4 : Forall (v32c_wk A v32c_X0) [(sh b, sh b + nsh (4 * cap)); (spz - 112 - 96 - 4096, spz - 112 - 96)]).
    { apply Forall_cons; [|apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]].
      apply (v32c_wk_oldsh Hc). intros a Ha. unfold v32c_X0. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. left. cbn [fst snd]. lia. }
    pose proof (v4_app_sh A (4 * cap') b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (v32c_band_of_aapp _ _ AAP)) as DAS.
    pose proof (v4_sh_apart A (4 * cap') b (4 * cap) ltac:(lia) ltac:(lia) (v4_mod16_8 A A16) (v4_mod16_8 b O16) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as DSS.
    pose proof (sh_nsh_high A (4 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHA2. unfold AHI_LO in SHA2.
    pose proof (sh_nsh_high b (4 * cap) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHB2. unfold AHI_LO in SHB2.
    assert (MID4 : v32c_mid sk3 m4 pid' A v32c_X0).
    { eapply v32c_mid_munch; [eapply v32c_mid_weaken; [exact MID | intros a Ha; destruct Ha] | exact ABR | exact NI
                             | exact MU4 | exact WM4 | exact MI4 | exact W4]. }
    pose proof MID4 as (_ & _ & _ & _ & _ & _ & S04 & _ & _ & XP4 & _ & _).
    destruct (v32c_hdr_X0 m4 XP4) as (F0' & F8' & F16' & ADV4 & WV4).
    assert (FLDT : forall a k z, spz - 112 - 96 <= a -> a + Z.of_nat k <= spz -> fldA m3 a k z -> fldA m4 a k z).
    { intros a k z Ha Hk Hf. unfold fldA in *. eapply fld_agree; [lia | lia | exact Hf |].
      intros a' Ha'. hnf in Ha'. apply MU4. rewrite u64_of_Z by lia. cbn [outside]. split; [lia | split; [lia | exact I]]. }
    repeat match goal with
           | Hf : fldA m3 ?a ?k ?z |- _ =>
               let Hn := fresh "T" in
               assert (Hn : fldA m4 a k z) by (apply FLDT; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Hf]); clear Hf
           end.
    repeat match goal with
           | Hw : wr_at asegs m3 ?a ?n |- _ =>
               let Hn := fresh "WT" in pose proof (wr_at_transport asegs _ _ _ _ Hw WM4) as Hn; clear Hw
           end.
    assert (Z8' : LbB_Kit.sh0 m4 (spz - 112 + 8)) by (eapply sh0_of_stack0; [exact S04 | lia]).
    assert (ZV8' : LbB_Kit.sh0 m4 (v + 8)) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZV' : LbB_Kit.sh0 m4 v) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
    eapply (v32c_s5 msF4 mo4 sk3 m4 _ pid' A jA Hc VIS4 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold v32c_B5at, v32_B5_pre.
      split; [exact G2|]. split; [exact G8|]. split; [exact G9|]. split; [exact G21|].
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
    - exact G3.
    - exact G4.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR4.
    - eapply (ah_mpres_trans H HH); [exact MP3 | exact MP4].
    - exact MID4.
    - exact ABR.
    - exact NI.
    - eapply rw_cells_transport; [exact CBA | exact MU4 | exact WM4 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
      cbn. split; [lia | split; [lia | exact I]].
    - eapply rw_cells_transport; [exact XC | exact MU4 | exact WM4 |]. cbn. split; [lia | split; [lia | exact I]].
    - eapply SHAD_transport; [exact SHA | exact MU4 | exact WM4 |]. rewrite cc_gen_length by lia.
      cbn. split; [lia | split; [lia | exact I]].
    - exact SH4.
  Qed.

  Lemma v32c_s3 : forall (msF2 : machine_state) (mo2 : Model) (sk2 : as_St H) (m2 : mem) (R2 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jall : list byte),
    as_VIS H sk2 msF2 = MS R2 F (Z_to_bv 64 (E0 + 200)) fc None m2 (seg_rom asegs) -> rfull R2 ->
    getr R2 2 = Z_to_bv 64 (spz - 112) -> getr R2 3 = gp -> getr R2 4 = tp -> getr R2 8 = Z_to_bv 64 (v + 8) ->
    getr R2 9 = Z_to_bv 64 src -> getr R2 10 = Z_to_bv 64 A -> getr R2 18 = Z_to_bv 64 (4 * cap') ->
    getr R2 19 = Z_to_bv 64 (sh (v + 8)) -> getr R2 20 = Z_to_bv 64 ASHADOW_BASE -> getr R2 21 = Z_to_bv 64 (4 * cap) ->
    getr R2 22 = Z_to_bv 64 cap' -> getr R2 23 = Z_to_bv 64 v ->
    getr R2 24 = s8 -> getr R2 25 = s9 -> getr R2 26 = s10 -> getr R2 27 = s11 ->
    as_AKREL H sk2 (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
    v32c_mid sk2 m2 pid' A [] -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m2 A [CB (Z.to_nat (4 * cap')) jall] -> addressable m2 A (4 * cap') ->
    as_SR H Q (mkCfg msF2 mo2).
  Proof.
    intros msF2 mo2 sk2 m2 R2 pid' A jall VIS2 HF2 G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR2 MP2 MID ABR NI
      CBall ADD2.
    pose proof RUNS as (_ & B3a & B3ak & B3b & B3bk & _).
    pose proof MID as (MI2 & ST2 & _ & _ & AC2 & _ & S02 & RH2 & FR2 & XP2 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof (v32c_band_of_aapp _ _ AAP) as ABND.
    pose proof v32c_vec_facts as (_ & _ & _ & _ & C0 & OB).
    destruct (v32c_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof OBJ as (_ & _ & _ & _ & _ & SD).
    pose proof SRCR as (SR4 & SR0 & SR47).
    assert (VB2 : 7241728 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    assert (HNEW : v + 24 <= A \/ A + 4 * cap' <= v) by (eapply v32c_hdr_fresh; [exact RH2 | exact NI | lia]).
    assert (XP2' : xpres H LB spz v32c_X0 m m2)
      by (eapply (xpres_weaken H); [exact XP2 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
    destruct (v32c_hdr_X0 m2 XP2') as (F0 & F8 & F16 & ADV2 & WV2).
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    assert (SRCF : src + 4 <= spz - 112 \/ spz <= src).
    { destruct (Z_le_gt_dec (src + 4) (spz - 112)) as [L1|L1]; [left; exact L1|].
      destruct (Z_le_gt_dec spz src) as [L2|L2]; [right; exact L2|]. exfalso.
      assert (SA : spz - 112 <= src /\ src + 4 <= spz) by (Z.div_mod_to_equations; lia).
      assert (WS0 : wr_at asegs m src 4) by (eapply wr_at_of_stk_win; [exact ST0 | lia | lia]).
      assert (BL : forall z, length (word_to_le_bytes 4 (Z_to_bv 64 z)) = 4%nat) by (intros z; reflexivity).
      pose proof (wr_at_store_ok asegs m src 4 0 4%nat WS0 ltac:(lia) ltac:(lia)) as SO. rewrite Z.add_0_r in SO.
      assert (KEY : forall y, nth_error (word_to_le_bytes 4 (Z_to_bv 64 x)) 0 = nth_error (word_to_le_bytes 4 (Z_to_bv 64 y)) 0).
      { intros y.
        assert (MIW : mem_inv asegs (write_to_mem m (wa src) (word_to_le_bytes 4 (Z_to_bv 64 y)))).
        { apply mem_inv_store; [exact MI0 | rewrite BL; exact SO]. }
        assert (MUW : munch [(src, src + 4)] m (write_to_mem m (wa src) (word_to_le_bytes 4 (Z_to_bv 64 y)))).
        { apply munch_write; [apply munch_refl | lia | rewrite BL; lia | cbn [inside]; left; rewrite BL; lia]. }
        assert (WMW : wmono asegs m (write_to_mem m (wa src) (word_to_le_bytes 4 (Z_to_bv 64 y)))).
        { apply wmono_write. apply wmono_refl. }
        assert (ACW : ACONST (write_to_mem m (wa src) (word_to_le_bytes 4 (Z_to_bv 64 y)))).
        { eapply ACONST_frame; [exact AC0 | exact MUW | exact WMW |]. apply Forall_cons; [|apply Forall_nil].
          apply aconst_ok_high; [|right; left; lia].
          pose proof (sh_below_aceil AIMG_TOP ltac:(unfold AIMG_TOP, AAPP_HI; lia)) as SBA. lia. }
        assert (APW : apres H LB spz m (write_to_mem m (wa src) (word_to_le_bytes 4 (Z_to_bv 64 y)))).
        { eapply (apres_of_munch H HH); [exact RH0 | exact MUW | exact WMW |].
          apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
        destruct (SRC _ ACW MIW APW) as [FX _].
        unfold fldA, fld in FX.
        assert (BX : bytes_at asegs (write_to_mem m (wa src) (word_to_le_bytes 4 (Z_to_bv 64 y))) src
                       (word_to_le_bytes 4 (Z_to_bv 64 x))).
        { apply bytes_at_of_rdn; [lia | rewrite BL; lia | rewrite BL; exact FX]. }
        destruct BX as (_ & _ & BX). specialize (BX 0%nat ltac:(rewrite BL; lia)).
        rewrite <- BX. unfold mrd. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
        rewrite write_to_mem_spec by (try rewrite BL; lia).
        rewrite wa_unsigned by lia. rewrite BL, Z.leb_refl, Z.sub_diag.
        destruct (Z.ltb_spec0 src (src + Z.of_nat 4)) as [_|NL]; [|exfalso; lia]. cbn [andb]. change (Z.to_nat 0) with 0%nat.
        destruct (nth_error (word_to_le_bytes 4 (Z_to_bv 64 y)) 0) eqn:EN0; [reflexivity|].
        apply nth_error_None in EN0. rewrite BL in EN0. lia. }
      pose proof (KEY 0) as K0. pose proof (KEY 1) as K1. rewrite K0 in K1.
      apply (f_equal (option_map bv_unsigned)) in K1. vm_compute in K1. discriminate K1. }
    destruct (SRC m2 AC2 MI2 (apres_of_xpres_nil32 m2 XP2)) as [FS ACS].
    destruct (v4_src_shk m2 src ACS SR4 SR0) as (k & SK & KR).
    destruct (rw_cells_CB_split asegs m2 A (Z.to_nat (4 * cap')) (Z.to_nat (4 * cap)) jall CBall ltac:(lia)) as [CBA _].
    pose proof (proj2 CBall) as WA. cbn [cells_size csize] in WA. rewrite Nat.add_0_r, Z2Nat.id in WA by lia.
    assert (WSL : wr_at asegs m2 (A + 4 * cap) 4) by (eapply v32c_wr_sub; [exact WA | lia | lia | lia]).
    assert (WSB : wr_at asegs m2 (spz - 112) 32) by (eapply wr_at_of_stk_win; [exact ST2 | lia | lia]).
    assert (WHF : wr_at asegs m2 (spz - 112 - 112) 112) by (eapply wr_at_of_stk_win; [exact ST2 | lia | lia]).
    assert (FV : fldA m2 (spz - 112 + 32) 8 v).
    { unfold fldA, fld. pose proof (rw_cells_read asegs m2 (spz - 80) FRAME 0%nat _ FR2 eq_refl) as RD.
      replace (spz - 80 + Z.of_nat 0) with (spz - 112 + 32) in RD by lia. rewrite <- rdn_of_ov. exact RD. }
    assert (ZV : LbB_Kit.sh0 m2 v) by (eapply sh0_of_addressable; [exact ADV2 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZV8 : LbB_Kit.sh0 m2 (v + 8)) by (eapply sh0_of_addressable; [exact ADV2 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZV16 : LbB_Kit.sh0 m2 (v + 16)) by (eapply sh0_of_addressable; [exact ADV2 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZSB : LbB_Kit.sh0 m2 (spz - 112 + 8)) by (eapply sh0_of_stack0; [exact S02 | lia]).
    assert (SHA0 : SHAD m2 A (cc_gen (4 * cap') (4 * cap'))) by (rewrite cc_gen_full; exact (proj2 ADD2)).
    pose proof (sh_nsh_high A (4 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHA2. unfold AHI_LO in SHA2.
    pose proof (v4_app_sh (A + 4 * cap) 4 A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct ABND; [left|right]; lia)) as DAS.
    pose proof (msteps_full asegs) as MSF.
    destruct OB as [[E1 E2]|(Hc & HIn & ABb)].
    -
      assert (C1 : cap' = 1) by (unfold cap', v4_newcap; rewrite E2; reflexivity).
      assert (BM4 : b mod 4 = 0) by (rewrite E1; reflexivity).
      assert (SK4 : LbB_Kit.shk m2 (A + 4 * cap) 4).
      { rewrite E2. replace (A + 4 * 0) with A by lia. apply v32c_shk4. pose proof ADD2 as ADD2'. rewrite C1 in ADD2'. exact ADD2'. }
      pose proof (B3b R2 F fc m2 A (spz - 112) v src cap b x cap') as B3b'.
      pose proof (B3bk R2 F fc m2 A (spz - 112) v src cap b x cap' k) as B3bk'.
      match type of B3b' with _ -> ?P => assert (EX : P) end.
      { destruct KR as [K0|KR'].
        - apply B3b'. subst k. unfold v32_B3b_pre.
          repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
        - assert (SR8 : src mod 8 = 0) by (clear - SR4 KR'; Z.div_mod_to_equations; lia).
          apply B3bk'. unfold v32_B3bk_pre.
          repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
      destruct EX as (R3 & M3 & Hms & MU3 & WM3 & U0 & U1 & U2 & W0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & S16 & XA & S24 & S8 & S0
                      & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K16 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & KK).
      pose proof (MSF _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
      assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
      assert (MID3 : v32c_mid sk2 M3 pid' A []).
      { eapply v32c_mid_munch; [exact MID | exact ABR | exact NI | exact MU3 | exact WM3 | exact MI3 |].
        apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_nil]. }
      pose proof MID3 as (_ & ST3 & _ & _ & AC3 & _ & S03 & _ & _ & XP3 & _ & _).
      assert (XP3' : xpres H LB spz v32c_X0 m M3)
        by (eapply (xpres_weaken H); [exact XP3 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
      destruct (v32c_hdr_X0 M3 XP3') as (F0' & F8' & F16' & ADV3 & WV3).
      rewrite G24 in W0.
      assert (W0' : fldA M3 (spz - 112 - 80) 8 (bv_unsigned s8)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W0).
      assert (WB80 : wr_at asegs M3 (spz - 112 - 80) 80) by (eapply wr_at_of_stk_win; [exact ST3 | lia | lia]).
      assert (WSB3 : wr_at asegs M3 (spz - 112) 32) by (eapply wr_at_of_stk_win; [exact ST3 | lia | lia]).
      assert (D4 : 4 * cap / 4 = cap) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
      assert (K10' : getr R3 10 = Z_to_bv 64 A) by (rewrite K10, D4; unfold wz; f_equal; lia).
      assert (K20' : getr R3 20 = wz A) by (rewrite K20, D4; unfold wz; f_equal; lia).
      assert (ZS0 : LbB_Kit.sh0 M3 (spz - 112)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZS8 : LbB_Kit.sh0 M3 (spz - 112 + 8)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZS16 : LbB_Kit.sh0 M3 (spz - 112 + 16)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZS24 : LbB_Kit.sh0 M3 (spz - 112 + 24)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZV3 : LbB_Kit.sh0 M3 v) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZV83 : LbB_Kit.sh0 M3 (v + 8)) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZV163 : LbB_Kit.sh0 M3 (v + 16)) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (XC3 : rw_cells asegs M3 (A + 4 * cap) [C4 (Z_to_bv 64 x)]).
      { pose proof (wr_at_transport asegs _ _ _ _ WSL WM3) as WSL3. pose proof WSL3 as (WL0 & WL1 & _).
        split; [|exact WSL3]. split; [clear - WL0; cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        apply bytes_at_of_rdn; [lia | rewrite length_le4; lia | rewrite length_le4; exact XA]. }
      assert (SHA3 : SHAD M3 A (cc_gen (4 * cap') (4 * cap'))).
      { eapply SHAD_transport; [exact SHA0 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia.
        cbn. split; [lia | split; [lia | exact I]]. }
      eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
      intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
      eapply (v32c_s6 msF3 mo3 sk2 M3 R3 pid' A [] VIS3 HF3).
      + exact K1.
      + exact K10'.
      + exact K11.
      + exact K12.
      + unfold v32c_B7at, v32_B7_pre.
        split; [exact K2|]. split; [exact K8|]. split; [exact K9|]. split; [exact K18|]. split; [exact K19|].
        split; [exact K20'|]. split; [exact K21|]. split; [exact K22|]. split; [exact K23|]. split; [exact K24|].
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 25%bv ltac:(inb)). exact G25.
      + rewrite (KK 26%bv ltac:(inb)). exact G26.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR3.
      + eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
      + eapply (v32c_mid_weaken _ _ _ _ [] v32c_X0); [exact MID3 | intros a Ha; destruct Ha].
      + exact ABR.
      + exact NI.
      + rewrite E2. change (Z.to_nat (4 * 0)) with 0%nat. apply v32c_CB0. lia.
      + exact XC3.
      + exact SHA3.
      + intros Hc. lia.
    -
      pose proof ABb as (O0 & O16 & On & OI & OC & OF & OAP).
      assert (B16 : 16 <= b) by exact (v4_mod16_16le b O0 O16).
      assert (BM4 : b mod 4 = 0) by (clear - O16; Z.div_mod_to_equations; lia).
      assert (SH0 : LbB_Kit.sh0 m2 (A + 4 * cap)).
      { eapply sh0_of_addressable; [exact ADD2|]. pose proof (v4_new_granule cap ltac:(lia)) as NG.
        change (vgrow cap) with cap' in NG. lia. }
      pose proof (B3a R2 F fc m2 A (spz - 112) v src cap b x cap') as B3a'.
      pose proof (B3ak R2 F fc m2 A (spz - 112) v src cap b x cap' k) as B3ak'.
      match type of B3a' with _ -> ?P => assert (EX : P) end.
      { destruct KR as [K0|KR'].
        - apply B3a'. subst k. unfold v32_B3a_pre.
          repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
        - assert (SR8 : src mod 8 = 0) by (clear - SR4 KR'; Z.div_mod_to_equations; lia).
          apply B3ak'. unfold v32_B3ak_pre.
          repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
      destruct EX as (R3 & M3 & Hms & MU3 & WM3 & U0 & U1 & U2 & W0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & S16 & XA & S24 & S8 & S0
                      & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K18 & K19 & K20 & K21 & K22 & K23 & KK).
      pose proof (MSF _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
      assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
      assert (MID3 : v32c_mid sk2 M3 pid' A []).
      { eapply v32c_mid_munch; [exact MID | exact ABR | exact NI | exact MU3 | exact WM3 | exact MI3 |].
        apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_nil]. }
      pose proof MID3 as (_ & ST3 & _ & _ & _ & _ & S03 & _ & _ & XP3 & _ & _).
      assert (XP3' : xpres H LB spz v32c_X0 m M3)
        by (eapply (xpres_weaken H); [exact XP3 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
      destruct (v32c_hdr_X0 M3 XP3') as (F0' & F8' & F16' & ADV3 & WV3).
      rewrite G24 in W0.
      assert (W0' : fldA M3 (spz - 112 - 80) 8 (bv_unsigned s8)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W0).
      assert (WB96 : wr_at asegs M3 (spz - 112 - 96) 96) by (eapply wr_at_of_stk_win; [exact ST3 | lia | lia]).
      assert (WSB3 : wr_at asegs M3 (spz - 112) 32) by (eapply wr_at_of_stk_win; [exact ST3 | lia | lia]).
      assert (ZS8 : LbB_Kit.sh0 M3 (spz - 112 + 8)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZV3 : LbB_Kit.sh0 M3 v) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZV83 : LbB_Kit.sh0 M3 (v + 8)) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (XC3 : rw_cells asegs M3 (A + 4 * cap) [C4 (Z_to_bv 64 x)]).
      { pose proof (wr_at_transport asegs _ _ _ _ WSL WM3) as WSL3. pose proof WSL3 as (WL0 & WL1 & _).
        split; [|exact WSL3]. split; [clear - WL0; cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        apply bytes_at_of_rdn; [lia | rewrite length_le4; lia | rewrite length_le4; exact XA]. }
      assert (SHA3 : SHAD M3 A (cc_gen (4 * cap') (4 * cap'))).
      { eapply SHAD_transport; [exact SHA0 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia.
        cbn. split; [lia | split; [lia | exact I]]. }
      eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
      intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
      eapply (v32c_s4 msF3 mo3 sk2 M3 R3 pid' A (firstn (Z.to_nat (4 * cap)) jall) ltac:(lia) VIS3 HF3).
      + exact K1.
      + exact K10.
      + exact K11.
      + rewrite K12. unfold wz. f_equal. lia.
      + rewrite K13. unfold wz. f_equal. lia.
      + unfold v32c_B5at, v32_B5_pre.
        split; [exact K2|]. split; [exact K8|]. split; [exact K9|]. split; [exact K21|].
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 25%bv ltac:(inb)). exact G25.
      + rewrite (KK 26%bv ltac:(inb)). exact G26.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR3.
      + eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
      + exact MID3.
      + exact ABR.
      + exact NI.
      + eapply rw_cells_transport; [exact CBA | exact MU3 | exact WM3 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        cbn. split; [lia | split; [lia | exact I]].
      + exact XC3.
      + exact SHA3.
  Qed.

  Lemma v32c_sn : forall (msF1 : machine_state) (mo1 : Model) (m1 : mem) (R1 : bvmap 5 word) (e1 : word),
    as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs) -> rfull R1 ->
    getr R1 1 = Z_to_bv 64 (E0 + 200) -> getr R1 2 = Z_to_bv 64 (spz - 112) -> getr R1 3 = gp -> getr R1 4 = tp ->
    getr R1 8 = Z_to_bv 64 (v + 8) -> getr R1 9 = Z_to_bv 64 src -> getr R1 10 = Z_to_bv 64 (4 * cap') ->
    getr R1 18 = Z_to_bv 64 (4 * cap') -> getr R1 19 = Z_to_bv 64 (sh (v + 8)) -> getr R1 20 = Z_to_bv 64 ASHADOW_BASE ->
    getr R1 21 = Z_to_bv 64 (4 * cap) -> getr R1 22 = Z_to_bv 64 cap' -> getr R1 23 = Z_to_bv 64 v ->
    getr R1 24 = s8 -> getr R1 25 = s9 -> getr R1 26 = s10 -> getr R1 27 = s11 ->
    as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    mem_inv asegs m1 -> stk asegs m1 lo spz -> rw_cells asegs m1 (errno_addr tp) [C4 e1] -> as_rauxv_ok H m1 B ->
    ACONST m1 -> as_RFS H LF m1 -> stack0 m1 lo shi -> as_RHEAP H s LB m1 -> rw_cells asegs m1 (spz - 80) FRAME ->
    xpres H LB spz [] m m1 -> lb_own LB m1 ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 m1 R1 e1 VIS1 HF1 G1 G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR1 MP1
      MI1 ST1 ERR1 RA1 AC1 RF1 S01 RH1 FR1 XP1 OW1.
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof v32c_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (v32c_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (SP112 : (spz - 112) mod 16 = 0).
    { replace (spz - 112) with (spz + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact SP16. }
    assert (CMB : as_Cm H (4 * cap') <= as_AL H s).
    { pose proof CM as CM'. change (v4_newcap cap) with cap' in CM'.
      assert (CF0 : 0 <= as_Cf H (4 * cap)) by (pose proof (ah_costs H HH) as (_ & _ & CF & _); apply CF; lia). lia. }
    rewrite (rfull_eq R1 HF1) in VIS1.
    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH) with (n := 4 * cap') (LB := LB) (lo := lo) (B := B) (errv := e1);
        [ exact VIS1 | exact RH1 | exact KR1 | exact AOK | exact CMB | exact RA1 | rewrite G2, u64_of_Z by lia; lia
        | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo (spz - 112) spz ST1 ltac:(lia)))
        | exact LO1 | rewrite G2, u64_of_Z by lia; unfold AOPNEW_STACK, AMALLOC_STACK; lia
        | rewrite G4; exact ERR1 | exact MI1 | rewrite G4; exact TPV | rewrite G2, u64_of_Z by lia; exact SP112
        | exact AC1 | exact G10 | lia ]. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & A & junk & p
                      & sk2 & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RAX2 & AP2 & ABR & RH2 & CB2 & ADDR & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite G1 in VIS2. destruct (v32c_E0_even 200 ltac:(lia) eq_refl) as [ER1 ER2].
    rewrite (ret_pc_even (E0 + 200) ER1 ER2) in VIS2.
    rewrite G2, u64_of_Z in AP2, ST2 by lia. rewrite G4 in ERR2.
    pose proof (ah_nodup H HH _ _ _ RH2) as ND. cbn [map] in ND. apply NoDup_cons_iff in ND as [NI _].
    cbn [blk_id fst] in NI.
    eapply (v32c_s3 msF2 mo2 sk2 m2 _ p A junk VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - exact G2.
    - exact G3.
    - exact G4.
    - exact G8.
    - exact G9.
    - reflexivity.
    - exact G18.
    - exact G19.
    - exact G20.
    - exact G21.
    - exact G22.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR2.
    - eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
    - split; [exact MI2|].
      split; [eapply (stk_merge asegs); [exact ST2 | | lia];
              eapply (apres_stk H); [exact AP2 | exact (proj2 (stk_split asegs m1 lo (spz - 112) spz ST1 ltac:(lia))) | lia]|].
      split; [exists errv2; exact ERR2|].
      split; [exact RAX2|]. split; [exact AC2|].
      split; [exact (RFS_via_apres H HH LF LB _ m1 m2 RF1 AP2)|].
      split; [eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]|].
      split; [exact RH2|].
      split; [eapply (apres_rw_cells H); [exact AP2 | exact FR1 | left; lia]|].
      split; [eapply (xpres_trans H); [exact XP1 |];
              eapply (xpres_weaken H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]|].
      split; [exact AL2|].
      apply lb_own_cons; [exact (own_of_rw_cells _ _ _ _ CB2 ltac:(lia)) | exact (lb_own_apres H _ _ _ _ _ OW1 AP2 (fun bb Hb => Hb))].
    - exact ABR.
    - exact NI.
    - exact CB2.
    - exact ADDR.
  Qed.

  Lemma v32c_main : forall (msF : machine_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 E0) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv VIS KR ERR.
    pose proof RUNS as (B1 & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof v32c_vec_facts as (F0 & F1 & F2 & _ & C0 & OB).
    destruct (v32c_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (GZ : gz m v 24) by (intros i Hi; eapply sh0_of_addressable; [exact ADV0 | change (8 * (24 / 8)) with 24; lia]).
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    assert (VSD : v + 24 <= spz - 112 \/ spz <= v) by (destruct OBJ as (_ & _ & _ & _ & _ & SD); lia).
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R0 eqn:HR0.
    assert (HF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
    destruct (B1 R0 F fc m v b cap src spz lo ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity)
                 ltac:(rewrite HR0; exact spz_sp32) AC0 F0 F1 F2 GZ ST0 ltac:(lia) ltac:(lia) SPH
                 ltac:(destruct VBAND; lia) ltac:(destruct VBAND; lia) VSD (proj1 OB0) (proj2 OB0) ltac:(lia))
      as (R1 & M1 & Hms & MU1 & WM1 & FR1 & K1 & K2 & K10 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & KK).
    assert (FRM : rw_cells asegs M1 (spz - 80) FRAME) by (rewrite HR0 in FR1; exact FR1).
    pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    destruct (stack_window_ok H LB LF (spz - 112) spz ltac:(lia) FS2) as (SW1 & SW2 & SW3).
    destruct (client_frame H HH s LB LF B [(spz - 112, spz)] m M1 RH0 RF0 AC0 RA0 MU1 WM1
                ltac:(apply Forall_cons; [exact SW1 | apply Forall_nil]) ltac:(apply Forall_cons; [exact SW2 | apply Forall_nil])
                ltac:(apply Forall_cons; [exact SW3 | apply Forall_nil]))
      as (RH1 & RF1 & AC1 & RA1).
    assert (ST1 : stk asegs M1 lo spz) by (apply (stk_high_transport m M1 lo spz ST0 WM1); unfold AIMG_TOP; lia).
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. split; [lia | exact I]. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S00 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (XP1 : xpres H LB spz [] m M1).
    { eapply (xpres_of_munch H s LB spz [] [(spz - 112, spz)] m m M1); [exact HH | exact RH0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (OW1 : lb_own LB M1) by exact (lb_own_wmono _ _ _ OWN WM1).
    eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R1 HF1) in VIS1.
    eapply (v32c_sn msF1 mo1 M1 R1 errv VIS1 HF1).
    - exact K1.
    - exact K2.
    - rewrite (KK 3%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 4%bv ltac:(inb)), HR0. reflexivity.
    - exact K8.
    - exact K9.
    - exact K10.
    - exact K18.
    - exact K19.
    - exact K20.
    - exact K21.
    - exact K22.
    - exact K23.
    - rewrite (KK 24%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 25%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 26%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 27%bv ltac:(inb)), HR0. reflexivity.
    - exact KR1.
    - exact MP1.
    - exact MI1.
    - exact ST1.
    - exact ERR1.
    - exact RA1.
    - exact AC1.
    - exact RF1.
    - exact S01.
    - exact RH1.
    - exact FRM.
    - exact XP1.
    - exact OW1.
  Qed.
End V4S32.

Theorem v4slow_of_runs {HCEIL : HeapCeil} : forall (H : asr) (c : v4_consts), asan_rt_hyps H ->
  vot_runs (v4_entry c) -> v4_del_ra c = v4_entry c + 488 -> v4_xmax c = 2 ^ 31 ->
  0 <= v4_entry c < 0x200000 /\ v4_entry c mod 4 = 0 ->
  v4slow_stmt H c.
Proof.
  intros H c HH RUNS DRA XM E0R. unfold v4slow_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF
    v b cap src x xs pid lo B shi errv.
  intros VIS -> -> VEC XSL V8 ADV OBJ VBAND VWR OWN OLD OLDSH GROW SRC XR SR4 SR0 SR47 RH KR AOK CM TRO RA SPB SP16 SP47 ST CE LOl
    ERR MI TPV RA2 AC RF S0 SHI.
  rewrite XM in XR.
  pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
  unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LOl.
  eapply v4_main with (src := src) (spz := bv_unsigned sp); try eassumption; try reflexivity.
  all: lazymatch goal with
       | |- _ /\ _ /\ _ mod 16 = 0 => split; [lia|]; split; [exact SP47 | exact SP16]
       | |- _ mod 4 = 0 /\ _ => split; [exact SR4|]; split; [exact SR0 | exact SR47]
       | |- aceil <= _ /\ _ => split; [exact CE | unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK; lia]
       end.
Qed.

Theorem v4slow_of_runs32 {HCEIL : HeapCeil} : forall (H : asr) (c : v4_consts), asan_rt_hyps H ->
  v32_runs (v4_entry c) -> v4_del_ra c = v4_entry c + 484 -> v4_xmax c = 2 ^ 32 ->
  0 <= v4_entry c < 0x200000 /\ v4_entry c mod 4 = 0 ->
  v4slow_stmt H c.
Proof.
  intros H c HH RUNS DRA XM E0R. unfold v4slow_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF
    v b cap src x xs pid lo B shi errv.
  intros VIS -> -> VEC XSL V8 ADV OBJ VBAND VWR OWN OLD OLDSH GROW SRC XR SR4 SR0 SR47 RH KR AOK CM TRO RA SPB SP16 SP47 ST CE LOl
    ERR MI TPV RA2 AC RF S0 SHI.
  rewrite XM in XR.
  pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
  unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LOl.
  eapply v32c_main with (src := src) (spz := bv_unsigned sp); try eassumption; try reflexivity.
  all: lazymatch goal with
       | |- _ /\ _ /\ _ mod 16 = 0 => split; [lia|]; split; [exact SP47 | exact SP16]
       | |- _ mod 4 = 0 /\ _ => split; [exact SR4|]; split; [exact SR0 | exact SR47]
       | |- aceil <= _ /\ _ => split; [exact CE | unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK; lia]
       end.
Qed.

Theorem v4slow_f79f8 {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H -> v4slow_stmt H V32_SLOW_CREF.
Proof.
  intros H HH. apply (v4slow_of_runs32 H V32_SLOW_CREF HH v32_runs_f871c);
    cbn [v4_entry v4_del_ra v4_xmax V32_SLOW_CREF]; [reflexivity | reflexivity | split; [lia | reflexivity]].
Qed.
Theorem v4slow_f7c80 {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H -> v4slow_stmt H V32_SLOW_RREF.
Proof.
  intros H HH. apply (v4slow_of_runs32 H V32_SLOW_RREF HH v32_runs_f898c);
    cbn [v4_entry v4_del_ra v4_xmax V32_SLOW_RREF]; [reflexivity | reflexivity | split; [lia | reflexivity]].
Qed.
Theorem v4slow_fa4fc {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H -> v4slow_stmt H VOT_SLOW_RREF.
Proof.
  intros H HH. apply (v4slow_of_runs H VOT_SLOW_RREF HH vot_runs_fb3d4);
    cbn [v4_entry v4_del_ra v4_xmax VOT_SLOW_RREF]; [reflexivity | reflexivity | split; [lia | reflexivity]].
Qed.
Theorem v4slow_fe724 {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H -> v4slow_stmt H VOT_SLOW_CREF.
Proof.
  intros H HH. apply (v4slow_of_runs H VOT_SLOW_CREF HH vot_runs_100040);
    cbn [v4_entry v4_del_ra v4_xmax VOT_SLOW_CREF]; [reflexivity | reflexivity | split; [lia | reflexivity]].
Qed.
