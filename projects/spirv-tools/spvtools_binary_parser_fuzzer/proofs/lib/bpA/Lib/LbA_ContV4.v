(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0 AsWalk CXXRep RtA_Iface RtA_Annot FakeStackRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_MILB LbA_Own LbA_ContStmt LbA_ContV4R.
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
  change Asan.M.loaded_segments with asegs. rewrite FakeStackRep.find_segment_asegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x91000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x91000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x17c000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x17c000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x185000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x185000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x6e6000); cbn [andb]; try lia; reflexivity.
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
  change (HLPropExec.seg_rom asegs (Z_to_bv 64 (A + i))) with (PropExec.seg_rom asegs (Z_to_bv 64 (A + i))) in B.
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
  exists k, LbA_Kit.shk m src k /\ (k = 0 \/ src mod 8 + 4 <= k < 8).
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

Section V4S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable c : v4_consts.
  Hypothesis RUNS : v4_runs (v4_entry c).
  Hypothesis DRA : v4_del_ra c = v4_entry c + 0x1a4.

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
            (v b cap src x : Z) (xs : list Z) (pid : bptr) (lo B shi spz : Z).
  Hypothesis SPZ : bv_unsigned sp = spz.
  Hypothesis SPR : 2 ^ 45 <= spz - 96 /\ spz <= 2 ^ 47 /\ spz mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis TRO : trace_ok (as_TR H) APC0_FREE [v4_del_ra c].
  Hypothesis VBAND : (0x6e6000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47).
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
  Hypothesis E0R : 0 <= v4_entry c < 0x100000 /\ v4_entry c mod 4 = 0.

  Let E0 := v4_entry c.
  Let cap' := v4_newcap cap.
  Let Q := v4slow_post H c ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap x xs pid lo B shi m mo.
  Let FRAME : list cell := map (fun w => C8 w) [s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra].

  Lemma spz_sp : sp = Z_to_bv 64 spz.
  Proof. rewrite <- SPZ. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Definition v4_mid (sk : as_St H) (mk : mem) (pid' : bptr) (A : Z) (Xk : list (Z * Z)) : Prop :=
    mem_inv asegs mk /\ stk asegs mk lo spz /\ (exists e, rw_cells asegs mk (errno_addr tp) [C4 e]) /\ as_rauxv_ok H mk B
    /\ ACONST mk /\ as_RFS H LF mk /\ stack0 mk lo shi /\ as_RHEAP H sk ((pid', A, 4 * cap') :: LB) mk
    /\ rw_cells asegs mk (spz - 96) FRAME /\ xpres H LB spz Xk m mk /\ as_AL H sk >= as_AL H s - as_Cm H (4 * cap')
    /\ lb_own ((pid', A, 4 * cap') :: LB) mk.

  Definition v4_wk (A : Z) (Xk : list (Z * Z)) (iv : Z * Z) : Prop :=
    (aceil <= fst iv /\ snd iv <= spz - 96)
    \/ (A <= fst iv /\ snd iv <= A + 4 * cap')
    \/ (sh A <= fst iv /\ snd iv <= sh A + nsh (4 * cap'))
    \/ ((forall a, fst iv <= a < snd iv -> rin_ivs Xk a) /\ aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv
        /\ stack0_ok iv /\ (snd iv <= spz - 96 \/ spz <= fst iv) /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)).

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
      - apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity; lia | right; left; lia].
      - eapply (aconst_ok_app A (4 * cap')); [exact BAPP | lia | lia].
      - apply aconst_ok_high; [lia | right; left; lia]. }
    assert (W4 : Forall stack0_ok W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold v4_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & Hw & _)]]]; [| | | exact Hw].
      - left. cbn. unfold AHI_LO. lia.
      - eapply (stack0_ok_aapp A (4 * cap')); [exact BAPP | lia | lia].
      - right. cbn. lia. }
    destruct (client_frame H HH sk _ LF B W mk mk' RH RF AC RA MU WM W1 W2 W3) as (RH' & RF' & AC' & RA').
    split; [exact MI'|]. split; [eapply FakeStackRep.stk_high_transport; [exact ST | exact WM | exact VSPZ]|].
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
    as_VIS H s1' msF1 = MS R1 F (Z_to_bv 64 (E0 + 0x1a4)) fc None m1 (seg_rom asegs) -> rfull R1 ->
    getr R1 2 = Z_to_bv 64 (spz - 96) -> getr R1 3 = gp -> getr R1 4 = tp -> getr R1 8 = Z_to_bv 64 (A + 4 * (cap + 1)) -> getr R1 27 = s11 ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    rw_cells asegs m1 (spz - 96) FRAME ->
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
    intros msF1 mo1 s1' m1 R1 pid' A e1 VIS1 HF1 G2 G3 G4 G8 G27 KR1 MP1 FR1 MI1 ST1 ERR1 RA1 XP1 ABR RH1 VEC1 SH1 ADV1 WV1 OW1 RF1 AC1 S01 AL1.
    destruct RUNS as (_ & _ & _ & _ & _ & _ & B11 & RET).
    destruct SPR as (SPL & SPH & SP16).
    destruct (B11 R1 F fc m1 spz s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra G2 FR1 SPL SPH)
      as (R' & Hms & K1 & K2 & K8 & K9 & K10 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & KK).
    assert (HF' : rfull R') by exact (msteps_full asegs _ _ Hms HF1).
    rewrite G8 in K10.
    assert (K3 : getr R' 3 = gp) by (rewrite (KK 3%bv ltac:(inb)); exact G3).
    assert (K4 : getr R' 4 = tp) by (rewrite (KK 4%bv ltac:(inb)); exact G4).
    assert (K27 : getr R' 27 = s11) by (rewrite (KK 27%bv ltac:(inb)); exact G27).
    eapply (sr_evt H HH) with
      (P := fun ms => ms = MS (mkR ra sp gp tp (getr R' 5) (getr R' 6) (getr R' 7) s0 s1 (Z_to_bv 64 (A + 4 * (cap + 1)))
                                   (getr R' 11) (getr R' 12) (getr R' 13) (getr R' 14) (getr R' 15) (getr R' 16) (getr R' 17)
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (getr R' 28) (getr R' 29) (getr R' 30) (getr R' 31))
                              F (ret_pc ra) fc None m1 (seg_rom asegs));
      [exact KR1 | exact VIS1 | |].
    { eapply evt_of_msteps; [exact Hms|]. rewrite (rfull_eq R' HF'). apply RET.
      rewrite K1, K2, K3, K4, K8, K9, K10, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27. unfold wz. rewrite <- spz_sp. reflexivity. }
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

  Lemma v4_shk4 : forall mk A, addressable mk A 4 -> LbA_Kit.shk mk A 4.
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

  Lemma v4_s9 : forall (msF8 : machine_state) (mo8 : Model) (sk8 : as_St H) (m8 : mem) (R8 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk8 msF8 = MS R8 F (Z_to_bv 64 (E0 + 0x188)) fc None m8 (seg_rom asegs) -> rfull R8 ->
    getr R8 2 = Z_to_bv 64 (spz - 96) -> getr R8 3 = gp -> getr R8 4 = tp -> getr R8 8 = Z_to_bv 64 (v + 8) ->
    getr R8 9 = Z_to_bv 64 (b + 4 * cap) -> getr R8 21 = Z_to_bv 64 b -> getr R8 24 = Z_to_bv 64 (sh (v + 8)) ->
    getr R8 27 = s11 ->
    as_AKREL H sk8 (mkCfg msF8 mo8) -> as_MPRES H mo mo8 ->
    v4_mid sk8 m8 pid' A v4_X1 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m8 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))] ->
    bytes_at asegs m8 A (le4s xs) -> rw_cells asegs m8 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m8 A (cc_gen (4 * cap') (4 * (cap + 1))) -> addressable m8 v 24 ->
    as_SR H Q (mkCfg msF8 mo8).
  Proof.
    intros msF8 mo8 sk8 m8 R8 pid' A VIS8 HF8 G2 G3 G4 G8 G9 G21 G24 G27 KR8 MP8 MID ABR NI HDR BUF XC SHA ADV8.
    pose proof RUNS as (_ & _ & _ & _ & _ & B9 & _ & _).
    pose proof MID as (MI8 & ST8 & (e8 & ERR8) & RA8 & AC8 & RF8 & S08 & RH8 & FR8 & XP8 & AL8 & OW8).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v4_vec_facts as (F0 & F1 & F2 & FE & C0 & OB).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB : 0x6e6000 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47 /\ (b = 0 -> cap = 0) /\ (b <> 0 -> 16 <= b)).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia|].
      split; [lia|]. split; [lia|]. split; [intros E; lia|]. intros _. exact (v4_mod16_16le b O0 O16). }
    destruct OB0 as (OB1 & OB2 & OB3 & OB4).
    pose proof (rw_cells_split3 _ _ _ _ _ HDR) as (HC0 & HC8 & HC16).
    assert (F8A : fldA m8 (v + 8) 8 (A + 4 * cap + 4)).
    { replace (A + 4 * cap + 4) with (A + 4 * (cap + 1)) by lia. apply fld_of_rw_cells8; [exact HC8 | lia]. }
    assert (GZ : gz m8 v 24) by (intros i Hi; eapply sh0_of_addressable; [exact ADV8 | change (8 * (24 / 8)) with 24; lia]).
    assert (SPL' : 2 ^ 45 <= spz - 96) by lia.
    assert (CR : 0 <= cap <= 2 ^ 24) by lia.
    assert (AH : A + 4 * cap + 4 <= 2 ^ 47) by lia.
    destruct (B9 R8 F fc m8 v b cap A spz G2 G8 G9 G21 G24 F8A GZ SPL' SPH (proj1 VB) (proj2 VB) AI AH OB1 OB2 CR OB3 OB4)
      as (R9 & M9 & HB9a & HB9b & EM9 & G98).
    subst M9.
    assert (HNEW : v + 24 <= A \/ A + 4 * cap' <= v) by (eapply v4_hdr_fresh; [exact RH8 | exact NI | lia]).
    assert (VEC9 : forall m9 LB9, rw_cells asegs m9 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))] ->
              bytes_at asegs m9 A (le4s xs) -> rw_cells asegs m9 (A + 4 * cap) [C4 (Z_to_bv 64 x)] -> In (A, 4 * cap') (lbl LB9) ->
              vec32A LB9 m9 v A (xs ++ [x]) cap').
    { intros m9 LB9 H1 H2 H3 H4. apply v4_vec32_new; [rewrite XSL; exact H1 | exact H2 | rewrite XSL; exact H3 | exact XR
        | intros i Hi; rewrite XSL in Hi; exact (proj1 (FE i Hi)) | lia | exact A16 | rewrite XSL; lia | lia | exact H4 | exact HNEW
        | unfold AIMG_TOP; lia | lia]. }
    destruct (Z.eq_dec b 0) as [Z0|NZ].
    -
      destruct (HB9b Z0) as [Hms KK].
      pose proof (msteps_full asegs _ _ Hms HF8) as HF9. cbn [ms_regs] in HF9.
      eapply (sr_blk H HH); [exact KR8 | exact VIS8 | exact HF8 | exact Hms |].
      intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R9 HF9) in VIS1.
      eapply (v4_s_end msF1 mo1 sk8 m8 R9 pid' A e8 VIS1 HF9).
      + rewrite (KK 2%bv ltac:(inb)). exact G2.
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite G98. unfold wz. f_equal. lia.
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
      destruct (HB9a NZ) as (Hms & K1 & K10 & K11 & KK).
      pose proof (msteps_full asegs _ _ Hms HF8) as HF9. cbn [ms_regs] in HF9.
      eapply (sr_blk H HH); [exact KR8 | exact VIS8 | exact HF8 | exact Hms |].
      intros msF9 mo9 KR9 MP9 VIS9.
      assert (K2 : getr R9 2 = Z_to_bv 64 (spz - 96)) by (rewrite (KK 2%bv ltac:(inb)); exact G2).
      assert (K4 : getr R9 4 = tp) by (rewrite (KK 4%bv ltac:(inb)); exact G4).
      assert (HINx : In (pid, b, 4 * cap) ((pid', A, 4 * cap') :: LB)) by (right; exact HIn).
      destruct (rw_cells_of_own _ m8 (pid, b, 4 * cap) OW8 HINx ltac:(cbn [blk_addr blk_size fst snd]; exact OI) ltac:(cbn [blk_addr blk_size fst snd]; lia)) as (obs & OC8).
      cbn [blk_addr blk_size fst snd] in OC8.
      destruct (v4_blk_shad sk8 m8 _ pid b (4 * cap) RH8 HINx) as (sbs & SHB & SHL).
      assert (CFB : as_Cf H (4 * cap) <= as_AL H sk8) by (pose proof CM as CM'; change (v4_newcap cap) with cap' in CM'; lia).
      assert (SP96 : (spz - 96) mod 16 = 0) by exact (v4_mod16_sub96 spz SP16).
      destruct (v4_E0_even 0x1a4 ltac:(lia) eq_refl) as [ER1 ER2].
      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (p := pid) (A := b) (n := 4 * cap) (LB := (pid', A, 4 * cap') :: LB) (lo := lo) (B := B)
          (errv := e8) (CH := []) (bs := obs) (sbs := sbs);
          [ exact VIS9 | exact RH8 | exact KR9 | exact HINx | exact CFB | exact OC8 | exact SHB | exact SHL
          | exact RA8 | rewrite K2, u64_of_Z by lia; lia
          | rewrite K2, u64_of_Z by lia; exact (proj1 (stk_split asegs m8 lo (spz - 96) spz ST8 ltac:(lia)))
          | exact LO1 | rewrite K2, u64_of_Z by lia; unfold AFREE_STACK; lia
          | rewrite K4; exact ERR8 | exact MI8 | rewrite K4; exact TPV | rewrite K2, u64_of_Z by lia; exact SP96 | exact AC8
          | rewrite G98; unfold wz; rewrite u64_of_Z by lia; apply (ah_chain_nil H HH); left; lia
          | rewrite K1; cbn [map]; unfold wz; rewrite u64_of_Z by lia; rewrite <- DRA; exact TRO
          | exact K10 ]. }
      intros c2 POST. destruct c2 as [msF2 mo2].
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m9 & s9'
                        & VIS2 & KR2 & MP2 & MI9 & ST9 & ERR9 & RA9 & AP9 & RH9 & AC9 & AL9).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite K1 in VIS2. unfold wz in VIS2. rewrite (ret_pc_even (v4_entry c + 0x1a4) ER1 ER2) in VIS2.
      rewrite K2, u64_of_Z in ST9, AP9 by lia. rewrite K4 in ERR9.

      assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 4 * cap); split; [reflexivity | exact HIn]).
      pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
      assert (RMx : as_lb_remove H pid ((pid', A, 4 * cap') :: LB) = (pid', A, 4 * cap') :: as_lb_remove H pid LB).
      { apply L2. cbn [blk_id fst]. exact NEQ. }
      rewrite RMx in AP9, RH9.

      assert (XPF0 : xpres H LB (spz - 96) (v4_oldx b (4 * cap)) m8 m9).
      { eapply (xpres_of_apres_rm H HH sk8 LB ((pid', A, 4 * cap') :: LB) (spz - 96) _ m8 m8 m9 pid b (4 * cap) RH8 HINx);
          [intros bb Hb; right; exact Hb | rewrite RMx; exact AP9 | |].
        - intros a Ha. unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. left. cbn [fst snd]. lia.
        - intros a Ha. unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. right. left. cbn [fst snd]. lia. }
      assert (XPF : xpres H LB spz (v4_oldx b (4 * cap)) m8 m9)
        by (eapply (xpres_weaken H); [exact XPF0 | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]).
      assert (HDR9 : rw_cells asegs m9 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))]).
      { eapply (xpres_rw_cells H); [exact XPF | exact HDR | exact (v4_xc_hdr Hc)]. }
      assert (INA : In (pid', A, 4 * cap') ((pid', A, 4 * cap') :: as_lb_remove H pid LB)) by (left; reflexivity).
      eapply (v4_s_end msF2 mo2 s9' m9 _ pid' A e8 VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
      + exact K2.
      + exact (eq_trans (KK 3%bv ltac:(inb)) G3).
      + exact K4.
      + replace (Z_to_bv 64 (A + 4 * (cap + 1))) with (wz (A + 4 * cap + 4)) by (unfold wz; f_equal; lia). exact G98.
      + exact (eq_trans (KK 27%bv ltac:(inb)) G27).
      + exact KR2.
      + eapply (ah_mpres_trans H HH); [exact MP8 | eapply (ah_mpres_trans H HH); [exact MP9 | exact MP2]].
      + eapply (apres_rw_cells H); [exact AP9 | exact FR8 | left; lia].
      + exact MI9.
      + eapply (stk_merge asegs); [exact ST9 | | lia].
        eapply (apres_stk H); [exact AP9 | exact (proj2 (stk_split asegs m8 lo (spz - 96) spz ST8 ltac:(lia))) | lia].
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

  Let HANN : annotate_gen_stmt := annotate_gen_ok.

  Lemma v4_s8 : forall (msF7 : machine_state) (mo7 : Model) (sk7 : as_St H) (m7 : mem) (R7 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk7 msF7 = MS R7 F (Z_to_bv 64 AANNOTATE_CC) fc None m7 (seg_rom asegs) -> rfull R7 ->
    getr R7 1 = Z_to_bv 64 (E0 + 0x188) -> getr R7 2 = Z_to_bv 64 (spz - 96) -> getr R7 3 = gp -> getr R7 4 = tp ->
    getr R7 8 = Z_to_bv 64 (v + 8) -> getr R7 9 = Z_to_bv 64 (b + 4 * cap) -> getr R7 10 = Z_to_bv 64 A ->
    getr R7 11 = Z_to_bv 64 (A + 4 * cap') -> getr R7 12 = Z_to_bv 64 (A + 4 * cap') -> getr R7 13 = Z_to_bv 64 (A + 4 * cap + 4) ->
    getr R7 21 = Z_to_bv 64 b -> getr R7 24 = Z_to_bv 64 (sh (v + 8)) -> getr R7 27 = s11 ->
    as_AKREL H sk7 (mkCfg msF7 mo7) -> as_MPRES H mo mo7 ->
    v4_mid sk7 m7 pid' A v4_X1 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m7 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * (cap + 1))); C8 (Z_to_bv 64 (A + 4 * cap'))] ->
    bytes_at asegs m7 A (le4s xs) -> rw_cells asegs m7 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m7 A (cc_gen (4 * cap') (4 * cap')) -> addressable m7 v 24 ->
    as_SR H Q (mkCfg msF7 mo7).
  Proof.
    intros msF7 mo7 sk7 m7 R7 pid' A VIS7 HF7 G1 G2 G3 G4 G8 G9 G10 G11 G12 G13 G21 G24 G27 KR7 MP7 MID ABR NI HDR BUF XC SHA ADV7.
    pose proof MID as (MI7 & ST7 & _ & _ & AC7 & _ & _ & RH7 & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v4_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
    assert (HNEW : v + 24 <= A \/ A + 4 * cap' <= v) by (eapply v4_hdr_fresh; [exact RH7 | exact NI | lia]).
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
      - rewrite G2, u64_of_Z by lia. exact (proj1 (stk_split asegs m7 lo (spz - 96) spz ST7 ltac:(lia))).
      - exact LO1.
      - rewrite G2, u64_of_Z by lia. unfold AINTRIN_STACK. lia.
      - exact MI7.
      - exact AC7.
      - unfold in_app_mem. destruct (v4_band_of_aapp _ _ AAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia. }
    intros msF8 mo8 KR8 MP8 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m8
                      & VIS8 & MU8 & WM8 & MI8 & ST8 & SH8 & AC8).
    rewrite G2, u64_of_Z in MU8, ST8 by lia. unfold AINTRIN_STACK in MU8.
    rewrite G1 in VIS8. destruct (v4_E0_even 0x188 ltac:(lia) eq_refl) as [ER1 ER2].
    rewrite (ret_pc_even (E0 + 0x188) ER1 ER2) in VIS8.
    assert (W8 : Forall (v4_wk A v4_X1) [(sh A, sh A + nsh (4 * cap')); (spz - 96 - 4096, spz - 96)]).
    { apply Forall_cons; [right; right; left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (DSV : disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 96 - 4096, spz - 96)] v 24).
    { pose proof (v4_app_sh v 24 A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) VB) as D. destruct OBJ as (_ & _ & _ & _ & _ & SD).
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSA : disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 96 - 4096, spz - 96)] A (4 * cap')).
    { pose proof (v4_app_sh A (4 * cap') A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) (v4_band_of_aapp _ _ AAP)) as D.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSS : disjoint_from [(sh A, sh A + nsh (4 * cap')); (spz - 96 - 4096, spz - 96)] (sh v) (nsh 24)).
    { pose proof (v4_sh_apart v 24 A (4 * cap') ltac:(lia) ltac:(lia) V8 (v4_mod16_8 A A16) ltac:(lia) ltac:(lia) HNEW) as D.
      pose proof (sh_nsh_high v 24 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; destruct VBAND; lia)) as D2. unfold AHI_LO in D2.
      cbn. split; [lia | split; [lia | exact I]]. }
    eapply (v4_s9 msF8 mo8 sk7 m8 _ pid' A VIS8 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - exact G2.
    - exact G3.
    - exact G4.
    - exact G8.
    - exact G9.
    - exact G21.
    - exact G24.
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
    - eapply addressable_transport; [exact ADV7 | exact MU8 | exact WM8 | exact DSS].
  Qed.

  Lemma v4_s7 : forall (msF6 : machine_state) (mo6 : Model) (sk6 : as_St H) (m6 : mem) (R6 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk6 msF6 = MS R6 F (Z_to_bv 64 (E0 + 0x158)) fc None m6 (seg_rom asegs) -> rfull R6 ->
    getr R6 2 = Z_to_bv 64 (spz - 96) -> getr R6 3 = gp -> getr R6 4 = tp -> getr R6 8 = Z_to_bv 64 (v + 8) ->
    getr R6 9 = Z_to_bv 64 v -> getr R6 18 = Z_to_bv 64 (v + 16) -> getr R6 19 = Z_to_bv 64 (4 * cap') ->
    getr R6 20 = Z_to_bv 64 A -> getr R6 22 = Z_to_bv 64 A -> getr R6 23 = Z_to_bv 64 (A + 4 * cap + 4) ->
    getr R6 24 = Z_to_bv 64 (sh (v + 8)) -> getr R6 25 = Z_to_bv 64 (sh (v + 16)) -> getr R6 26 = Z_to_bv 64 ASHADOW_BASE ->
    getr R6 27 = s11 ->
    as_AKREL H sk6 (mkCfg msF6 mo6) -> as_MPRES H mo mo6 ->
    v4_mid sk6 m6 pid' A v4_X0 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    bytes_at asegs m6 A (le4s xs) -> rw_cells asegs m6 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m6 A (cc_gen (4 * cap') (4 * cap')) ->
    as_SR H Q (mkCfg msF6 mo6).
  Proof.
    intros msF6 mo6 sk6 m6 R6 pid' A VIS6 HF6 G2 G3 G4 G8 G9 G18 G19 G20 G22 G23 G24 G25 G26 G27 KR6 MP6 MID ABR NI BUF XC SHA.
    pose proof RUNS as (_ & _ & _ & _ & B7 & _ & _ & _).
    pose proof MID as (MI6 & ST6 & _ & _ & _ & _ & _ & RH6 & _ & XP6 & _ & _).
    pose proof SPR as (SPL & SPH & SP16).
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v4_vec_facts as (_ & _ & _ & _ & C0 & OB).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
    assert (VB2 : 0x6e6000 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    assert (VAPP : v + 24 <= 0x7fff8000 \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
    assert (HNEW : v + 24 <= A \/ A + 4 * cap' <= v) by (eapply v4_hdr_fresh; [exact RH6 | exact NI | lia]).
    destruct (v4_hdr_X0 m6 XP6) as (F0 & _ & F16 & ADV6 & WV6).
    assert (GZ : gz m6 v 24) by (intros i Hi; eapply sh0_of_addressable; [exact ADV6 | change (8 * (24 / 8)) with 24; lia]).
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    destruct (B7 R6 F fc m6 v b cap cap' A spz G2 G8 G9 G18 G19 G20 G22 G23 G24 G25 G26 F0 F16 GZ WV6 SPL SPH (proj1 VB2) (proj2 VB2) VAPP
                 AI ltac:(lia) (proj1 OB0) (proj2 OB0) ltac:(lia) ltac:(lia))
      as (R7 & M7 & Hms & MU7 & WM7 & HC7 & K1 & K9 & K10 & K11 & K12 & K13 & K21 & KK).
    pose proof (msteps_full asegs _ _ Hms HF6) as HF7. cbn [ms_regs] in HF7.
    assert (MI7 : mem_inv asegs M7) by exact (msteps_mem_inv asegs _ _ Hms MI6).
    eapply (sr_blk H HH); [exact KR6 | exact VIS6 | exact HF6 | exact Hms |].
    intros msF7 mo7 KR7 MP7 VIS7. rewrite <- (rfull_eq R7 HF7) in VIS7.
    assert (DV : disjoint_from [(v, v + 24)] A (4 * cap')) by (cbn; split; [lia | exact I]).
    eapply (v4_s8 msF7 mo7 sk6 M7 R7 pid' A VIS7 HF7).
    - exact K1.
    - rewrite (KK 2%bv ltac:(inb)). exact G2.
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - rewrite (KK 8%bv ltac:(inb)). exact G8.
    - exact K9.
    - exact K10.
    - exact K11.
    - exact K12.
    - exact K13.
    - exact K21.
    - rewrite (KK 24%bv ltac:(inb)). exact G24.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR7.
    - eapply (ah_mpres_trans H HH); [exact MP6 | exact MP7].
    - eapply v4_mid_munch; [eapply v4_mid_weaken; [exact MID | intros a Ha; right; exact Ha] | exact ABR | exact NI
                           | exact MU7 | exact WM7 | exact MI7 |].
      apply Forall_cons; [apply v4_wk_hdr; intros a Ha; left; cbn [fst snd]; lia | apply Forall_nil].
    - exact ABR.
    - exact NI.
    - replace (A + 4 * (cap + 1)) with (A + 4 * cap + 4) by lia. exact HC7.
    - eapply bytes_at_transport; [exact BUF | exact MU7 |]. eapply v4_dj_sub; [exact DV | lia | rewrite le4s_length; unfold Zlen in XSL; lia].
    - eapply rw_cells_transport; [exact XC | exact MU7 | exact WM7 |]. cbn [cells_size csize Nat.add Z.of_nat].
      eapply v4_dj_sub; [exact DV | lia | lia].
    - eapply SHAD_transport; [exact SHA | exact MU7 | exact WM7 |]. rewrite cc_gen_length by lia.
      pose proof (v4_app_sh v 24 A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) VB) as D. cbn. split; [lia | exact I].
    - eapply addressable_transport; [exact ADV6 | exact MU7 | exact WM7 |].
      pose proof (v4_app_sh v 24 v 24 ltac:(lia) ltac:(lia) ltac:(lia) VB) as D. cbn. split; [lia | exact I].
  Qed.

  Lemma v4_s6 : forall (msF5 : machine_state) (mo5 : Model) (sk5 : as_St H) (m5 : mem) (R5 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    as_VIS H sk5 msF5 = MS R5 F (Z_to_bv 64 AASAN_MEMCPY) fc None m5 (seg_rom asegs) -> rfull R5 ->
    getr R5 1 = Z_to_bv 64 (E0 + 0x158) -> getr R5 2 = Z_to_bv 64 (spz - 96) -> getr R5 3 = gp -> getr R5 4 = tp ->
    getr R5 8 = Z_to_bv 64 (v + 8) -> getr R5 9 = Z_to_bv 64 v -> getr R5 10 = Z_to_bv 64 A -> getr R5 11 = Z_to_bv 64 b ->
    getr R5 12 = Z_to_bv 64 (4 * cap) -> getr R5 18 = Z_to_bv 64 (v + 16) -> getr R5 19 = Z_to_bv 64 (4 * cap') ->
    getr R5 20 = Z_to_bv 64 A -> getr R5 22 = Z_to_bv 64 A -> getr R5 23 = Z_to_bv 64 (A + 4 * cap + 4) ->
    getr R5 24 = Z_to_bv 64 (sh (v + 8)) -> getr R5 25 = Z_to_bv 64 (sh (v + 16)) -> getr R5 26 = Z_to_bv 64 ASHADOW_BASE ->
    getr R5 27 = s11 ->
    as_AKREL H sk5 (mkCfg msF5 mo5) -> as_MPRES H mo mo5 ->
    v4_mid sk5 m5 pid' A v4_X0 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m5 A [CB (Z.to_nat (4 * cap)) jA] -> rw_cells asegs m5 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m5 A (cc_gen (4 * cap') (4 * cap')) -> (0 < cap -> SHAD m5 b (cc_gen (4 * cap) (4 * cap))) ->
    as_SR H Q (mkCfg msF5 mo5).
  Proof.
    intros msF5 mo5 sk5 m5 R5 pid' A jA VIS5 HF5 G1 G2 G3 G4 G8 G9 G10 G11 G12 G18 G19 G20 G22 G23 G24 G25 G26 G27 KR5 MP5
      MID ABR NI CBA XC SHA OSH.
    pose proof MID as (MI5 & ST5 & _ & _ & AC5 & _ & _ & RH5 & _ & XP5 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v4_vec_facts as (_ & _ & _ & FE & C0 & OB).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
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
      - exact (proj1 (stk_split asegs m5 lo (spz - 96) spz ST5 ltac:(lia))).
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
    rewrite G1 in VIS6. destruct (v4_E0_even 0x158 ltac:(lia) eq_refl) as [ER1 ER2].
    rewrite (ret_pc_even (E0 + 0x158) ER1 ER2) in VIS6.
    assert (W6 : Forall (v4_wk A v4_X0) [(A, A + 4 * cap); (spz - 96 - 4096, spz - 96)]).
    { apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    eapply (v4_s7 msF6 mo6 sk5 m6 _ pid' A VIS6 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - exact G2.
    - exact G3.
    - exact G4.
    - exact G8.
    - exact G9.
    - exact G18.
    - exact G19.
    - exact G20.
    - exact G22.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR6.
    - eapply (ah_mpres_trans H HH); [exact MP5 | exact MP6].
    - eapply v4_mid_munch; [exact MID | exact ABR | exact NI | exact MU6 | exact WM6 | exact MI6 | exact W6].
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
    as_VIS H sk4 msF4 = MS R4 F (Z_to_bv 64 (E0 + 0x12c)) fc None m4 (seg_rom asegs) -> rfull R4 ->
    getr R4 2 = Z_to_bv 64 (spz - 96) -> getr R4 3 = gp -> getr R4 4 = tp -> getr R4 8 = Z_to_bv 64 (v + 8) ->
    getr R4 9 = Z_to_bv 64 v -> getr R4 18 = Z_to_bv 64 (v + 16) -> getr R4 19 = Z_to_bv 64 (4 * cap') ->
    getr R4 20 = Z_to_bv 64 A -> getr R4 22 = Z_to_bv 64 (A + 4 * cap) -> getr R4 23 = Z_to_bv 64 (sh v) ->
    getr R4 24 = Z_to_bv 64 (sh (v + 8)) -> getr R4 25 = Z_to_bv 64 (sh (v + 16)) -> getr R4 26 = Z_to_bv 64 ASHADOW_BASE ->
    getr R4 27 = s11 ->
    as_AKREL H sk4 (mkCfg msF4 mo4) -> as_MPRES H mo mo4 ->
    v4_mid sk4 m4 pid' A v4_X0 -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m4 A [CB (Z.to_nat (4 * cap)) jA] -> rw_cells asegs m4 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m4 A (cc_gen (4 * cap') (4 * cap')) -> SHAD m4 b (cc_gen (4 * cap) (4 * cap)) ->
    as_SR H Q (mkCfg msF4 mo4).
  Proof.
    intros msF4 mo4 sk4 m4 R4 pid' A jA Hc VIS4 HF4 G2 G3 G4 G8 G9 G18 G19 G20 G22 G23 G24 G25 G26 G27 KR4 MP4 MID ABR NI CBA XC SHA OSH.
    pose proof RUNS as (_ & _ & _ & B5 & _ & _ & _ & _).
    pose proof MID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & XP4 & _ & _).
    pose proof SPR as (SPL & SPH & SP16).
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof v4_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    destruct (v4_old_facts Hc) as (HIn & (O0 & O16 & On & OI & OC & OF & OAP) & OD & NZ).
    assert (VB2 : 0x6e6000 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    destruct (v4_hdr_X0 m4 XP4) as (F0 & F8 & F16 & ADV4 & _).
    assert (GZ : gz m4 v 24) by (intros i Hi; eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
    destruct (B5 R4 F fc m4 v b cap A spz G2 G8 G9 G18 G20 G22 G23 G24 G25 G26 F0 F8 F16 GZ SPL SPH (proj1 VB2) (proj2 VB2)
                 AI ltac:(lia) (v4_mod16_16le b O0 O16) ltac:(lia) ltac:(lia))
      as (R5 & M5 & Hms & EM5 & K1 & K10 & K11 & K12 & K22 & K23 & KK).
    subst M5.
    pose proof (msteps_full asegs _ _ Hms HF4) as HF5. cbn [ms_regs] in HF5.
    eapply (sr_blk H HH); [exact KR4 | exact VIS4 | exact HF4 | exact Hms |].
    intros msF5 mo5 KR5 MP5 VIS5. rewrite <- (rfull_eq R5 HF5) in VIS5.
    eapply (v4_s6 msF5 mo5 sk4 m4 R5 pid' A jA VIS5 HF5).
    - exact K1.
    - rewrite (KK 2%bv ltac:(inb)). exact G2.
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - rewrite (KK 8%bv ltac:(inb)). exact G8.
    - rewrite (KK 9%bv ltac:(inb)). exact G9.
    - exact K10.
    - exact K11.
    - exact K12.
    - rewrite (KK 18%bv ltac:(inb)). exact G18.
    - rewrite (KK 19%bv ltac:(inb)). exact G19.
    - rewrite (KK 20%bv ltac:(inb)). exact G20.
    - exact K22.
    - exact K23.
    - rewrite (KK 24%bv ltac:(inb)). exact G24.
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

  Lemma v4_s4 : forall (msF3 : machine_state) (mo3 : Model) (sk3 : as_St H) (m3 : mem) (R3 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    0 < cap ->
    as_VIS H sk3 msF3 = MS R3 F (Z_to_bv 64 AANNOTATE_CC) fc None m3 (seg_rom asegs) -> rfull R3 ->
    getr R3 1 = Z_to_bv 64 (E0 + 0x12c) -> getr R3 2 = Z_to_bv 64 (spz - 96) -> getr R3 3 = gp -> getr R3 4 = tp ->
    getr R3 8 = Z_to_bv 64 (v + 8) -> getr R3 9 = Z_to_bv 64 v -> getr R3 10 = Z_to_bv 64 b ->
    getr R3 11 = Z_to_bv 64 (b + 4 * cap) -> getr R3 12 = Z_to_bv 64 (b + 4 * cap) -> getr R3 13 = Z_to_bv 64 (b + 4 * cap) ->
    getr R3 18 = Z_to_bv 64 (v + 16) -> getr R3 19 = Z_to_bv 64 (4 * cap') ->
    getr R3 20 = Z_to_bv 64 A -> getr R3 22 = Z_to_bv 64 (A + 4 * cap) -> getr R3 23 = Z_to_bv 64 (sh v) ->
    getr R3 24 = Z_to_bv 64 (sh (v + 8)) -> getr R3 25 = Z_to_bv 64 (sh (v + 16)) -> getr R3 26 = Z_to_bv 64 ASHADOW_BASE ->
    getr R3 27 = s11 ->
    as_AKREL H sk3 (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
    v4_mid sk3 m3 pid' A [] -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m3 A [CB (Z.to_nat (4 * cap)) jA] -> rw_cells asegs m3 (A + 4 * cap) [C4 (Z_to_bv 64 x)] ->
    SHAD m3 A (cc_gen (4 * cap') (4 * cap')) ->
    as_SR H Q (mkCfg msF3 mo3).
  Proof.
    intros msF3 mo3 sk3 m3 R3 pid' A jA Hc VIS3 HF3 G1 G2 G3 G4 G8 G9 G10 G11 G12 G13 G18 G19 G20 G22 G23 G24 G25 G26 G27 KR3 MP3
      MID ABR NI CBA XC SHA.
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
      - rewrite G2, u64_of_Z by lia. exact (proj1 (stk_split asegs m3 lo (spz - 96) spz ST3 ltac:(lia))).
      - exact LO1.
      - rewrite G2, u64_of_Z by lia. unfold AINTRIN_STACK. lia.
      - exact MI3.
      - exact AC3.
      - unfold in_app_mem. destruct (v4_band_of_aapp _ _ OAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia. }
    intros msF4 mo4 KR4 MP4 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4
                      & VIS4 & MU4 & WM4 & MI4 & ST4 & SH4 & AC4).
    rewrite G2, u64_of_Z in MU4, ST4 by lia. unfold AINTRIN_STACK in MU4.
    rewrite G1 in VIS4. destruct (v4_E0_even 0x12c ltac:(lia) eq_refl) as [ER1 ER2].
    rewrite (ret_pc_even (E0 + 0x12c) ER1 ER2) in VIS4.
    assert (W4 : Forall (v4_wk A v4_X0) [(sh b, sh b + nsh (4 * cap)); (spz - 96 - 4096, spz - 96)]).
    { apply Forall_cons; [|apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]].
      apply (v4_wk_oldsh Hc). intros a Ha. unfold v4_X0. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. left. cbn [fst snd]. lia. }
    pose proof (v4_app_sh A (4 * cap') b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (v4_band_of_aapp _ _ AAP)) as DAS.
    pose proof (v4_sh_apart A (4 * cap') b (4 * cap) ltac:(lia) ltac:(lia) (v4_mod16_8 A A16) (v4_mod16_8 b O16) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as DSS.
    pose proof (sh_nsh_high A (4 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHA2. unfold AHI_LO in SHA2.
    eapply (v4_s5 msF4 mo4 sk3 m4 _ pid' A jA Hc VIS4 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - exact G2.
    - exact G3.
    - exact G4.
    - exact G8.
    - exact G9.
    - exact G18.
    - exact G19.
    - exact G20.
    - exact G22.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR4.
    - eapply (ah_mpres_trans H HH); [exact MP3 | exact MP4].
    - eapply v4_mid_munch; [eapply v4_mid_weaken; [exact MID | intros a Ha; destruct Ha] | exact ABR | exact NI
                           | exact MU4 | exact WM4 | exact MI4 | exact W4].
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
    as_VIS H sk2 msF2 = MS R2 F (Z_to_bv 64 (E0 + 0xcc)) fc None m2 (seg_rom asegs) -> rfull R2 ->
    getr R2 2 = Z_to_bv 64 (spz - 96) -> getr R2 3 = gp -> getr R2 4 = tp -> getr R2 8 = Z_to_bv 64 (v + 8) ->
    getr R2 9 = Z_to_bv 64 v -> getr R2 10 = Z_to_bv 64 A -> getr R2 18 = Z_to_bv 64 (v + 16) -> getr R2 19 = Z_to_bv 64 (4 * cap') ->
    getr R2 21 = Z_to_bv 64 src -> getr R2 22 = Z_to_bv 64 (4 * cap) -> getr R2 23 = Z_to_bv 64 (sh v) ->
    getr R2 24 = Z_to_bv 64 (sh (v + 8)) -> getr R2 25 = Z_to_bv 64 (sh (v + 16)) -> getr R2 26 = Z_to_bv 64 ASHADOW_BASE ->
    getr R2 27 = s11 ->
    as_AKREL H sk2 (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
    v4_mid sk2 m2 pid' A [] -> ablock_range H A (4 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m2 A [CB (Z.to_nat (4 * cap')) jall] -> addressable m2 A (4 * cap') ->
    as_SR H Q (mkCfg msF2 mo2).
  Proof.
    intros msF2 mo2 sk2 m2 R2 pid' A jall VIS2 HF2 G2 G3 G4 G8 G9 G10 G18 G19 G21 G22 G23 G24 G25 G26 G27 KR2 MP2 MID ABR NI
      CBall ADD2.
    pose proof RUNS as (_ & B3a & B3b & _ & _ & _ & _ & _).
    pose proof MID as (MI2 & ST2 & _ & _ & AC2 & _ & _ & RH2 & _ & XP2 & _ & _).
    pose proof SPR as (SPL & SPH & SP16).
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof (v4_band_of_aapp _ _ AAP) as ABND.
    pose proof v4_vec_facts as (_ & _ & _ & _ & C0 & OB).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB2 : 0x6e6000 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    assert (HNEW : v + 24 <= A \/ A + 4 * cap' <= v) by (eapply v4_hdr_fresh; [exact RH2 | exact NI | lia]).
    assert (XP2' : xpres H LB spz v4_X0 m m2)
      by (eapply (xpres_weaken H); [exact XP2 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
    destruct (v4_hdr_X0 m2 XP2') as (F0 & F8 & F16 & ADV2 & _).
    assert (GZ : gz m2 v 24) by (intros i Hi; eapply sh0_of_addressable; [exact ADV2 | change (8 * (24 / 8)) with 24; lia]).
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }

    destruct (SRC m2 AC2 MI2 (apres_of_xpres_nil m2 XP2)) as [FS ACS].
    pose proof SRCR as (SR4 & SR0 & SR47).
    destruct (v4_src_shk m2 src ACS SR4 SR0) as (k & SK & KR).

    destruct (rw_cells_CB_split asegs m2 A (Z.to_nat (4 * cap')) (Z.to_nat (4 * cap)) jall CBall ltac:(lia)) as [CBA REST].
    rewrite Z2Nat.id in REST by lia.
    assert (WSL : wr_at asegs m2 (A + 4 * cap) 4).
    { eapply v4_wr_sub; [exact (proj2 REST) | lia | | lia]. cbn [cells_size csize]. lia. }
    assert (B3P : v4_B3pre R2 m2 v b cap A src x k spz).
    { unfold v4_B3pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia. }
    assert (SHA0 : SHAD m2 A (cc_gen (4 * cap') (4 * cap'))) by (rewrite cc_gen_full; exact (proj2 ADD2)).
    pose proof (msteps_full asegs) as MSF.
    destruct OB as [[E1 E2]|(Hc & HIn & ABb)].
    -
      rewrite E1, E2 in B3P.
      assert (C1 : cap' = 1) by (unfold cap', v4_newcap; rewrite E2; reflexivity).
      assert (SK4 : LbA_Kit.shk m2 A 4).
      { apply v4_shk4. pose proof ADD2 as ADD2'. rewrite C1 in ADD2'. exact ADD2'. }
      destruct (B3b R2 F fc m2 v A src x k spz B3P SK4)
        as (R3 & M3 & Hms & MU3 & WM3 & XC3 & K1 & K10 & K11 & K12 & K20 & K22 & K23 & KK).
      pose proof (MSF _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
      assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
      eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
      intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
      eapply (v4_s6 msF3 mo3 sk2 M3 R3 pid' A [] VIS3 HF3).
      + exact K1.
      + rewrite (KK 2%bv ltac:(inb)). exact G2.
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 8%bv ltac:(inb)). exact G8.
      + rewrite (KK 9%bv ltac:(inb)). exact G9.
      + exact K10.
      + rewrite E1. exact K11.
      + rewrite E2. exact K12.
      + rewrite (KK 18%bv ltac:(inb)). exact G18.
      + rewrite (KK 19%bv ltac:(inb)). exact G19.
      + exact K20.
      + exact K22.
      + rewrite E2. replace (A + 4 * 0 + 4) with (A + 4) by lia. exact K23.
      + rewrite (KK 24%bv ltac:(inb)). exact G24.
      + rewrite (KK 25%bv ltac:(inb)). exact G25.
      + rewrite (KK 26%bv ltac:(inb)). exact G26.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR3.
      + eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
      + eapply (v4_mid_weaken _ _ _ _ [] v4_X0); [| intros a Ha; destruct Ha].
        eapply v4_mid_munch; [exact MID | exact ABR | exact NI | exact MU3 | exact WM3 | exact MI3 |].
        apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_nil].
      + exact ABR.
      + exact NI.
      + rewrite E2. change (Z.to_nat (4 * 0)) with 0%nat. apply v4_CB0. lia.
      + rewrite E2. replace (A + 4 * 0) with A by lia. exact XC3.
      + eapply SHAD_transport; [exact SHA0 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia.
        pose proof (v4_app_sh A 4 A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct ABND; [left|right]; lia)) as D.
        cbn. split; [lia | exact I].
      + intros Hc. lia.
    -
      assert (SH0 : LbA_Kit.sh0 m2 (A + 4 * cap)).
      { eapply sh0_of_addressable; [exact ADD2|]. pose proof (v4_new_granule cap ltac:(lia)) as NG.
        change (vgrow cap) with cap' in NG. lia. }
      pose proof ABb as (O0 & O16 & On & OI & OC & OF & OAP).
      destruct (B3a R2 F fc m2 v b cap A src x k spz B3P (v4_mod16_16le b O0 O16) ltac:(lia) SH0)
        as (R3 & M3 & Hms & MU3 & WM3 & XC3 & K1 & K10 & K11 & K12 & K13 & K20 & K22 & KK).
      pose proof (MSF _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
      assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
      eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
      intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
      eapply (v4_s4 msF3 mo3 sk2 M3 R3 pid' A (firstn (Z.to_nat (4 * cap)) jall) ltac:(lia) VIS3 HF3).
      + exact K1.
      + rewrite (KK 2%bv ltac:(inb)). exact G2.
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 8%bv ltac:(inb)). exact G8.
      + rewrite (KK 9%bv ltac:(inb)). exact G9.
      + exact K10.
      + exact K11.
      + exact K12.
      + exact K13.
      + rewrite (KK 18%bv ltac:(inb)). exact G18.
      + rewrite (KK 19%bv ltac:(inb)). exact G19.
      + exact K20.
      + exact K22.
      + rewrite (KK 23%bv ltac:(inb)). exact G23.
      + rewrite (KK 24%bv ltac:(inb)). exact G24.
      + rewrite (KK 25%bv ltac:(inb)). exact G25.
      + rewrite (KK 26%bv ltac:(inb)). exact G26.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR3.
      + eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
      + eapply v4_mid_munch; [exact MID | exact ABR | exact NI | exact MU3 | exact WM3 | exact MI3 |].
        apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_nil].
      + exact ABR.
      + exact NI.
      + eapply rw_cells_transport; [exact CBA | exact MU3 | exact WM3 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        cbn. split; [lia | exact I].
      + exact XC3.
      + eapply SHAD_transport; [exact SHA0 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia.
        pose proof (v4_app_sh (A + 4 * cap) 4 A (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct ABND; [left|right]; lia)) as D.
        cbn. split; [lia | exact I].
  Qed.

  Lemma v4_sn : forall (msF1 : machine_state) (mo1 : Model) (m1 : mem) (R1 : bvmap 5 word) (e1 : word),
    as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs) -> rfull R1 ->
    getr R1 1 = Z_to_bv 64 (E0 + 0xcc) -> getr R1 2 = Z_to_bv 64 (spz - 96) -> getr R1 3 = gp -> getr R1 4 = tp ->
    getr R1 8 = Z_to_bv 64 (v + 8) -> getr R1 9 = Z_to_bv 64 v -> getr R1 10 = Z_to_bv 64 (4 * cap') ->
    getr R1 18 = Z_to_bv 64 (v + 16) -> getr R1 19 = Z_to_bv 64 (4 * cap') -> getr R1 21 = Z_to_bv 64 src ->
    getr R1 22 = Z_to_bv 64 (4 * cap) -> getr R1 23 = Z_to_bv 64 (sh v) -> getr R1 24 = Z_to_bv 64 (sh (v + 8)) ->
    getr R1 25 = Z_to_bv 64 (sh (v + 16)) -> getr R1 26 = Z_to_bv 64 ASHADOW_BASE -> getr R1 27 = s11 ->
    as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    mem_inv asegs m1 -> stk asegs m1 lo spz -> rw_cells asegs m1 (errno_addr tp) [C4 e1] -> as_rauxv_ok H m1 B ->
    ACONST m1 -> as_RFS H LF m1 -> stack0 m1 lo shi -> as_RHEAP H s LB m1 -> rw_cells asegs m1 (spz - 96) FRAME ->
    xpres H LB spz [] m m1 -> lb_own LB m1 ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 m1 R1 e1 VIS1 HF1 G1 G2 G3 G4 G8 G9 G10 G18 G19 G21 G22 G23 G24 G25 G26 G27 KR1 MP1
      MI1 ST1 ERR1 RA1 AC1 RF1 S01 RH1 FR1 XP1 OW1.
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof v4_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (CMB : as_Cm H (4 * cap') <= as_AL H s).
    { pose proof CM as CM'. change (v4_newcap cap) with cap' in CM'.
      assert (CF0 : 0 <= as_Cf H (4 * cap)) by (pose proof (ah_costs H HH) as (_ & _ & CF & _); apply CF; lia). lia. }
    rewrite (rfull_eq R1 HF1) in VIS1.
    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH) with (n := 4 * cap') (LB := LB) (lo := lo) (B := B) (errv := e1);
        [ exact VIS1 | exact RH1 | exact KR1 | exact AOK | exact CMB | exact RA1 | rewrite G2, u64_of_Z by lia; lia
        | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo (spz - 96) spz ST1 ltac:(lia)))
        | exact LO1 | rewrite G2, u64_of_Z by lia; unfold AOPNEW_STACK, AMALLOC_STACK; lia
        | rewrite G4; exact ERR1 | exact MI1 | rewrite G4; exact TPV | rewrite G2, u64_of_Z by lia; exact (v4_mod16_sub96 spz SP16)
        | exact AC1 | exact G10 | lia ]. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & A & junk & p
                      & sk2 & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RAX2 & AP2 & ABR & RH2 & CB2 & ADDR & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite G1 in VIS2. destruct (v4_E0_even 0xcc ltac:(lia) eq_refl) as [ER1 ER2].
    rewrite (ret_pc_even (E0 + 0xcc) ER1 ER2) in VIS2.
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
              eapply (apres_stk H); [exact AP2 | exact (proj2 (stk_split asegs m1 lo (spz - 96) spz ST1 ltac:(lia))) | lia]|].
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
    pose proof RUNS as (B1 & _ & _ & _ & _ & _ & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof v4_vec_facts as (F0 & F1 & F2 & _ & C0 & OB).
    destruct (v4_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB2 : 0x6e6000 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    assert (GZ : gz m v 24) by (intros i Hi; eapply sh0_of_addressable; [exact ADV0 | change (8 * (24 / 8)) with 24; lia]).
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    assert (VSD : v + 24 <= spz - 96 \/ spz <= v) by (destruct OBJ as (_ & _ & _ & _ & _ & SD); lia).
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R0 eqn:HR0.
    assert (HF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
    destruct (B1 R0 F fc m v b cap src spz lo ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity)
                 ltac:(rewrite HR0; exact spz_sp) AC0 F0 F1 F2 GZ ST0 ltac:(lia) SPL SPH (proj1 VB2) (proj2 VB2) VSD
                 (proj1 OB0) (proj2 OB0) ltac:(lia))
      as (R1 & M1 & Hms & MU1 & WM1 & FR1 & K1 & K2 & K10 & K8 & K9 & K18 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & KK).
    assert (FRM : rw_cells asegs M1 (spz - 96) FRAME) by (rewrite HR0 in FR1; exact FR1).
    pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    destruct (stack_window_ok H LB LF (spz - 96) spz ltac:(lia) FS2) as (SW1 & SW2 & SW3).
    destruct (client_frame H HH s LB LF B [(spz - 96, spz)] m M1 RH0 RF0 AC0 RA0 MU1 WM1
                ltac:(apply Forall_cons; [exact SW1 | apply Forall_nil]) ltac:(apply Forall_cons; [exact SW2 | apply Forall_nil])
                ltac:(apply Forall_cons; [exact SW3 | apply Forall_nil]))
      as (RH1 & RF1 & AC1 & RA1).
    assert (ST1 : stk asegs M1 lo spz).
    { apply (stk_merge asegs M1 lo (spz - 96) spz); [| | lia].
      - eapply stk_transport_disjoint; [exact (proj1 (stk_split asegs m lo (spz - 96) spz ST0 ltac:(lia))) | exact MU1 | exact WM1 |].
        cbn. split; [lia | exact I].
      - pose proof (stk_of_rw_cells asegs M1 _ _ FRM) as K. unfold FRAME in K. rewrite v4_cells_size_map_C8' in K.
        change (8 * Z.of_nat (length [s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra])) with 96 in K.
        replace (spz - 96 + 96) with spz in K by lia. exact K. }
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. split; [lia | exact I]. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S00 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (XP1 : xpres H LB spz [] m M1).
    { eapply (xpres_of_munch H s LB spz [] [(spz - 96, spz)] m m M1); [exact HH | exact RH0 | exact MU1 | exact WM1 |].
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
    - exact K21.
    - exact K22.
    - exact K23.
    - exact K24.
    - exact K25.
    - exact K26.
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

Theorem v4slow_of_runs {HCEIL : HeapCeil} : forall (H : asr) (c : v4_consts), asan_rt_hyps H ->
  v4_runs (v4_entry c) -> v4_del_ra c = v4_entry c + 0x1a4 -> 0 <= v4_entry c < 0x100000 /\ v4_entry c mod 4 = 0 ->
  v4slow_stmt H c.
Proof.
  intros H c HH RUNS DRA E0R. unfold v4slow_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF
    v b cap src x xs pid lo B shi errv.
  intros VIS -> -> VEC XSL V8 ADV OBJ VBAND VWR OWN OLD OLDSH GROW SRC XR SR4 SR0 SR47 RH KR AOK CM TRO RA SPB SP16 SP47 ST CE LOl
    ERR MI TPV RA2 AC RF S0 SHI.
  pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
  unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LOl.
  eapply (v4_main H HH c RUNS DRA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF v b cap src x xs pid lo B shi
            (bv_unsigned sp)); try eassumption; try reflexivity.
  - split; [lia|]. split; [exact SP47 | exact SP16].
  - split; [exact SR4|]. split; [exact SR0 | exact SR47].
  - split; [exact CE | unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK; lia].
Qed.

Theorem v4slow_f79f8 {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H -> v4slow_stmt H V32_SLOW_CREF.
Proof.
  intros H HH. apply (v4slow_of_runs H V32_SLOW_CREF HH v4_runs_f79f8); [apply v4_del_ra_ok; left; reflexivity | split; [cbn [v4_entry V32_SLOW_CREF V32_SLOW_RREF VOT_SLOW_RREF VOT_SLOW_CREF]; lia | reflexivity]].
Qed.
Theorem v4slow_f7c80 {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H -> v4slow_stmt H V32_SLOW_RREF.
Proof.
  intros H HH. apply (v4slow_of_runs H V32_SLOW_RREF HH v4_runs_f7c80); [apply v4_del_ra_ok; right; left; reflexivity | split; [cbn [v4_entry V32_SLOW_CREF V32_SLOW_RREF VOT_SLOW_RREF VOT_SLOW_CREF]; lia | reflexivity]].
Qed.
Theorem v4slow_fa4fc {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H -> v4slow_stmt H VOT_SLOW_RREF.
Proof.
  intros H HH. apply (v4slow_of_runs H VOT_SLOW_RREF HH v4_runs_fa4fc); [apply v4_del_ra_ok; right; right; left; reflexivity | split; [cbn [v4_entry V32_SLOW_CREF V32_SLOW_RREF VOT_SLOW_RREF VOT_SLOW_CREF]; lia | reflexivity]].
Qed.
Theorem v4slow_fe724 {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H -> v4slow_stmt H VOT_SLOW_CREF.
Proof.
  intros H HH. apply (v4slow_of_runs H VOT_SLOW_CREF HH v4_runs_fe724); [apply v4_del_ra_ok; right; right; right; left; reflexivity | split; [cbn [v4_entry V32_SLOW_CREF V32_SLOW_RREF VOT_SLOW_RREF VOT_SLOW_CREF]; lia | reflexivity]].
Qed.

