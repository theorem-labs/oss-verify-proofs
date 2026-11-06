(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvw Z4d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3 Sj_new Zpt Zps Zpo Zwn Zsl Z4a Z73 Z5g Z6m Z71 Z5h Z5i Z5j Z6q Z6y Z6p Z45 Z4e Z4l Z4m Z4n Z4o Z52 Z57.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma atp_elsA_snd : forall D d e0 P1 L1 rest, atp_elsA D d = e0 :: (P1, L1) :: rest ->
  L1 = zlength (atp_ptr d)
  /\ ((P1 = 0 /\ atp_ptr d = []) \/ (exists o1 : nat, P1 = D + Z.of_nat o1 /\ (o1 + length (atp_ptr d) <= length d)%nat /\ atp_ptr d = firstn (length (atp_ptr d)) (skipn o1 d))).
Proof.
  intros D d e0 P1 L1 rest E. unfold atp_elsA, atp_P, atp_ptr in *.
  pose proof (poffs_parts d) as PP. pose proof (poffs_length d) as PL.
  destruct (poffs d) as [|e0' [|[o1 n1] tl]] eqn:EP; cbn [map app length] in E, PP; rewrite <- PP in *.
  - cbn in E. injection E as E0 E1 E2. subst. cbn. split; [reflexivity| left; split; reflexivity].
  - cbn in E. injection E as E0 E1 E2. subst. cbn. split; [reflexivity| left; split; reflexivity].
  - injection E as E0 E1 E2 E3. cbn [nth].
    pose proof (poffs_bound d (o1, n1) ltac:(rewrite EP; right; left; reflexivity)) as B. cbn [fst snd] in B.
    assert (LN : length (firstn n1 (skipn o1 d)) = n1) by (rewrite length_firstn, length_skipn; lia).
    rewrite LN. split; [unfold zlength; rewrite LN; lia|]. right. exists o1. split; [lia|]. split; [lia| reflexivity].
Qed.

Lemma skipn_chars : forall k (bs : list byte), skipn k (chars bs) = chars (skipn k bs).
Proof. intros k bs. unfold chars. rewrite skipn_map. reflexivity. Qed.

Lemma atp_ptr_bytes : forall d (bs : list byte) e0 P1 L1 rest m, atp_elsA d (chars bs) = e0 :: (P1, L1) :: rest -> bytes_at bsegs m d bs ->
  exists bsp : list byte, atp_ptr (chars bs) = chars bsp /\ L1 = Z.of_nat (length bsp)
    /\ ((P1 = 0 /\ bsp = []) \/ (d <= P1 /\ P1 + Z.of_nat (length bsp) <= d + Z.of_nat (length bs) /\ bytes_at bsegs m P1 bsp)).
Proof.
  intros d bs e0 P1 L1 rest m E BS. destruct (atp_elsA_snd d (chars bs) e0 P1 L1 rest E) as (EL1 & CASES).
  destruct CASES as [(-> & E0)|(o1 & EP1 & B & EQ)].
  - exists []. rewrite E0 in *. split; [reflexivity|]. split; [exact EL1| left; split; reflexivity].
  - set (k := length (atp_ptr (chars bs))) in *. exists (firstn k (skipn o1 bs)).
    unfold chars in B. rewrite length_map in B.
    assert (LK : length (firstn k (skipn o1 bs)) = k) by (rewrite length_firstn, length_skipn; lia).
    split; [rewrite <- firstn_chars, <- skipn_chars; exact EQ|]. split; [rewrite LK, EL1; unfold zlength; lia|].
    right. rewrite LK. split; [lia|]. split; [lia|]. rewrite EP1. apply bytes_at_firstn'. apply (bytes_at_skipn m d bs o1 BS). lia.
Qed.

Section Kit3.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold FUZZ_STACK, ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK, ATPA_DESTROY_STACK, PID_STACK in *;
                 unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition fin_postA (Σ : rts RT) (PMc : Model -> Prop) (usp lo : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
      /\ rt_after_f RT Σ' usp lo m m'
      /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp LIB_FP m m' /\ LIB m') c
    /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ'.

Lemma lp_inv_xfer_junk : forall Σ Σx Σy m mx my usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A (jq' je' jo' jn' : list byte),
  lp_inv RT LIB Σ Σx m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A ->
  rt_frames RT Σ = [] -> (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σx)) -> In (A, 16 * Z.of_nat (atp_P (chars bs))) (rt_live RT Σx) ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp - 304 <= sp' <= usp - 288 ->
  rt_frames RT Σy = rt_frames RT Σx -> rt_sp0 RT Σy = rt_sp0 RT Σx ->
  ART RT Σy my -> mem_inv bsegs my -> stk bsegs my lo sp' ->
  (forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> ~ (sp' + 56 <= bv_unsigned a < sp' + 136) -> my a = mx a) ->
  rw_cells bsegs my (sp' + 56) [CB 24 jq'; CB 16 je'; CB 24 jo'; CB 16 jn'] ->
  lp_inv RT LIB Σ Σy m my usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A.
Proof using LIB_loc AF.
  intros until jn'. intros INV FRS0 INCL INA INLV LOW LOR SPR FRS SP ARTy MIy STy EQ RJ.
  destruct INV as (ARTx & _ & STx & (j0 & j1 & j2 & j4 & jq & je & jo & jn & jr & j13 & L1) & L2 & L3 & L4 & L5 & VR & BS & LB & PRES & FRSx & SPx).
  pose proof (af_sp0_range RT AF Σx mx ARTx) as SPR0. rewrite SPx in SPR0.
  assert (INF : In (f, 2%nat) (rt_frames RT Σx)) by (rewrite FRSx; left; reflexivity).
  pose proof (fframe_ranges RT AF Σx mx f 2%nat ARTx INF) as (F0 & FR1 & _ & SHB1 & SHT). change (fs_size 2) with 256 in FR1, SHT. rewrite SPx in FR1, SHT.
  assert (SHF : shad (f + 256) = f / 8 + 2147450880 + 32) by (unfold shad, SHB; Z.div_mod_to_equations; lia). rewrite SHF in SHT.
  assert (FLO : f + 256 <= sp') by (clear - FR1 LOW LOR SPR; ul).
  assert (SLO : f / 8 + 2147450880 + 32 < sp') by (clear - SHT LOW LOR SPR; ul).
  destruct VR as (E & R & C & A0 & AH & SV & BLK).
  assert (AG : forall (Q : Z -> Prop), (forall x, Q x -> lp_rng usp sp' f A d bs x /\ ~ (sp' + 56 <= x < sp' + 136)) -> agree_on Q mx my).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (H1 & H2). apply EQ; [left; exact H1| exact H2]. }
  unfold lp_inv. split; [exact ARTy|]. split; [exact MIy|]. split; [exact STy|].
  split. { exists j0, j1, j2, j4, jq', je', jo', jn', jr, j13. unfold fa_locals2 in *.
           lazymatch type of L1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) =>
             change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ [c6; c7; c8; c9] ++ rest) in L1 end.
           apply Zvw.rw_cells_app in L1. destruct L1 as [X1 L1]. apply Zvw.rw_cells_app in L1. destruct L1 as [_ X3].
           cbn [cells_size csize Nat.add app] in X1, X3.
           lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) =>
             change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ [c6; c7; c8; c9] ++ rest) end.
           apply Zvw.rw_cells_app. split.
           { apply (rw_cells_agree_nw bsegs mx my _ _ X1). apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; lia| lia]. }
           apply Zvw.rw_cells_app. split; [cbn [cells_size csize Nat.add]; replace (sp' + Z.of_nat 56) with (sp' + 56) by lia; exact RJ|].
           cbn [cells_size csize Nat.add app]. apply (rw_cells_agree_nw bsegs mx my _ _ X3). apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; lia| lia]. }
  split. { apply (stk_agree_nw bsegs mx my _ _ L2). apply AG. intros x Hx. cbv beta in Hx. split; [left; lia| lia]. }
  split. { apply (rw_cells_agree_nw bsegs mx my _ _ L3). apply AG. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; lia| lia]. }
  split. { apply (rw_cells_agree_nw bsegs mx my _ _ L4). apply AG. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| lia]. }
  split. { apply (rw_cells_agree_nw bsegs mx my _ _ L5). apply AG. intros x Hx. unfold fa_shadow2 in Hx. cbn [map app repeat cells_size csize Nat.add] in Hx.
           split; [right; right; left; lia| lia]. }
  split. { unfold vrepA. split; [exact E|]. split; [exact R|]. split; [exact C|]. split; [exact A0|]. split; [exact AH|].
           split. { apply (rw_cells_agree_nw bsegs mx my _ _ SV). apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| lia]. }
           destruct BLK as [B|(C1 & A16 & ASG & EL)]; [left; exact B| right]. split; [exact C1|]. split; [exact A16|]. split; [exact ASG|].
           apply (rw_cells_agree_nw bsegs mx my _ _ EL). apply AG. intros x Hx. rewrite velts_size, atp_elsA_length in Hx.
           pose proof (af_live_range RT AF Σx mx A _ ARTx INA) as (_ & AR1 & _). rewrite SPx in AR1.
           split; [right; right; right; left; lia|]. clear - Hx AR1 LOW LOR SPR. ul. }
  split. { apply (bytes_at_agree bsegs mx my _ _ BS). apply AG. intros x Hx. cbv beta in Hx. split; [do 4 right; left; exact Hx|].
           destruct INLV as [(p & k & Hin & Q1 & Q2)|(E0 & _)]; [| subst bs; cbn [length] in Hx; lia].
           pose proof (af_live_range RT AF Σx mx p k ARTx (INCL _ Hin)) as (_ & R1 & _). rewrite SPx in R1. clear - Hx Q1 Q2 R1 LOW LOR SPR. ul. }
  split. { apply (LIB_agree2 LIB LIB_loc mx my LB). apply AG. intros x Hx. pose proof (proj2 (lib_fp_static x Hx)). split; [do 5 right; exact Hx|].
           clear - H SPR0 LOW LOR SPR. ul. }
  split. { intros a Ha Hout. rewrite <- (PRES a Ha Hout). apply EQ; [right; split; [exact Ha| exact Hout]|].
           destruct Ha as [H|[H|[H|[H|H]]]]; [lia| pose proof (client_static_range _ H); unfold SEGTOP_A in *; lia| | |].
           - destruct H as (p & k & Hin & Hr). pose proof (af_live_range RT AF Σx mx p k ARTx (INCL _ Hin)) as (_ & R1 & _). rewrite SPx in R1.
             clear - Hr R1 LOW LOR SPR. ul.
           - destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin.
           - destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin. }
  split; [rewrite FRS; exact FRSx| rewrite SP; exact SPx].
Qed.

Lemma pdone_xfer : forall (Σ Σ' : rts RT) (m m' : mem) (P : Z) (L : list (Z * Z)),
  pdone RT Σ m P L -> ART RT Σ m -> rt_frames RT Σ' = rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ ->
  (forall a : word, (in_fframe (rt_frames RT Σ) (bv_unsigned a) \/ in_fframe_shadow (rt_frames RT Σ) (bv_unsigned a) \/ in_live (rt_live RT Σ) (bv_unsigned a)) -> m' a = m a) ->
  pdone RT Σ' m' P L.
Proof using AF.
  intros Σ Σ' m m' P L PD ARTm FRS LV EQ.
  destruct PD as (impl & tape & sbuf & idx & oc & ia & nt & ns & nidx & noc & nia & dcap & pre8 & mid & mid2 & rest & ipre8 & imid & irest
                  & FOBJ & PC & INM & I8 & IC & INS & INT & INA & INO & INX & NS0 & NT0 & NA0 & NO0 & NX0 & ND6 & EL).
  exists impl, tape, sbuf, idx, oc, ia, nt, ns, nidx, noc, nia, dcap, pre8, mid, mid2, rest, ipre8, imid, irest.
  destruct (fobj_shadow_range RT AF Σ m P 80 ARTm FOBJ) as (f & c & Hf & S1 & S2 & Q0).
  split. { apply (fobj_agree RT AF Σ Σ' m m' P 80 ARTm FOBJ FRS). intros a Ha. cbv beta in Ha. apply EQ. right; left. exists f, c. split; [exact Hf| lia]. }
  pose proof FOBJ as (_ & _ & (f' & c' & Hf' & FL & FH) & _). change ((80 + 7) / 8) with 10 in FH.
  split. { apply (rw_cells_agree_nw bsegs m m' _ _ PC). intros a Ha. unfold pd_cells in Ha. cbn [cells_size csize Nat.add] in Ha. apply EQ. left. exists f', c'. split; [exact Hf'| lia]. }
  rewrite LV. split; [exact INM|]. split; [exact I8|].
  split. { apply (rw_cells_agree_nw bsegs m m' _ _ IC). intros a Ha. unfold dl_cells in Ha. cbn [cells_size csize Nat.add] in Ha. apply EQ. right; right. exists impl, 96. split; [exact INM| lia]. }
  repeat (split; [assumption|]). exact EL.
Qed.

Lemma fobjV_of_shadow1 : forall (Σ : rts RT) (m : mem) (f : Z) (t : list byte),
  0 < f -> f mod 64 = 0 -> rt_frames RT Σ = [(f, 2%nat)] -> rw_cells bsegs m (f / 8 + 2147450880) (fa_shadow1 t) -> fobj RT Σ m (f + 32) 24.
Proof.
  intros Σ m f t FPOS F64 FRS FS.
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((24 + 7) / 8) with 3.
  split; [exists f, 2%nat; rewrite FRS; change (fs_size 2) with 256; split; [left; reflexivity| lia]|].
  replace (shad (f + 32)) with (f / 8 + 2147450880 + Z.of_nat 4) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  unfold fa_shadow1 in FS. cbn [map app repeat] in FS.
  lazymatch type of FS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?d0 :: ?d1 :: ?d2 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: rest) with ([c0; c1; c2; c3] ++ [d0; d1; d2] ++ rest) in FS end.
  apply Zvw.rw_cells_app in FS. destruct FS as [_ FS]. apply Zvw.rw_cells_app in FS. destruct FS as [FS _].
  cbn [cells_size csize Nat.add] in FS. destruct FS as [[_ HB] _]. exact HB.
Qed.

End Kit3.
