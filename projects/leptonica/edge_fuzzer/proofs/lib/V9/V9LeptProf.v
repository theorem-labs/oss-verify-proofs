(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptScan LeptNuma.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9LeptBase V9_code_edB V9LeptScan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma sub_al4 : forall s k, (s mod 16 = 0)%Z -> (k mod 4 = 0)%Z -> ((s - k) mod 4 = 0)%Z.
Proof.
  intros s k H1 H2. apply Zmod_divides in H1 as [c ->]; [|lia]. apply Zmod_divides in H2 as [e ->]; [|lia].
  replace (16 * c - 4 * e)%Z with ((4 * c - e) * 4)%Z by ring. apply Z_mod_mult.
Qed.

Section ProfSegs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
  Ltac zlit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).

  (* [comment removed for export] *)
  Definition DIMS (m : word -> option byte) (aw ah w h : Z) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 aw) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 ah) (word_to_le_bytes 4 (Z_to_bv 64 0)))
           (Z_to_bv 64 aw) (word_to_le_bytes 4 (Z_to_bv 64 w))) (Z_to_bv 64 ah) (word_to_le_bytes 4 (Z_to_bv 64 h)).

  (* [comment removed for export] *)
  Ltac depth_inline PX Hd ALp retpc :=
    stepb_ft F_645dc D_645dc ltac:(condZ);
    zand F_645e0 D_645e0 andi_7 ALp;
    stepb_ft F_645e4 D_645e4 ltac:(condZ);
    stepLD F_645e8 D_645e8 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; repeat rdn_peel1; rewrite <- Hd; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia);
    try rewrite (v_lw_small 1) by lia;
    stepret F_645ec D_645ec retpc ltac:(bveq).
  (* [comment removed for export] *)
  Ltac dims_inline PX SOK vv aw ah ALw ALh ALp retpc :=
    zand F_6397c D_6397c andi_3 ALw;
    stepb_ft F_63980 D_63980 ltac:(condZ);
    stepb_ft F_63984 D_63984 ltac:(condZ);
    stepST F_63988 D_63988 (Z_to_bv 64 aw) (Z_to_bv 64 0) ltac:(sok_in SOK);
    zand F_6398c D_6398c andi_3 ALh;
    stepb_ft F_63990 D_63990 ltac:(condZ);
    stepb_ft F_63994 D_63994 ltac:(condZ);
    stepST F_63998 D_63998 (Z_to_bv 64 ah) (Z_to_bv 64 0) ltac:(sok_in SOK);
    zlit F_6399c D_6399c (Z_to_bv 64 0);
    stepb_tk F_639a0 D_639a0 ltac:(condZ);
    stepb_ft F_639ac D_639ac ltac:(condZ);
    zand F_639b0 D_639b0 andi_7 ALp;
    stepb_ft F_639b4 D_639b4 ltac:(condZ);
    zlit F_639b8 D_639b8 (Z_to_bv 64 0);
    stepb_ft F_639bc D_639bc ltac:(condZ);
    stepLD F_639c0 D_639c0 (Z_to_le_bytes 4 (p_w vv)) (Z_to_bv 64 (p_w vv)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia);
    rewrite (v_lw_small (p_w vv)) by lia;
    stepST F_639c4 D_639c4 (Z_to_bv 64 aw) (Z_to_bv 64 (p_w vv)) ltac:(sok_in SOK);
    stepb_ft F_639c8 D_639c8 ltac:(condZ);
    zlit F_639cc D_639cc (Z_to_bv 64 0);
    stepb_ft F_639d0 D_639d0 ltac:(condZ);
    stepLD F_639d4 D_639d4 (Z_to_le_bytes 4 (p_h vv)) (Z_to_bv 64 (p_h vv)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia);
    rewrite (v_lw_small (p_h vv)) by lia;
    stepST F_639d8 D_639d8 (Z_to_bv 64 ah) (Z_to_bv 64 (p_h vv)) ltac:(sok_in SOK);
    stepb_tk F_639dc D_639dc ltac:(condZ);
    sn F_63a24 D_63a24;
    stepret F_63a28 D_63a28 retpc ltac:(bveq).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Scan.
  Variables (s pix : Z) (v : pixv) (m0 : word -> option byte).
  Hypothesis Hs : (0x20100 <= s)%Z.
  Hypothesis Hs64 : (s < 2 ^ 64)%Z.
  Hypothesis Hs16 : (s mod 16 = 0)%Z.
  Hypothesis PX0 : PIXat m0 pix v.
  Hypothesis Hd1 : p_d v = 1%Z.
  Hypothesis Hw1 : (1 <= p_w v)%Z.
  Hypothesis Hw32 : (p_w v <= 32 * p_wpl v)%Z.
  Hypothesis Hsz : (4 * (p_wpl v * p_h v) <= 2 ^ 26)%Z.
  Hypothesis ALd : (p_data v mod 4 = 0)%Z.
  Hypothesis Hdp : (4 <= p_data v)%Z.
  Hypothesis Gp : (4096 <= pix)%Z.
  Hypothesis ALp : (pix mod 8 = 0)%Z.
  Hypothesis Hpix : (pix + 64 <= s - 240)%Z.
  Hypothesis Hdat : (p_data v + 4 * (p_wpl v * p_h v) <= s - 240)%Z.
  Hypothesis SOK0 : store_ok SEGS m0 (Z_to_bv 64 (s - 240)) 240 = true.
  Hypothesis RDEF : forall a : word, (p_data v <= u a < p_data v + 4 * (p_wpl v * p_h v))%Z -> m0 a <> None.
  Hypothesis JT0 : rdn SEGS m0 (Z_to_bv 64 0x1c70c) 4 = Some (Z_to_le_bytes 4 0x48348).

  Definition scanR (a : word) : Prop := (s - 240 <= u a < s - 96)%Z \/ (s - 76 <= u a < s - 72)%Z \/ (s - 68 <= u a < s - 64)%Z.
  Definition sinv (m : word -> option byte) : Prop := mem_grows m0 m /\ forall a : word, ~ scanR a -> m a = m0 a.
  Definition pxa (x y : Z) : Z := (p_data v + 4 * (p_wpl v * y) + 4 * (x / 32))%Z.
  Definition pxl (x y : Z) : Z := pbit (mword m0 (pxa x y)) x.

  Lemma sinv_refl : sinv m0.
  Proof. split; [apply mem_grows_refl | intros a _; reflexivity]. Qed.

  Lemma pxa_in : forall x y, (0 <= x < p_w v)%Z -> (0 <= y < p_h v)%Z ->
    (p_data v <= pxa x y)%Z /\ (pxa x y + 4 <= p_data v + 4 * (p_wpl v * p_h v))%Z.
  Proof.
    intros x y Hx Hy. unfold pxa. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_wpl _ WF).
    assert (0 <= x / 32 < p_wpl v)%Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (p_wpl v * (y + 1) <= p_wpl v * p_h v)%Z by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= p_wpl v * y)%Z by (apply Z.mul_nonneg_nonneg; lia). lia.
  Qed.

  Lemma sinv_facts : forall m, sinv m ->
    PIXat m pix v /\ store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true /\ rdn SEGS m (Z_to_bv 64 0x1c70c) 4 = Some (Z_to_le_bytes 4 0x48348) /\
    (forall x y, (0 <= x < p_w v)%Z -> (0 <= y < p_h v)%Z -> rdn SEGS m (Z_to_bv 64 (pxa x y)) 4 = Some (Z_to_le_bytes 4 (mword m0 (pxa x y)))).
  Proof.
    intros m [G E]. pose proof PX0 as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rd.
    split; [apply (PIXat_frame m0); [exact PX0 | intros x Hx; apply E; unfold scanR; lia]|].
    split; [exact (store_ok_mono SEGS _ m0 m _ G SOK0)|].
    split; [rewrite <- JT0; apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros x Hx; apply E; unfold scanR; cbn in Hx; lia]|].
    intros x y Hx Hy. destruct (pxa_in x y Hx Hy) as [A1 A2].
    assert (BA : bytes_at m0 (pxa x y) (Z_to_le_bytes 4 (mword m0 (pxa x y)))).
    { apply mword_bytes_at. intros i Hi. apply RDEF. rewrite u_Z2bv by lia. lia. }
    pose proof (bytes_at_rdn SEGS m0 (pxa x y) (Z_to_le_bytes 4 (mword m0 (pxa x y))) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) BA) as R0.
    rewrite length_Z_to_le_bytes in R0.
    rewrite <- R0. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; apply E; unfold scanR; cbn in Ha; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma px_read : forall regs m (sc x y pv : Z) (ret : word),
    sinv m -> (0 <= x < p_w v)%Z -> (0 <= y < p_h v)%Z ->
    (s - 176 <= sc <= s - 96)%Z -> (sc mod 16 = 0)%Z -> (sc <= pv)%Z -> (pv + 4 <= sc + 64)%Z -> (pv mod 4 = 0)%Z -> (pv + 4 <= s - 96 \/ pv = s - 76)%Z ->
    getr regs 2 = Z_to_bv 64 sc -> getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y -> getr regs 13 = Z_to_bv 64 pv ->
    exists regs' m',
      msteps SEGS (mkst regs (0x6496c : word) m rom) (mkst regs' ret m' rom)
      /\ sinv m' /\ rdn SEGS m' (Z_to_bv 64 pv) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (pxl x y)))
      /\ (forall a : word, ~ (sc - 64 <= u a < sc)%Z -> ~ (pv <= u a < pv + 4)%Z -> m' a = m a)
      /\ getr regs' 2 = Z_to_bv 64 sc
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m sc x y pv ret SI Hx Hy Hsc Hsc16 Hpv1 Hpv2 ALpv Hpv3 H2 H1 Hret H10 H11 H12 H13.
    destruct (sinv_facts m SI) as (PX & SOK & JT & RW). pose proof SI as [G E].
    assert (SOKf : store_ok SEGS m (Z_to_bv 64 (sc - 64)) 64 = true).
    { eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    assert (SOKv : store_ok SEGS m (Z_to_bv 64 pv) 4 = true).
    { eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    destruct (pgp1_run rom regs m sc pv pix x y (mword m0 (pxa x y)) v ret ltac:(lia) ltac:(lia) Hpv1 Hpv2 PX Hd1 Hw1 Hw32 Hsz Hx Hy ALd Hdp
                Gp ltac:(lia) ltac:(lia) Hsc16 ALpv ALp SOKf SOKv (RW x y Hx Hy) (mword_range _ _) JT H2 H1 Hret H10 H11 H12 H13)
      as (r' & RUN & Q2 & Q10 & Q8 & Q9 & Q18 & Q19 & Q20 & AG).
    eexists r', _. split; [exact RUN|].
    assert (OUT : forall a : word, ~ (sc - 64 <= u a < sc)%Z -> ~ (pv <= u a < pv + 4)%Z ->
              wbytes (PGF m sc pv ret regs (p_w v) (p_h v) 1) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 (pbit (mword m0 (pxa x y)) x))) a = m a).
    { intros a N1 N2. rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia).
      apply PGF_out; lia. }
    split; [split|].
    - eapply mem_grows_trans; [exact G|]. eapply mem_grows_trans; [| apply wbytes_grows].
      unfold PGF. repeat (eapply mem_grows_trans; [| apply wbytes_grows]). apply mem_grows_refl.
    - intros a NR. rewrite OUT by (unfold scanR in NR; lia). apply E. exact NR.
    - split; [apply rdn_wbytes_hit4; rewrite u_Z2bv by lia; lia|].
      split; [exact OUT|]. split; [exact Q2|].
      intros r Hr. destruct (bv_eq_dec 5 r 2%bv) as [->|N2]; [rewrite Q2, H2; reflexivity|].
      destruct (bv_eq_dec 5 r 8%bv) as [->|N8]; [exact Q8|]. destruct (bv_eq_dec 5 r 9%bv) as [->|N9]; [exact Q9|].
      destruct (bv_eq_dec 5 r 18%bv) as [->|N18]; [exact Q18|]. destruct (bv_eq_dec 5 r 19%bv) as [->|N19]; [exact Q19|].
      destruct (bv_eq_dec 5 r 20%bv) as [->|N20]; [exact Q20|].
      apply AG. cbn [In] in *. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[]]]]]]]]]]]]]]]]; subst r; first [contradiction | apply Hr; tauto].
  Qed.

  (* [comment removed for export] *)
  Lemma sinv_wbytes : forall m (z : Z) bs, sinv m -> (0 <= z)%Z ->
    ((s - 240 <= z /\ z + Z.of_nat (length bs) <= s - 96) \/ (s - 76 <= z /\ z + Z.of_nat (length bs) <= s - 72) \/ (s - 68 <= z /\ z + Z.of_nat (length bs) <= s - 64))%Z ->
    sinv (wbytes m (Z_to_bv 64 z) bs).
  Proof.
    intros m z bs [G E] Hz HR. split.
    - eapply mem_grows_trans; [exact G | apply wbytes_grows].
    - intros a NR. unfold scanR in NR. rewrite wbytes_outside by (rewrite ?u_Z2bv by lia; lia). apply E. exact NR.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FRO (m : word -> option byte) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (getr regs 20)))
      (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (getr regs 21)).
  Definition frameO (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
    [((s - 104)%Z, ret); ((s - 112)%Z, getr r0 8); ((s - 120)%Z, getr r0 9); ((s - 128)%Z, getr r0 18); ((s - 136)%Z, getr r0 19);
     ((s - 144)%Z, getr r0 20); ((s - 152)%Z, getr r0 21)].

  Lemma loff_A : forall regs m (x y : Z) (ret : word),
    sinv m -> (0 <= x < p_w v)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y ->
    getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 (s - 68) ->
    exists regs' m', msteps SEGS (mkst regs (0x82d10 : word) m rom) (mkst regs' (0x82eec : word) m' rom)
      /\ sinv m' /\ cellsZ m' (frameO ret regs)
      /\ (forall a : word, ~ (s - 176 <= u a < s - 96)%Z -> ~ (s - 68 <= u a < s - 64)%Z -> m' a = m a)
      /\ getr regs' 2 = Z_to_bv 64 (s - 176) /\ getr regs' 8 = Z_to_bv 64 (s - 68) /\ getr regs' 9 = Z_to_bv 64 y /\ getr regs' 18 = Z_to_bv 64 x
      /\ getr regs' 19 = Z_to_bv 64 pix /\ getr regs' 21 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs m x y ret SI Hx H2 H1 H10 H11 H12 H13 H14.
    destruct (sinv_facts m SI) as (PX & SOK & _ & _).
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF).
    assert (AL68 : ((s - 68) mod 4 = 0)%Z) by (apply sub_al4; [exact Hs16 | reflexivity]).
    assert (AL156 : ((s - 156) mod 4 = 0)%Z) by (apply sub_al4; [exact Hs16 | reflexivity]).
    assert (AL160 : ((s - 160) mod 4 = 0)%Z) by (apply sub_al4; [exact Hs16 | reflexivity]).
    eexists _, _. split.
    - zv F_82cb8 D_82cb8 (Z_to_bv 64 (s - 176)).
      stepST F_82cbc D_82cbc (Z_to_bv 64 (s - 104)) ret ltac:(sok_in SOK).
      stepST F_82cc0 D_82cc0 (Z_to_bv 64 (s - 112)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_82cc4 D_82cc4 (Z_to_bv 64 (s - 120)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_82cc8 D_82cc8 (Z_to_bv 64 (s - 128)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_82ccc D_82ccc (Z_to_bv 64 (s - 136)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_82cd0 D_82cd0 (Z_to_bv 64 (s - 144)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_82cd4 D_82cd4 (Z_to_bv 64 (s - 152)) (getr regs 21) ltac:(sok_in SOK).
      stepb_ft F_82cd8 D_82cd8 ltac:(condZ).
      sn F_82cdc D_82cdc. sn F_82ce0 D_82ce0.
      zand F_82ce4 D_82ce4 andi_3 AL68.
      stepb_ft F_82ce8 D_82ce8 ltac:(condZ).
      stepST F_82cec D_82cec (Z_to_bv 64 (s - 68)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_82cf0 D_82cf0 ltac:(condZ).
      sn F_82cf4 D_82cf4. sn F_82cf8 D_82cf8. sn F_82cfc D_82cfc. sn F_82d00 D_82d00. sn F_82d04 D_82d04.
      depth_inline PX Hd1 ALp (0x82d60 : word).
      sn F_82d08 D_82d08.
      stepb_ft F_82d0c D_82d0c ltac:(condZ).
      sn F_82d10 D_82d10.
      stepb_tk F_82d14 D_82d14 ltac:(condZ).
      zv F_82ddc D_82ddc (Z_to_bv 64 (s - 156)). zv F_82de0 D_82de0 (Z_to_bv 64 (s - 160)). sn F_82de4 D_82de4. sn F_82de8 D_82de8. sn F_82dec D_82dec.
      dims_inline PX SOK v (s - 156)%Z (s - 160)%Z AL156 AL160 ALp (0x82e48 : word).
      sn F_82df0 D_82df0.
      stepb_ft F_82df4 D_82df4 ltac:(condZ).
      stepb_tk F_82df8 D_82df8 ltac:(condZ).
      stepb_ft F_82e8c D_82e8c ltac:(condZ).
      sn F_82e90 D_82e90.
      apply mst_refl.
    - split.
      { repeat (apply sinv_wbytes; [| lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]). exact SI. }
      split; [unfold frameO; cbn [cellsZ]; repeat split; rdn_solve|].
      split; [intros a N1 N2; rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia); reflexivity|].
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma loff_pre : forall regs m (c y : Z),
    getr regs 2 = Z_to_bv 64 (s - 176) -> getr regs 9 = Z_to_bv 64 y -> getr regs 18 = Z_to_bv 64 c -> getr regs 19 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (mkst regs (0x82eec : word) m rom) (mkst regs' (0x6496c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 176) /\ getr regs' 1 = Z_to_bv 64 0x82f04 /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 c
      /\ getr regs' 12 = Z_to_bv 64 y /\ getr regs' 13 = Z_to_bv 64 (s - 164) /\ getr regs' 20 = Z_to_bv 64 c
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 20]%list) regs regs'.
  Proof.
    intros regs m c y H2 H9 H18 H19. eexists. split.
    - sn F_82e94 D_82e94. zv F_82e98 D_82e98 (Z_to_bv 64 (s - 164)). sn F_82e9c D_82e9c. sn F_82ea0 D_82ea0. sn F_82ea4 D_82ea4. sn F_82ea8 D_82ea8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma loff_found : forall regs m (c : Z),
    (0 <= c < p_w v)%Z -> rdn SEGS m (Z_to_bv 64 (s - 164)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    getr regs 2 = Z_to_bv 64 (s - 176) -> getr regs 20 = Z_to_bv 64 c -> getr regs 21 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x82f04 : word) m rom) (mkst regs' (0x82e90 : word) m rom)
      /\ getr regs' 11 = Z_to_bv 64 (c + 1) /\ regs_agree (fun r => In r [10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m c Hc Rv H2 H20 H21. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    eexists. split.
    - stepLD F_82eac D_82eac (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 1) by lia.
      stepb_tk F_82eb0 D_82eb0 ltac:(condZ).
      sn F_82efc D_82efc.
      stepat F_82f00 D_82f00 (Z_to_bv 64 (c + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
      stepb_tk F_82f04 D_82f04 ltac:(condZ). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma loff_cont : forall regs m (c : Z),
    (1 <= c < p_w v)%Z -> rdn SEGS m (Z_to_bv 64 (s - 164)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    getr regs 2 = Z_to_bv 64 (s - 176) -> getr regs 20 = Z_to_bv 64 c -> getr regs 21 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x82f04 : word) m rom) (mkst regs' (0x82eec : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 (c - 1) /\ regs_agree (fun r => In r [10; 18]%list) regs regs'.
  Proof.
    intros regs m c Hc Rv H2 H20 H21. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    eexists. split.
    - stepLD F_82eac D_82eac (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 0) by lia.
      stepb_ft F_82eb0 D_82eb0 ltac:(condZ).
      stepat F_82eb4 D_82eb4 (Z_to_bv 64 (c - 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
      stepb_tk F_82eb8 D_82eb8 ltac:(condZ). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma loff_end : forall regs m,
    rdn SEGS m (Z_to_bv 64 (s - 164)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    getr regs 2 = Z_to_bv 64 (s - 176) -> getr regs 20 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x82f04 : word) m rom) (mkst regs' (0x82e90 : word) m rom)
      /\ getr regs' 11 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m Rv H2 H20 H21.
    eexists. split.
    - stepLD F_82eac D_82eac (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 0) by lia.
      stepb_ft F_82eb0 D_82eb0 ltac:(condZ).
      sn F_82eb4 D_82eb4.
      stepb_ft F_82eb8 D_82eb8 ltac:(condZ).
      sn F_82ebc D_82ebc. sn F_82ec0 D_82ec0.
      zlit F_82f00 D_82f00 (Z_to_bv 64 0).
      stepb_tk F_82f04 D_82f04 ltac:(pin; vm_compute; reflexivity). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma frameO_out : forall m m' ret r0, (forall a : word, ~ (s - 240 <= u a < s - 176)%Z -> ~ (s - 164 <= u a < s - 160)%Z -> m' a = m a) ->
    cellsZ m (frameO ret r0) -> cellsZ m' (frameO ret r0).
  Proof.
    intros m m' ret r0 OUT. apply cellsZ_keep. unfold frameO.
    repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros z Hz; apply OUT; lia]] |]). apply Forall_nil.
  Qed.

  Lemma loff_loop : forall (k : nat) regs m (c y : Z) (ret : word) (r0 : bvmap 5 word),
    (c <= Z.of_nat k)%Z -> sinv m -> cellsZ m (frameO ret r0) -> (0 <= c < p_w v)%Z -> (0 <= y < p_h v)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 176) -> getr regs 9 = Z_to_bv 64 y -> getr regs 18 = Z_to_bv 64 c -> getr regs 19 = Z_to_bv 64 pix ->
    getr regs 21 = Z_to_bv 64 1 ->
    exists regs' m' c', msteps SEGS (mkst regs (0x82eec : word) m rom) (mkst regs' (0x82e90 : word) m' rom)
      /\ sinv m' /\ cellsZ m' (frameO ret r0) /\ (0 <= c' <= c + 1)%Z /\ getr regs' 11 = Z_to_bv 64 c'
      /\ (forall a : word, ~ (s - 240 <= u a < s - 176)%Z -> ~ (s - 164 <= u a < s - 160)%Z -> m' a = m a)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs m c y ret r0 Hk SI CE Hc Hy H2 H9 H18 H19 H21.
    all: destruct (loff_pre regs m c y H2 H9 H18 H19) as (r1 & RUN1 & P2 & P1 & P10 & P11 & P12 & P13 & P20 & AG1).
    all: destruct (px_read r1 m (s - 176)%Z c y (s - 164)%Z (Z_to_bv 64 0x82f04) SI Hc Hy ltac:(lia)
                     ltac:(replace (s - 176)%Z with (s + (-176))%Z by lia; apply mod16_plus_mod16; [exact Hs16 | reflexivity]) ltac:(lia) ltac:(lia)
                     ltac:(apply sub_al4; [exact Hs16 | reflexivity]) ltac:(left; lia) P2 P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13)
           as (r2 & m2 & RUN2 & SI2 & Rv & OUT2 & Q2 & AG2).
    all: replace (Z_to_bv 64 0x82f04) with (0x82f04 : word) in RUN2 by (apply bv_eq; reflexivity).
    all: replace (s - 176 - 64)%Z with (s - 240)%Z in OUT2 by lia; replace (s - 164 + 4)%Z with (s - 160)%Z in OUT2 by lia.
    all: pose proof (frameO_out m m2 ret r0 OUT2 CE) as CE2.
    all: assert (Q20 : getr r2 20 = Z_to_bv 64 c) by (rewrite (AG2 20%bv) by notin_list; exact P20).
    all: assert (Q21 : getr r2 21 = Z_to_bv 64 1) by (rewrite (AG2 21%bv), (AG1 21%bv) by notin_list; exact H21).
    all: destruct (pbit_cases (mword m0 (pxa c y)) c) as [B0|B1]; unfold pxl in Rv.
    - rewrite B0 in Rv. assert (c = 0)%Z by lia. subst c.
      destruct (loff_end r2 m2 Rv Q2 Q20 Q21) as (r3 & RUN3 & V11 & AG3).
      exists r3, m2, 0%Z. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
      split; [exact SI2|]. split; [exact CE2|]. split; [lia|]. split; [exact V11|]. split; [exact OUT2 | ra_chain].
    - rewrite B1 in Rv.
      destruct (loff_found r2 m2 c Hc Rv Q2 Q20 Q21) as (r3 & RUN3 & V11 & AG3).
      exists r3, m2, (c + 1)%Z. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
      split; [exact SI2|]. split; [exact CE2|]. split; [lia|]. split; [exact V11|]. split; [exact OUT2 | ra_chain].
    - rewrite B0 in Rv. destruct (Z.eq_dec c 0) as [->|NZ].
      + destruct (loff_end r2 m2 Rv Q2 Q20 Q21) as (r3 & RUN3 & V11 & AG3).
        exists r3, m2, 0%Z. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
        split; [exact SI2|]. split; [exact CE2|]. split; [lia|]. split; [exact V11|]. split; [exact OUT2 | ra_chain].
      + destruct (loff_cont r2 m2 c ltac:(lia) Rv Q2 Q20 Q21) as (r3 & RUN3 & V18 & AG3).
        destruct (IH r3 m2 (c - 1)%Z y ret r0 ltac:(lia) SI2 CE2 ltac:(lia) Hy) as (r4 & m4 & c' & RUN4 & SI4 & CE4 & Hc' & W11 & OUT4 & AG4).
        { rewrite (AG3 2%bv) by notin_list. exact Q2. }
        { rewrite (AG3 9%bv), (AG2 9%bv), (AG1 9%bv) by notin_list. exact H9. }
        { exact V18. }
        { rewrite (AG3 19%bv), (AG2 19%bv), (AG1 19%bv) by notin_list. exact H19. }
        { rewrite (AG3 21%bv) by notin_list. exact Q21. }
        exists r4, m4, c'. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|].
        split; [exact SI4|]. split; [exact CE4|]. split; [lia|]. split; [exact W11|].
        split; [intros a N1 N2; rewrite (OUT4 a N1 N2); exact (OUT2 a N1 N2) | ra_chain].
    - rewrite B1 in Rv.
      destruct (loff_found r2 m2 c Hc Rv Q2 Q20 Q21) as (r3 & RUN3 & V11 & AG3).
      exists r3, m2, (c + 1)%Z. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
      split; [exact SI2|]. split; [exact CE2|]. split; [lia|]. split; [exact V11|]. split; [exact OUT2 | ra_chain].
  Qed.

  (* [comment removed for export] *)
  Lemma loff_Z : forall regs r0 m (c' : Z) (ret : word),
    (0 <= c' < 2 ^ 31)%Z -> ret_ok ret -> cellsZ m (frameO ret r0) -> store_ok SEGS m (Z_to_bv 64 (s - 68)) 4 = true ->
    getr regs 2 = Z_to_bv 64 (s - 176) -> getr regs 8 = Z_to_bv 64 (s - 68) -> getr regs 11 = Z_to_bv 64 c' ->
    exists regs', msteps SEGS (mkst regs (0x82e90 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 (s - 68)) (word_to_le_bytes 4 (Z_to_bv 64 c'))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96)
      /\ (forall x, In x [8; 9; 18; 19; 20; 21]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs r0 m c' ret Hc Hret CE SOKl H2 H8 H11. unfold frameO in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & _). eexists. split.
    - sn F_82e38 D_82e38.
      stepST F_82e3c D_82e3c (Z_to_bv 64 (s - 68)) (Z_to_bv 64 c') ltac:(store_ok_peel; exact SOKl).
      sn F_82e40 D_82e40.
      stepLD8 F_82db8 D_82db8 ret. stepLD8 F_82dbc D_82dbc (getr r0 8). stepLD8 F_82dc0 D_82dc0 (getr r0 9). stepLD8 F_82dc4 D_82dc4 (getr r0 18).
      stepLD8 F_82dc8 D_82dc8 (getr r0 19). stepLD8 F_82dcc D_82dcc (getr r0 20). stepLD8 F_82dd0 D_82dd0 (getr r0 21).
      zv F_82dd4 D_82dd4 (Z_to_bv 64 (s - 96)). stepret F_82dd8 D_82dd8 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  Lemma lastoff_run : forall regs m (x y : Z) (ret : word),
    sinv m -> (0 <= x < p_w v)%Z -> (0 <= y < p_h v)%Z -> ret_ok ret ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y ->
    getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 (s - 68) ->
    exists regs' m' c', msteps SEGS (mkst regs (0x82d10 : word) m rom) (mkst regs' ret m' rom)
      /\ sinv m' /\ (0 <= c' <= x + 1)%Z /\ rdn SEGS m' (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 c'))
      /\ (forall a : word, ~ (s - 240 <= u a < s - 96)%Z -> ~ (s - 68 <= u a < s - 64)%Z -> m' a = m a)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m x y ret SI Hx Hy Hret H2 H1 H10 H11 H12 H13 H14.
    pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF) as Rw.
    destruct (loff_A regs m x y ret SI Hx H2 H1 H10 H11 H12 H13 H14) as (r1 & m1 & RUN1 & SI1 & CE1 & OUT1 & P2 & P8 & P9 & P18 & P19 & P21 & AG1).
    destruct (loff_loop (Z.to_nat x) r1 m1 x y ret regs ltac:(lia) SI1 CE1 Hx Hy P2 P9 P18 P19 P21)
      as (r2 & m2 & c' & RUN2 & SI2 & CE2 & Hc' & Q11 & OUT2 & AG2).
    destruct (sinv_facts m2 SI2) as (_ & SOK2 & _ & _).
    assert (SOKl : store_ok SEGS m2 (Z_to_bv 64 (s - 68)) 4 = true).
    { eapply store_ok_sub; [ | exact SOK2 | | ]; rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    destruct (loff_Z r2 regs m2 c' ret ltac:(lia) Hret CE2 SOKl) as (r3 & RUN3 & V2 & VR & AG3).
    { rewrite (AG2 2%bv) by notin_list. exact P2. }
    { rewrite (AG2 8%bv) by notin_list. exact P8. }
    { exact Q11. }
    exists r3, (wbytes m2 (Z_to_bv 64 (s - 68)) (word_to_le_bytes 4 (Z_to_bv 64 c'))), c'. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
    split; [apply sinv_wbytes; [exact SI2 | lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
    split; [exact Hc'|]. split; [apply rdn_wbytes_hit4; rewrite u_Z2bv by lia; lia|].
    split.
    - intros a N1 N2. rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia).
      rewrite (OUT2 a ltac:(lia) ltac:(lia)). apply OUT1; lia.
    - intros r Hr. destruct (bv_eq_dec 5 r 2%bv) as [->|N2]; [rewrite V2, H2; reflexivity|].
      destruct (bv_eq_dec 5 r 8%bv) as [->|N8]; [apply VR; in_list|]. destruct (bv_eq_dec 5 r 9%bv) as [->|N9]; [apply VR; in_list|].
      destruct (bv_eq_dec 5 r 18%bv) as [->|N18]; [apply VR; in_list|]. destruct (bv_eq_dec 5 r 19%bv) as [->|N19]; [apply VR; in_list|].
      destruct (bv_eq_dec 5 r 20%bv) as [->|N20]; [apply VR; in_list|]. destruct (bv_eq_dec 5 r 21%bv) as [->|N21]; [apply VR; in_list|].
      assert (NI : forall L, (forall q, In q L -> q = 2%bv \/ q = 8%bv \/ q = 9%bv \/ q = 18%bv \/ q = 19%bv \/ q = 20%bv \/ q = 21%bv \/ In q [1; 10; 11; 12; 13; 14; 15; 16; 17]%bv) -> ~ In r L).
      { intros L HL HI. destruct (HL r HI) as [X|[X|[X|[X|[X|[X|[X|X]]]]]]]; first [contradiction | exact (Hr X)]. }
      rewrite (AG3 r), (AG2 r), (AG1 r); [reflexivity | | |]; apply NI; intros q Hq; cbn [In] in Hq |- *;
        repeat (destruct Hq as [<-|Hq]; [tauto|]); destruct Hq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FRN (m : word -> option byte) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (getr regs 20)).
  Definition frameN (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
    [((s - 104)%Z, ret); ((s - 112)%Z, getr r0 8); ((s - 120)%Z, getr r0 9); ((s - 128)%Z, getr r0 18); ((s - 136)%Z, getr r0 19); ((s - 144)%Z, getr r0 20)].

  Lemma lon_A : forall regs m (x y : Z) (ret : word),
    sinv m -> (0 <= x < p_w v)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y ->
    getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 (s - 68) ->
    exists regs' m', msteps SEGS (mkst regs (0x82f74 : word) m rom) (mkst regs' (0x830b4 : word) m' rom)
      /\ sinv m' /\ cellsZ m' (frameN ret regs) /\ rdn SEGS m' (Z_to_bv 64 (s - 148)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v)))
      /\ (forall a : word, ~ (s - 160 <= u a < s - 96)%Z -> ~ (s - 68 <= u a < s - 64)%Z -> m' a = m a)
      /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 8 = Z_to_bv 64 (s - 68) /\ getr regs' 9 = Z_to_bv 64 y /\ getr regs' 18 = Z_to_bv 64 x
      /\ getr regs' 19 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m x y ret SI Hx H2 H1 H10 H11 H12 H13 H14.
    destruct (sinv_facts m SI) as (PX & SOK & _ & _).
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF).
    assert (AL68 : ((s - 68) mod 4 = 0)%Z) by (apply sub_al4; [exact Hs16 | reflexivity]).
    assert (AL148 : ((s - 148) mod 4 = 0)%Z) by (apply sub_al4; [exact Hs16 | reflexivity]).
    assert (AL152 : ((s - 152) mod 4 = 0)%Z) by (apply sub_al4; [exact Hs16 | reflexivity]).
    eexists _, _. split.
    - zv F_82f1c D_82f1c (Z_to_bv 64 (s - 160)).
      stepST F_82f20 D_82f20 (Z_to_bv 64 (s - 104)) ret ltac:(sok_in SOK).
      stepST F_82f24 D_82f24 (Z_to_bv 64 (s - 112)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_82f28 D_82f28 (Z_to_bv 64 (s - 120)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_82f2c D_82f2c (Z_to_bv 64 (s - 128)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_82f30 D_82f30 (Z_to_bv 64 (s - 136)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_82f34 D_82f34 (Z_to_bv 64 (s - 144)) (getr regs 20) ltac:(sok_in SOK).
      stepb_ft F_82f38 D_82f38 ltac:(condZ).
      sn F_82f3c D_82f3c. sn F_82f40 D_82f40.
      zand F_82f44 D_82f44 andi_3 AL68.
      stepb_ft F_82f48 D_82f48 ltac:(condZ).
      stepST F_82f4c D_82f4c (Z_to_bv 64 (s - 68)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_82f50 D_82f50 ltac:(condZ).
      sn F_82f54 D_82f54. sn F_82f58 D_82f58. sn F_82f5c D_82f5c. sn F_82f60 D_82f60. sn F_82f64 D_82f64.
      depth_inline PX Hd1 ALp (0x82fc0 : word).
      sn F_82f68 D_82f68.
      stepb_ft F_82f6c D_82f6c ltac:(condZ).
      sn F_82f70 D_82f70.
      stepb_tk F_82f74 D_82f74 ltac:(condZ).
      zv F_83034 D_83034 (Z_to_bv 64 (s - 148)). zv F_83038 D_83038 (Z_to_bv 64 (s - 152)). sn F_8303c D_8303c. sn F_83040 D_83040. sn F_83044 D_83044.
      dims_inline PX SOK v (s - 148)%Z (s - 152)%Z AL148 AL152 ALp (0x830a0 : word).
      sn F_83048 D_83048.
      stepb_ft F_8304c D_8304c ltac:(condZ).
      stepb_ft F_83050 D_83050 ltac:(condZ).
      stepLD F_83054 D_83054 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepb_ft F_83058 D_83058 ltac:(condZ).
      apply mst_refl.
    - split.
      { repeat (apply sinv_wbytes; [| lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]). exact SI. }
      split; [unfold frameN; cbn [cellsZ]; repeat split; rdn_solve|].
      split; [rdn_peel1; apply rdn_wbytes_hit4; rewrite u_Z2bv by lia; lia|].
      split; [intros a N1 N2; rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia); reflexivity|].
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma lon_pre : forall regs m (c y : Z),
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 9 = Z_to_bv 64 y -> getr regs 18 = Z_to_bv 64 c -> getr regs 19 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (mkst regs (0x830b4 : word) m rom) (mkst regs' (0x6496c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 1 = Z_to_bv 64 0x830c8 /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 c
      /\ getr regs' 12 = Z_to_bv 64 y /\ getr regs' 13 = Z_to_bv 64 (s - 156)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m c y H2 H9 H18 H19. eexists. split.
    - zv F_8305c D_8305c (Z_to_bv 64 (s - 156)). sn F_83060 D_83060. sn F_83064 D_83064. sn F_83068 D_83068. sn F_8306c D_8306c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma lon_off : forall regs m,
    rdn SEGS m (Z_to_bv 64 (s - 156)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) -> getr regs 2 = Z_to_bv 64 (s - 160) ->
    exists regs', msteps SEGS (mkst regs (0x830c8 : word) m rom) (mkst regs' (0x830dc : word) m rom)
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m Rv H2. eexists. split.
    - stepLD F_83070 D_83070 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 0) by lia.
      stepb_tk F_83074 D_83074 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  Lemma lon_on : forall regs m (c : Z) (pcn : word),
    (0 <= c < p_w v)%Z -> (pcn = (if (c + 1 <? p_w v)%Z then (0x830b4 : word) else (0x830dc : word))) ->
    rdn SEGS m (Z_to_bv 64 (s - 156)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    rdn SEGS m (Z_to_bv 64 (s - 148)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) ->
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 18 = Z_to_bv 64 c ->
    exists regs', msteps SEGS (mkst regs (0x830c8 : word) m rom) (mkst regs' pcn m rom)
      /\ getr regs' 18 = Z_to_bv 64 (c + 1) /\ regs_agree (fun r => In r [10; 18]%list) regs regs'.
  Proof.
    intros regs m c pcn Hc Epc Rv Rw H2 H18. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    destruct (Z.ltb_spec (c + 1) (p_w v)) as [LT|GE]; subst pcn.
    - eexists. split.
      + stepLD F_83070 D_83070 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        try rewrite (v_lw_small 1) by lia.
        stepb_ft F_83074 D_83074 ltac:(condZ).
        stepLD F_83078 D_83078 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small (p_w v)) by lia.
        stepat F_8307c D_8307c (Z_to_bv 64 (c + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
        stepb_tk F_83080 D_83080 ltac:(condZ). apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + stepLD F_83070 D_83070 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        try rewrite (v_lw_small 1) by lia.
        stepb_ft F_83074 D_83074 ltac:(condZ).
        stepLD F_83078 D_83078 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small (p_w v)) by lia.
        stepat F_8307c D_8307c (Z_to_bv 64 (c + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
        stepb_ft F_83080 D_83080 ltac:(condZ). apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma frameN_out : forall m m' ret r0, (forall a : word, ~ (s - 224 <= u a < s - 160)%Z -> ~ (s - 156 <= u a < s - 152)%Z -> m' a = m a) ->
    cellsZ m (frameN ret r0) -> cellsZ m' (frameN ret r0).
  Proof.
    intros m m' ret r0 OUT. apply cellsZ_keep. unfold frameN.
    repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros z Hz; apply OUT; lia]] |]). apply Forall_nil.
  Qed.

  Lemma lon_loop : forall (k : nat) regs m (c y : Z) (ret : word) (r0 : bvmap 5 word),
    (p_w v - c <= Z.of_nat k)%Z -> sinv m -> cellsZ m (frameN ret r0) -> (0 <= c < p_w v)%Z -> (0 <= y < p_h v)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 148)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) ->
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 9 = Z_to_bv 64 y -> getr regs 18 = Z_to_bv 64 c -> getr regs 19 = Z_to_bv 64 pix ->
    exists regs' m' c', msteps SEGS (mkst regs (0x830b4 : word) m rom) (mkst regs' (0x830dc : word) m' rom)
      /\ sinv m' /\ cellsZ m' (frameN ret r0) /\ (c <= c' <= p_w v)%Z /\ (pxl c y = 1%Z -> c + 1 <= c')%Z /\ getr regs' 18 = Z_to_bv 64 c'
      /\ (forall a : word, ~ (s - 224 <= u a < s - 160)%Z -> ~ (s - 156 <= u a < s - 152)%Z -> m' a = m a)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs m c y ret r0 Hk SI CE Hc Hy Rw H2 H9 H18 H19; [lia|].
    destruct (lon_pre regs m c y H2 H9 H18 H19) as (r1 & RUN1 & P2 & P1 & P10 & P11 & P12 & P13 & AG1).
    destruct (px_read r1 m (s - 160)%Z c y (s - 156)%Z (Z_to_bv 64 0x830c8) SI Hc Hy ltac:(lia)
                ltac:(replace (s - 160)%Z with (s + (-160))%Z by lia; apply mod16_plus_mod16; [exact Hs16 | reflexivity]) ltac:(lia) ltac:(lia)
                ltac:(apply sub_al4; [exact Hs16 | reflexivity]) ltac:(left; lia) P2 P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13)
      as (r2 & m2 & RUN2 & SI2 & Rv & OUT2 & Q2 & AG2).
    replace (Z_to_bv 64 0x830c8) with (0x830c8 : word) in RUN2 by (apply bv_eq; reflexivity).
    replace (s - 160 - 64)%Z with (s - 224)%Z in OUT2 by lia. replace (s - 156 + 4)%Z with (s - 152)%Z in OUT2 by lia.
    pose proof (frameN_out m m2 ret r0 OUT2 CE) as CE2.
    assert (Rw2 : rdn SEGS m2 (Z_to_bv 64 (s - 148)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v)))).
    { rewrite <- Rw. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; cbn in Ha; apply OUT2; lia]. }
    assert (Q18 : getr r2 18 = Z_to_bv 64 c) by (rewrite (AG2 18%bv), (AG1 18%bv) by notin_list; exact H18).
    unfold pxl in Rv |- *. destruct (pbit_cases (mword m0 (pxa c y)) c) as [B0|B1].
    - rewrite B0 in Rv. destruct (lon_off r2 m2 Rv Q2) as (r3 & RUN3 & AG3).
      exists r3, m2, c. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
      split; [exact SI2|]. split; [exact CE2|]. split; [lia|]. split; [intros X; rewrite B0 in X; discriminate|].
      split; [rewrite (AG3 18%bv) by notin_list; exact Q18|]. split; [exact OUT2 | ra_chain].
    - rewrite B1 in Rv.
      destruct (lon_on r2 m2 c _ Hc eq_refl Rv Rw2 Q2 Q18) as (r3 & RUN3 & V18 & AG3).
      destruct (Z.ltb_spec (c + 1) (p_w v)) as [LT|GE].
      + destruct (IH r3 m2 (c + 1)%Z y ret r0 ltac:(lia) SI2 CE2 ltac:(lia) Hy Rw2) as (r4 & m4 & c' & RUN4 & SI4 & CE4 & Hc' & _ & W18 & OUT4 & AG4).
        { rewrite (AG3 2%bv) by notin_list. exact Q2. }
        { rewrite (AG3 9%bv), (AG2 9%bv), (AG1 9%bv) by notin_list. exact H9. }
        { exact V18. }
        { rewrite (AG3 19%bv), (AG2 19%bv), (AG1 19%bv) by notin_list. exact H19. }
        exists r4, m4, c'. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|].
        split; [exact SI4|]. split; [exact CE4|]. split; [lia|]. split; [intros _; lia|]. split; [exact W18|].
        split; [intros a N1 N2; rewrite (OUT4 a N1 N2); exact (OUT2 a N1 N2) | ra_chain].
      + exists r3, m2, (c + 1)%Z. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
        split; [exact SI2|]. split; [exact CE2|]. split; [lia|]. split; [intros _; lia|]. split; [exact V18|]. split; [exact OUT2 | ra_chain].
  Qed.

  Lemma lon_Z : forall regs r0 m (c' : Z) (ret : word),
    (1 <= c' <= p_w v)%Z -> ret_ok ret -> cellsZ m (frameN ret r0) -> store_ok SEGS m (Z_to_bv 64 (s - 68)) 4 = true ->
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 (s - 68) -> getr regs 18 = Z_to_bv 64 c' ->
    exists regs', msteps SEGS (mkst regs (0x830dc : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 (s - 68)) (word_to_le_bytes 4 (Z_to_bv 64 (c' - 1)))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96)
      /\ (forall x, In x [8; 9; 18; 19; 20]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs r0 m c' ret Hc Hret CE SOKl H2 H8 H18. unfold frameN in CE. cbn [cellsZ] in CE.
    pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & _). eexists. split.
    - stepat F_83084 D_83084 (Z_to_bv 64 (c' - 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
      stepb_ft F_83088 D_83088 ltac:(condZ).
      sn F_8308c D_8308c.
      stepST F_83090 D_83090 (Z_to_bv 64 (s - 68)) (Z_to_bv 64 (c' - 1)) ltac:(store_ok_peel; exact SOKl).
      sn F_83094 D_83094.
      stepLD8 F_83014 D_83014 ret. stepLD8 F_83018 D_83018 (getr r0 8). stepLD8 F_8301c D_8301c (getr r0 9). stepLD8 F_83020 D_83020 (getr r0 18).
      stepLD8 F_83024 D_83024 (getr r0 19). stepLD8 F_83028 D_83028 (getr r0 20).
      zv F_8302c D_8302c (Z_to_bv 64 (s - 96)). stepret F_83030 D_83030 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  Lemma laston_run : forall regs m (x y : Z) (ret : word),
    sinv m -> (0 <= x < p_w v)%Z -> (0 <= y < p_h v)%Z -> pxl x y = 1%Z -> ret_ok ret ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y ->
    getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 (s - 68) ->
    exists regs' m' loc, msteps SEGS (mkst regs (0x82f74 : word) m rom) (mkst regs' ret m' rom)
      /\ sinv m' /\ (x <= loc < p_w v)%Z /\ rdn SEGS m' (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc))
      /\ (forall a : word, ~ (s - 240 <= u a < s - 96)%Z -> ~ (s - 68 <= u a < s - 64)%Z -> m' a = m a)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m x y ret SI Hx Hy HON Hret H2 H1 H10 H11 H12 H13 H14.
    pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF) as Rw.
    destruct (lon_A regs m x y ret SI Hx H2 H1 H10 H11 H12 H13 H14) as (r1 & m1 & RUN1 & SI1 & CE1 & Rw1 & OUT1 & P2 & P8 & P9 & P18 & P19 & AG1).
    destruct (lon_loop (Z.to_nat (p_w v - x)) r1 m1 x y ret regs ltac:(lia) SI1 CE1 Hx Hy Rw1 P2 P9 P18 P19)
      as (r2 & m2 & c' & RUN2 & SI2 & CE2 & Hc' & HC & Q18 & OUT2 & AG2).
    specialize (HC HON).
    destruct (sinv_facts m2 SI2) as (_ & SOK2 & _ & _).
    assert (SOKl : store_ok SEGS m2 (Z_to_bv 64 (s - 68)) 4 = true).
    { eapply store_ok_sub; [ | exact SOK2 | | ]; rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    destruct (lon_Z r2 regs m2 c' ret ltac:(lia) Hret CE2 SOKl) as (r3 & RUN3 & V2 & VR & AG3).
    { rewrite (AG2 2%bv) by notin_list. exact P2. }
    { rewrite (AG2 8%bv) by notin_list. exact P8. }
    { exact Q18. }
    exists r3, (wbytes m2 (Z_to_bv 64 (s - 68)) (word_to_le_bytes 4 (Z_to_bv 64 (c' - 1)))), (c' - 1)%Z.
    split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
    split; [apply sinv_wbytes; [exact SI2 | lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
    split; [lia|]. split; [apply rdn_wbytes_hit4; rewrite u_Z2bv by lia; lia|].
    split.
    - intros a N1 N2. rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia).
      rewrite (OUT2 a ltac:(lia) ltac:(lia)). apply OUT1; lia.
    - intros r Hr. destruct (bv_eq_dec 5 r 2%bv) as [->|N2]; [rewrite V2, H2; reflexivity|].
      destruct (bv_eq_dec 5 r 8%bv) as [->|N8]; [apply VR; in_list|]. destruct (bv_eq_dec 5 r 9%bv) as [->|N9]; [apply VR; in_list|].
      destruct (bv_eq_dec 5 r 18%bv) as [->|N18]; [apply VR; in_list|]. destruct (bv_eq_dec 5 r 19%bv) as [->|N19]; [apply VR; in_list|].
      destruct (bv_eq_dec 5 r 20%bv) as [->|N20]; [apply VR; in_list|].
      assert (NI : forall L, (forall q, In q L -> q = 2%bv \/ q = 8%bv \/ q = 9%bv \/ q = 18%bv \/ q = 19%bv \/ q = 20%bv \/ In q [1; 10; 11; 12; 13; 14; 15; 16; 17]%bv) -> ~ In r L).
      { intros L HL HI. destruct (HL r HI) as [X|[X|[X|[X|[X|[X|X]]]]]]; first [contradiction | exact (Hr X)]. }
      rewrite (AG3 r), (AG2 r), (AG1 r); [reflexivity | | |]; apply NI; intros q Hq; cbn [In] in Hq |- *;
        repeat (destruct Hq as [<-|Hq]; [tauto|]); destruct Hq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis RW0 : rdn SEGS m0 (Z_to_bv 64 (s - 60)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))).

  (* [comment removed for export] *)
  Collection ScanHyps := Hs Hs64 Hs16 PX0 Hd1 Hw1 Hw32 Hsz ALd Hdp Gp ALp Hpix Hdat SOK0 RDEF JT0 RW0.

  Lemma sinv_w : forall m, sinv m -> rdn SEGS m (Z_to_bv 64 (s - 60)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))).
  Proof. intros m [_ E]. rewrite <- RW0. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; apply E; unfold scanR; cbn in Ha; lia]. Qed.

  (* [comment removed for export] *)
  Lemma vp_fix0 : forall regs m (c' : Z),
    sinv m -> (0 <= c' <= p_w v)%Z -> rdn SEGS m (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 c')) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs' loc, msteps SEGS (mkst regs (0x828e0 : word) m rom)
                                  (mkst regs' (0x828f8 : word) (wbytes m (Z_to_bv 64 (s - 68)) (word_to_le_bytes 4 (Z_to_bv 64 loc))) rom)
      /\ (0 <= loc < p_w v)%Z /\ getr regs' 10 = Z_to_bv 64 loc /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m c' SI Hc Rl H2. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    destruct (sinv_facts m SI) as (_ & SOK & _ & _). pose proof (sinv_w m SI) as Rw.
    destruct (Z.eq_dec c' 0) as [->|NZ].
    - exists (regupd (regupd (regupd regs 11 (Z_to_bv 64 0)) 11 (Z_to_bv 64 (p_w v))) 10 (Z_to_bv 64 (p_w v - 1))), (p_w v - 1)%Z. split.
      + stepLD F_82888 D_82888 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact Rl) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        try rewrite (v_lw_small 0) by lia.
        stepb_ft F_8288c D_8288c ltac:(condZ).
        stepLD F_82890 D_82890 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small (p_w v)) by lia.
        stepat F_82894 D_82894 (Z_to_bv 64 (p_w v - 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
        stepb_ft F_82898 D_82898 ltac:(condZ).
        stepST F_8289c D_8289c (Z_to_bv 64 (s - 68)) (Z_to_bv 64 (p_w v - 1)) ltac:(sok_in SOK).
        apply mst_refl.
      + split; [lia|]. split; [gres; reflexivity | solve_regs_agree].
    - exists (regupd (regupd regs 11 (Z_to_bv 64 c')) 10 (Z_to_bv 64 (c' - 1))), (c' - 1)%Z. split.
      + stepLD F_82888 D_82888 (word_to_le_bytes 4 (Z_to_bv 64 c')) (Z_to_bv 64 c') ltac:(addr_norm; exact Rl) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small c') by lia.
        stepb_tk F_8288c D_8288c ltac:(condZ).
        stepat F_82894 D_82894 (Z_to_bv 64 (c' - 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
        stepb_ft F_82898 D_82898 ltac:(condZ).
        stepST F_8289c D_8289c (Z_to_bv 64 (s - 68)) (Z_to_bv 64 (c' - 1)) ltac:(sok_in SOK).
        apply mst_refl.
      + split; [lia|]. split; [gres; reflexivity | solve_regs_agree].
  Qed.

  Lemma vp_fixk : forall regs m (c' : Z),
    sinv m -> (0 <= c' <= p_w v)%Z -> rdn SEGS m (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 c')) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs' loc, msteps SEGS (mkst regs (0x82980 : word) m rom)
                                  (mkst regs' (0x82934 : word) (wbytes m (Z_to_bv 64 (s - 68)) (word_to_le_bytes 4 (Z_to_bv 64 loc))) rom)
      /\ (0 <= loc < p_w v)%Z /\ getr regs' 10 = Z_to_bv 64 loc /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m c' SI Hc Rl H2. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    destruct (sinv_facts m SI) as (_ & SOK & _ & _). pose proof (sinv_w m SI) as Rw.
    destruct (Z.eq_dec c' 0) as [->|NZ].
    - exists (regupd (regupd (regupd regs 11 (Z_to_bv 64 0)) 11 (Z_to_bv 64 (p_w v))) 10 (Z_to_bv 64 (p_w v - 1))), (p_w v - 1)%Z. split.
      + stepLD F_82928 D_82928 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact Rl) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        try rewrite (v_lw_small 0) by lia.
        stepb_ft F_8292c D_8292c ltac:(condZ).
        stepLD F_82930 D_82930 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small (p_w v)) by lia.
        stepat F_82934 D_82934 (Z_to_bv 64 (p_w v - 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
        stepb_ft F_82938 D_82938 ltac:(condZ).
        stepST F_8293c D_8293c (Z_to_bv 64 (s - 68)) (Z_to_bv 64 (p_w v - 1)) ltac:(sok_in SOK).
        sn F_82940 D_82940.
        apply mst_refl.
      + split; [lia|]. split; [gres; reflexivity | solve_regs_agree].
    - exists (regupd (regupd regs 11 (Z_to_bv 64 c')) 10 (Z_to_bv 64 (c' - 1))), (c' - 1)%Z. split.
      + stepLD F_82928 D_82928 (word_to_le_bytes 4 (Z_to_bv 64 c')) (Z_to_bv 64 c') ltac:(addr_norm; exact Rl) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small c') by lia.
        stepb_tk F_8292c D_8292c ltac:(condZ).
        stepat F_82934 D_82934 (Z_to_bv 64 (c' - 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
        stepb_ft F_82938 D_82938 ltac:(condZ).
        stepST F_8293c D_8293c (Z_to_bv 64 (s - 68)) (Z_to_bv 64 (c' - 1)) ltac:(sok_in SOK).
        sn F_82940 D_82940.
        apply mst_refl.
      + split; [lia|]. split; [gres; reflexivity | solve_regs_agree].
  Qed.

  (* [comment removed for export] *)
  Lemma vp_row0 : forall regs,
    (1 <= p_h v)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 1 = Z_to_bv 64 0x828e0 -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 (p_w v - 1) ->
    getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 (s - 68) ->
    exists regs' m' loc, msteps SEGS (mkst regs (0x82d10 : word) m0 rom) (mkst regs' (0x828f8 : word) m' rom)
      /\ sinv m' /\ (0 <= loc < p_w v)%Z /\ getr regs' 10 = Z_to_bv 64 loc
      /\ rdn SEGS m' (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc))
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof using ScanHyps.
    intros regs Hh H2 H1 H10 H11 H12 H13 H14.
    destruct (lastoff_run regs m0 (p_w v - 1)%Z 0%Z (Z_to_bv 64 0x828e0) sinv_refl ltac:(lia) ltac:(lia) ltac:(red; apply bv_eq; reflexivity) H2 H1 H10 H11 H12 H13 H14)
      as (r1 & m1 & c' & RUN1 & SI1 & Hc' & Rc' & OUT1 & AG1).
    replace (Z_to_bv 64 0x828e0) with (0x828e0 : word) in RUN1 by (apply bv_eq; reflexivity).
    destruct (vp_fix0 r1 m1 c' SI1 ltac:(lia) Rc') as (r2 & loc & RUN2 & Hl & W10 & AG2).
    { rewrite (AG1 2%bv) by notin_list. exact H2. }
    exists r2, (wbytes m1 (Z_to_bv 64 (s - 68)) (word_to_le_bytes 4 (Z_to_bv 64 loc))), loc.
    split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|].
    split; [apply sinv_wbytes; [exact SI1 | lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
    split; [exact Hl|]. split; [exact W10|]. split; [apply rdn_wbytes_hit4; rewrite u_Z2bv by lia; lia | ra_chain].
  Qed.

  Lemma row_pre : forall regs m (loc y : Z),
    (0 <= loc < p_w v)%Z -> rdn SEGS m (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 20 = Z_to_bv 64 y ->
    exists regs', msteps SEGS (mkst regs (0x8294c : word) m rom) (mkst regs' (0x6496c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x82960 /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 loc
      /\ getr regs' 12 = Z_to_bv 64 y /\ getr regs' 13 = Z_to_bv 64 (s - 76)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m loc y Hl Rl H2 H19 H20. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF). eexists. split.
    - stepLD F_828f4 D_828f4 (word_to_le_bytes 4 (Z_to_bv 64 loc)) (Z_to_bv 64 loc) ltac:(addr_norm; exact Rl) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small loc) by lia.
      zv F_828f8 D_828f8 (Z_to_bv 64 (s - 76)). sn F_828fc D_828fc. sn F_82900 D_82900. sn F_82904 D_82904. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma row_on_pre : forall regs m (loc y : Z),
    (0 <= loc < p_w v)%Z -> rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    rdn SEGS m (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 20 = Z_to_bv 64 y -> getr regs 21 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x82960 : word) m rom) (mkst regs' (0x82f74 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x82930 /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 loc
      /\ getr regs' 12 = Z_to_bv 64 y /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 (s - 68)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m loc y Hl Rv Rl H2 H19 H20 H21. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF). eexists. split.
    - stepLD F_82908 D_82908 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 1) by lia.
      stepLD F_8290c D_8290c (word_to_le_bytes 4 (Z_to_bv 64 loc)) (Z_to_bv 64 loc) ltac:(addr_norm; exact Rl) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small loc) by lia.
      stepb_tk F_82910 D_82910 ltac:(condZ).
      zv F_828c4 D_828c4 (Z_to_bv 64 (s - 68)). sn F_828c8 D_828c8. sn F_828cc D_828cc. sn F_828d0 D_828d0. sn F_828d4 D_828d4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma row_on_post : forall regs m (loc : Z),
    (0 <= loc < p_w v)%Z -> rdn SEGS m (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc)) -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x82930 : word) m rom) (mkst regs' (0x82934 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 loc /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m loc Hl Rl H2. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF). eexists. split.
    - stepLD F_828d8 D_828d8 (word_to_le_bytes 4 (Z_to_bv 64 loc)) (Z_to_bv 64 loc) ltac:(addr_norm; exact Rl) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small loc) by lia. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma row_off_pre : forall regs m (loc y : Z),
    (0 <= loc < p_w v)%Z -> rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    rdn SEGS m (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 20 = Z_to_bv 64 y -> getr regs 21 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x82960 : word) m rom) (mkst regs' (0x82d10 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x82980 /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 loc
      /\ getr regs' 12 = Z_to_bv 64 y /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 (s - 68)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m loc y Hl Rv Rl H2 H19 H20 H21. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF). eexists. split.
    - stepLD F_82908 D_82908 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 0) by lia.
      stepLD F_8290c D_8290c (word_to_le_bytes 4 (Z_to_bv 64 loc)) (Z_to_bv 64 loc) ltac:(addr_norm; exact Rl) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small loc) by lia.
      stepb_ft F_82910 D_82910 ltac:(condZ).
      sn F_82914 D_82914. zv F_82918 D_82918 (Z_to_bv 64 (s - 68)). sn F_8291c D_8291c. sn F_82920 D_82920. sn F_82924 D_82924. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma vp_row : forall regs (loc y : Z),
    (0 <= loc < p_w v)%Z -> (0 <= y < p_h v)%Z -> rdn SEGS m0 (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 20 = Z_to_bv 64 y -> getr regs 21 = Z_to_bv 64 1 ->
    exists regs' m' loc', msteps SEGS (mkst regs (0x8294c : word) m0 rom) (mkst regs' (0x82934 : word) m' rom)
      /\ sinv m' /\ (0 <= loc' < p_w v)%Z /\ getr regs' 10 = Z_to_bv 64 loc'
      /\ rdn SEGS m' (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc'))
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof using ScanHyps.
    intros regs loc y Hl Hy Rl H2 H19 H20 H21.
    destruct (row_pre regs m0 loc y Hl Rl H2 H19 H20) as (r1 & RUN1 & P2 & P1 & P10 & P11 & P12 & P13 & AG1).
    destruct (px_read r1 m0 (s - 96)%Z loc y (s - 76)%Z (Z_to_bv 64 0x82960) sinv_refl Hl Hy ltac:(lia)
                ltac:(replace (s - 96)%Z with (s + (-96))%Z by lia; apply mod16_plus_mod16; [exact Hs16 | reflexivity]) ltac:(lia) ltac:(lia)
                ltac:(apply sub_al4; [exact Hs16 | reflexivity]) ltac:(right; reflexivity) P2 P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13)
      as (r2 & m2 & RUN2 & SI2 & Rv & OUT2 & Q2 & AG2).
    replace (Z_to_bv 64 0x82960) with (0x82960 : word) in RUN2 by (apply bv_eq; reflexivity).
    assert (Rl2 : rdn SEGS m2 (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc))).
    { rewrite <- Rl. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; cbn in Ha; apply OUT2; lia]. }
    assert (Q19 : getr r2 19 = Z_to_bv 64 pix) by (rewrite (AG2 19%bv), (AG1 19%bv) by notin_list; exact H19).
    assert (Q20 : getr r2 20 = Z_to_bv 64 y) by (rewrite (AG2 20%bv), (AG1 20%bv) by notin_list; exact H20).
    assert (Q21 : getr r2 21 = Z_to_bv 64 1) by (rewrite (AG2 21%bv), (AG1 21%bv) by notin_list; exact H21).
    destruct (pbit_cases (mword m0 (pxa loc y)) loc) as [B0|B1]; pose proof Rv as Rv'; unfold pxl in Rv'.
    - rewrite B0 in Rv'.
      destruct (row_off_pre r2 m2 loc y Hl Rv' Rl2 Q2 Q19 Q20 Q21) as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V13 & V14 & AG3).
      destruct (lastoff_run r3 m2 loc y (Z_to_bv 64 0x82980) SI2 Hl Hy ltac:(red; apply bv_eq; reflexivity) V2 V1 V10 V11 V12 V13 V14)
        as (r4 & m4 & c' & RUN4 & SI4 & Hc' & Rc' & OUT4 & AG4).
      replace (Z_to_bv 64 0x82980) with (0x82980 : word) in RUN4 by (apply bv_eq; reflexivity).
      destruct (vp_fixk r4 m4 c' SI4 ltac:(lia) Rc') as (r5 & loc' & RUN5 & Hl' & W10 & AG5).
      { rewrite (AG4 2%bv) by notin_list. exact V2. }
      exists r5, (wbytes m4 (Z_to_bv 64 (s - 68)) (word_to_le_bytes 4 (Z_to_bv 64 loc'))), loc'.
      split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|].
      split; [apply sinv_wbytes; [exact SI4 | lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
      split; [exact Hl'|]. split; [exact W10|]. split; [apply rdn_wbytes_hit4; rewrite u_Z2bv by lia; lia | ra_chain].
    - rewrite B1 in Rv'.
      destruct (row_on_pre r2 m2 loc y Hl Rv' Rl2 Q2 Q19 Q20 Q21) as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V13 & V14 & AG3).
      destruct (laston_run r3 m2 loc y (Z_to_bv 64 0x82930) SI2 Hl Hy B1 ltac:(red; apply bv_eq; reflexivity) V2 V1 V10 V11 V12 V13 V14)
        as (r4 & m4 & loc' & RUN4 & SI4 & Hl' & Rl' & OUT4 & AG4).
      replace (Z_to_bv 64 0x82930) with (0x82930 : word) in RUN4 by (apply bv_eq; reflexivity).
      destruct (row_on_post r4 m4 loc' ltac:(lia) Rl') as (r5 & RUN5 & W10 & AG5).
      { rewrite (AG4 2%bv) by notin_list. exact V2. }
      exists r5, m4, loc'.
      split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|].
      split; [exact SI4|]. split; [lia|]. split; [exact W10|]. split; [exact Rl' | ra_chain].
  Qed.

  End Scan.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FRP (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)).
  Definition frameP (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
    [((s - 8)%Z, ret); ((s - 16)%Z, getr r0 8); ((s - 24)%Z, getr r0 9); ((s - 32)%Z, getr r0 18); ((s - 40)%Z, getr r0 19); ((s - 48)%Z, getr r0 20);
     ((s - 56)%Z, getr r0 21)].

  (* [comment removed for export] *)
  Lemma vp_A : forall regs m (s pix : Z) (v : pixv) (ret : word),
    (0x20000 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> PIXat m pix v -> p_d v = 1%Z -> (4096 <= pix)%Z -> (pix mod 8 = 0)%Z -> (pix + 64 <= s - 240)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x82768 : word) m rom) (mkst regs' (0x61688 : word) (DIMS (FRP m s ret regs) (s - 60) (s - 64) (p_w v) (p_h v)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x82878 /\ getr regs' 10 = Z_to_bv 64 (p_h v)
      /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 pix /\ getr regs' 20 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s pix v ret Hs Hs64 Hs16 PX Hd1 Gp ALp Hpix SOK H2 H1 H10 H11 H12.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF).
    assert (AL60 : ((s - 60) mod 4 = 0)%Z) by (apply sub_al4; [exact Hs16 | reflexivity]).
    assert (AL64 : ((s - 64) mod 4 = 0)%Z) by (apply sub_al4; [exact Hs16 | reflexivity]).
    eexists. split.
    - zv F_82710 D_82710 (Z_to_bv 64 (s - 96)).
      stepST F_82714 D_82714 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_82718 D_82718 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_8271c D_8271c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_82720 D_82720 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_82724 D_82724 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_82728 D_82728 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_8272c D_8272c (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepb_ft F_82730 D_82730 ltac:(condZ).
      sn F_82734 D_82734. sn F_82738 D_82738. sn F_8273c D_8273c. sn F_82740 D_82740.
      depth_inline PX Hd1 ALp (0x8279c : word).
      sn F_82744 D_82744.
      stepb_ft F_82748 D_82748 ltac:(condZ).
      sn F_8274c D_8274c.
      stepb_tk F_82750 D_82750 ltac:(condZ).
      zv F_827f4 D_827f4 (Z_to_bv 64 (s - 60)). zv F_827f8 D_827f8 (Z_to_bv 64 (s - 64)). zv F_827fc D_827fc (Z_to_bv 64 (s - 64)).
      sn F_82800 D_82800. sn F_82804 D_82804. sn F_82808 D_82808.
      dims_inline PX SOK v (s - 60)%Z (s - 64)%Z AL60 AL64 ALp (0x82864 : word).
      sn F_8280c D_8280c.
      stepb_tk F_82810 D_82810 ltac:(condZ).
      stepLD F_82818 D_82818 (word_to_le_bytes 4 (Z_to_bv 64 (p_h v))) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      sn F_8281c D_8281c.
      unfold DIMS, FRP. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma vp_B : forall regs m (s pix na w : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> rdn SEGS m (Z_to_bv 64 (s - 60)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 na -> getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 pix -> getr regs 20 = Z_to_bv 64 2 ->
    exists regs', msteps SEGS (mkst regs (0x82878 : word) m rom) (mkst regs' (0x82d10 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x828e0 /\ getr regs' 9 = Z_to_bv 64 na /\ getr regs' 10 = Z_to_bv 64 pix
      /\ getr regs' 11 = Z_to_bv 64 (w - 1) /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 (s - 68)
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m s pix na w Hs Hs64 Hw Rw H2 H10 H18 H19 H20. eexists. split.
    - sn F_82820 D_82820.
      stepb_ft F_82824 D_82824 ltac:(condZ).
      sn F_82828 D_82828.
      stepb_tk F_8282c D_8282c ltac:(condZ).
      stepLD F_82868 D_82868 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small w) by lia.
      stepat F_8286c D_8286c (Z_to_bv 64 (w - 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
      stepb_ft F_82870 D_82870 ltac:(condZ).
      sn F_82874 D_82874. zv F_82878 D_82878 (Z_to_bv 64 (s - 68)). sn F_8287c D_8287c. sn F_82880 D_82880. sn F_82884 D_82884. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma vp_D_exit : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> rdn SEGS m (Z_to_bv 64 (s - 64)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x82904 : word) m rom) (mkst regs' (0x82c2c : word) m rom)
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 Rh H2. eexists. split.
    - stepLD F_828ac D_828ac (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 1) by lia.
      sn F_828b0 D_828b0.
      stepb_tk F_828b4 D_828b4 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.
  Lemma vp_D_loop : forall regs m (s h : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (2 <= h < 2 ^ 31)%Z -> rdn SEGS m (Z_to_bv 64 (s - 64)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x82904 : word) m rom) (mkst regs' (0x8294c : word) m rom)
      /\ getr regs' 20 = Z_to_bv 64 1 /\ getr regs' 21 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [10; 11; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s h Hs Hs64 Hh Rh H2. eexists. split.
    - stepLD F_828ac D_828ac (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small h) by lia.
      sn F_828b0 D_828b0.
      stepb_ft F_828b4 D_828b4 ltac:(condZ).
      sn F_828b8 D_828b8. sn F_828bc D_828bc. sn F_828c0 D_828c0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma vp_F : forall regs m (s h y : Z) (pcn : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= y < h)%Z -> (h < 2 ^ 31)%Z -> pcn = (if (y + 1 <? h)%Z then (0x8294c : word) else (0x82c2c : word)) ->
    rdn SEGS m (Z_to_bv 64 (s - 64)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 20 = Z_to_bv 64 y ->
    exists regs', msteps SEGS (mkst regs (0x82940 : word) m rom) (mkst regs' pcn m rom)
      /\ getr regs' 20 = Z_to_bv 64 (y + 1) /\ regs_agree (fun r => In r [10; 20]%list) regs regs'.
  Proof.
    intros regs m s h y pcn Hs Hs64 Hy Hh Epc Rh H2 H20.
    destruct (Z.ltb_spec (y + 1) h) as [LT|GE]; subst pcn.
    - eexists. split.
      + stepLD F_828e8 D_828e8 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small h) by lia.
        stepat F_828ec D_828ec (Z_to_bv 64 (y + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
        stepb_ft F_828f0 D_828f0 ltac:(condZ). apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + stepLD F_828e8 D_828e8 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small h) by lia.
        stepat F_828ec D_828ec (Z_to_bv 64 (y + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
        stepb_tk F_828f0 D_828f0 ltac:(condZ). apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma vp_Z : forall regs r0 m (s na : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameP s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 na ->
    exists regs', msteps SEGS (mkst regs (0x82c2c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 na
      /\ (forall x, In x [8; 9; 18; 19; 20; 21]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs r0 m s na ret Hs Hs64 Hret CE H2 H8 H9. unfold frameP in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & _). eexists. split.
    - stepb_tk F_82bd4 D_82bd4 ltac:(condZ).
      sn F_827cc D_827cc.
      stepLD8 F_827d0 D_827d0 ret. stepLD8 F_827d4 D_827d4 (getr r0 8). stepLD8 F_827d8 D_827d8 (getr r0 9). stepLD8 F_827dc D_827dc (getr r0 18).
      stepLD8 F_827e0 D_827e0 (getr r0 19). stepLD8 F_827e4 D_827e4 (getr r0 20). stepLD8 F_827e8 D_827e8 (getr r0 21).
      zv F_827ec D_827ec (Z_to_bv 64 s). stepret F_827f0 D_827f0 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

End ProfSegs.

(* [comment removed for export] *)
Section ProfFP.
Variable rom : word -> option byte.

  Lemma vp_C0 : forall (fx' : FPState) regs m (loc na : Z), frm_zero (@fp_csr fx') -> (0 <= loc < 2 ^ 31)%Z ->
    getr regs 10 = Z_to_bv 64 loc -> getr regs 9 = Z_to_bv 64 na ->
    exists (fx'' : FPState) regs', frm_zero (@fp_csr fx'') /\ reg_get (@fp_regs fx'') 10 = nan_box (Z_to_bv 32 (f32i loc))
      /\ msteps SEGS (@mkst fx' regs (0x828f8 : word) m rom) (@mkst fx'' regs' (0x61848 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x82904 /\ getr regs' 10 = Z_to_bv 64 na /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros fx' regs m loc na Hz Hl H10 H9.
    pose proof (fpv_step_fcvt_f_of_x fx' SEGS regs (0x828f8 : word) m rom W_828a0 FC_S FC_W 10 10 7 RNE FMT_S true 32%Z F_828a0 eq_refl D_828a0
                  (or_introl (conj eq_refl eq_refl)) (or_introl (conj eq_refl (conj eq_refl eq_refl))) Hz fpv_rm_dyn) as ST.
    rewrite H10 in ST. rewrite u_Z2bv in ST by lia.
    exists (mkFP (bvmap_set 10%bv (fpv_box FMT_S (fst (fp_of_int (fp_format FMT_S) RNE true 32 loc))) (@fp_regs fx')) (fpv_acc (@fp_csr fx') (snd (fp_of_int (fp_format FMT_S) RNE true 32 loc)))).
    eexists. split; [| split; [| split]].
    3:{ eapply mst_step; [reflexivity | exact ST |]. step_simpl. sn F_828a4 D_828a4. sn F_828a8 D_828a8. apply mst_refl. }
    - cbn [fp_csr]. apply fpv_frm_acc. exact Hz.
    - cbn [fp_regs]. rewrite fpv_get_same. reflexivity.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma vp_Ck : forall (fx' : FPState) regs m (loc na : Z), frm_zero (@fp_csr fx') -> (0 <= loc < 2 ^ 31)%Z ->
    getr regs 10 = Z_to_bv 64 loc -> getr regs 9 = Z_to_bv 64 na ->
    exists (fx'' : FPState) regs', frm_zero (@fp_csr fx'') /\ reg_get (@fp_regs fx'') 10 = nan_box (Z_to_bv 32 (f32i loc))
      /\ msteps SEGS (@mkst fx' regs (0x82934 : word) m rom) (@mkst fx'' regs' (0x61848 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x82940 /\ getr regs' 10 = Z_to_bv 64 na /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros fx' regs m loc na Hz Hl H10 H9.
    pose proof (fpv_step_fcvt_f_of_x fx' SEGS regs (0x82934 : word) m rom W_828dc FC_S FC_W 10 10 7 RNE FMT_S true 32%Z F_828dc eq_refl D_828dc
                  (or_introl (conj eq_refl eq_refl)) (or_introl (conj eq_refl (conj eq_refl eq_refl))) Hz fpv_rm_dyn) as ST.
    rewrite H10 in ST. rewrite u_Z2bv in ST by lia.
    exists (mkFP (bvmap_set 10%bv (fpv_box FMT_S (fst (fp_of_int (fp_format FMT_S) RNE true 32 loc))) (@fp_regs fx')) (fpv_acc (@fp_csr fx') (snd (fp_of_int (fp_format FMT_S) RNE true 32 loc)))).
    eexists. split; [| split; [| split]].
    3:{ eapply mst_step; [reflexivity | exact ST |]. step_simpl. sn F_828e0 D_828e0. sn F_828e4 D_828e4. apply mst_refl. }
    - cbn [fp_csr]. apply fpv_frm_acc. exact Hz.
    - cbn [fp_regs]. rewrite fpv_get_same. reflexivity.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End ProfFP.
