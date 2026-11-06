(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptScan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9LeptBase O9_code_edB O9LeptScan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ProfSegs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FRE (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
      (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
      (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
      (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
      (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
      (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)))
      (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)).
  (* [comment removed for export] *)
  Definition DIMS (m : word -> option byte) (aw ah w h : Z) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 aw) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 ah) (word_to_le_bytes 4 (Z_to_bv 64 0)))
           (Z_to_bv 64 aw) (word_to_le_bytes 4 (Z_to_bv 64 w))) (Z_to_bv 64 ah) (word_to_le_bytes 4 (Z_to_bv 64 h)).

  (* [comment removed for export] *)
  Ltac depth_inline PX Hd retpc :=
    stepb_ft F_63264 D_63264 ltac:(condZ);
    stepLD F_63268 D_63268 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; repeat rdn_peel1; rewrite <- Hd; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia);
    try rewrite (v_lw_small 1) by lia;
    stepret F_6326c D_6326c retpc ltac:(bveq).
  (* [comment removed for export] *)
  Ltac dims_inline PX SOK vv aw ah retpc :=
    stepb_ft F_628b8 D_628b8 ltac:(condZ);
    stepST F_628bc D_628bc (Z_to_bv 64 aw) (Z_to_bv 64 0) ltac:(sok_in SOK);
    stepb_ft F_628c0 D_628c0 ltac:(condZ);
    stepST F_628c4 D_628c4 (Z_to_bv 64 ah) (Z_to_bv 64 0) ltac:(sok_in SOK);
    stepb_tk F_628c8 D_628c8 ltac:(condZ);
    stepb_ft F_628d0 D_628d0 ltac:(condZ);
    stepb_ft F_628d4 D_628d4 ltac:(condZ);
    stepLD F_628d8 D_628d8 (Z_to_le_bytes 4 (p_w vv)) (Z_to_bv 64 (p_w vv)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia);
    rewrite (v_lw_small (p_w vv)) by lia;
    stepST F_628dc D_628dc (Z_to_bv 64 aw) (Z_to_bv 64 (p_w vv)) ltac:(sok_in SOK);
    stepb_ft F_628e0 D_628e0 ltac:(condZ);
    stepLD F_628e4 D_628e4 (Z_to_le_bytes 4 (p_h vv)) (Z_to_bv 64 (p_h vv)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia);
    rewrite (v_lw_small (p_h vv)) by lia;
    stepST F_628e8 D_628e8 (Z_to_bv 64 ah) (Z_to_bv 64 (p_h vv)) ltac:(sok_in SOK);
    sn F_628ec D_628ec;
    stepb_tk F_628f0 D_628f0 ltac:(condZ);
    sn F_628fc D_628fc;
    stepret F_62900 D_62900 retpc ltac:(bveq).

  (* [comment removed for export] *)
  Lemma ep_A : forall regs m (s pix : Z) (v : pixv) (ret : word),
    (0x20000 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_d v = 1%Z -> (4096 <= pix)%Z -> (pix + 64 <= s - 208)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x77d90 : word) m rom) (mkst regs' (0x609ec : word) (DIMS (FRE m s ret regs) (s - 116) (s - 120) (p_w v) (p_h v)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = Z_to_bv 64 0x77ee8 /\ getr regs' 10 = Z_to_bv 64 (p_h v)
      /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 pix /\ getr regs' 20 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s pix v ret Hs Hs64 PX Hd1 Gp Hpix SOK H2 H1 H10 H11 H12.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF).
    eexists. split.
    - zv F_77d38 D_77d38 (Z_to_bv 64 (s - 144)).
      stepST F_77d3c D_77d3c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_77d40 D_77d40 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_77d44 D_77d44 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_77d48 D_77d48 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_77d4c D_77d4c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_77d50 D_77d50 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_77d54 D_77d54 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_77d58 D_77d58 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_77d5c D_77d5c (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_77d60 D_77d60 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_77d64 D_77d64 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_77d68 D_77d68 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepST F_77d6c D_77d6c (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
      stepb_ft F_77d70 D_77d70 ltac:(condZ).
      sn F_77d74 D_77d74. sn F_77d78 D_77d78. sn F_77d7c D_77d7c. sn F_77d80 D_77d80.
      depth_inline PX Hd1 (0x77ddc : word).
      sn F_77d84 D_77d84.
      stepb_ft F_77d88 D_77d88 ltac:(condZ).
      sn F_77d8c D_77d8c.
      stepb_tk F_77d90 D_77d90 ltac:(condZ).
      zv F_77e64 D_77e64 (Z_to_bv 64 (s - 116)). zv F_77e68 D_77e68 (Z_to_bv 64 (s - 120)). zv F_77e6c D_77e6c (Z_to_bv 64 (s - 120)).
      sn F_77e70 D_77e70. sn F_77e74 D_77e74. sn F_77e78 D_77e78.
      dims_inline PX SOK v (s - 116)%Z (s - 120)%Z (0x77ed4 : word).
      sn F_77e7c D_77e7c.
      stepb_tk F_77e80 D_77e80 ltac:(condZ).
      stepLD F_77e88 D_77e88 (word_to_le_bytes 4 (Z_to_bv 64 (p_h v))) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      sn F_77e8c D_77e8c.
      unfold DIMS, FRE. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Scan.
  Variables (s pix : Z) (v : pixv) (m0 : word -> option byte).
  Hypothesis Hs : (0x20100 <= s)%Z.
  Hypothesis Hs64 : (s < 2 ^ 64)%Z.
  Hypothesis PX0 : PIXat m0 pix v.
  Hypothesis Hd1 : p_d v = 1%Z.
  Hypothesis Hw1 : (1 <= p_w v)%Z.
  Hypothesis Hw32 : (p_w v <= 32 * p_wpl v)%Z.
  Hypothesis Hsz : (4 * (p_wpl v * p_h v) <= 2 ^ 26)%Z.
  Hypothesis ALd : (p_data v mod 4 = 0)%Z.
  Hypothesis Hdp : (1 <= p_data v)%Z.
  Hypothesis Gp : (4096 <= pix)%Z.
  Hypothesis Hpix : (pix + 64 <= s - 208)%Z.
  Hypothesis Hdat : (p_data v + 4 * (p_wpl v * p_h v) <= s - 208)%Z.
  Hypothesis SOK0 : store_ok SEGS m0 (Z_to_bv 64 (s - 208)) 208 = true.
  Hypothesis RDEF : forall a : word, (p_data v <= u a < p_data v + 4 * (p_wpl v * p_h v))%Z -> m0 a <> None.
  Hypothesis JT0 : rdn SEGS m0 (Z_to_bv 64 0x1c64c) 4 = Some (Z_to_le_bytes 4 0x46fe0).

  (* [comment removed for export] *)
  Definition scanR (a : word) : Prop := (s - 208 <= u a < s - 120)%Z \/ (s - 112 <= u a < s - 104)%Z.
  Definition sinv (m : word -> option byte) : Prop := mem_grows m0 m /\ forall a : word, ~ scanR a -> m a = m0 a.
  (* [comment removed for export] *)
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
    PIXat m pix v /\ store_ok SEGS m (Z_to_bv 64 (s - 208)) 208 = true /\ rdn SEGS m (Z_to_bv 64 0x1c64c) 4 = Some (Z_to_le_bytes 4 0x46fe0) /\
    (forall x y, (0 <= x < p_w v)%Z -> (0 <= y < p_h v)%Z -> rdn SEGS m (Z_to_bv 64 (pxa x y)) 4 = Some (Z_to_le_bytes 4 (mword m0 (pxa x y)))).
  Proof.
    intros m [G E]. pose proof PX0 as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rd.
    split; [apply (PIXat_frame m0); [exact PX0 | intros x Hx; apply E; unfold scanR; lia]|].
    split; [exact (store_ok_mono SEGS _ m0 m _ G SOK0)|].
    split; [rewrite <- JT0; apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros x Hx; apply E; unfold scanR; cbn in Hx; lia]|].
    intros x y Hx Hy. destruct (pxa_in x y Hx Hy) as [A1 A2].
    assert (BA : bytes_at m0 (pxa x y) (Z_to_le_bytes 4 (mword m0 (pxa x y)))).
    { apply mword_bytes_at. intros i Hi. apply RDEF. rewrite u_Z2bv by lia. lia. }
    pose proof (bytes_at_rdn SEGS m0 (pxa x y) (Z_to_le_bytes 4 (mword m0 (pxa x y))) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) BA) as R0. rewrite length_Z_to_le_bytes in R0.
    rewrite <- R0. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; apply E; unfold scanR; cbn in Ha; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma px_read : forall regs m (x y pv : Z) (ret : word),
    sinv m -> (0 <= x < p_w v)%Z -> (0 <= y < p_h v)%Z -> (pv = s - 124 \/ pv = s - 112)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y -> getr regs 13 = Z_to_bv 64 pv ->
    exists regs' m',
      msteps SEGS (mkst regs (0x6357c : word) m rom) (mkst regs' ret m' rom)
      /\ sinv m' /\ rdn SEGS m' (Z_to_bv 64 pv) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (pxl x y)))
      /\ (forall a : word, ~ (s - 208 <= u a < s - 144)%Z -> ~ (pv <= u a < pv + 4)%Z -> m' a = m a)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m x y pv ret SI Hx Hy Hpv H2 H1 Hret H10 H11 H12 H13.
    destruct (sinv_facts m SI) as (PX & SOK & JT & RW). pose proof SI as [G E].
    assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 144 - 64)) 64 = true).
    { replace (s - 144 - 64)%Z with (s - 208)%Z by lia. eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    assert (SOKv : store_ok SEGS m (Z_to_bv 64 pv) 4 = true).
    { eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    destruct (pgp1_run rom regs m (s - 144) pv pix x y (mword m0 (pxa x y)) v ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PX Hd1 Hw1 Hw32 Hsz Hx Hy ALd Hdp
                Gp ltac:(lia) ltac:(lia) SOKf SOKv (RW x y Hx Hy) (mword_range _ _) JT H2 H1 Hret H10 H11 H12 H13)
      as (r' & RUN & Q2 & Q10 & Q8 & Q9 & Q18 & Q19 & Q20 & AG).
    eexists r', _. split; [exact RUN|].
    assert (OUT : forall a : word, ~ (s - 208 <= u a < s - 144)%Z -> ~ (pv <= u a < pv + 4)%Z ->
              wbytes (PGF m (s - 144) pv ret regs (p_w v) (p_h v) 1) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 (pbit (mword m0 (pxa x y)) x))) a = m a).
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
      apply AG. cbn [In] in *. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[]]]]]]]]]]]]]; subst r; first [contradiction | apply Hr; tauto].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis RW0 : rdn SEGS m0 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))).

  (* [comment removed for export] *)
  Collection ScanHyps := Hs Hs64 PX0 Hd1 Hw1 Hw32 Hsz ALd Hdp Gp Hpix Hdat SOK0 RDEF JT0 RW0.

  Lemma sinv_w : forall m, sinv m -> rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))).
  Proof. intros m [_ E]. rewrite <- RW0. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; apply E; unfold scanR; cbn in Ha; lia]. Qed.

  Lemma off_pre : forall regs m (c y : Z),
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 23 = Z_to_bv 64 y -> getr regs 24 = Z_to_bv 64 c ->
    exists regs', msteps SEGS (mkst regs (0x78254 : word) m rom) (mkst regs' (0x6357c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = Z_to_bv 64 0x7826c /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 c
      /\ getr regs' 12 = Z_to_bv 64 y /\ getr regs' 13 = Z_to_bv 64 (s - 112) /\ getr regs' 25 = Z_to_bv 64 c
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 25]%list) regs regs'.
  Proof.
    intros regs m c y H2 H19 H23 H24. eexists. split.
    - sn F_781fc D_781fc. zv F_78200 D_78200 (Z_to_bv 64 (s - 112)). sn F_78204 D_78204. sn F_78208 D_78208. sn F_7820c D_7820c. sn F_78210 D_78210. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma off_found : forall regs m (c : Z),
    (0 <= c < p_w v)%Z -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 25 = Z_to_bv 64 c -> getr regs 26 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x7826c : word) m rom) (mkst regs' (0x781a4 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (c + 1) /\ regs_agree (fun r => In r [10; 24]%list) regs regs'.
  Proof.
    intros regs m c Hc Rv H2 H25 H26. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    eexists. split.
    - stepLD F_78214 D_78214 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 1) by lia.
      stepb_tk F_78218 D_78218 ltac:(condZ).
      sn F_7826c D_7826c.
      stepat F_78270 D_78270 (Z_to_bv 64 (c + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
      stepb_ft F_78274 D_78274 ltac:(condZ).
      sn F_78278 D_78278. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma off_cont : forall regs m (c : Z),
    (1 <= c < p_w v)%Z -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 25 = Z_to_bv 64 c -> getr regs 26 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x7826c : word) m rom) (mkst regs' (0x78254 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (c - 1) /\ regs_agree (fun r => In r [10; 24]%list) regs regs'.
  Proof.
    intros regs m c Hc Rv H2 H25 H26. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    eexists. split.
    - stepLD F_78214 D_78214 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 0) by lia.
      stepb_ft F_78218 D_78218 ltac:(condZ).
      stepat F_7821c D_7821c (Z_to_bv 64 (c - 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
      stepb_tk F_78220 D_78220 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma off_end : forall regs m,
    rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x7826c : word) m rom) (mkst regs' (0x781a4 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (p_w v) /\ regs_agree (fun r => In r [10; 24]%list) regs regs'.
  Proof.
    intros regs m Rv Rw H2 H25 H26. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    eexists. split.
    - stepLD F_78214 D_78214 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 0) by lia.
      stepb_ft F_78218 D_78218 ltac:(condZ).
      sn F_7821c D_7821c.
      stepb_ft F_78220 D_78220 ltac:(condZ).
      sn F_78224 D_78224.
      stepLD F_78148 D_78148 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma off_scan : forall (k : nat) regs m (c y : Z),
    (c <= Z.of_nat k)%Z -> sinv m -> (0 <= c < p_w v)%Z -> (0 <= y < p_h v)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 23 = Z_to_bv 64 y -> getr regs 24 = Z_to_bv 64 c ->
    getr regs 26 = Z_to_bv 64 1 ->
    exists regs' m' c', msteps SEGS (mkst regs (0x78254 : word) m rom) (mkst regs' (0x781a4 : word) m' rom)
      /\ sinv m' /\ (1 <= c' <= p_w v)%Z /\ getr regs' 24 = Z_to_bv 64 c'
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 24; 25]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs m c y Hk SI Hc Hy H2 H19 H23 H24 H26.
    all: destruct (off_pre regs m c y H2 H19 H23 H24) as (r1 & RUN1 & P2 & P1 & P10 & P11 & P12 & P13 & P25 & AG1).
    all: destruct (px_read r1 m c y (s - 112)%Z (Z_to_bv 64 0x7826c) SI Hc Hy ltac:(right; reflexivity) P2 P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13)
           as (r2 & m2 & RUN2 & SI2 & Rv & OUT2 & Q2 & AG2).
    all: replace (Z_to_bv 64 0x7826c) with (0x7826c : word) in RUN2 by (apply bv_eq; reflexivity).
    all: assert (Q25 : getr r2 25 = Z_to_bv 64 c) by (rewrite (AG2 25%bv) by notin_list; exact P25).
    all: assert (Q26 : getr r2 26 = Z_to_bv 64 1) by (rewrite (AG2 26%bv), (AG1 26%bv) by notin_list; exact H26).
    all: destruct (pbit_cases (mword m0 (pxa c y)) c) as [B0|B1]; unfold pxl in Rv.
    - (* [comment removed for export] *)
      rewrite B0 in Rv. assert (c = 0)%Z by lia. subst c.
      destruct (off_end r2 m2 Rv (sinv_w m2 SI2) Q2 Q25 Q26) as (r3 & RUN3 & V24 & AG3).
      exists r3, m2, (p_w v). split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
      split; [exact SI2|]. split; [lia|]. split; [exact V24|]. ra_chain.
    - rewrite B1 in Rv.
      destruct (off_found r2 m2 c Hc Rv Q2 Q25 Q26) as (r3 & RUN3 & V24 & AG3).
      exists r3, m2, (c + 1)%Z. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
      split; [exact SI2|]. split; [lia|]. split; [exact V24|]. ra_chain.
    - rewrite B0 in Rv. destruct (Z.eq_dec c 0) as [->|NZ].
      + destruct (off_end r2 m2 Rv (sinv_w m2 SI2) Q2 Q25 Q26) as (r3 & RUN3 & V24 & AG3).
        exists r3, m2, (p_w v). split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
        split; [exact SI2|]. split; [lia|]. split; [exact V24|]. ra_chain.
      + destruct (off_cont r2 m2 c ltac:(lia) Rv Q2 Q25 Q26) as (r3 & RUN3 & V24 & AG3).
        destruct (IH r3 m2 (c - 1)%Z y ltac:(lia) SI2 ltac:(lia) Hy) as (r4 & m4 & c' & RUN4 & SI4 & Hc' & W24 & AG4).
        { rewrite (AG3 2%bv) by notin_list. exact Q2. }
        { rewrite (AG3 19%bv), (AG2 19%bv), (AG1 19%bv) by notin_list. exact H19. }
        { rewrite (AG3 23%bv), (AG2 23%bv), (AG1 23%bv) by notin_list. exact H23. }
        { exact V24. }
        { rewrite (AG3 26%bv) by notin_list. exact Q26. }
        exists r4, m4, c'. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|].
        split; [exact SI4|]. split; [exact Hc'|]. split; [exact W24|]. ra_chain.
    - rewrite B1 in Rv.
      destruct (off_found r2 m2 c Hc Rv Q2 Q25 Q26) as (r3 & RUN3 & V24 & AG3).
      exists r3, m2, (c + 1)%Z. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
      split; [exact SI2|]. split; [lia|]. split; [exact V24|]. ra_chain.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma on_pre : forall regs m (c y : Z),
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 23 = Z_to_bv 64 y -> getr regs 24 = Z_to_bv 64 c ->
    exists regs', msteps SEGS (mkst regs (0x78204 : word) m rom) (mkst regs' (0x6357c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = Z_to_bv 64 0x78218 /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 c
      /\ getr regs' 12 = Z_to_bv 64 y /\ getr regs' 13 = Z_to_bv 64 (s - 112)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m c y H2 H19 H23 H24. eexists. split.
    - zv F_781ac D_781ac (Z_to_bv 64 (s - 112)). sn F_781b0 D_781b0. sn F_781b4 D_781b4. sn F_781b8 D_781b8. sn F_781bc D_781bc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma on_off : forall regs m,
    rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) -> getr regs 2 = Z_to_bv 64 (s - 144) ->
    exists regs', msteps SEGS (mkst regs (0x78218 : word) m rom) (mkst regs' (0x781a4 : word) m rom)
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m Rv H2. eexists. split.
    - stepLD F_781c0 D_781c0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 0) by lia.
      stepb_tk F_781c4 D_781c4 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma on_on : forall regs m (c : Z) (pcn : word),
    (0 <= c < p_w v)%Z -> (pcn = (if (c + 1 <? p_w v)%Z then (0x78204 : word) else (0x781a4 : word))) ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    rdn SEGS m (Z_to_bv 64 (s - 136)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 24 = Z_to_bv 64 c ->
    exists regs', msteps SEGS (mkst regs (0x78218 : word) m rom) (mkst regs' pcn m rom)
      /\ getr regs' 24 = Z_to_bv 64 (c + 1) /\ regs_agree (fun r => In r [10; 24]%list) regs regs'.
  Proof.
    intros regs m c pcn Hc Epc Rv Rw H2 H24. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    destruct (Z.ltb_spec (c + 1) (p_w v)) as [LT|GE]; subst pcn.
    - eexists. split.
      + stepLD F_781c0 D_781c0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        try rewrite (v_lw_small 1) by lia.
        stepb_ft F_781c4 D_781c4 ltac:(condZ).
        stepLD F_781c8 D_781c8 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small (p_w v)) by lia.
        stepat F_781cc D_781cc (Z_to_bv 64 (c + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
        stepb_tk F_781d0 D_781d0 ltac:(condZ). apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + stepLD F_781c0 D_781c0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        try rewrite (v_lw_small 1) by lia.
        stepb_ft F_781c4 D_781c4 ltac:(condZ).
        stepLD F_781c8 D_781c8 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small (p_w v)) by lia.
        stepat F_781cc D_781cc (Z_to_bv 64 (c + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
        stepb_ft F_781d0 D_781d0 ltac:(condZ).
        sn F_781d4 D_781d4. apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma on_scan : forall (k : nat) regs m (c y : Z),
    (p_w v - c <= Z.of_nat k)%Z -> sinv m -> (0 <= c < p_w v)%Z -> (0 <= y < p_h v)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 136)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 23 = Z_to_bv 64 y -> getr regs 24 = Z_to_bv 64 c ->
    exists regs' m' c', msteps SEGS (mkst regs (0x78204 : word) m rom) (mkst regs' (0x781a4 : word) m' rom)
      /\ sinv m' /\ (c <= c' <= p_w v)%Z /\ (pxl c y = 1%Z -> c + 1 <= c')%Z /\ getr regs' 24 = Z_to_bv 64 c'
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 24]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs m c y Hk SI Hc Hy Rw H2 H19 H23 H24; [lia|].
    destruct (on_pre regs m c y H2 H19 H23 H24) as (r1 & RUN1 & P2 & P1 & P10 & P11 & P12 & P13 & AG1).
    destruct (px_read r1 m c y (s - 112)%Z (Z_to_bv 64 0x78218) SI Hc Hy ltac:(right; reflexivity) P2 P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13)
      as (r2 & m2 & RUN2 & SI2 & Rv & OUT2 & Q2 & AG2).
    replace (Z_to_bv 64 0x78218) with (0x78218 : word) in RUN2 by (apply bv_eq; reflexivity).
    assert (Rw2 : rdn SEGS m2 (Z_to_bv 64 (s - 136)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v)))).
    { rewrite <- Rw. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; cbn in Ha; apply OUT2; lia]. }
    assert (Q24 : getr r2 24 = Z_to_bv 64 c) by (rewrite (AG2 24%bv), (AG1 24%bv) by notin_list; exact H24).
    unfold pxl in Rv |- *. destruct (pbit_cases (mword m0 (pxa c y)) c) as [B0|B1].
    - rewrite B0 in Rv. destruct (on_off r2 m2 Rv Q2) as (r3 & RUN3 & AG3).
      exists r3, m2, c. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
      split; [exact SI2|]. split; [lia|]. split; [intros X; rewrite B0 in X; discriminate|].
      split; [rewrite (AG3 24%bv) by notin_list; exact Q24 | ra_chain].
    - rewrite B1 in Rv.
      destruct (on_on r2 m2 c _ Hc eq_refl Rv Rw2 Q2 Q24) as (r3 & RUN3 & V24 & AG3).
      destruct (Z.ltb_spec (c + 1) (p_w v)) as [LT|GE].
      + destruct (IH r3 m2 (c + 1)%Z y ltac:(lia) SI2 ltac:(lia) Hy Rw2) as (r4 & m4 & c' & RUN4 & SI4 & Hc' & _ & W24 & AG4).
        { rewrite (AG3 2%bv) by notin_list. exact Q2. }
        { rewrite (AG3 19%bv), (AG2 19%bv), (AG1 19%bv) by notin_list. exact H19. }
        { rewrite (AG3 23%bv), (AG2 23%bv), (AG1 23%bv) by notin_list. exact H23. }
        { exact V24. }
        exists r4, m4, c'. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|].
        split; [exact SI4|]. split; [lia|]. split; [intros _; lia|]. split; [exact W24 | ra_chain].
      + exists r3, m2, (c + 1)%Z. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
        split; [exact SI2|]. split; [lia|]. split; [intros _; lia|]. split; [exact V24 | ra_chain].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma r0_pre : forall regs m (c : Z),
    (0 <= c < p_w v)%Z -> getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 21 = Z_to_bv 64 (c + 1) ->
    exists regs', msteps SEGS (mkst regs (0x77f8c : word) m rom) (mkst regs' (0x6357c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = Z_to_bv 64 0x77fa4 /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 c
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 (s - 112) /\ getr regs' 20 = Z_to_bv 64 c
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 20]%list) regs regs'.
  Proof.
    intros regs m c Hc H2 H19 H21. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF). eexists. split.
    - stepat F_77f34 D_77f34 (Z_to_bv 64 c) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
      zv F_77f38 D_77f38 (Z_to_bv 64 (s - 112)). sn F_77f3c D_77f3c. sn F_77f40 D_77f40. sn F_77f44 D_77f44. sn F_77f48 D_77f48. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma r0_found : forall regs m (c : Z),
    (0 <= c < p_w v)%Z -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 21 = Z_to_bv 64 (c + 1) -> getr regs 22 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x77fa4 : word) m rom) (mkst regs' (0x78150 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (c + 1) /\ regs_agree (fun r => In r [10; 21; 24]%list) regs regs'.
  Proof.
    intros regs m c Hc Rv H2 H21 H22. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    eexists. split.
    - stepLD F_77f4c D_77f4c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 1) by lia.
      stepb_tk F_77f50 D_77f50 ltac:(condZ).
      zv F_780e8 D_780e8 (Z_to_bv 64 c).
      stepat F_780ec D_780ec (Z_to_bv 64 (c + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
      stepb_tk F_780f0 D_780f0 ltac:(condZ). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma r0_cont : forall regs m (c : Z),
    (1 <= c < p_w v)%Z -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 20 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x77fa4 : word) m rom) (mkst regs' (0x77f8c : word) m rom)
      /\ getr regs' 21 = Z_to_bv 64 c /\ regs_agree (fun r => In r [10; 21]%list) regs regs'.
  Proof.
    intros regs m c Hc Rv H2 H20 H22. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    eexists. split.
    - stepLD F_77f4c D_77f4c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 0) by lia.
      stepb_ft F_77f50 D_77f50 ltac:(condZ).
      sn F_77f54 D_77f54.
      stepb_tk F_77f58 D_77f58 ltac:(condZ). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma r0_end : forall regs m,
    rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 20 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x77fa4 : word) m rom) (mkst regs' (0x78150 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (p_w v) /\ regs_agree (fun r => In r [10; 21; 24]%list) regs regs'.
  Proof.
    intros regs m Rv Rw H2 H20 H22. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF).
    eexists. split.
    - stepLD F_77f4c D_77f4c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 0) by lia.
      stepb_ft F_77f50 D_77f50 ltac:(condZ).
      sn F_77f54 D_77f54.
      stepb_ft F_77f58 D_77f58 ltac:(condZ).
      sn F_77f5c D_77f5c.
      stepLD F_780f4 D_780f4 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma r0_scan : forall (k : nat) regs m (c : Z),
    (c <= Z.of_nat k)%Z -> sinv m -> (0 <= c < p_w v)%Z -> (1 <= p_h v)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 21 = Z_to_bv 64 (c + 1) -> getr regs 22 = Z_to_bv 64 1 ->
    exists regs' m' c', msteps SEGS (mkst regs (0x77f8c : word) m rom) (mkst regs' (0x78150 : word) m' rom)
      /\ sinv m' /\ (1 <= c' <= p_w v)%Z /\ getr regs' 24 = Z_to_bv 64 c'
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 20; 21; 24]%list) regs regs'.
  Proof using ScanHyps.
    induction k as [|k IH]; intros regs m c Hk SI Hc Hh H2 H19 H21 H22.
    all: destruct (r0_pre regs m c Hc H2 H19 H21) as (r1 & RUN1 & P2 & P1 & P10 & P11 & P12 & P13 & P20 & AG1).
    all: destruct (px_read r1 m c 0%Z (s - 112)%Z (Z_to_bv 64 0x77fa4) SI Hc ltac:(lia) ltac:(right; reflexivity) P2 P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13)
           as (r2 & m2 & RUN2 & SI2 & Rv & OUT2 & Q2 & AG2).
    all: replace (Z_to_bv 64 0x77fa4) with (0x77fa4 : word) in RUN2 by (apply bv_eq; reflexivity).
    all: assert (Q20 : getr r2 20 = Z_to_bv 64 c) by (rewrite (AG2 20%bv) by notin_list; exact P20).
    all: assert (Q21 : getr r2 21 = Z_to_bv 64 (c + 1)) by (rewrite (AG2 21%bv), (AG1 21%bv) by notin_list; exact H21).
    all: assert (Q22 : getr r2 22 = Z_to_bv 64 1) by (rewrite (AG2 22%bv), (AG1 22%bv) by notin_list; exact H22).
    all: destruct (pbit_cases (mword m0 (pxa c 0)) c) as [B0|B1]; unfold pxl in Rv.
    - rewrite B0 in Rv. assert (c = 0)%Z by lia. subst c.
      destruct (r0_end r2 m2 Rv (sinv_w m2 SI2) Q2 Q20 Q22) as (r3 & RUN3 & V24 & AG3).
      exists r3, m2, (p_w v). split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
      split; [exact SI2|]. split; [lia|]. split; [exact V24|]. ra_chain.
    - rewrite B1 in Rv.
      destruct (r0_found r2 m2 c Hc Rv Q2 Q21 Q22) as (r3 & RUN3 & V24 & AG3).
      exists r3, m2, (c + 1)%Z. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
      split; [exact SI2|]. split; [lia|]. split; [exact V24|]. ra_chain.
    - rewrite B0 in Rv. destruct (Z.eq_dec c 0) as [->|NZ].
      + destruct (r0_end r2 m2 Rv (sinv_w m2 SI2) Q2 Q20 Q22) as (r3 & RUN3 & V24 & AG3).
        exists r3, m2, (p_w v). split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
        split; [exact SI2|]. split; [lia|]. split; [exact V24|]. ra_chain.
      + destruct (r0_cont r2 m2 c ltac:(lia) Rv Q2 Q20 Q22) as (r3 & RUN3 & V21 & AG3).
        destruct (IH r3 m2 (c - 1)%Z ltac:(lia) SI2 ltac:(lia) Hh) as (r4 & m4 & c' & RUN4 & SI4 & Hc' & W24 & AG4).
        { rewrite (AG3 2%bv) by notin_list. exact Q2. }
        { rewrite (AG3 19%bv), (AG2 19%bv), (AG1 19%bv) by notin_list. exact H19. }
        { rewrite V21. f_equal. lia. }
        { rewrite (AG3 22%bv) by notin_list. exact Q22. }
        exists r4, m4, c'. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|].
        split; [exact SI4|]. split; [exact Hc'|]. split; [exact W24|]. ra_chain.
    - rewrite B1 in Rv.
      destruct (r0_found r2 m2 c Hc Rv Q2 Q21 Q22) as (r3 & RUN3 & V24 & AG3).
      exists r3, m2, (c + 1)%Z. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|].
      split; [exact SI2|]. split; [lia|]. split; [exact V24|]. ra_chain.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sinv_dims : forall m, sinv m ->
    sinv (DIMS m (s - 136) (s - 108) (p_w v) (p_h v)) /\
    rdn SEGS (DIMS m (s - 136) (s - 108) (p_w v) (p_h v)) (Z_to_bv 64 (s - 136)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))).
  Proof.
    intros m [G E]. unfold DIMS. split; [split|].
    - eapply mem_grows_trans; [exact G|]. repeat (eapply mem_grows_trans; [| apply wbytes_grows]). apply mem_grows_refl.
    - intros a NR. unfold scanR in NR. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). apply E. exact NR.
    - rdn_peel1. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia.
  Qed.

  Lemma row_pre : forall regs m (c y : Z),
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 23 = Z_to_bv 64 y -> getr regs 24 = Z_to_bv 64 c ->
    exists regs', msteps SEGS (mkst regs (0x781c0 : word) m rom) (mkst regs' (0x6357c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = Z_to_bv 64 0x781d4 /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 c
      /\ getr regs' 12 = Z_to_bv 64 y /\ getr regs' 13 = Z_to_bv 64 (s - 124)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m c y H2 H19 H23 H24. eexists. split.
    - zv F_78168 D_78168 (Z_to_bv 64 (s - 124)). sn F_7816c D_7816c. sn F_78170 D_78170. sn F_78174 D_78174. sn F_78178 D_78178. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma row_on_pre : forall regs m (c : Z),
    (0 <= c < p_w v)%Z -> PIXat m pix v -> store_ok SEGS m (Z_to_bv 64 (s - 208)) 208 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 24 = Z_to_bv 64 c -> getr regs 26 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x781d4 : word) m rom) (mkst regs' (0x78204 : word) (DIMS m (s - 136) (s - 108) (p_w v) (p_h v)) rom)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m c Hc PX SOK Rv H2 H19 H24 H26. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF).
    eexists. split.
    - stepLD F_7817c D_7817c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 1) by lia.
      stepb_ft F_78180 D_78180 ltac:(condZ).
      sn F_78184 D_78184. sn F_78188 D_78188.
      depth_inline PX Hd1 (0x781e4 : word).
      stepb_ft F_7818c D_7818c ltac:(condZ).
      zv F_78190 D_78190 (Z_to_bv 64 (s - 136)). zv F_78194 D_78194 (Z_to_bv 64 (s - 108)). sn F_78198 D_78198. sn F_7819c D_7819c. sn F_781a0 D_781a0.
      dims_inline PX SOK v (s - 136)%Z (s - 108)%Z (0x781fc : word).
      stepLD F_781a4 D_781a4 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepb_ft F_781a8 D_781a8 ltac:(condZ).
      unfold DIMS. apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma row_off_pre : forall regs m (c : Z),
    (0 <= c < p_w v)%Z -> PIXat m pix v -> store_ok SEGS m (Z_to_bv 64 (s - 208)) 208 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 24 = Z_to_bv 64 c -> getr regs 26 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x781d4 : word) m rom) (mkst regs' (0x78254 : word) (DIMS m (s - 136) (s - 108) (p_w v) (p_h v)) rom)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m c Hc PX SOK Rv H2 H19 H24 H26. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF).
    eexists. split.
    - stepLD F_7817c D_7817c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 0) by lia.
      stepb_tk F_78180 D_78180 ltac:(condZ).
      sn F_781d8 D_781d8. sn F_781dc D_781dc.
      depth_inline PX Hd1 (0x78238 : word).
      stepb_ft F_781e0 D_781e0 ltac:(condZ).
      zv F_781e4 D_781e4 (Z_to_bv 64 (s - 136)). zv F_781e8 D_781e8 (Z_to_bv 64 (s - 108)). sn F_781ec D_781ec. sn F_781f0 D_781f0. sn F_781f4 D_781f4.
      dims_inline PX SOK v (s - 136)%Z (s - 108)%Z (0x78250 : word).
      stepb_ft F_781f8 D_781f8 ltac:(condZ).
      unfold DIMS. apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma row_dec : forall regs m (c' : Z), (1 <= c' <= p_w v)%Z -> getr regs 24 = Z_to_bv 64 c' ->
    exists regs', msteps SEGS (mkst regs (0x781a4 : word) m rom) (mkst regs' (0x781a8 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (c' - 1) /\ regs_agree (fun r => In r [24]%list) regs regs'.
  Proof.
    intros regs m c' Hc H24. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF). eexists. split.
    - stepat F_7814c D_7814c (Z_to_bv 64 (c' - 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma r0_dec : forall regs m (c' : Z), (1 <= c' <= p_w v)%Z -> getr regs 24 = Z_to_bv 64 c' ->
    exists regs', msteps SEGS (mkst regs (0x78150 : word) m rom) (mkst regs' (0x78154 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (c' - 1) /\ regs_agree (fun r => In r [24]%list) regs regs'.
  Proof using ScanHyps.
    intros regs m c' Hc H24. pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF). eexists. split.
    - stepat F_780f8 D_780f8 (Z_to_bv 64 (c' - 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ep_row : forall regs (c y : Z),
    (0 <= c < p_w v)%Z -> (0 <= y < p_h v)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 23 = Z_to_bv 64 y -> getr regs 24 = Z_to_bv 64 c ->
    getr regs 26 = Z_to_bv 64 1 ->
    exists regs' m' loc, msteps SEGS (mkst regs (0x781c0 : word) m0 rom) (mkst regs' (0x781a8 : word) m' rom)
      /\ sinv m' /\ (0 <= loc < p_w v)%Z /\ getr regs' 24 = Z_to_bv 64 loc
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 24; 25]%list) regs regs'.
  Proof using ScanHyps.
    intros regs c y Hc Hy H2 H19 H23 H24 H26.
    destruct (row_pre regs m0 c y H2 H19 H23 H24) as (r1 & RUN1 & P2 & P1 & P10 & P11 & P12 & P13 & AG1).
    destruct (px_read r1 m0 c y (s - 124)%Z (Z_to_bv 64 0x781d4) sinv_refl Hc Hy ltac:(left; reflexivity) P2 P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13)
      as (r2 & m2 & RUN2 & SI2 & Rv & OUT2 & Q2 & AG2).
    replace (Z_to_bv 64 0x781d4) with (0x781d4 : word) in RUN2 by (apply bv_eq; reflexivity).
    destruct (sinv_facts m2 SI2) as (PX2 & SOK2 & _ & _).
    assert (Q19 : getr r2 19 = Z_to_bv 64 pix) by (rewrite (AG2 19%bv), (AG1 19%bv) by notin_list; exact H19).
    assert (Q23 : getr r2 23 = Z_to_bv 64 y) by (rewrite (AG2 23%bv), (AG1 23%bv) by notin_list; exact H23).
    assert (Q24 : getr r2 24 = Z_to_bv 64 c) by (rewrite (AG2 24%bv), (AG1 24%bv) by notin_list; exact H24).
    assert (Q26 : getr r2 26 = Z_to_bv 64 1) by (rewrite (AG2 26%bv), (AG1 26%bv) by notin_list; exact H26).
    destruct (sinv_dims m2 SI2) as [SI3 Rw3].
    destruct (pbit_cases (mword m0 (pxa c y)) c) as [B0|B1]; pose proof Rv as Rv'; unfold pxl in Rv'.
    - (* [comment removed for export] *)
      rewrite B0 in Rv'.
      destruct (row_off_pre r2 m2 c Hc PX2 SOK2 Rv' Q2 Q19 Q24 Q26) as (r3 & RUN3 & AG3).
      destruct (off_scan (Z.to_nat c) r3 _ c y ltac:(lia) SI3 Hc Hy) as (r4 & m4 & c' & RUN4 & SI4 & Hc' & V24 & AG4).
      { rewrite (AG3 2%bv) by notin_list. exact Q2. }
      { rewrite (AG3 19%bv) by notin_list. exact Q19. }
      { rewrite (AG3 23%bv) by notin_list. exact Q23. }
      { rewrite (AG3 24%bv) by notin_list. exact Q24. }
      { rewrite (AG3 26%bv) by notin_list. exact Q26. }
      destruct (row_dec r4 m4 c' Hc' V24) as (r5 & RUN5 & W24 & AG5).
      exists r5, m4, (c' - 1)%Z.
      split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|].
      split; [exact SI4|]. split; [lia|]. split; [exact W24|]. ra_chain.
    - (* [comment removed for export] *)
      rewrite B1 in Rv'.
      destruct (row_on_pre r2 m2 c Hc PX2 SOK2 Rv' Q2 Q19 Q24 Q26) as (r3 & RUN3 & AG3).
      destruct (on_scan (Z.to_nat (p_w v - c)) r3 _ c y ltac:(lia) SI3 Hc Hy Rw3) as (r4 & m4 & c' & RUN4 & SI4 & Hc' & HON & V24 & AG4).
      { rewrite (AG3 2%bv) by notin_list. exact Q2. }
      { rewrite (AG3 19%bv) by notin_list. exact Q19. }
      { rewrite (AG3 23%bv) by notin_list. exact Q23. }
      { rewrite (AG3 24%bv) by notin_list. exact Q24. }
      specialize (HON B1).
      destruct (row_dec r4 m4 c' ltac:(lia) V24) as (r5 & RUN5 & W24 & AG5).
      exists r5, m4, (c' - 1)%Z.
      split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|].
      split; [exact SI4|]. split; [lia|]. split; [exact W24|]. ra_chain.
  Qed.

  End Scan.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition frameE (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
    [((s - 8)%Z, ret); ((s - 16)%Z, getr r0 8); ((s - 24)%Z, getr r0 9); ((s - 32)%Z, getr r0 18); ((s - 40)%Z, getr r0 19); ((s - 48)%Z, getr r0 20);
     ((s - 56)%Z, getr r0 21); ((s - 64)%Z, getr r0 22); ((s - 72)%Z, getr r0 23); ((s - 80)%Z, getr r0 24); ((s - 88)%Z, getr r0 25);
     ((s - 96)%Z, getr r0 26); ((s - 104)%Z, getr r0 27)].

  (* [comment removed for export] *)
  Lemma ep_B : forall regs m (s pix na : Z) (v : pixv),
    (0x20100 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_d v = 1%Z -> (1 <= p_w v)%Z -> (4096 <= pix)%Z -> (pix + 64 <= s - 208)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 208)) 208 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 na -> getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 pix -> getr regs 20 = Z_to_bv 64 2 ->
    exists regs',
      msteps SEGS (mkst regs (0x77ee8 : word) m rom) (mkst regs' (0x77f8c : word) (DIMS m (s - 136) (s - 108) (p_w v) (p_h v)) rom)
      /\ getr regs' 9 = Z_to_bv 64 na /\ getr regs' 21 = Z_to_bv 64 (p_w v) /\ getr regs' 22 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 14; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m s pix na v Hs Hs64 PX Hd1 Hw1 Gp Hpix SOK Rw H2 H10 H18 H19 H20.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF).
    eexists. split.
    - sn F_77e90 D_77e90.
      stepb_ft F_77e94 D_77e94 ltac:(condZ).
      sn F_77e98 D_77e98.
      stepb_tk F_77e9c D_77e9c ltac:(condZ).
      stepLD F_77f08 D_77f08 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      sn F_77f0c D_77f0c. sn F_77f10 D_77f10.
      depth_inline PX Hd1 (0x77f6c : word).
      stepb_ft F_77f14 D_77f14 ltac:(condZ).
      zv F_77f18 D_77f18 (Z_to_bv 64 (s - 136)). zv F_77f1c D_77f1c (Z_to_bv 64 (s - 108)). sn F_77f20 D_77f20. sn F_77f24 D_77f24. sn F_77f28 D_77f28.
      dims_inline PX SOK v (s - 136)%Z (s - 108)%Z (0x77f84 : word).
      stepb_ft F_77f2c D_77f2c ltac:(condZ).
      sn F_77f30 D_77f30.
      unfold DIMS. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ep_D_exit : forall regs m (s : Z),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    getr regs 2 = Z_to_bv 64 (s - 144) ->
    exists regs', msteps SEGS (mkst regs (0x78160 : word) m rom) (mkst regs' (0x78800 : word) m rom)
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 Rh H2. eexists. split.
    - stepLD F_78108 D_78108 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 1) by lia.
      sn F_7810c D_7810c.
      stepb_tk F_78110 D_78110 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  Lemma ep_D_loop : forall regs m (s h : Z),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> (2 <= h < 2 ^ 31)%Z -> rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    rdn SEGS m (Z_to_bv 64 0xee570) 8 = Some (Z_to_le_bytes 8 0xef750) ->
    store_ok SEGS m (Z_to_bv 64 (s - 144)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 144) ->
    exists regs', msteps SEGS (mkst regs (0x78160 : word) m rom)
                              (mkst regs' (0x781c0 : word) (wbytes m (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 0x140b6))) rom)
      /\ getr regs' 23 = Z_to_bv 64 1 /\ getr regs' 26 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [10; 11; 12; 20; 21; 22; 23; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s h Hs Hs64 Hh Rh GOT SOK H2. eexists. split.
    - stepLD F_78108 D_78108 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small h) by lia.
      sn F_7810c D_7810c.
      stepb_ft F_78110 D_78110 ltac:(condZ).
      sn F_78114 D_78114. sn F_78118 D_78118. sn F_7811c D_7811c. sn F_78120 D_78120. sn F_78124 D_78124.
      stepLD F_78128 D_78128 (Z_to_le_bytes 8 0xef750) (Z_to_bv 64 0xef750) ltac:(addr_norm; exact GOT) ltac:(apply lez8; lia).
      sn F_7812c D_7812c.
      zv F_78130 D_78130 (Z_to_bv 64 0x140b6).
      stepST F_78134 D_78134 (Z_to_bv 64 (s - 144)) (Z_to_bv 64 0x140b6) ltac:(store_ok_peel; exact SOK).
      sn F_78138 D_78138. sn F_7813c D_7813c. sn F_78140 D_78140. sn F_78144 D_78144. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ep_F : forall regs m (s h y : Z) (pcn : word),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= y < h)%Z -> (h < 2 ^ 31)%Z -> pcn = (if (y + 1 <? h)%Z then (0x781c0 : word) else (0x78800 : word)) ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 23 = Z_to_bv 64 y ->
    exists regs', msteps SEGS (mkst regs (0x781b4 : word) m rom) (mkst regs' pcn m rom)
      /\ getr regs' 23 = Z_to_bv 64 (y + 1) /\ regs_agree (fun r => In r [10; 23]%list) regs regs'.
  Proof.
    intros regs m s h y pcn Hs Hs64 Hy Hh Epc Rh H2 H23.
    destruct (Z.ltb_spec (y + 1) h) as [LT|GE]; subst pcn.
    - eexists. split.
      + stepLD F_7815c D_7815c (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small h) by lia.
        stepat F_78160 D_78160 (Z_to_bv 64 (y + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
        stepb_ft F_78164 D_78164 ltac:(condZ). apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + stepLD F_7815c D_7815c (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small h) by lia.
        stepat F_78160 D_78160 (Z_to_bv 64 (y + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
        stepb_tk F_78164 D_78164 ltac:(condZ). apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ep_Z : forall regs r0 m (s na : Z) (ret : word),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameE s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 na ->
    exists regs', msteps SEGS (mkst regs (0x78800 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 na
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs r0 m s na ret Hs Hs64 Hret CE H2 H8 H9. unfold frameE in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _). eexists. split.
    - stepb_tk F_787a8 D_787a8 ltac:(condZ).
      sn F_77e24 D_77e24.
      stepLD8 F_77e28 D_77e28 ret. stepLD8 F_77e2c D_77e2c (getr r0 8). stepLD8 F_77e30 D_77e30 (getr r0 9). stepLD8 F_77e34 D_77e34 (getr r0 18).
      stepLD8 F_77e38 D_77e38 (getr r0 19). stepLD8 F_77e3c D_77e3c (getr r0 20). stepLD8 F_77e40 D_77e40 (getr r0 21). stepLD8 F_77e44 D_77e44 (getr r0 22).
      stepLD8 F_77e48 D_77e48 (getr r0 23). stepLD8 F_77e4c D_77e4c (getr r0 24). stepLD8 F_77e50 D_77e50 (getr r0 25). stepLD8 F_77e54 D_77e54 (getr r0 26).
      stepLD8 F_77e58 D_77e58 (getr r0 27).
      zv F_77e5c D_77e5c (Z_to_bv 64 s). stepret F_77e60 D_77e60 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

End ProfSegs.

(* [comment removed for export] *)
Section ProfFP.
Variable rom : word -> option byte.

  Lemma ep_C0 : forall (fx' : FPState) regs m (na : Z), frm_zero (@fp_csr fx') -> getr regs 9 = Z_to_bv 64 na ->
    exists fr cs regs', frm_zero cs
      /\ msteps SEGS (@mkst fx' regs (0x78154 : word) m rom) (@mkst (mkFP fr cs) regs' (0x60b90 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x78160 /\ getr regs' 10 = Z_to_bv 64 na /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros fx' regs m na Hz H9.
    destruct (fp_step_fcvt_to_f fx' SEGS regs (0x78154 : word) m rom W_780fc FC_S FC_W 10 24 7 F_780fc eq_refl D_780fc
                (or_introl eq_refl) Hz ltac:(right; reflexivity)) as (fr & cs & Hz' & ST).
    exists fr, cs. eexists. split; [exact Hz'|]. split.
    - eapply mst_step; [reflexivity | exact ST |]. step_simpl.
      sn F_78100 D_78100. sn F_78104 D_78104. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ep_Ck : forall (fx' : FPState) regs m (na : Z), frm_zero (@fp_csr fx') -> getr regs 9 = Z_to_bv 64 na ->
    exists fr cs regs', frm_zero cs
      /\ msteps SEGS (@mkst fx' regs (0x781a8 : word) m rom) (@mkst (mkFP fr cs) regs' (0x60b90 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x781b4 /\ getr regs' 10 = Z_to_bv 64 na /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros fx' regs m na Hz H9.
    destruct (fp_step_fcvt_to_f fx' SEGS regs (0x781a8 : word) m rom W_78150 FC_S FC_W 10 24 7 F_78150 eq_refl D_78150
                (or_introl eq_refl) Hz ltac:(right; reflexivity)) as (fr & cs & Hz' & ST).
    exists fr, cs. eexists. split; [exact Hz'|]. split.
    - eapply mst_step; [reflexivity | exact ST |]. step_simpl.
      sn F_78154 D_78154. sn F_78158 D_78158. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End ProfFP.
