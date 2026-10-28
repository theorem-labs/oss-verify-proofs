(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith DitherLib LeptExec LeptExecW LeptExecFP LeptExecX LeptExecB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpReal FpBound FpSiteC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptBilSegs V2LeptBilSegs2 V2LeptBilSegs2hD V2LeptBilSegs2hR V2LeptBilSegs2hT V2LeptBilSegs2hS.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Section Segs.
Variable rom : word -> option byte.

Lemma bh_kloop : forall (m : nat) (fr : bvmap 5 word) cs regs (M : word -> option byte) (s datas wpl kval spat rng H i j k sm nm : Z),
  Z.of_nat m = (11 - k)%Z -> (-10 <= k <= 10)%Z -> frm_zero cs ->
  (4096 <= datas)%Z -> (datas + 4 * (wpl * H) <= 2 ^ 47)%Z -> (datas mod 4 = 0)%Z -> (1 <= wpl <= 5000)%Z -> (4 * (wpl * H) <= 67108864)%Z ->
  (0 <= i)%Z -> (i + 22 <= H)%Z -> (0 <= j)%Z -> (j + 22 <= 4 * wpl)%Z ->
  (4096 <= spat)%Z -> (spat + 44 <= 2 ^ 47)%Z -> (spat mod 4 = 0)%Z -> (4096 <= rng)%Z -> (rng + 1024 <= 2 ^ 47)%Z -> (0 <= kval <= 255)%Z ->
  rd_bytes M datas (4 * (wpl * H)) -> kcell_ok spat 11 M -> kcell_ok rng 256 M ->
  bc_avg (k + 10) sm nm ->
  hfix regs s kval spat rng wpl ->
  getr regs 11 = Z_to_bv 64 (datas + 4 * ((i + 11) * wpl)) -> getr regs 14 = Z_to_bv 64 (j + 11) -> getr regs 15 = Z_to_bv 64 (j + 11) ->
  getr regs 17 = Z_to_bv 64 k ->
  reg_get fr 14 = Z_to_bv 64 (sbox nm) -> reg_get fr 15 = Z_to_bv 64 (sbox sm) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a158) M rom)
    (fun fin => exists fr' cs' regs' sm' nm', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a218) M rom /\ frm_zero cs' /\
       regs_agree (fun x => In x HKT) regs regs' /\ getr regs' 16 = Z_to_bv 64 (j + 11) /\ bc_avg 21 sm' nm' /\
       reg_get fr' 14 = Z_to_bv 64 (sbox nm') /\ reg_get fr' 15 = Z_to_bv 64 (sbox sm') /\ pass_fp fr fr').
Proof.
  induction m as [|m IH];
    intros fr cs regs M s datas wpl kval spat rng H i j k sm nm Hm Hk FZ Hd1 Hd2 Hd3 Hwpl Hsz Hi1 Hi2 Hj1 Hj2
      Hp1 Hp2 Hp3 Hg1 Hg2 Hkv RD KS KR BA HF H11 H14 H15 H17 F14 F15.
  - lia.
  - eapply reach_bind.
    { exact (bh_tap rom fr cs regs M s datas wpl H i j k kval spat rng (k + 10)%Z sm nm FZ Hd1 Hd2 Hd3 Hwpl Hsz Hj1 Hj2 Hi1 Hi2 Hk
               Hp1 Hp2 Hp3 Hg1 Hg2 Hkv RD KS KR BA ltac:(lia) ltac:(lia) HF H11 H14 H15 H17 F14 F15). }
    intros fin (fr1 & cs1 & regs1 & s1 & n1 & E1 & FZ1 & RA1 & R16 & R17 & BA1 & F141 & F151 & PF1).
    subst fin.
    assert (K : forall r, ~ In r HKT -> getr regs1 r = getr regs r) by exact RA1.
    destruct (Z.ltb_spec k 10) as [Hk10 | Hk10]; cbv iota.
    + eapply reach_weaken;
        [| eapply (IH fr1 cs1 regs1 M s datas wpl kval spat rng H i j (k + 1)%Z s1 n1);
           first [ lia | eassumption
                 | (replace (k + 1 + 10)%Z with (k + 10 + 1)%Z by ring; exact BA1)
                 | (rewrite K by (unfold HKT; notin_list); eassumption)
                 | (unfold hfix; rewrite !K by (unfold HKT; notin_list); exact HF) ] ].
      intros fin (fr2 & cs2 & regs2 & s2 & n2 & E2 & FZ2 & RA2 & R162 & BA2 & F142 & F152 & PF2).
      exists fr2, cs2, regs2, s2, n2.
      split; [exact E2|]. split; [exact FZ2|].
      split; [exact (regs_agree_trans _ _ _ _ RA1 RA2)|]. split; [exact R162|].
      split; [exact BA2|]. split; [exact F142|]. split; [exact F152|].
      intros x Hx. rewrite (PF2 x Hx). exact (PF1 x Hx).
    + apply reach_done.
      exists fr1, cs1, regs1, s1, n1.
      split; [reflexivity|]. split; [exact FZ1|]. split; [exact RA1|]. split; [exact R16|].
      split; [replace 21%Z with (k + 10 + 1)%Z by lia; exact BA1|].
      split; [exact F141|]. split; [exact F151|]. exact PF1.
Qed.

Lemma bhl_ag_keep : forall (L : list reg) regs regs' (r : reg) (v : word),
  regs_agree (fun x => In x L) regs regs' -> existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = false ->
  getr regs r = v -> getr regs' r = v.
Proof.
  intros L regs regs' r v AG E H. rewrite AG; [exact H|]. intros Hin.
  assert (T : existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = true).
  { apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

Lemma bhl_ag_comp : forall (L1 L2 L : list reg) r1 r2 r3,
  regs_agree (fun x => In x L1) r1 r2 -> regs_agree (fun x => In x L2) r2 r3 ->
  forallb (fun x => existsb (fun y => Z.eqb (bv_unsigned y) (bv_unsigned x)) L) (L1 ++ L2) = true ->
  regs_agree (fun x => In x L) r1 r3.
Proof.
  intros L1 L2 L r1 r2 r3 A1 A2 B r Hr. rewrite forallb_forall in B.
  assert (IN : forall x, In x (L1 ++ L2) -> In x L).
  { intros x Hx. specialize (B x Hx). apply existsb_exists in B. destruct B as (y & Hy & E).
    apply Z.eqb_eq in E. apply bv_eq in E. subst. exact Hy. }
  rewrite A2, A1; [reflexivity | |].
  - intros Hin. apply Hr, IN, in_or_app. left. exact Hin.
  - intros Hin. apply Hr, IN, in_or_app. right. exact Hin.
Qed.

Lemma bhl_pass_trans : forall fr1 fr2 fr3, pass_fp fr1 fr2 -> pass_fp fr2 fr3 -> pass_fp fr1 fr3.
Proof. intros fr1 fr2 fr3 P Q r Hr. rewrite (Q r Hr). exact (P r Hr). Qed.

Lemma bhl_fsc_pass : forall fr fr', bc_fsc fr -> pass_fp fr fr' -> bc_fsc fr'.
Proof.
  intros fr fr' (A & B & C) P. unfold bc_fsc.
  rewrite (P 8%bv), (P 9%bv), (P 18%bv); [split; [exact A | split; [exact B | exact C]] | | |];
    let H := fresh "H" in intro H; vm_compute in H; lia.
Qed.

Lemma bhl_agw : forall (L1 L : list reg) r1 r2,
  regs_agree (fun x => In x L1) r1 r2 ->
  forallb (fun x => existsb (fun y => Z.eqb (bv_unsigned y) (bv_unsigned x)) L) L1 = true ->
  regs_agree (fun x => In x L) r1 r2.
Proof.
  intros L1 L r1 r2 A B r Hr. rewrite forallb_forall in B. apply A. intros Hin. apply Hr.
  specialize (B r Hin). apply existsb_exists in B. destruct B as (y & Hy & E).
  apply Z.eqb_eq in E. apply bv_eq in E. subst. exact Hy.
Qed.

Ltac bhl_agk AG H := apply (bhl_ag_keep _ _ _ _ _ AG); [vm_compute; reflexivity | exact H].
Ltac bhl_agc A1 A2 := eapply bhl_ag_comp; [exact A1 | exact A2 | vm_compute; reflexivity].
Ltac bhl_as := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Ltac bhl_fix AG FX := apply (hfix_keep _ _ _ _ _ _ _ FX); eapply bhl_agw; [exact AG | vm_compute; reflexivity].

Lemma bhl_out : forall (datat wpl h z : Z) (n : nat),
  (datat + 4 * (wpl * (h + 22)) <= z \/ z + Z.of_nat n <= datat)%Z ->
  forall r, In r (HR datat wpl h) -> (z + Z.of_nat n <= fst r \/ fst r + snd r <= z)%Z.
Proof. intros datat wpl h z n D r Hr. destruct Hr as [<-|[]]. cbn [fst snd]. lia. Qed.

Lemma bhl_mem : forall s datas datat wpl w h spat rng kval (M0 M : word -> option byte),
  hgeo s datas datat wpl w h spat rng kval -> hmem0 s datas datat wpl w h spat rng M0 ->
  rinv (HR datat wpl h) M0 M -> hmem0 s datas datat wpl w h spat rng M.
Proof.
  intros s datas datat wpl w h spat rng kval M0 M G V RI.
  destruct G as (Gs1 & Gs2 & Gw & Gh & Gw2 & Gh2 & Gwpl & Gsz & Gs_1 & Gs_2 & Gs_3 & Gt1 & Gt2 & Gt3 &
                 Gp1 & Gp2 & Gp3 & Gr1 & Gr2 & Gk & Ds & Dfr & Dp & Dr & Dc).
  destruct V as (Rs & SOK & Ksp & Krn & Inone & C240 & C224 & C216 & C208 & C200 & C192 & C184).
  assert (RD : forall z (n : nat), (0 <= z)%Z -> (z + Z.of_nat n <= 2 ^ 64)%Z ->
                 (datat + 4 * (wpl * (h + 22)) <= z \/ z + Z.of_nat n <= datat)%Z ->
                 rdn SEGS M (Z_to_bv 64 z) n = rdn SEGS M0 (Z_to_bv 64 z) n).
  { intros z n Z0 Z1 D. apply (rinv_rdn SEGS _ _ _ z n RI Z0 Z1). apply bhl_out. exact D. }
  unfold hmem0, hframe. repeat (lazymatch goal with |- _ /\ _ => split end).
  - intros p Hp. destruct (Rs p Hp) as [b Hb]. exists b. rewrite RD; [exact Hb | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia |].
    cbn [Z.of_nat Pos.of_succ_nat]. lia.
  - eapply store_ok_mono; [exact (proj1 RI) | exact SOK].
  - intros k Hk. destruct (Ksp k Hk) as (x & Hx & F). exists x. split; [|exact F].
    rewrite RD; [exact Hx | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - intros k Hk. destruct (Krn k Hk) as (x & Hx & F). exists x. split; [|exact F].
    rewrite RD; [exact Hx | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - intros j Hj. rewrite (proj2 RI (Z_to_bv 64 j)); [exact (Inone j Hj)|].
    intros r Hr. destruct Hr as [<-|[]]. unfold inreg. cbn [fst snd]. unfold bc_chalf in *.
    rewrite u_Z2bv by lia. lia.
  - rewrite RD; [exact C240 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - rewrite RD; [exact C224 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - rewrite RD; [exact C216 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - rewrite RD; [exact C208 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - rewrite RD; [exact C200 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - rewrite RD; [exact C192 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - rewrite RD; [exact C184 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
Qed.

Lemma bhl_wpl : forall w, (1 <= w)%Z -> (w + 22 <= 20000)%Z ->
  (1 <= wpl_of (w + 22) 8 <= 5000)%Z /\ (w + 22 <= 4 * wpl_of (w + 22) 8)%Z.
Proof.
  intros w H1 H2. unfold wpl_of.
  pose proof (Z.div_mod ((w + 22) * 8 + 31)%Z 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound ((w + 22) * 8 + 31)%Z 32 ltac:(lia)) as B.
  set (q := (((w + 22) * 8 + 31) / 32)%Z) in *. set (r := (((w + 22) * 8 + 31) mod 32)%Z) in *. lia.
Qed.

Lemma bh_jloop : forall (m : nat) (fr : bvmap 5 word) cs regs (M0 M : word -> option byte) (s datas datat wpl w h spat rng kval i j : Z),
  Z.of_nat m = (w - j)%Z -> (0 <= j < w)%Z -> (0 <= i < h)%Z -> frm_zero cs ->
  hgeo s datas datat wpl w h spat rng kval -> hmem0 s datas datat wpl w h spat rng M0 -> rinv (HR datat wpl h) M0 M ->
  bc_fsc fr -> hfix regs s kval spat rng wpl -> getr regs 10 = Z_to_bv 64 i ->
  getr regs 11 = Z_to_bv 64 (datas + 4 * ((i + 11) * wpl)) -> getr regs 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl)) ->
  getr regs 13 = Z_to_bv 64 j ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a134) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a28c) M' rom /\ frm_zero cs' /\
       rinv (HR datat wpl h) M0 M' /\ regs_agree (fun r => In r HPL) regs regs' /\ getr regs' 10 = Z_to_bv 64 i /\ pass_fp fr fr').
Proof.
  intros m. induction m as [|m IH];
    intros fr cs regs M0 M s datas datat wpl w h spat rng kval i j Hm Hj Hi FZ G V0 RI FSC FX H10 H11 H12 H13.
  { lia. }
  pose proof (bhl_mem _ _ _ _ _ _ _ _ _ M0 M G V0 RI) as V.
  pose proof G as (Gs1 & Gs2 & Gw & Gh & Gw2 & Gh2 & Gwpl & Gsz & Gs_1 & Gs_2 & Gs_3 & Gt1 & Gt2 & Gt3 &
                   Gp1 & Gp2 & Gp3 & Gr1 & Gr2 & Gk & Ds & Dfr & Dp & Dr & Dc).
  pose proof V as (Rs & SOK & Ksp & Krn & Inone & HF).
  destruct (bhl_wpl w ltac:(lia) ltac:(lia)) as [Wp1 Wp2].
  eapply reach_bind; [apply (bh_col rom fr cs regs M s datas datat wpl w h spat rng kval j); first [bhl_as | lia]|].
  intros fin1 (fr1 & cs1 & r1 & -> & FZ1 & A14 & A15 & A17 & AG1 & F14 & F15 & P1).
  assert (FX1 : hfix r1 s kval spat rng wpl) by bhl_fix AG1 FX.
  assert (B10 : getr r1 10 = Z_to_bv 64 i) by bhl_agk AG1 H10.
  assert (B11 : getr r1 11 = Z_to_bv 64 (datas + 4 * ((i + 11) * wpl))) by bhl_agk AG1 H11.
  assert (B12 : getr r1 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl))) by bhl_agk AG1 H12.
  assert (B13 : getr r1 13 = Z_to_bv 64 j) by bhl_agk AG1 H13.
  eapply reach_bind;
    [apply bh_kloop with (m := 21%nat) (fr := fr1) (cs := cs1) (regs := r1) (M := M) (s := s) (datas := datas) (wpl := wpl)
       (kval := kval) (spat := spat) (rng := rng) (H := (h + 22)%Z) (i := i) (j := j) (k := (-10)%Z)
       (sm := p_zero) (nm := p_zero);
       first [bhl_as | reflexivity | lia | exact bc_avg_init]|].
  intros fin2 (fr2 & cs2 & r2 & sm & nm & -> & FZ2 & AG2 & C16 & AV & F14b & F15b & P2).
  assert (FX2 : hfix r2 s kval spat rng wpl) by bhl_fix AG2 FX1.
  assert (C10 : getr r2 10 = Z_to_bv 64 i) by bhl_agk AG2 B10.
  assert (C11 : getr r2 11 = Z_to_bv 64 (datas + 4 * ((i + 11) * wpl))) by bhl_agk AG2 B11.
  assert (C12 : getr r2 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl))) by bhl_agk AG2 B12.
  assert (C13 : getr r2 13 = Z_to_bv 64 j) by bhl_agk AG2 B13.
  assert (C15 : getr r2 15 = Z_to_bv 64 (j + 11)) by bhl_agk AG2 A15.
  assert (C14 : getr r2 14 = Z_to_bv 64 (j + 11)) by bhl_agk AG2 A14.
  assert (P12 : pass_fp fr fr2) by (eapply bhl_pass_trans; [exact P1 | exact P2]).
  assert (FSC2 : bc_fsc fr2) by (eapply bhl_fsc_pass; [exact FSC | exact P12]).
  eapply reach_bind; [apply (bh_site rom fr2 cs2 r2 M s datas datat wpl w h spat rng kval i j sm nm); first [bhl_as | lia]|].
  intros fin3 (fr3 & cs3 & r3 & M3 & -> & FZ3 & RI3 & AG3 & P3).
  assert (RIa : rinv (HR datat wpl h) M0 M3) by (eapply rinv_trans; [exact RI | exact RI3]).
  pose proof (bhl_mem _ _ _ _ _ _ _ _ _ M0 M3 G V0 RIa) as V3.
  pose proof V3 as (Rs3 & SOK3 & Ksp3 & Krn3 & Inone3 & HF3).
  assert (FX3 : hfix r3 s kval spat rng wpl) by bhl_fix AG3 FX2.
  assert (D10 : getr r3 10 = Z_to_bv 64 i) by bhl_agk AG3 C10.
  assert (D11 : getr r3 11 = Z_to_bv 64 (datas + 4 * ((i + 11) * wpl))) by bhl_agk AG3 C11.
  assert (D12 : getr r3 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl))) by bhl_agk AG3 C12.
  assert (D13 : getr r3 13 = Z_to_bv 64 j) by bhl_agk AG3 C13.
  assert (P13 : pass_fp fr fr3) by (eapply bhl_pass_trans; [exact P12 | exact P3]).
  eapply reach_bind; [apply (bh_clatch rom fr3 cs3 r3 M3 s datas datat wpl w h spat rng kval j); first [bhl_as | lia]|].
  intros fin4 (r4 & -> & S13 & AG4).
  assert (A12 : regs_agree (fun r => In r HPL) regs r2) by bhl_agc AG1 AG2.
  assert (A13 : regs_agree (fun r => In r HPL) regs r3) by bhl_agc A12 AG3.
  assert (A14' : regs_agree (fun r => In r HPL) regs r4) by bhl_agc A13 AG4.
  assert (E10 : getr r4 10 = Z_to_bv 64 i) by bhl_agk AG4 D10.
  destruct (Z.ltb_spec (j + 1) w) as [Hmore|Hlast].
  - assert (FX4 : hfix r4 s kval spat rng wpl) by bhl_fix AG4 FX3.
    assert (E11 : getr r4 11 = Z_to_bv 64 (datas + 4 * ((i + 11) * wpl))) by bhl_agk AG4 D11.
    assert (E12 : getr r4 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl))) by bhl_agk AG4 D12.
    assert (FSC3 : bc_fsc fr3) by (eapply bhl_fsc_pass; [exact FSC | exact P13]).
    eapply reach_weaken; [|apply (IH fr3 cs3 r4 M0 M3 s datas datat wpl w h spat rng kval i (j + 1)%Z); first [bhl_as | lia]].
    intros fin (fr5 & cs5 & r5 & M5 & -> & FZ5 & RI5 & AG5 & G10 & P5).
    exists fr5, cs5, r5, M5. split; [reflexivity|].
    split; [exact FZ5|]. split; [exact RI5|]. split; [bhl_agc A14' AG5|]. split; [exact G10|].
    eapply bhl_pass_trans; [exact P13 | exact P5].
  - apply reach_done. exists fr3, cs3, r4, M3. split; [reflexivity|].
    split; [exact FZ3|]. split; [exact RIa|]. split; [exact A14'|]. split; [exact E10|]. exact P13.
Qed.

Lemma bh_iloop : forall (m : nat) (fr : bvmap 5 word) cs regs (M0 M : word -> option byte) (s datas datat wpl w h spat rng kval i : Z),
  Z.of_nat m = (h - i)%Z -> (0 <= i < h)%Z -> frm_zero cs ->
  hgeo s datas datat wpl w h spat rng kval -> hmem0 s datas datat wpl w h spat rng M0 -> rinv (HR datat wpl h) M0 M ->
  bc_fsc fr -> hfix regs s kval spat rng wpl -> getr regs 10 = Z_to_bv 64 i ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a09c) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a2a0) M' rom /\ frm_zero cs' /\
       rinv (HR datat wpl h) M0 M' /\ regs_agree (fun r => In r HPL) regs regs' /\ pass_fp fr fr').
Proof.
  intros m. induction m as [|m IH];
    intros fr cs regs M0 M s datas datat wpl w h spat rng kval i Hm Hi FZ G V0 RI FSC FX H10.
  { lia. }
  pose proof (bhl_mem _ _ _ _ _ _ _ _ _ M0 M G V0 RI) as V.
  pose proof G as (Gs1 & Gs2 & Gw & Gh & Gw2 & Gh2 & Gwpl & Gsz & Gs_1 & Gs_2 & Gs_3 & Gt1 & Gt2 & Gt3 &
                   Gp1 & Gp2 & Gp3 & Gr1 & Gr2 & Gk & Ds & Dfr & Dp & Dr & Dc).
  pose proof V as (Rs & SOK & Ksp & Krn & Inone & HF).
  eapply reach_bind; [apply (bh_row rom fr cs regs M s datas datat wpl w h spat rng kval i); first [bhl_as | lia]|].
  intros fin1 (r1 & -> & R11 & R12 & R13 & AG1).
  assert (FX1 : hfix r1 s kval spat rng wpl) by bhl_fix AG1 FX.
  assert (B10 : getr r1 10 = Z_to_bv 64 i) by bhl_agk AG1 H10.
  eapply reach_bind;
    [apply (bh_jloop (Z.to_nat w) fr cs r1 M0 M s datas datat wpl w h spat rng kval i 0%Z);
       first [bhl_as | lia | (rewrite Z2Nat.id by lia; lia)]|].
  intros fin2 (fr2 & cs2 & r2 & M2 & -> & FZ2 & RI2 & AG2 & G10 & P2).
  pose proof (bhl_mem _ _ _ _ _ _ _ _ _ M0 M2 G V0 RI2) as V2.
  pose proof V2 as (Rs2 & SOK2 & Ksp2 & Krn2 & Inone2 & HF2).
  assert (FX2 : hfix r2 s kval spat rng wpl) by (exact (hfix_keep _ _ _ _ _ _ _ FX1 AG2)).
  eapply reach_bind; [apply (bh_rlatch rom fr2 cs2 r2 M2 s datas datat wpl w h spat rng kval i); first [bhl_as | lia]|].
  intros fin3 (r3 & -> & L10 & AG3).
  assert (A12 : regs_agree (fun r => In r HPL) regs r2) by bhl_agc AG1 AG2.
  assert (A13 : regs_agree (fun r => In r HPL) regs r3) by bhl_agc A12 AG3.
  destruct (Z.ltb_spec (i + 1) h) as [Hmore|Hlast].
  - assert (FX3 : hfix r3 s kval spat rng wpl) by (exact (hfix_keep _ _ _ _ _ _ _ FX2 AG3)).
    assert (FSC2 : bc_fsc fr2) by (eapply bhl_fsc_pass; [exact FSC | exact P2]).
    eapply reach_weaken; [|apply (IH fr2 cs2 r3 M0 M2 s datas datat wpl w h spat rng kval (i + 1)%Z); first [bhl_as | lia]].
    intros fin (fr5 & cs5 & r5 & M5 & -> & FZ5 & RI5 & AG5 & P5).
    exists fr5, cs5, r5, M5. split; [reflexivity|].
    split; [exact FZ5|]. split; [exact RI5|]. split; [bhl_agc A13 AG5|].
    eapply bhl_pass_trans; [exact P2 | exact P5].
  - apply reach_done. exists fr2, cs2, r3, M2. split; [reflexivity|].
    split; [exact FZ2|]. split; [exact RI2|]. split; [exact A13|]. exact P2.
Qed.

Lemma bc_hpass : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (s datas datat wpl w h spat rng kval : Z),
  frm_zero cs -> bc_fsc fr ->
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (1 <= w)%Z -> (1 <= h)%Z -> (w + 22 <= 20000)%Z -> (h + 22 <= 20000)%Z -> wpl = wpl_of (w + 22) 8 -> (4 * (wpl * (h + 22)) <= 67108864)%Z ->
  (4096 <= datas)%Z -> (datas + 4 * (wpl * (h + 22)) <= 2 ^ 47)%Z -> (datas mod 4 = 0)%Z ->
  (4096 <= datat)%Z -> (datat + 4 * (wpl * (h + 22)) <= 2 ^ 47)%Z -> (datat mod 4 = 0)%Z ->
  (4096 <= spat)%Z -> (spat + 44 <= 2 ^ 47)%Z -> (spat mod 4 = 0)%Z -> (4096 <= rng)%Z -> (rng + 1024 <= 2 ^ 47)%Z -> (0 <= kval <= 255)%Z ->
  (datat + 4 * (wpl * (h + 22)) <= datas \/ datas + 4 * (wpl * (h + 22)) <= datat)%Z ->
  (datat + 4 * (wpl * (h + 22)) <= s - 320 \/ s <= datat)%Z ->
  (datat + 4 * (wpl * (h + 22)) <= spat \/ spat + 44 <= datat)%Z ->
  (datat + 4 * (wpl * (h + 22)) <= rng \/ rng + 1024 <= datat)%Z ->
  (datat + 4 * (wpl * (h + 22)) <= bc_chalf \/ bc_chalf + 8 <= datat)%Z ->
  rd_bytes M datas (4 * (wpl * (h + 22))) -> store_ok SEGS M (Z_to_bv 64 datat) (Z.to_nat (4 * (wpl * (h + 22)))) = true ->
  kcell_ok spat 11 M -> kcell_ok rng 256 M -> img_none M bc_chalf 8 ->
  rdn SEGS M (Z_to_bv 64 (s - 240)) 8 = Some (Z_to_le_bytes 8 wpl) ->
  rdn SEGS M (Z_to_bv 64 (s - 224)) 8 = Some (Z_to_le_bytes 8 datas) ->
  rdn SEGS M (Z_to_bv 64 (s - 216)) 8 = Some (Z_to_le_bytes 8 h) ->
  rdn SEGS M (Z_to_bv 64 (s - 208)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS M (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 bc_cptr) ->
  rdn SEGS M (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS M (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 (-10) -> getr regs 9 = Z_to_bv 64 kval ->
  getr regs 18 = Z_to_bv 64 10 -> getr regs 19 = Z_to_bv 64 (- 2 ^ 31) -> getr regs 20 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 spat ->
  getr regs 22 = Z_to_bv 64 3 -> getr regs 23 = Z_to_bv 64 rng -> getr regs 24 = Z_to_bv 64 1 -> getr regs 25 = Z_to_bv 64 wpl ->
  getr regs 26 = Z_to_bv 64 (2 ^ 64 - 1 - rng) -> getr regs 27 = Z_to_bv 64 1 -> getr regs 29 = Z_to_bv 64 11 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a098) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a2a0) M' rom /\ frm_zero cs' /\
       rinv [(datat, (4 * (wpl * (h + 22)))%Z)] M M' /\ regs_agree (fun r => In r HPL) regs regs' /\ pass_fp fr fr').
Proof.
  intros fr cs regs M s datas datat wpl w h spat rng kval FZ FSC Hs Hs16 Hw1 Hh1 Hw2 Hh2 Ewpl Hsz
    Hd1 Hd2 Hd3 Ht1 Ht2 Ht3 Hp1 Hp2 Hp3 Hr1 Hr2 Hk Dj1 Dj2 Dj3 Dj4 Dj5 RD SOK KS KR IMG
    R240 R224 R216 R208 R200 R192 R184 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H29.
  pose proof (conj H2 (conj H8 (conj H9 (conj H18 (conj H19 (conj H20 (conj H21 (conj H22 (conj H23 (conj H24
    (conj H25 (conj H26 (conj H27 H29))))))))))))) as HF0.
  change (hfix regs s kval spat rng wpl) in HF0.
  pose proof (conj RD (conj SOK (conj KS (conj KR (conj IMG (conj R240 (conj R224 (conj R216 (conj R208 (conj R200
    (conj R192 R184))))))))))) as HM.
  change (hmem0 s datas datat wpl w h spat rng M) in HM.
  assert (HG : hgeo s datas datat wpl w h spat rng kval) by (unfold hgeo; repeat split; first [assumption | lia]).
  clear H26.
  ex_entry regs [s; kval; spat; rng; wpl] HRe.
  assert (HK : know_ok SEGS (ex_env regs [s; kval; spat; rng; wpl]) M []) by (ex_know regs).
  exb_open HRe HK ST.
  exb_adriveS 8%nat 400%nat [0x3a09c%Z] (SCR [] [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HRx Hlf Hms.
  eapply reach_msteps; [exact Hms|].
  assert (AG : regs_agree (fun r => In r HPL) regs R) by (unfold HPL; ex_agree HRe HRx).
  assert (G10 : getr R 10 = Z_to_bv 64 0) by (ex_reg regs HRx).
  pose proof (hfix_keep regs R s kval spat rng wpl HF0 AG) as HF.
  change (mem_denot (ex_env regs [s; kval; spat; rng; wpl]) M []) with M.
  eapply reach_weaken;
    [| exact (bh_iloop (Z.to_nat h) fr cs R M M s datas datat wpl w h spat rng kval 0%Z
                ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) FZ HG HM (rinv_refl _ _) FSC HF G10)].
  intros fin (fr2 & cs2 & regs2 & M2 & -> & FZ2 & RI2 & AG2 & PF2).
  exists fr2, cs2, regs2, M2.
  split; [reflexivity|]. split; [exact FZ2|]. split; [exact RI2|].
  split; [exact (regs_agree_trans _ _ _ _ AG AG2)|].
  exact PF2.
Qed.

End Segs.
