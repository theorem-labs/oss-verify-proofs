(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib MemSplit MmapSim SeqExec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21_code_16000_17000.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma rdn_def : forall segs m (a : Z) (n : nat),
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < Z.of_nat n)%Z -> m (Z_to_bv 64 (a + i)) <> None) ->
  exists bs, rdn segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
  intros segs m a n. revert a. induction n as [|n IH]; intros a Ha Hn Hd.
  - exists []. split; reflexivity.
  - cbn [rdn].
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
    2:{ exfalso. apply (Hd 0%Z ltac:(lia)). rewrite Z.add_0_r. exact E. }
    destruct (IH (a + 1)%Z ltac:(lia) ltac:(lia)) as (bs & Hbs & Hl).
    { intros i Hi. replace (a + 1 + i)%Z with (a + (1 + i))%Z by lia. apply Hd. lia. }
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) by (apply bv_eq; rewrite zbv_plus1; reflexivity).
    rewrite Hbs. exists (b :: bs). split; [reflexivity | cbn; rewrite Hl; reflexivity].
Qed.

(* [comment removed for export] *)
Ltac stepSTv F D aa oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; reflexivity | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; reflexivity | reflexivity | oktac ]
    end
  | step_simpl ].

Section SelLoop.
Context {fx : FPState}.
  Variable rom : word -> option byte.
  Variable m0 : word -> option byte.                 (* [comment removed for export] *)
  Variables datas w h d wpl s x1 x2 y1 y2 sindex : Z.
  Variable ibs : list byte.                          (* [comment removed for export] *)
  Variable ib : byte.                                (* [comment removed for export] *)

  Hypothesis Hw : (1 <= w <= 20000)%Z.
  Hypothesis Hh : (1 <= h <= 20000)%Z.
  Hypothesis Hd : (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z.
  Hypothesis Hwpl : (wpl = (w * d + 31) / 32)%Z.
  Hypothesis Hdatas : (4096 <= datas)%Z.
  Hypothesis Hdal : (datas mod 4 = 0)%Z.
  Hypothesis Hs : (144 <= s /\ s < 2 ^ 64)%Z.
  Hypothesis HR : (datas + 4 * (wpl * h) <= s - 144)%Z.      (* [comment removed for export] *)
  Hypothesis Hx1 : (0 <= x1 < 2 ^ 31 - 1)%Z.
  Hypothesis Hx2 : (0 <= x2 < 2 ^ 31 - 1)%Z.
  Hypothesis Hy1 : (0 <= y1 < 2 ^ 31 - 1)%Z.
  Hypothesis Hy2 : (0 <= y2 < 2 ^ 31 - 1)%Z.
  Hypothesis Hsindex : (0 <= sindex < 2 ^ 31)%Z.
  Hypothesis Cw : rdn SEGS m0 (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w).
  Hypothesis Ch : rdn SEGS m0 (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h).
  Hypothesis Cx1 : rdn SEGS m0 (Z_to_bv 64 (s - 116)) 4 = Some (Z_to_le_bytes 4 x1).
  Hypothesis Cy1 : rdn SEGS m0 (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 y1).
  Hypothesis Cidx : rdn SEGS m0 (Z_to_bv 64 (s - 132)) 4 = Some ibs.
  Hypothesis Lidx : length ibs = 4%nat.
  Hypothesis Cidx1 : rdn SEGS m0 (Z_to_bv 64 (s - 132)) 1 = Some [ib].
  Hypothesis RAS0 : forall a : word, (datas <= bv_unsigned a < datas + 4 * (wpl * h))%Z -> m0 a <> None.

  (* [comment removed for export] *)
  Lemma wpl_bounds : (1 <= wpl <= 5001 /\ w * d <= 32 * wpl /\ 32 * wpl <= w * d + 31)%Z.
  Proof.
    clear - Hw Hd Hwpl.
    assert (Hwd : (1 <= w * d <= 20000 * 8)%Z) by (destruct Hd as [->|[->|[->| ->]]]; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    subst wpl. split; [|split].
    - split; [apply Z.div_le_lower_bound; lia|]. apply Z.div_le_upper_bound; lia.
    - pose proof (Z.div_mod (w * d + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (w * d + 31) 32 ltac:(lia)). lia.
    - pose proof (Z.div_mod (w * d + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (w * d + 31) 32 ltac:(lia)). lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Definition inras (a : word) : Prop := (datas <= bv_unsigned a < datas + 4 * (wpl * h))%Z.
  Definition RB (m : word -> option byte) : Prop :=
    (forall a : word, ~ inras a -> m a = m0 a) /\ (forall a : word, inras a -> m a <> None).

  Lemma RB_m0 : RB m0.
  Proof. split; [intros a _; reflexivity | exact RAS0]. Qed.

  Lemma RB_store : forall m (a : word) bs, RB m ->
    (datas <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat (length bs) <= datas + 4 * (wpl * h))%Z -> RB (wbytes m a bs).
  Proof.
    intros m a bs [E D] Hlo Hhi. split.
    - intros x Hx. unfold inras in Hx. rewrite wbytes_outside; [apply E; unfold inras; exact Hx | lia | lia].
    - intros x Hx. apply wbytes_grows. apply D. exact Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma RB_cell : forall m (a : Z) (n : nat) bs, RB m -> (s - 144 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
    rdn SEGS m0 (Z_to_bv 64 a) n = Some bs -> rdn SEGS m (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros m a n bs [E _] Hlo Hhi R. rewrite <- R. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply E. unfold inras. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma RB_rdn : forall m (a : Z) (n : nat), RB m -> (datas <= a)%Z -> (a + Z.of_nat n <= datas + 4 * (wpl * h))%Z ->
    exists bs, rdn SEGS m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
  Proof.
    intros m a n [_ D] Hlo Hhi. apply rdn_def; [lia | lia |]. intros i Hi. apply D. unfold inras. rewrite u_Z2bv by lia. lia.
  Qed.

  Lemma RB_sok : forall m (a : Z) (n : nat), RB m -> (datas <= a)%Z -> (a + Z.of_nat n <= datas + 4 * (wpl * h))%Z ->
    store_ok SEGS m (Z_to_bv 64 a) n = true.
  Proof.
    intros m a n [_ D] Hlo Hhi. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (D x ltac:(unfold inras; lia) E).
  Qed.

  (* [comment removed for export] *)
  Lemma row_in_raster : forall i, (0 <= i < h)%Z -> (0 <= 4 * wpl * i /\ 4 * wpl * i + 4 * wpl <= 4 * (wpl * h))%Z.
  Proof.
    intros i Hi. clear - Hi Hw Hd Hwpl. pose proof wpl_bounds as (Hwpl1 & _).
    assert (wpl * (i + 1) <= wpl * h)%Z by (apply Z.mul_le_mono_nonneg_l; lia). nia.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma row_base_al4 : forall i, ((datas + 4 * wpl * i) mod 4 = 0)%Z.
  Proof.
    intros i. clear - Hdal. replace (datas + 4 * wpl * i)%Z with (datas + (wpl * i) * 4)%Z by lia.
    rewrite Z_mod_plus_full. exact Hdal.
  Qed.
  Lemma pix_word : forall j, (0 <= j < w)%Z -> (0 <= j * d / 32 < wpl)%Z.
  Proof.
    intros j Hj. clear - Hj Hw Hd Hwpl. pose proof wpl_bounds as (_ & Hwd & _).
    assert (0 <= j * d)%Z by lia. assert (j * d + d <= w * d)%Z by nia.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
  Qed.
  Lemma div4_32 : forall j, (0 <= j)%Z -> (j * 4 / 32 = j / 8)%Z.
  Proof. intros j Hj. lia. Qed.
  Lemma div2_32 : forall j, (0 <= j)%Z -> (j * 2 / 32 = j / 16)%Z.
  Proof. intros j Hj. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma word_at : forall m i q, RB m -> (0 <= i < h)%Z -> (0 <= q < wpl)%Z ->
    exists bs, rdn SEGS m (Z_to_bv 64 (datas + 4 * wpl * i + 4 * q)) 4 = Some bs /\ length bs = 4%nat
               /\ store_ok SEGS m (Z_to_bv 64 (datas + 4 * wpl * i + 4 * q)) 4 = true
               /\ (datas <= datas + 4 * wpl * i + 4 * q /\ datas + 4 * wpl * i + 4 * q + 4 <= datas + 4 * (wpl * h))%Z.
  Proof.
    intros m i q HRB Hi Hq. pose proof (row_in_raster i Hi) as Hrow.
    assert (B : (datas <= datas + 4 * wpl * i + 4 * q /\ datas + 4 * wpl * i + 4 * q + 4 <= datas + 4 * (wpl * h))%Z) by lia.
    destruct (RB_rdn m (datas + 4 * wpl * i + 4 * q) 4 HRB ltac:(lia) ltac:(cbn; lia)) as (bs & Hbs & Lbs).
    exists bs. split; [exact Hbs|]. split; [exact Lbs|]. split; [| exact B]. apply RB_sok; [exact HRB | lia | cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma byte8_at : forall m i j, RB m -> (0 <= i < h)%Z -> (d = 8)%Z -> (0 <= j < w)%Z ->
    exists f b, v_xori (Z_to_bv 64 (datas + 4 * wpl * i + j)) 3 = Z_to_bv 64 f /\ (datas <= f /\ f + 1 <= datas + 4 * (wpl * h))%Z
                /\ rdn SEGS m (Z_to_bv 64 f) 1 = Some [b] /\ store_ok SEGS m (Z_to_bv 64 f) 1 = true.
  Proof.
    intros m i j HRB Hi Hd8 Hj.
    pose proof wpl_bounds as (Hwpl1 & Hwd & _). rewrite Hd8 in Hwd. pose proof (row_in_raster i Hi) as Hrow.
    pose proof (flip3_bounds (datas + 4 * wpl * i) wpl (datas + 4 * wpl * i + j) (row_base_al4 i) ltac:(lia)) as Hf.
    set (p := (datas + 4 * wpl * i + j)%Z) in *. set (f := (p - p mod 4 + (3 - p mod 4))%Z) in *.
    exists f.
    destruct (RB_rdn m f 1 HRB ltac:(lia) ltac:(cbn; lia)) as (bs & Hbs & Lbs).
    destruct bs as [|b [|]]; try discriminate Lbs.
    exists b. split; [|split; [lia| split; [exact Hbs|]]].
    - apply zbv_xori3. lia.
    - apply RB_sok; [exact HRB | lia | cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Definition LC (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 144) /\ getr regs 10 = Z_to_bv 64 wpl /\ getr regs 8 = Z_to_bv 64 sindex /\
    getr regs 9 = Z_to_bv 64 d /\ getr regs 18 = Z_to_bv 64 datas /\ getr regs 20 = Z_to_bv 64 x2 /\ getr regs 13 = Z_to_bv 64 (x2 + 1) /\
    getr regs 14 = Z_to_bv 64 3 /\ getr regs 15 = Z_to_bv 64 1 /\ getr regs 17 = Z_to_bv 64 2 /\ getr regs 7 = Z_to_bv 64 4 /\ getr regs 30 = Z_to_bv 64 8.

  #[local] Definition lc_regs : list (bv 5) := [2; 10; 8; 9; 18; 20; 13; 14; 15; 17; 7; 30]%bv.

  Lemma LC_agree : forall (P : bv 5 -> Prop) regs regs', LC regs -> regs_agree P regs regs' ->
    (forall r, In r lc_regs -> ~ P r) -> LC regs'.
  Proof.
    intros P regs regs' L AG NP. unfold LC in *.
    assert (E : forall r, In r lc_regs -> getr regs' r = getr regs r) by (intros r Hr; apply AG; apply NP; exact Hr).
    rewrite !E by (cbn; repeat (first [left; reflexivity | right])). exact L.
  Qed.

  Ltac lc_disjoint := let r := fresh "r" in let Hr := fresh "Hr" in
    intros r Hr; cbn in Hr; repeat (destruct Hr as [<-|Hr]; [notin_list|]); destruct Hr.
  Ltac lc_via HL AG := eapply (LC_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) _ _ HL); [eapply regs_agree_trans; [regs_agree_weaken AG|]; solve_regs_agree | lc_disjoint].
  Ltac lc_via1 HL AG := eapply (LC_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) _ _ HL); [regs_agree_weaken AG | lc_disjoint].

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma px8 : forall regs m i j, RB m -> LC regs -> (d = 8)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 31 = Z_to_bv 64 j -> getr regs 21 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16448 : word) m rom) (mkst regs' (0x1642c : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 31 = Z_to_bv 64 j /\ getr regs' 21 = Z_to_bv 64 (datas + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m i j HRB HL Hd8 Hi Hj H31 H21.
    pose proof HL as (L2 & L10 & L8 & L9 & L18 & L20 & L13 & L14 & L15 & L17 & L7 & L30).
    pose proof wpl_bounds as (Hwpl1 & _). pose proof (row_in_raster i Hi) as Hrow.
    destruct (byte8_at m i j HRB Hi Hd8 Hj) as (f & b & Hxf & Hf & Hb & SOKf).
    pose proof (RB_cell m (s - 132) 1 [ib] HRB ltac:(lia) ltac:(cbn; lia) Cidx1) as Ci.
    pose proof (u_byte64 b) as Hbr.
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x16448 : word) m rom) (mkst r1 (0x164a8 : word) m rom)
                            /\ getr r1 23 = Z_to_bv 64 f /\ getr r1 24 = Z_to_bv 64 (bv_unsigned b)
                            /\ regs_agree (fun r : reg => In r [23; 24]%list) regs r1).
    { eexists. split.
      - stepb_tk F_16344 D_16344 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_ft F_16390 D_16390 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_ft F_16394 D_16394 ltac:(condZ).                                          (* [comment removed for export] *)
        stepiv F_16398 D_16398 (Z_to_bv 64 (datas + 4 * wpl * i + j)) ltac:(gres; pin; imm_norm; rewrite zbv_add; f_equal; lia).   (* [comment removed for export] *)
        stepiv F_1639c D_1639c (Z_to_bv 64 f) ltac:(gres; pin; imm_norm; exact Hxf).   (* [comment removed for export] *)
        stepLBU F_163a0 D_163a0 b ltac:(rdn_addr f; exact Hb).                           (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q23 & Q24 & AG1).
    pose proof (AG1 8 ltac:(notin_list)) as Q8. rewrite L8 in Q8. pose proof (AG1 2 ltac:(notin_list)) as Q2. rewrite L2 in Q2.
    destruct (c_eq (getr r1 8) (getr r1 24)) eqn:Hc.
    - (* [comment removed for export] *)
      eexists. eexists. split; [|split; [|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_163a4 D_163a4 ltac:(exact Hc).                                       (* [comment removed for export] *)
        stepLBU F_163a8 D_163a8 ib ltac:(rdn_addr (s - 132)%Z; exact Ci).               (* [comment removed for export] *)
        stepSTv F_163ac D_163ac (Z_to_bv 64 f) ltac:(store_ok_peel; exact SOKf).         (* [comment removed for export] *)
        sn F_163b0 D_163b0.                                                              (* [comment removed for export] *)
        apply mst_refl.
      + apply RB_store; [exact HRB | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; cbn; lia].
      + eapply (LC_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs _ HL); [| lc_disjoint]. eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
      + gres. rewrite (AG1 31) by notin_list. exact H31.
      + gres. rewrite (AG1 21) by notin_list. exact H21.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - (* [comment removed for export] *)
      eexists. exists m. split; [|split; [exact HRB|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_163a4 D_163a4 ltac:(exact Hc).                                       (* [comment removed for export] *)
        apply mst_refl.
      + eapply (LC_agree _ regs _ HL); [exact AG1 | lc_disjoint].
      + rewrite (AG1 31) by notin_list. exact H31.
      + rewrite (AG1 21) by notin_list. exact H21.
      + regs_agree_weaken AG1.
  Qed.

  (* [comment removed for export] *)
  Lemma idx4 : forall m, RB m -> rdn SEGS m (Z_to_bv 64 (s - 132)) 4 = Some ibs.
  Proof. intros m HRB. exact (RB_cell m (s - 132) 4 ibs HRB ltac:(lia) ltac:(cbn; lia) Cidx). Qed.
  Lemma idx1 : forall m, RB m -> rdn SEGS m (Z_to_bv 64 (s - 132)) 1 = Some [ib].
  Proof. intros m HRB. exact (RB_cell m (s - 132) 1 [ib] HRB ltac:(lia) ltac:(cbn; lia) Cidx1). Qed.

  Ltac zva F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia]).
  Ltac zvs F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).

  (* [comment removed for export] *)
  Lemma px4 : forall regs m i j, RB m -> LC regs -> (d = 4)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 31 = Z_to_bv 64 j -> getr regs 21 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16448 : word) m rom) (mkst regs' (0x1642c : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 31 = Z_to_bv 64 j /\ getr regs' 21 = Z_to_bv 64 (datas + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m i j HRB HL Hd4 Hi Hj H31 H21.
    pose proof HL as (L2 & L10 & L8 & L9 & L18 & L20 & L13 & L14 & L15 & L17 & L7 & L30).
    pose proof wpl_bounds as (Hwpl1 & _). pose proof (row_in_raster i Hi) as Hrow.
    pose proof (pix_word j Hj) as Hq. rewrite Hd4, div4_32 in Hq by lia.
    destruct (word_at m i (j / 8) HRB Hi Hq) as (bs & Hbs & Lbs & SOKa & Ba).
    pose proof (idx4 m HRB) as Ci.
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x16448 : word) m rom) (mkst r1 (0x16514 : word) m rom)
                            /\ getr r1 23 = Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 8))
                            /\ regs_agree (fun r : reg => In r [23; 24; 25; 26]%list) regs r1).
    { eexists. split.
      - stepb_tk F_16344 D_16344 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_tk F_16390 D_16390 ltac:(condZ).                                          (* [comment removed for export] *)
        sn F_163f0 D_163f0. fixv (Z_to_bv 64 (j / 8)) ltac:(change 8%Z with (2 ^ 3)%Z; apply zbv_srliw_small; lia).   (* [comment removed for export] *)
        zvs F_163f4 D_163f4 (Z_to_bv 64 (4 * (j / 8))).                                 (* [comment removed for export] *)
        zva F_163f8 D_163f8 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 8))).          (* [comment removed for export] *)
        stepLD F_163fc D_163fc bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(rdn_addr (datas + 4 * wpl * i + 4 * (j / 8))%Z; exact Hbs) ltac:(symmetry; apply u_lez4; exact Lbs).   (* [comment removed for export] *)
        sn F_16400 D_16400. sn F_16404 D_16404. sn F_16408 D_16408. sn F_1640c D_1640c.  (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q23 & AG1).
    pose proof (AG1 8 ltac:(notin_list)) as Q8. rewrite L8 in Q8. pose proof (AG1 2 ltac:(notin_list)) as Q2. rewrite L2 in Q2.
    destruct (c_eq (getr r1 26) (getr r1 8)) eqn:Hc.
    - (* [comment removed for export] *)
      eexists. eexists. split; [|split; [|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_16410 D_16410 ltac:(exact Hc).                                       (* [comment removed for export] *)
        stepLD F_16414 D_16414 ibs (Z_to_bv 64 (bytes_le_to_Z ibs)) ltac:(rdn_addr (s - 132)%Z; exact Ci) ltac:(symmetry; apply u_lez4; exact Lidx).   (* [comment removed for export] *)
        sn F_16418 D_16418. sn F_1641c D_1641c. sn F_16420 D_16420. sn F_16424 D_16424. sn F_16428 D_16428.   (* [comment removed for export] *)
        sn F_1642c D_1642c.                                                              (* [comment removed for export] *)
        sn F_1631c D_1631c. sn F_16320 D_16320.                                          (* [comment removed for export] *)
        stepSTv F_16324 D_16324 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 8))) ltac:(store_ok_peel; exact SOKa).   (* [comment removed for export] *)
        apply mst_refl.
      + apply RB_store; [exact HRB | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
      + lc_via HL AG1.
      + gres. rewrite (AG1 31) by notin_list. exact H31.
      + gres. rewrite (AG1 21) by notin_list. exact H21.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - (* [comment removed for export] *)
      eexists. exists m. split; [|split; [exact HRB|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_16410 D_16410 ltac:(exact Hc).                                       (* [comment removed for export] *)
        apply mst_refl.
      + lc_via1 HL AG1.
      + rewrite (AG1 31) by notin_list. exact H31.
      + rewrite (AG1 21) by notin_list. exact H21.
      + regs_agree_weaken AG1.
  Qed.

  (* [comment removed for export] *)
  Lemma px2 : forall regs m i j, RB m -> LC regs -> (d = 2)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 31 = Z_to_bv 64 j -> getr regs 21 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16448 : word) m rom) (mkst regs' (0x1642c : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 31 = Z_to_bv 64 j /\ getr regs' 21 = Z_to_bv 64 (datas + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m i j HRB HL Hd2 Hi Hj H31 H21.
    pose proof HL as (L2 & L10 & L8 & L9 & L18 & L20 & L13 & L14 & L15 & L17 & L7 & L30).
    pose proof wpl_bounds as (Hwpl1 & _). pose proof (row_in_raster i Hi) as Hrow.
    pose proof (pix_word j Hj) as Hq. rewrite Hd2, div2_32 in Hq by lia.
    destruct (word_at m i (j / 16) HRB Hi Hq) as (bs & Hbs & Lbs & SOKa & Ba).
    pose proof (idx4 m HRB) as Ci.
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x16448 : word) m rom) (mkst r1 (0x16474 : word) m rom)
                            /\ getr r1 23 = Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 16))
                            /\ regs_agree (fun r : reg => In r [23; 24; 25; 26]%list) regs r1).
    { eexists. split.
      - stepb_ft F_16344 D_16344 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_ft F_16348 D_16348 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_ft F_1634c D_1634c ltac:(condZ).                                          (* [comment removed for export] *)
        sn F_16350 D_16350. fixv (Z_to_bv 64 (j / 16)) ltac:(change 16%Z with (2 ^ 4)%Z; apply zbv_srliw_small; lia).  (* [comment removed for export] *)
        zvs F_16354 D_16354 (Z_to_bv 64 (4 * (j / 16))).                                (* [comment removed for export] *)
        zva F_16358 D_16358 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 16))).         (* [comment removed for export] *)
        stepLD F_1635c D_1635c bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(rdn_addr (datas + 4 * wpl * i + 4 * (j / 16))%Z; exact Hbs) ltac:(symmetry; apply u_lez4; exact Lbs).   (* [comment removed for export] *)
        sn F_16360 D_16360. sn F_16364 D_16364. sn F_16368 D_16368. sn F_1636c D_1636c.  (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q23 & AG1).
    pose proof (AG1 8 ltac:(notin_list)) as Q8. rewrite L8 in Q8. pose proof (AG1 2 ltac:(notin_list)) as Q2. rewrite L2 in Q2.
    destruct (c_eq (getr r1 26) (getr r1 8)) eqn:Hc.
    - eexists. eexists. split; [|split; [|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_16370 D_16370 ltac:(exact Hc).                                       (* [comment removed for export] *)
        stepLD F_16374 D_16374 ibs (Z_to_bv 64 (bytes_le_to_Z ibs)) ltac:(rdn_addr (s - 132)%Z; exact Ci) ltac:(symmetry; apply u_lez4; exact Lidx).   (* [comment removed for export] *)
        sn F_16378 D_16378. sn F_1637c D_1637c. sn F_16380 D_16380. sn F_16384 D_16384. sn F_16388 D_16388.   (* [comment removed for export] *)
        sn F_1638c D_1638c.                                                              (* [comment removed for export] *)
        sn F_1631c D_1631c. sn F_16320 D_16320.                                          (* [comment removed for export] *)
        stepSTv F_16324 D_16324 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 16))) ltac:(store_ok_peel; exact SOKa).   (* [comment removed for export] *)
        apply mst_refl.
      + apply RB_store; [exact HRB | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
      + lc_via HL AG1.
      + gres. rewrite (AG1 31) by notin_list. exact H31.
      + gres. rewrite (AG1 21) by notin_list. exact H21.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - eexists. exists m. split; [|split; [exact HRB|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_16370 D_16370 ltac:(exact Hc).                                       (* [comment removed for export] *)
        apply mst_refl.
      + lc_via1 HL AG1.
      + rewrite (AG1 31) by notin_list. exact H31.
      + rewrite (AG1 21) by notin_list. exact H21.
      + regs_agree_weaken AG1.
  Qed.

  (* [comment removed for export] *)
  Lemma px1 : forall regs m i j, RB m -> LC regs -> (d = 1)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 31 = Z_to_bv 64 j -> getr regs 21 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16448 : word) m rom) (mkst regs' (0x1642c : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 31 = Z_to_bv 64 j /\ getr regs' 21 = Z_to_bv 64 (datas + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m i j HRB HL Hd1 Hi Hj H31 H21.
    pose proof HL as (L2 & L10 & L8 & L9 & L18 & L20 & L13 & L14 & L15 & L17 & L7 & L30).
    pose proof wpl_bounds as (Hwpl1 & _). pose proof (row_in_raster i Hi) as Hrow.
    pose proof (pix_word j Hj) as Hq. rewrite Hd1, Z.mul_1_r in Hq.
    destruct (word_at m i (j / 32) HRB Hi Hq) as (bs & Hbs & Lbs & SOKa & Ba).
    pose proof (idx4 m HRB) as Ci.
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x16448 : word) m rom) (mkst r1 (0x164d4 : word) m rom)
                            /\ getr r1 23 = Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 32))
                            /\ regs_agree (fun r : reg => In r [23; 24; 25]%list) regs r1).
    { eexists. split.
      - stepb_ft F_16344 D_16344 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_tk F_16348 D_16348 ltac:(condZ).                                          (* [comment removed for export] *)
        sn F_163b4 D_163b4. fixv (Z_to_bv 64 (j / 32)) ltac:(change 32%Z with (2 ^ 5)%Z; apply zbv_srliw_small; lia).  (* [comment removed for export] *)
        zvs F_163b8 D_163b8 (Z_to_bv 64 (4 * (j / 32))).                                (* [comment removed for export] *)
        zva F_163bc D_163bc (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 32))).         (* [comment removed for export] *)
        stepLD F_163c0 D_163c0 bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(rdn_addr (datas + 4 * wpl * i + 4 * (j / 32))%Z; exact Hbs) ltac:(symmetry; apply u_lez4; exact Lbs).   (* [comment removed for export] *)
        sn F_163c4 D_163c4. sn F_163c8 D_163c8. sn F_163cc D_163cc.                      (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q23 & AG1).
    pose proof (AG1 8 ltac:(notin_list)) as Q8. rewrite L8 in Q8. pose proof (AG1 2 ltac:(notin_list)) as Q2. rewrite L2 in Q2.
    pose proof (AG1 31 ltac:(notin_list)) as Q31. rewrite H31 in Q31.
    destruct (c_eq (getr r1 25) (getr r1 8)) eqn:Hc.
    - (* [comment removed for export] *)
      assert (S2 : exists r2, msteps SEGS (mkst r1 (0x164d4 : word) m rom) (mkst r2 (0x164e4 : word) m rom)
                              /\ getr r2 23 = Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 32))
                              /\ regs_agree (fun r : reg => In r [25; 26]%list) r1 r2).
      { eexists. split.
        - stepb_ft F_163d0 D_163d0 ltac:(exact Hc).                                     (* [comment removed for export] *)
          stepLD F_163d4 D_163d4 ibs (Z_to_bv 64 (bytes_le_to_Z ibs)) ltac:(rdn_addr (s - 132)%Z; exact Ci) ltac:(symmetry; apply u_lez4; exact Lidx).   (* [comment removed for export] *)
          sn F_163d8 D_163d8. sn F_163dc D_163dc.                                        (* [comment removed for export] *)
          apply mst_refl.
        - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
      destruct S2 as (r2 & S2 & P23 & AG2).
      destruct (c_eq (getr r2 26) (Z_to_bv 64 0)) eqn:Hc2.
      + (* [comment removed for export] *)
        eexists. eexists. split; [|split; [|split; [|split; [|split]]]].
        * eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
          stepb_ft F_163e0 D_163e0 ltac:(exact Hc2).                                    (* [comment removed for export] *)
          sn F_163e4 D_163e4. sn F_163e8 D_163e8.                                        (* [comment removed for export] *)
          sn F_163ec D_163ec.                                                            (* [comment removed for export] *)
          stepSTv F_16324 D_16324 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 32))) ltac:(store_ok_peel; exact SOKa).   (* [comment removed for export] *)
          apply mst_refl.
        * apply RB_store; [exact HRB | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
        * eapply (LC_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) _ _ HL); [| lc_disjoint]. eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. solve_regs_agree.
        * gres. rewrite (AG2 31) by notin_list. exact Q31.
        * gres. rewrite (AG2 21), (AG1 21) by notin_list. exact H21.
        * eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. solve_regs_agree.
      + (* [comment removed for export] *)
        eexists. eexists. split; [|split; [|split; [|split; [|split]]]].
        * eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
          stepb_tk F_163e0 D_163e0 ltac:(exact Hc2).                                    (* [comment removed for export] *)
          sn F_16320 D_16320.                                                            (* [comment removed for export] *)
          stepSTv F_16324 D_16324 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 32))) ltac:(store_ok_peel; exact SOKa).   (* [comment removed for export] *)
          apply mst_refl.
        * apply RB_store; [exact HRB | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
        * eapply (LC_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) _ _ HL); [| lc_disjoint]. eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. solve_regs_agree.
        * gres. rewrite (AG2 31) by notin_list. exact Q31.
        * gres. rewrite (AG2 21), (AG1 21) by notin_list. exact H21.
        * eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. solve_regs_agree.
    - (* [comment removed for export] *)
      eexists. exists m. split; [|split; [exact HRB|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_163d0 D_163d0 ltac:(exact Hc).                                       (* [comment removed for export] *)
        apply mst_refl.
      + lc_via1 HL AG1.
      + exact Q31.
      + rewrite (AG1 21) by notin_list. exact H21.
      + regs_agree_weaken AG1.
  Qed.

  (* [comment removed for export] *)
  Lemma px : forall regs m i j, RB m -> LC regs -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 31 = Z_to_bv 64 j -> getr regs 21 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16448 : word) m rom) (mkst regs' (0x1642c : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 31 = Z_to_bv 64 j /\ getr regs' 21 = Z_to_bv 64 (datas + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m i j HRB HL Hi Hj H31 H21.
    destruct Hd as [D1|[D2|[D4|D8]]]; [apply px1 | apply px2 | apply px4 | apply px8]; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma col_iter : forall regs m i j, RB m -> LC regs -> (0 <= i < h)%Z -> (0 <= j < 2 ^ 31)%Z ->
    getr regs 31 = Z_to_bv 64 j -> getr regs 21 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x1643c : word) m rom) (mkst regs' (0x1642c : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 31 = Z_to_bv 64 j /\ getr regs' 21 = Z_to_bv 64 (datas + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m i j HRB HL Hi Hj H31 H21.
    pose proof HL as (L2 & L10 & L8 & L9 & L18 & L20 & L13 & L14 & L15 & L17 & L7 & L30).
    pose proof (RB_cell m (s - 108) 4 _ HRB ltac:(lia) ltac:(cbn; lia) Cw) as Cw'.
    destruct (Z_lt_ge_dec j w) as [LT|GE].
    - assert (S1 : exists r1, msteps SEGS (mkst regs (0x1643c : word) m rom) (mkst r1 (0x16448 : word) m rom)
                              /\ regs_agree (fun r : reg => In r [23]%list) regs r1).
      { eexists. split.
        - stepb_ft F_16338 D_16338 ltac:(condZ).                                                     (* [comment removed for export] *)
          stepLD F_1633c D_1633c (Z_to_le_bytes 4 w) (Z_to_bv 64 w) ltac:(rdn_addr (s - 108)%Z; exact Cw') ltac:(apply lez4; lia).   (* [comment removed for export] *)
          rewrite (v_lw_small w) by lia.
          stepb_ft F_16340 D_16340 ltac:(condZ).                                                     (* [comment removed for export] *)
          apply mst_refl.
        - solve_regs_agree. }
      destruct S1 as (r1 & S1 & AG1).
      destruct (px r1 m i j HRB ltac:(eapply (LC_agree _ regs _ HL); [exact AG1 | lc_disjoint]) Hi ltac:(lia)
                  ltac:(rewrite (AG1 31) by notin_list; exact H31) ltac:(rewrite (AG1 21) by notin_list; exact H21))
        as (r2 & m2 & S2 & RB2 & LC2 & Q31 & Q21 & AG2).
      exists r2, m2. split; [eapply msteps_trans; [exact S1 | exact S2] |].
      split; [exact RB2|]. split; [exact LC2|]. split; [exact Q31|]. split; [exact Q21|].
      eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2].
    - eexists. exists m. split; [| split; [exact HRB | split; [| split; [| split]]]].
      + stepb_ft F_16338 D_16338 ltac:(condZ).                                                       (* [comment removed for export] *)
        stepLD F_1633c D_1633c (Z_to_le_bytes 4 w) (Z_to_bv 64 w) ltac:(rdn_addr (s - 108)%Z; exact Cw') ltac:(apply lez4; lia).   (* [comment removed for export] *)
        rewrite (v_lw_small w) by lia.
        stepb_tk F_16340 D_16340 ltac:(condZ).                                                       (* [comment removed for export] *)
        apply mst_refl.
      + eapply (LC_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs _ HL); [solve_regs_agree | lc_disjoint].
      + gres. exact H31.
      + gres. exact H21.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma col_loop : forall k regs m i j, RB m -> LC regs -> (0 <= i < h)%Z ->
    (Z.of_nat k = x2 - j)%Z -> (0 <= j)%Z ->
    getr regs 31 = Z_to_bv 64 j -> getr regs 21 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x1643c : word) m rom) (mkst regs' (0x163e8 : word) m' rom)
      /\ RB m' /\ LC regs'
      /\ regs_agree (fun r : reg => In r [19; 22; 23; 24; 25; 26; 27; 31]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs m i j HRB HL Hi Hk Hj H31 H21;
      destruct (col_iter regs m i j HRB HL Hi ltac:(lia) H31 H21) as (r1 & m1 & S1 & RB1 & LC1 & Q31 & Q21 & AG1);
      pose proof LC1 as (L2 & L10 & L8 & L9 & L18 & L20 & L13 & L14 & L15 & L17 & L7 & L30).
    - (* [comment removed for export] *)
      eexists. exists m1. split; [| split; [exact RB1 | split]].
      + eapply msteps_trans; [exact S1|].
        sn F_16328 D_16328. fixv (Z_to_bv 64 (j + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; reflexivity).   (* [comment removed for export] *)
        sn F_1632c D_1632c. sn F_16330 D_16330.                                                      (* [comment removed for export] *)
        stepb_tk F_16334 D_16334 ltac:(condZ).                                                       (* [comment removed for export] *)
        apply mst_refl.
      + eapply (LC_agree (fun r : reg => In r [19; 22; 23; 24; 25; 26; 27; 31]%list) r1 _ LC1); [solve_regs_agree | lc_disjoint].
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (S2 : exists r2, msteps SEGS (mkst r1 (0x1642c : word) m1 rom) (mkst r2 (0x1643c : word) m1 rom)
                              /\ getr r2 31 = Z_to_bv 64 (j + 1) /\ regs_agree (fun r : reg => In r [19; 22; 31]%list) r1 r2).
      { eexists. split.
        - sn F_16328 D_16328. fixv (Z_to_bv 64 (j + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; reflexivity). (* [comment removed for export] *)
          sn F_1632c D_1632c. sn F_16330 D_16330.                                                    (* [comment removed for export] *)
          stepb_ft F_16334 D_16334 ltac:(condZ).                                                     (* [comment removed for export] *)
          apply mst_refl.
        - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
      destruct S2 as (r2 & S2 & P31 & AG2).
      destruct (IH r2 m1 i (j + 1)%Z RB1 ltac:(eapply (LC_agree _ r1 _ LC1); [exact AG2 | lc_disjoint]) Hi ltac:(lia) ltac:(lia) P31
                  ltac:(rewrite (AG2 21) by notin_list; exact Q21)) as (r3 & m3 & S3 & RB3 & LC3 & AG3).
      exists r3, m3. split; [| split; [exact RB3 | split; [exact LC3|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3].
  Qed.

  (* [comment removed for export] *)
  Lemma row_iter : forall regs m i, RB m -> LC regs -> (0 <= i < 2 ^ 31)%Z -> getr regs 11 = Z_to_bv 64 i ->
    exists regs' m',
      msteps SEGS (mkst regs (0x163f4 : word) m rom) (mkst regs' (0x163e8 : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 11 = Z_to_bv 64 i
      /\ regs_agree (fun r : reg => In r [19; 21; 22; 23; 24; 25; 26; 27; 31]%list) regs regs'.
  Proof.
    intros regs m i HRB HL Hi H11.
    pose proof HL as (L2 & L10 & L8 & L9 & L18 & L20 & L13 & L14 & L15 & L17 & L7 & L30).
    pose proof wpl_bounds as (Hwpl1 & _).
    pose proof (RB_cell m (s - 112) 4 _ HRB ltac:(lia) ltac:(cbn; lia) Ch) as Ch'.
    pose proof (RB_cell m (s - 116) 4 _ HRB ltac:(lia) ltac:(cbn; lia) Cx1) as Cx1'.
    destruct (Z_lt_ge_dec i h) as [LT|GE].
    2:{ (* [comment removed for export] *)
      eexists. exists m. split; [| split; [exact HRB | split; [| split]]].
      - stepb_ft F_162f0 D_162f0 ltac:(condZ).                                                       (* [comment removed for export] *)
        stepLD F_162f4 D_162f4 (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(rdn_addr (s - 112)%Z; exact Ch') ltac:(apply lez4; lia).   (* [comment removed for export] *)
        rewrite (v_lw_small h) by lia.
        stepb_tk F_162f8 D_162f8 ltac:(condZ).                                                       (* [comment removed for export] *)
        apply mst_refl.
      - eapply (LC_agree (fun r : reg => In r [19; 21; 22; 23; 24; 25; 26; 27; 31]%list) regs _ HL); [solve_regs_agree | lc_disjoint].
      - gres. exact H11.
      - solve_regs_agree. }
    destruct (Z_lt_ge_dec x2 x1) as [EMP|NE].
    { (* [comment removed for export] *)
      eexists. exists m. split; [| split; [exact HRB | split; [| split]]].
      - stepb_ft F_162f0 D_162f0 ltac:(condZ).                                                       (* [comment removed for export] *)
        stepLD F_162f4 D_162f4 (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(rdn_addr (s - 112)%Z; exact Ch') ltac:(apply lez4; lia).   (* [comment removed for export] *)
        rewrite (v_lw_small h) by lia.
        stepb_ft F_162f8 D_162f8 ltac:(condZ).                                                       (* [comment removed for export] *)
        stepLD F_162fc D_162fc (Z_to_le_bytes 4 x1) (Z_to_bv 64 x1) ltac:(rdn_addr (s - 116)%Z; exact Cx1') ltac:(apply lez4; lia). (* [comment removed for export] *)
        rewrite (v_lw_small x1) by lia.
        stepb_tk F_16300 D_16300 ltac:(condZ).                                                       (* [comment removed for export] *)
        apply mst_refl.
      - eapply (LC_agree (fun r : reg => In r [19; 21; 22; 23; 24; 25; 26; 27; 31]%list) regs _ HL); [solve_regs_agree | lc_disjoint].
      - gres. exact H11.
      - solve_regs_agree. }
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x163f4 : word) m rom) (mkst r1 (0x1643c : word) m rom)
                            /\ getr r1 31 = Z_to_bv 64 x1 /\ getr r1 21 = Z_to_bv 64 (datas + 4 * wpl * i)
                            /\ regs_agree (fun r : reg => In r [19; 21; 22; 31]%list) regs r1).
    { eexists. split.
      - stepb_ft F_162f0 D_162f0 ltac:(condZ).                                                       (* [comment removed for export] *)
        stepLD F_162f4 D_162f4 (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(rdn_addr (s - 112)%Z; exact Ch') ltac:(apply lez4; lia).   (* [comment removed for export] *)
        rewrite (v_lw_small h) by lia.
        stepb_ft F_162f8 D_162f8 ltac:(condZ).                                                       (* [comment removed for export] *)
        stepLD F_162fc D_162fc (Z_to_le_bytes 4 x1) (Z_to_bv 64 x1) ltac:(rdn_addr (s - 116)%Z; exact Cx1') ltac:(apply lez4; lia). (* [comment removed for export] *)
        rewrite (v_lw_small x1) by lia.
        stepb_ft F_16300 D_16300 ltac:(condZ).                                                       (* [comment removed for export] *)
        zva F_16304 D_16304 (Z_to_bv 64 (i * wpl)).                                                  (* [comment removed for export] *)
        sn F_16308 D_16308.                                                                          (* [comment removed for export] *)
        zvs F_1630c D_1630c (Z_to_bv 64 (4 * (i * wpl))).                                           (* [comment removed for export] *)
        zva F_16310 D_16310 (Z_to_bv 64 (datas + 4 * wpl * i)).                                      (* [comment removed for export] *)
        sn F_16314 D_16314. sn F_16318 D_16318.                                                      (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q31 & Q21 & AG1).
    destruct (col_loop (Z.to_nat (x2 - x1)) r1 m i x1 HRB ltac:(eapply (LC_agree _ regs _ HL); [exact AG1 | lc_disjoint]) ltac:(lia)
                ltac:(lia) ltac:(lia) Q31 Q21) as (r2 & m2 & S2 & RB2 & LC2 & AG2).
    exists r2, m2. split; [| split; [exact RB2 | split; [exact LC2 | split]]].
    - eapply msteps_trans; [exact S1 | exact S2].
    - rewrite (AG2 11), (AG1 11) by notin_list. exact H11.
    - eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma row_loop : forall k regs m i, RB m -> LC regs -> (Z.of_nat k = y2 - i)%Z -> (0 <= i)%Z ->
    getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 (y2 + 1) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x163f4 : word) m rom) (mkst regs' (0x163ac : word) m' rom)
      /\ RB m' /\ LC regs'
      /\ regs_agree (fun r : reg => In r [11; 19; 21; 22; 23; 24; 25; 26; 27; 31]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs m i HRB HL Hk Hi H11 H12;
      destruct (row_iter regs m i HRB HL ltac:(lia) H11) as (r1 & m1 & S1 & RB1 & LC1 & Q11 & AG1);
      pose proof LC1 as (L2 & L10 & L8 & L9 & L18 & L20 & L13 & L14 & L15 & L17 & L7 & L30);
      pose proof (AG1 12 ltac:(notin_list)) as Q12; rewrite H12 in Q12.
    - (* [comment removed for export] *)
      eexists. exists m1. split; [| split; [exact RB1 | split]].
      + eapply msteps_trans; [exact S1|].
        sn F_162e4 D_162e4. fixv (Z_to_bv 64 (i + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; reflexivity).   (* [comment removed for export] *)
        zva F_162e8 D_162e8 (Z_to_bv 64 (i + 1)).                                                    (* [comment removed for export] *)
        stepb_tk F_162ec D_162ec ltac:(condZ).                                                       (* [comment removed for export] *)
        apply mst_refl.
      + eapply (LC_agree (fun r : reg => In r [11; 19; 21; 22; 23; 24; 25; 26; 27; 31]%list) r1 _ LC1); [solve_regs_agree | lc_disjoint].
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (S2 : exists r2, msteps SEGS (mkst r1 (0x163e8 : word) m1 rom) (mkst r2 (0x163f4 : word) m1 rom)
                              /\ getr r2 11 = Z_to_bv 64 (i + 1) /\ regs_agree (fun r : reg => In r [11; 31]%list) r1 r2).
      { eexists. split.
        - sn F_162e4 D_162e4. fixv (Z_to_bv 64 (i + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; reflexivity). (* [comment removed for export] *)
          zva F_162e8 D_162e8 (Z_to_bv 64 (i + 1)).                                                  (* [comment removed for export] *)
          stepb_ft F_162ec D_162ec ltac:(condZ).                                                     (* [comment removed for export] *)
          apply mst_refl.
        - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
      destruct S2 as (r2 & S2 & P11 & AG2).
      destruct (IH r2 m1 (i + 1)%Z RB1 ltac:(eapply (LC_agree _ r1 _ LC1); [exact AG2 | lc_disjoint]) ltac:(lia) ltac:(lia) P11
                  ltac:(rewrite (AG2 12) by notin_list; exact Q12)) as (r3 & m3 & S3 & RB3 & LC3 & AG3).
      exists r3, m3. split; [| split; [exact RB3 | split; [exact LC3|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3].
  Qed.

  Definition loop_clob : list (bv 5) := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

  (* [comment removed for export] *)
  Theorem sel_loop : forall regs m, RB m ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 wpl -> getr regs 8 = Z_to_bv 64 sindex ->
    getr regs 9 = Z_to_bv 64 d -> getr regs 18 = Z_to_bv 64 datas -> getr regs 20 = Z_to_bv 64 x2 -> getr regs 21 = Z_to_bv 64 y2 ->
    exists regs' m',
      msteps SEGS (mkst regs (0x163a4 : word) m rom) (mkst regs' (0x16568 : word) m' rom)
      /\ RB m' /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r : reg => In r loop_clob) regs regs'.
  Proof.
    intros regs m HRB H2 H10 H8 H9 H18 H20 H21.
    pose proof wpl_bounds as (Hwpl1 & _).
    pose proof (RB_cell m (s - 120) 4 _ HRB ltac:(lia) ltac:(cbn; lia) Cy1) as Cy1'.
    destruct (Z_lt_ge_dec y2 y1) as [EMP|NE].
    { (* [comment removed for export] *)
      eexists. exists m. split; [| split; [exact HRB | split; [| split]]].
      - stepLD F_162a0 D_162a0 (Z_to_le_bytes 4 y1) (Z_to_bv 64 y1) ltac:(rdn_addr (s - 120)%Z; exact Cy1') ltac:(apply lez4; lia). (* [comment removed for export] *)
        rewrite (v_lw_small y1) by lia.
        stepb_ft F_162a4 D_162a4 ltac:(condZ).                                                       (* [comment removed for export] *)
        sn F_162a8 D_162a8. sn F_162ac D_162ac.                                                      (* [comment removed for export] *)
        apply mst_refl.
      - gres. exact H2.
      - gres. reflexivity.
      - unfold loop_clob. solve_regs_agree. }
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x163a4 : word) m rom) (mkst r1 (0x163f4 : word) m rom)
                            /\ LC r1 /\ getr r1 11 = Z_to_bv 64 y1 /\ getr r1 12 = Z_to_bv 64 (y2 + 1)
                            /\ regs_agree (fun r : reg => In r loop_clob) regs r1).
    { eexists. split; [|split].
      - stepLD F_162a0 D_162a0 (Z_to_le_bytes 4 y1) (Z_to_bv 64 y1) ltac:(rdn_addr (s - 120)%Z; exact Cy1') ltac:(apply lez4; lia). (* [comment removed for export] *)
        rewrite (v_lw_small y1) by lia.
        stepb_tk F_162a4 D_162a4 ltac:(condZ).                                                       (* [comment removed for export] *)
        sn F_162b0 D_162b0. fixv (Z_to_bv 64 (y2 + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; reflexivity).   (* [comment removed for export] *)
        sn F_162b4 D_162b4. fixv (Z_to_bv 64 (x2 + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; reflexivity).   (* [comment removed for export] *)
        sn F_162b8 D_162b8. sn F_162bc D_162bc. sn F_162c0 D_162c0. sn F_162c4 D_162c4.
        sn F_162c8 D_162c8. sn F_162cc D_162cc. sn F_162d0 D_162d0. sn F_162d4 D_162d4.
        sn F_162d8 D_162d8. sn F_162dc D_162dc. sn F_162e0 D_162e0.
        apply mst_refl.
      - unfold LC. repeat split; gres; pin; reflexivity.
      - repeat split; gres; pin; try reflexivity. unfold loop_clob. solve_regs_agree. }
    destruct S1 as (r1 & S1 & LC1 & Q11 & Q12 & AG1).
    destruct (row_loop (Z.to_nat (y2 - y1)) r1 m y1 HRB LC1 ltac:(lia) ltac:(lia) Q11 Q12) as (r2 & m2 & S2 & RB2 & LC2 & AG2).
    pose proof LC2 as (L2 & _).
    eexists. exists m2. split; [| split; [exact RB2 | split; [| split]]].
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
      sn F_162a8 D_162a8. sn F_162ac D_162ac.                                                        (* [comment removed for export] *)
      apply mst_refl.
    - gres. exact L2.
    - gres. reflexivity.
    - eapply regs_agree_trans; [exact AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. unfold loop_clob. solve_regs_agree.
  Qed.

End SelLoop.
