(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib MemSplit MmapSim SeqExec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21LeptUb V21_code_16000_17000.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
  Lemma iwpl_small : forall i, (0 <= i < h)%Z -> (0 <= i * wpl /\ i * wpl + wpl <= wpl * h /\ wpl * h <= 100020000)%Z.
  Proof.
    intros i Hi. clear - Hi Hh Hw Hd Hwpl. pose proof wpl_bounds as (Hwpl1 & _).
    assert (wpl * (i + 1) <= wpl * h)%Z by (apply Z.mul_le_mono_nonneg_l; lia). nia.
  Qed.

  (* [comment removed for export] *)
  Definition LC (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 144) /\ getr regs 10 = Z_to_bv 64 wpl /\ getr regs 8 = Z_to_bv 64 sindex /\
    getr regs 9 = Z_to_bv 64 d /\ getr regs 18 = Z_to_bv 64 datas /\ getr regs 20 = Z_to_bv 64 x2 /\ getr regs 21 = Z_to_bv 64 y2 /\
    getr regs 12 = Z_to_bv 64 1 /\ getr regs 13 = Z_to_bv 64 3 /\ getr regs 14 = Z_to_bv 64 1 /\
    getr regs 16 = Z_to_bv 64 2 /\ getr regs 5 = Z_to_bv 64 30 /\ getr regs 6 = Z_to_bv 64 4 /\
    getr regs 28 = Z_to_bv 64 28 /\ getr regs 29 = Z_to_bv 64 8.
  (* [comment removed for export] *)

  #[local] Definition lc_regs : list (bv 5) := [2; 10; 8; 9; 18; 20; 21; 12; 13; 14; 16; 5; 6; 28; 29]%bv.

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
  Ltac lcd HL := pose proof HL as (L2 & L10 & L8 & L9 & L18 & L20 & L21 & L12 & L13 & L14 & L16 & L5 & L6 & L28 & L29).

  (* [comment removed for export] *)
  Lemma idx4 : forall m, RB m -> rdn SEGS m (Z_to_bv 64 (s - 132)) 4 = Some ibs.
  Proof. intros m HRB. exact (RB_cell m (s - 132) 4 ibs HRB ltac:(lia) ltac:(cbn; lia) Cidx). Qed.
  Lemma idx1 : forall m, RB m -> rdn SEGS m (Z_to_bv 64 (s - 132)) 1 = Some [ib].
  Proof. intros m HRB. exact (RB_cell m (s - 132) 1 [ib] HRB ltac:(lia) ltac:(cbn; lia) Cidx1). Qed.

  Ltac zva F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia]).
  Ltac zvs F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
  (* [comment removed for export] *)
  Ltac seqz_nz F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
  Ltac litv F D v := sn F D; fixv v ltac:(apply bv_eq; vm_compute; reflexivity).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma px8 : forall regs m i j, RB m -> LC regs -> (d = 8)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 22 = Z_to_bv 64 j -> getr regs 30 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16ba4 : word) m rom) (mkst regs' (0x16d00 : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 22 = Z_to_bv 64 j /\ getr regs' 30 = Z_to_bv 64 (datas + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m i j HRB HL Hd8 Hi Hj H22 H30. lcd HL.
    pose proof wpl_bounds as (Hwpl1 & Hwd & _). pose proof (row_in_raster i Hi) as Hrow.
    assert (Hjr : (j < 4 * wpl)%Z) by (rewrite Hd8 in Hwd; lia).
    destruct (byte8_at m i j HRB Hi Hd8 Hj) as (f & b & Hxf & Hf & Hb & SOKf).
    pose proof (RB_cell m (s - 132) 1 [ib] HRB ltac:(lia) ltac:(cbn; lia) Cidx1) as Ci.
    pose proof (u_byte64 b) as Hbr.
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x16ba4 : word) m rom) (mkst r1 (0x16c34 : word) m rom)
                            /\ getr r1 23 = Z_to_bv 64 f /\ getr r1 24 = Z_to_bv 64 (bv_unsigned b)
                            /\ regs_agree (fun r : reg => In r [23; 24]%list) regs r1).
    { eexists. split.
      - stepb_tk F_16aa0 D_16aa0 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_ft F_16b08 D_16b08 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_ft F_16b0c D_16b0c ltac:(condZ).                                          (* [comment removed for export] *)
        zva F_16b10 D_16b10 (Z_to_bv 64 (datas + 4 * wpl * i + j)).                    (* [comment removed for export] *)
        stepb_ft F_16b14 D_16b14 ltac:(condZ).                                          (* [comment removed for export] *)
        seqz_nz F_16b18 D_16b18.                                                         (* [comment removed for export] *)
        litv F_16b1c D_16b1c (Z_to_bv 64 1).                                            (* [comment removed for export] *)
        stepb_ft F_16b20 D_16b20 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_ft F_16b24 D_16b24 ltac:(condZ).                                          (* [comment removed for export] *)
        stepiv F_16b28 D_16b28 (Z_to_bv 64 f) ltac:(gres; pin; imm_norm; exact Hxf).   (* [comment removed for export] *)
        stepLBU F_16b2c D_16b2c b ltac:(rdn_addr f; exact Hb).                           (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q23 & Q24 & AG1).
    pose proof (AG1 8 ltac:(notin_list)) as Q8. rewrite L8 in Q8. pose proof (AG1 2 ltac:(notin_list)) as Q2. rewrite L2 in Q2.
    destruct (c_eq (getr r1 8) (getr r1 24)) eqn:Hc.
    - (* [comment removed for export] *)
      eexists. eexists. split; [|split; [|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_16b30 D_16b30 ltac:(exact Hc).                                       (* [comment removed for export] *)
        stepLBU F_16b34 D_16b34 ib ltac:(rdn_addr (s - 132)%Z; exact Ci).               (* [comment removed for export] *)
        stepSTv F_16b38 D_16b38 (Z_to_bv 64 f) ltac:(store_ok_peel; exact SOKf).         (* [comment removed for export] *)
        sn F_16b3c D_16b3c.                                                              (* [comment removed for export] *)
        apply mst_refl.
      + apply RB_store; [exact HRB | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; cbn; lia].
      + eapply (LC_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs _ HL); [| lc_disjoint]. eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
      + gres. rewrite (AG1 22) by notin_list. exact H22.
      + gres. rewrite (AG1 30) by notin_list. exact H30.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - (* [comment removed for export] *)
      eexists. exists m. split; [|split; [exact HRB|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_16b30 D_16b30 ltac:(exact Hc).                                       (* [comment removed for export] *)
        apply mst_refl.
      + eapply (LC_agree _ regs _ HL); [exact AG1 | lc_disjoint].
      + rewrite (AG1 22) by notin_list. exact H22.
      + rewrite (AG1 30) by notin_list. exact H30.
      + regs_agree_weaken AG1.
  Qed.

  (* [comment removed for export] *)
  Lemma px4 : forall regs m i j, RB m -> LC regs -> (d = 4)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 22 = Z_to_bv 64 j -> getr regs 31 = Z_to_bv 64 (4 * j) -> getr regs 30 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16ba4 : word) m rom) (mkst regs' (0x16d00 : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 22 = Z_to_bv 64 j /\ getr regs' 30 = Z_to_bv 64 (datas + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m i j HRB HL Hd4 Hi Hj H22 H31 H30. lcd HL.
    pose proof wpl_bounds as (Hwpl1 & _). pose proof (row_in_raster i Hi) as Hrow.
    pose proof (pix_word j Hj) as Hq. rewrite Hd4, div4_32 in Hq by lia.
    destruct (word_at m i (j / 8) HRB Hi Hq) as (bs & Hbs & Lbs & SOKa & Ba).
    pose proof (word_addr_al4 datas wpl i (j / 8) Hdal) as ALa.
    pose proof (idx4 m HRB) as Ci.
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x16ba4 : word) m rom) (mkst r1 (0x16cd8 : word) m rom)
                            /\ getr r1 23 = Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 8))
                            /\ regs_agree (fun r : reg => In r [23; 24; 25; 26]%list) regs r1).
    { eexists. split.
      - stepb_tk F_16aa0 D_16aa0 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_tk F_16b08 D_16b08 ltac:(condZ).                                          (* [comment removed for export] *)
        sn F_16b98 D_16b98. fixv (Z_to_bv 64 (j / 8)) ltac:(change 8%Z with (2 ^ 3)%Z; apply zbv_srliw_small; lia).   (* [comment removed for export] *)
        zvs F_16b9c D_16b9c (Z_to_bv 64 (4 * (j / 8))).                                 (* [comment removed for export] *)
        zva F_16ba0 D_16ba0 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 8))).          (* [comment removed for export] *)
        stepb_ft F_16ba4 D_16ba4 ltac:(condZ).                                          (* [comment removed for export] *)
        seqz_nz F_16ba8 D_16ba8.                                                         (* [comment removed for export] *)
        litv F_16bac D_16bac (Z_to_bv 64 1).                                            (* [comment removed for export] *)
        stepb_ft F_16bb0 D_16bb0 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_ft F_16bb4 D_16bb4 ltac:(condZ).                                          (* [comment removed for export] *)
        guard4 F_16bb8 D_16bb8 ALa. stepb_ft F_16bbc D_16bbc ltac:(condZ).              (* [comment removed for export] *)
        stepLD F_16bc0 D_16bc0 bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(rdn_addr (datas + 4 * wpl * i + 4 * (j / 8))%Z; exact Hbs) ltac:(symmetry; apply u_lez4; exact Lbs).   (* [comment removed for export] *)
        sn F_16bc4 D_16bc4. sn F_16bc8 D_16bc8. sn F_16bcc D_16bcc. sn F_16bd0 D_16bd0.  (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q23 & AG1).
    pose proof (AG1 8 ltac:(notin_list)) as Q8. rewrite L8 in Q8. pose proof (AG1 2 ltac:(notin_list)) as Q2. rewrite L2 in Q2.
    destruct (c_eq (getr r1 26) (getr r1 8)) eqn:Hc.
    - (* [comment removed for export] *)
      eexists. eexists. split; [|split; [|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_16bd4 D_16bd4 ltac:(exact Hc).                                       (* [comment removed for export] *)
        stepLD F_16bd8 D_16bd8 ibs (Z_to_bv 64 (bytes_le_to_Z ibs)) ltac:(rdn_addr (s - 132)%Z; exact Ci) ltac:(symmetry; apply u_lez4; exact Lidx).   (* [comment removed for export] *)
        sn F_16bdc D_16bdc. sn F_16be0 D_16be0. sn F_16be4 D_16be4. sn F_16be8 D_16be8. sn F_16bec D_16bec.   (* [comment removed for export] *)
        sn F_16bf0 D_16bf0. sn F_16bf4 D_16bf4.                                          (* [comment removed for export] *)
        stepSTv F_16bf8 D_16bf8 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 8))) ltac:(store_ok_peel; exact SOKa).   (* [comment removed for export] *)
        apply mst_refl.
      + apply RB_store; [exact HRB | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
      + lc_via HL AG1.
      + gres. rewrite (AG1 22) by notin_list. exact H22.
      + gres. rewrite (AG1 30) by notin_list. exact H30.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - (* [comment removed for export] *)
      eexists. exists m. split; [|split; [exact HRB|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_16bd4 D_16bd4 ltac:(exact Hc).                                       (* [comment removed for export] *)
        apply mst_refl.
      + lc_via1 HL AG1.
      + rewrite (AG1 22) by notin_list. exact H22.
      + rewrite (AG1 30) by notin_list. exact H30.
      + regs_agree_weaken AG1.
  Qed.

  (* [comment removed for export] *)
  Lemma px2 : forall regs m i j, RB m -> LC regs -> (d = 2)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 22 = Z_to_bv 64 j -> getr regs 19 = Z_to_bv 64 (2 * j) -> getr regs 30 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16ba4 : word) m rom) (mkst regs' (0x16d00 : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 22 = Z_to_bv 64 j /\ getr regs' 30 = Z_to_bv 64 (datas + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m i j HRB HL Hd2 Hi Hj H22 H19 H30. lcd HL.
    pose proof wpl_bounds as (Hwpl1 & _). pose proof (row_in_raster i Hi) as Hrow.
    pose proof (pix_word j Hj) as Hq. rewrite Hd2, div2_32 in Hq by lia.
    destruct (word_at m i (j / 16) HRB Hi Hq) as (bs & Hbs & Lbs & SOKa & Ba).
    pose proof (word_addr_al4 datas wpl i (j / 16) Hdal) as ALa.
    pose proof (idx4 m HRB) as Ci.
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x16ba4 : word) m rom) (mkst r1 (0x16bec : word) m rom)
                            /\ getr r1 23 = Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 16))
                            /\ regs_agree (fun r : reg => In r [23; 24; 25; 26]%list) regs r1).
    { eexists. split.
      - stepb_ft F_16aa0 D_16aa0 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_ft F_16aa4 D_16aa4 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_ft F_16aa8 D_16aa8 ltac:(condZ).                                          (* [comment removed for export] *)
        sn F_16aac D_16aac. fixv (Z_to_bv 64 (j / 16)) ltac:(change 16%Z with (2 ^ 4)%Z; apply zbv_srliw_small; lia).  (* [comment removed for export] *)
        zvs F_16ab0 D_16ab0 (Z_to_bv 64 (4 * (j / 16))).                                (* [comment removed for export] *)
        zva F_16ab4 D_16ab4 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 16))).         (* [comment removed for export] *)
        stepb_ft F_16ab8 D_16ab8 ltac:(condZ).                                          (* [comment removed for export] *)
        seqz_nz F_16abc D_16abc.                                                         (* [comment removed for export] *)
        litv F_16ac0 D_16ac0 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
        stepb_ft F_16ac4 D_16ac4 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_ft F_16ac8 D_16ac8 ltac:(condZ).                                          (* [comment removed for export] *)
        guard4 F_16acc D_16acc ALa. stepb_ft F_16ad0 D_16ad0 ltac:(condZ).              (* [comment removed for export] *)
        stepLD F_16ad4 D_16ad4 bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(rdn_addr (datas + 4 * wpl * i + 4 * (j / 16))%Z; exact Hbs) ltac:(symmetry; apply u_lez4; exact Lbs).   (* [comment removed for export] *)
        sn F_16ad8 D_16ad8. sn F_16adc D_16adc. sn F_16ae0 D_16ae0. sn F_16ae4 D_16ae4.  (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q23 & AG1).
    pose proof (AG1 8 ltac:(notin_list)) as Q8. rewrite L8 in Q8. pose proof (AG1 2 ltac:(notin_list)) as Q2. rewrite L2 in Q2.
    destruct (c_eq (getr r1 26) (getr r1 8)) eqn:Hc.
    - eexists. eexists. split; [|split; [|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_16ae8 D_16ae8 ltac:(exact Hc).                                       (* [comment removed for export] *)
        stepLD F_16aec D_16aec ibs (Z_to_bv 64 (bytes_le_to_Z ibs)) ltac:(rdn_addr (s - 132)%Z; exact Ci) ltac:(symmetry; apply u_lez4; exact Lidx).   (* [comment removed for export] *)
        sn F_16af0 D_16af0. sn F_16af4 D_16af4. sn F_16af8 D_16af8. sn F_16afc D_16afc. sn F_16b00 D_16b00.   (* [comment removed for export] *)
        sn F_16b04 D_16b04.                                                              (* [comment removed for export] *)
        sn F_16bf0 D_16bf0. sn F_16bf4 D_16bf4.                                          (* [comment removed for export] *)
        stepSTv F_16bf8 D_16bf8 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 16))) ltac:(store_ok_peel; exact SOKa).   (* [comment removed for export] *)
        apply mst_refl.
      + apply RB_store; [exact HRB | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
      + lc_via HL AG1.
      + gres. rewrite (AG1 22) by notin_list. exact H22.
      + gres. rewrite (AG1 30) by notin_list. exact H30.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - eexists. exists m. split; [|split; [exact HRB|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_16ae8 D_16ae8 ltac:(exact Hc).                                       (* [comment removed for export] *)
        apply mst_refl.
      + lc_via1 HL AG1.
      + rewrite (AG1 22) by notin_list. exact H22.
      + rewrite (AG1 30) by notin_list. exact H30.
      + regs_agree_weaken AG1.
  Qed.

  (* [comment removed for export] *)
  Lemma px1 : forall regs m i j, RB m -> LC regs -> (d = 1)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 22 = Z_to_bv 64 j -> getr regs 30 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16ba4 : word) m rom) (mkst regs' (0x16d00 : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 22 = Z_to_bv 64 j /\ getr regs' 30 = Z_to_bv 64 (datas + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m i j HRB HL Hd1 Hi Hj H22 H30. lcd HL.
    pose proof wpl_bounds as (Hwpl1 & _). pose proof (row_in_raster i Hi) as Hrow.
    pose proof (pix_word j Hj) as Hq. rewrite Hd1, Z.mul_1_r in Hq.
    destruct (word_at m i (j / 32) HRB Hi Hq) as (bs & Hbs & Lbs & SOKa & Ba).
    pose proof (word_addr_al4 datas wpl i (j / 32) Hdal) as ALa.
    pose proof (idx4 m HRB) as Ci.
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x16ba4 : word) m rom) (mkst r1 (0x16c7c : word) m rom)
                            /\ getr r1 23 = Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 32))
                            /\ regs_agree (fun r : reg => In r [23; 24; 25]%list) regs r1).
    { eexists. split.
      - stepb_ft F_16aa0 D_16aa0 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_tk F_16aa4 D_16aa4 ltac:(condZ).                                          (* [comment removed for export] *)
        sn F_16b40 D_16b40. fixv (Z_to_bv 64 (j / 32)) ltac:(change 32%Z with (2 ^ 5)%Z; apply zbv_srliw_small; lia).  (* [comment removed for export] *)
        zvs F_16b44 D_16b44 (Z_to_bv 64 (4 * (j / 32))).                                (* [comment removed for export] *)
        zva F_16b48 D_16b48 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 32))).         (* [comment removed for export] *)
        stepb_ft F_16b4c D_16b4c ltac:(condZ).                                          (* [comment removed for export] *)
        seqz_nz F_16b50 D_16b50.                                                         (* [comment removed for export] *)
        litv F_16b54 D_16b54 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
        stepb_ft F_16b58 D_16b58 ltac:(condZ).                                          (* [comment removed for export] *)
        stepb_ft F_16b5c D_16b5c ltac:(condZ).                                          (* [comment removed for export] *)
        guard4 F_16b60 D_16b60 ALa. stepb_ft F_16b64 D_16b64 ltac:(condZ).              (* [comment removed for export] *)
        stepLD F_16b68 D_16b68 bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(rdn_addr (datas + 4 * wpl * i + 4 * (j / 32))%Z; exact Hbs) ltac:(symmetry; apply u_lez4; exact Lbs).   (* [comment removed for export] *)
        sn F_16b6c D_16b6c. sn F_16b70 D_16b70. sn F_16b74 D_16b74.                      (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q23 & AG1).
    pose proof (AG1 8 ltac:(notin_list)) as Q8. rewrite L8 in Q8. pose proof (AG1 2 ltac:(notin_list)) as Q2. rewrite L2 in Q2.
    pose proof (AG1 22 ltac:(notin_list)) as Q22. rewrite H22 in Q22.
    destruct (c_eq (getr r1 25) (getr r1 8)) eqn:Hc.
    - (* [comment removed for export] *)
      assert (S2 : exists r2, msteps SEGS (mkst r1 (0x16c7c : word) m rom) (mkst r2 (0x16c8c : word) m rom)
                              /\ getr r2 23 = Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 32))
                              /\ regs_agree (fun r : reg => In r [25; 26]%list) r1 r2).
      { eexists. split.
        - stepb_ft F_16b78 D_16b78 ltac:(exact Hc).                                     (* [comment removed for export] *)
          stepLD F_16b7c D_16b7c ibs (Z_to_bv 64 (bytes_le_to_Z ibs)) ltac:(rdn_addr (s - 132)%Z; exact Ci) ltac:(symmetry; apply u_lez4; exact Lidx).   (* [comment removed for export] *)
          sn F_16b80 D_16b80. sn F_16b84 D_16b84.                                        (* [comment removed for export] *)
          apply mst_refl.
        - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
      destruct S2 as (r2 & S2 & P23 & AG2).
      destruct (c_eq (getr r2 26) (Z_to_bv 64 0)) eqn:Hc2.
      + (* [comment removed for export] *)
        eexists. eexists. split; [|split; [|split; [|split; [|split]]]].
        * eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
          stepb_ft F_16b88 D_16b88 ltac:(exact Hc2).                                    (* [comment removed for export] *)
          sn F_16b8c D_16b8c. sn F_16b90 D_16b90.                                        (* [comment removed for export] *)
          sn F_16b94 D_16b94.                                                            (* [comment removed for export] *)
          stepSTv F_16bf8 D_16bf8 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 32))) ltac:(store_ok_peel; exact SOKa).   (* [comment removed for export] *)
          apply mst_refl.
        * apply RB_store; [exact HRB | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
        * eapply (LC_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) _ _ HL); [| lc_disjoint]. eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. solve_regs_agree.
        * gres. rewrite (AG2 22) by notin_list. exact Q22.
        * gres. rewrite (AG2 30), (AG1 30) by notin_list. exact H30.
        * eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. solve_regs_agree.
      + (* [comment removed for export] *)
        eexists. eexists. split; [|split; [|split; [|split; [|split]]]].
        * eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
          stepb_tk F_16b88 D_16b88 ltac:(exact Hc2).                                    (* [comment removed for export] *)
          sn F_16bf4 D_16bf4.                                                            (* [comment removed for export] *)
          stepSTv F_16bf8 D_16bf8 (Z_to_bv 64 (datas + 4 * wpl * i + 4 * (j / 32))) ltac:(store_ok_peel; exact SOKa).   (* [comment removed for export] *)
          apply mst_refl.
        * apply RB_store; [exact HRB | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
        * eapply (LC_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) _ _ HL); [| lc_disjoint]. eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. solve_regs_agree.
        * gres. rewrite (AG2 22) by notin_list. exact Q22.
        * gres. rewrite (AG2 30), (AG1 30) by notin_list. exact H30.
        * eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. solve_regs_agree.
    - (* [comment removed for export] *)
      eexists. exists m. split; [|split; [exact HRB|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_16b78 D_16b78 ltac:(exact Hc).                                       (* [comment removed for export] *)
        apply mst_refl.
      + lc_via1 HL AG1.
      + exact Q22.
      + rewrite (AG1 30) by notin_list. exact H30.
      + regs_agree_weaken AG1.
  Qed.

  (* [comment removed for export] *)
  Lemma px : forall regs m i j, RB m -> LC regs -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 22 = Z_to_bv 64 j -> getr regs 31 = Z_to_bv 64 (4 * j) -> getr regs 19 = Z_to_bv 64 (2 * j) ->
    getr regs 30 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16ba4 : word) m rom) (mkst regs' (0x16d00 : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 22 = Z_to_bv 64 j /\ getr regs' 30 = Z_to_bv 64 (datas + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m i j HRB HL Hi Hj H22 H31 H19 H30.
    destruct Hd as [D1|[D2|[D4|D8]]]; [apply px1 | apply px2 | apply px4 | apply px8]; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma col_iter : forall regs m i j, RB m -> LC regs -> (0 <= i < h)%Z -> (0 <= j < 2 ^ 31 - 1)%Z ->
    getr regs 22 = Z_to_bv 64 j -> getr regs 31 = Z_to_bv 64 (4 * j) -> getr regs 19 = Z_to_bv 64 (2 * j) ->
    getr regs 30 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16b98 : word) m rom) (mkst regs' (0x16d14 : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 22 = Z_to_bv 64 (j + 1) /\ getr regs' 23 = Z_to_bv 64 (j + 1)
      /\ getr regs' 31 = Z_to_bv 64 (4 * (j + 1)) /\ getr regs' 19 = Z_to_bv 64 (2 * (j + 1))
      /\ getr regs' 30 = Z_to_bv 64 (datas + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [19; 22; 23; 24; 25; 26; 27; 31]%list) regs regs'.
  Proof.
    intros regs m i j HRB HL Hi Hj H22 H31 H19 H30. lcd HL.
    pose proof (RB_cell m (s - 108) 4 _ HRB ltac:(lia) ltac:(cbn; lia) Cw) as Cw'.
    (* [comment removed for export] *)
    assert (PIX : exists r1 m1, msteps SEGS (mkst regs (0x16b98 : word) m rom) (mkst r1 (0x16d00 : word) m1 rom)
                  /\ RB m1 /\ LC r1 /\ getr r1 22 = Z_to_bv 64 j /\ getr r1 31 = Z_to_bv 64 (4 * j) /\ getr r1 19 = Z_to_bv 64 (2 * j)
                  /\ getr r1 30 = Z_to_bv 64 (datas + 4 * wpl * i)
                  /\ regs_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs r1).
    { destruct (Z_lt_ge_dec j w) as [LT|GE].
      - assert (S1 : exists r1, msteps SEGS (mkst regs (0x16b98 : word) m rom) (mkst r1 (0x16ba4 : word) m rom)
                                /\ regs_agree (fun r : reg => In r [23]%list) regs r1).
        { eexists. split.
          - stepb_ft F_16a94 D_16a94 ltac:(condZ).                                                     (* [comment removed for export] *)
            stepLD F_16a98 D_16a98 (Z_to_le_bytes 4 w) (Z_to_bv 64 w) ltac:(rdn_addr (s - 108)%Z; exact Cw') ltac:(apply lez4; lia).   (* [comment removed for export] *)
            rewrite (v_lw_small w) by lia.
            stepb_ft F_16a9c D_16a9c ltac:(condZ).                                                     (* [comment removed for export] *)
            apply mst_refl.
          - solve_regs_agree. }
        destruct S1 as (r1 & S1 & AG1).
        destruct (px r1 m i j HRB ltac:(eapply (LC_agree _ regs _ HL); [exact AG1 | lc_disjoint]) Hi ltac:(lia)
                    ltac:(rewrite (AG1 22) by notin_list; exact H22) ltac:(rewrite (AG1 31) by notin_list; exact H31)
                    ltac:(rewrite (AG1 19) by notin_list; exact H19) ltac:(rewrite (AG1 30) by notin_list; exact H30))
          as (r2 & m2 & S2 & RB2 & LC2 & Q22 & Q30 & AG2).
        exists r2, m2. split; [eapply msteps_trans; [exact S1 | exact S2] |].
        split; [exact RB2|]. split; [exact LC2|]. split; [exact Q22|].
        split; [rewrite (AG2 31), (AG1 31) by notin_list; exact H31|]. split; [rewrite (AG2 19), (AG1 19) by notin_list; exact H19|].
        split; [exact Q30|]. eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2].
      - eexists. exists m. split; [| split; [exact HRB | split; [| split; [| split; [| split; [|split]]]]]].
        + stepb_ft F_16a94 D_16a94 ltac:(condZ).                                                       (* [comment removed for export] *)
          stepLD F_16a98 D_16a98 (Z_to_le_bytes 4 w) (Z_to_bv 64 w) ltac:(rdn_addr (s - 108)%Z; exact Cw') ltac:(apply lez4; lia).   (* [comment removed for export] *)
          rewrite (v_lw_small w) by lia.
          stepb_tk F_16a9c D_16a9c ltac:(condZ).                                                       (* [comment removed for export] *)
          apply mst_refl.
        + eapply (LC_agree (fun r : reg => In r [23; 24; 25; 26; 27]%list) regs _ HL); [solve_regs_agree | lc_disjoint].
        + gres. exact H22. + gres. exact H31. + gres. exact H19. + gres. exact H30.
        + solve_regs_agree. }
    destruct PIX as (r1 & m1 & S1 & RB1 & LC1 & Q22 & Q31 & Q19 & Q30 & AG1). clear L2 L10 L8 L9 L18 L20 L21 L12 L13 L14 L16 L5 L6 L28 L29. lcd LC1.
    eexists. exists m1. split; [| split; [exact RB1 | split; [| split; [| split; [| split; [| split; [|split]]]]]]].
    - eapply msteps_trans; [exact S1|].
      sn F_16bfc D_16bfc. fixv (Z_to_bv 64 (j + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_16c00 D_16c00 ltac:(condZ).                                                         (* [comment removed for export] *)
      zva F_16c04 D_16c04 (Z_to_bv 64 (4 * (j + 1))).                                                (* [comment removed for export] *)
      zva F_16c08 D_16c08 (Z_to_bv 64 (2 * (j + 1))).                                                (* [comment removed for export] *)
      sn F_16c0c D_16c0c.                                                                            (* [comment removed for export] *)
      apply mst_refl.
    - eapply (LC_agree (fun r : reg => In r [19; 22; 23; 24; 25; 26; 27; 31]%list) r1 _ LC1); [solve_regs_agree | lc_disjoint].
    - gres. pin. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. exact Q30.
    - eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma col_loop : forall k regs m i j, RB m -> LC regs -> (0 <= i < h)%Z ->
    (Z.of_nat k = x2 - j)%Z -> (0 <= j)%Z ->
    getr regs 22 = Z_to_bv 64 j -> getr regs 31 = Z_to_bv 64 (4 * j) -> getr regs 19 = Z_to_bv 64 (2 * j) ->
    getr regs 30 = Z_to_bv 64 (datas + 4 * wpl * i) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16b98 : word) m rom) (mkst regs' (0x16d18 : word) m' rom)
      /\ RB m' /\ LC regs'
      /\ regs_agree (fun r : reg => In r [19; 22; 23; 24; 25; 26; 27; 31]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs m i j HRB HL Hi Hk Hj H22 H31 H19 H30;
      destruct (col_iter regs m i j HRB HL Hi ltac:(lia) H22 H31 H19 H30) as (r1 & m1 & S1 & RB1 & LC1 & Q22 & Q23 & Q31 & Q19 & Q30 & AG1);
      lcd LC1.
    - (* [comment removed for export] *)
      eexists. exists m1. split; [| split; [exact RB1 | split]].
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_16c10 D_16c10 ltac:(condZ).                                                       (* [comment removed for export] *)
        apply mst_refl.
      + eapply (LC_agree (fun r : reg => In r [19; 22; 23; 24; 25; 26; 27; 31]%list) r1 _ LC1); [solve_regs_agree | lc_disjoint].
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (S2 : exists r2, msteps SEGS (mkst r1 (0x16d14 : word) m1 rom) (mkst r2 (0x16b98 : word) m1 rom)
                              /\ regs_agree (fun r : reg => In r []%list) r1 r2).
      { eexists. split.
        - stepb_tk F_16c10 D_16c10 ltac:(condZ).                                                     (* [comment removed for export] *)
          apply mst_refl.
        - solve_regs_agree. }
      destruct S2 as (r2 & S2 & AG2).
      destruct (IH r2 m1 i (j + 1)%Z RB1 ltac:(eapply (LC_agree _ r1 _ LC1); [exact AG2 | lc_disjoint]) Hi ltac:(lia) ltac:(lia)
                  ltac:(rewrite (AG2 22) by notin_list; exact Q22) ltac:(rewrite (AG2 31) by notin_list; exact Q31)
                  ltac:(rewrite (AG2 19) by notin_list; exact Q19) ltac:(rewrite (AG2 30) by notin_list; exact Q30)) as (r3 & m3 & S3 & RB3 & LC3 & AG3).
      exists r3, m3. split; [| split; [exact RB3 | split; [exact LC3|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3].
  Qed.

  (* [comment removed for export] *)
  Lemma row_iter : forall regs m i, RB m -> LC regs -> (0 <= i < 2 ^ 31)%Z -> getr regs 11 = Z_to_bv 64 i ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16b48 : word) m rom) (mkst regs' (0x16d18 : word) m' rom)
      /\ RB m' /\ LC regs' /\ getr regs' 11 = Z_to_bv 64 i
      /\ regs_agree (fun r : reg => In r [19; 22; 23; 24; 25; 26; 27; 30; 31]%list) regs regs'.
  Proof.
    intros regs m i HRB HL Hi H11. lcd HL.
    pose proof wpl_bounds as (Hwpl1 & _).
    pose proof (RB_cell m (s - 112) 4 _ HRB ltac:(lia) ltac:(cbn; lia) Ch) as Ch'.
    pose proof (RB_cell m (s - 116) 4 _ HRB ltac:(lia) ltac:(cbn; lia) Cx1) as Cx1'.
    destruct (Z_lt_ge_dec i h) as [LT|GE].
    2:{ (* [comment removed for export] *)
      eexists. exists m. split; [| split; [exact HRB | split; [| split]]].
      - stepb_ft F_16a44 D_16a44 ltac:(condZ).                                                       (* [comment removed for export] *)
        stepLD F_16a48 D_16a48 (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(rdn_addr (s - 112)%Z; exact Ch') ltac:(apply lez4; lia).   (* [comment removed for export] *)
        rewrite (v_lw_small h) by lia.
        stepb_tk F_16a4c D_16a4c ltac:(condZ).                                                       (* [comment removed for export] *)
        apply mst_refl.
      - eapply (LC_agree (fun r : reg => In r [19; 22; 23; 24; 25; 26; 27; 30; 31]%list) regs _ HL); [solve_regs_agree | lc_disjoint].
      - gres. exact H11.
      - solve_regs_agree. }
    pose proof (iwpl_small i ltac:(lia)) as Hiw. pose proof (row_in_raster i ltac:(lia)) as Hrow.
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x16b48 : word) m rom) (mkst r1 (0x16b8c : word) m rom)
                            /\ getr r1 30 = Z_to_bv 64 (datas + 4 * wpl * i) /\ getr r1 22 = Z_to_bv 64 x1
                            /\ regs_agree (fun r : reg => In r [19; 22; 30; 31]%list) regs r1).
    { eexists. split.
      - stepb_ft F_16a44 D_16a44 ltac:(condZ).                                                       (* [comment removed for export] *)
        stepLD F_16a48 D_16a48 (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(rdn_addr (s - 112)%Z; exact Ch') ltac:(apply lez4; lia).   (* [comment removed for export] *)
        rewrite (v_lw_small h) by lia.
        stepb_ft F_16a4c D_16a4c ltac:(condZ).                                                       (* [comment removed for export] *)
        zva F_16a50 D_16a50 (Z_to_bv 64 (i * wpl)).                                                  (* [comment removed for export] *)
        sn F_16a54 D_16a54. fixv (Z_to_bv 64 (i * wpl)) ltac:(apply zbv_mulw_small; lia).          (* [comment removed for export] *)
        stepb_ft F_16a58 D_16a58 ltac:(condZ).                                                       (* [comment removed for export] *)
        sn F_16a5c D_16a5c. fixv (Z_to_bv 64 (i * wpl)) ltac:(rewrite v_addiw_Z, Z.add_0_r, sw32_small by lia; reflexivity).   (* [comment removed for export] *)
        zvs F_16a60 D_16a60 (Z_to_bv 64 (4 * (i * wpl))).                                           (* [comment removed for export] *)
        zva F_16a64 D_16a64 (Z_to_bv 64 (datas + 4 * wpl * i)).                                      (* [comment removed for export] *)
        seqz_nz F_16a68 D_16a68.                                                                      (* [comment removed for export] *)
        stepb_ft F_16a6c D_16a6c ltac:(condZ).                                                       (* [comment removed for export] *)
        sn F_16a70 D_16a70. fixv (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).                           (* [comment removed for export] *)
        sn F_16a74 D_16a74. fixv (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).                             (* [comment removed for export] *)
        litv F_16a78 D_16a78 (Z_to_bv 64 0).                                                         (* [comment removed for export] *)
        litv F_16a7c D_16a7c (Z_to_bv 64 1).                                                         (* [comment removed for export] *)
        stepb_ft F_16a80 D_16a80 ltac:(condZ).                                                       (* [comment removed for export] *)
        stepLD F_16a84 D_16a84 (Z_to_le_bytes 4 x1) (Z_to_bv 64 x1) ltac:(rdn_addr (s - 116)%Z; exact Cx1') ltac:(apply lez4; lia). (* [comment removed for export] *)
        rewrite (v_lw_small x1) by lia.
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q30 & Q22 & AG1).
    assert (HL1 : LC r1) by (eapply (LC_agree _ regs _ HL); [exact AG1 | lc_disjoint]).
    clear L2 L10 L8 L9 L18 L20 L21 L12 L13 L14 L16 L5 L6 L28 L29. lcd HL1.
    destruct (Z_lt_ge_dec x2 x1) as [EMP|NE].
    { (* [comment removed for export] *)
      eexists. exists m. split; [| split; [exact HRB | split; [exact HL1 |split]]].
      - eapply msteps_trans; [exact S1|].
        stepb_tk F_16a88 D_16a88 ltac:(condZ).                                                       (* [comment removed for export] *)
        apply mst_refl.
      - rewrite (AG1 11) by notin_list. exact H11.
      - regs_agree_weaken AG1. }
    (* [comment removed for export] *)
    assert (S2 : exists r2, msteps SEGS (mkst r1 (0x16b8c : word) m rom) (mkst r2 (0x16b98 : word) m rom)
                            /\ getr r2 31 = Z_to_bv 64 (4 * x1) /\ getr r2 19 = Z_to_bv 64 (2 * x1)
                            /\ regs_agree (fun r : reg => In r [19; 31]%list) r1 r2).
    { eexists. split.
      - stepb_ft F_16a88 D_16a88 ltac:(condZ).                                                       (* [comment removed for export] *)
        zvs F_16a8c D_16a8c (Z_to_bv 64 (4 * x1)).                                                   (* [comment removed for export] *)
        stepiv F_16a90 D_16a90 (Z_to_bv 64 (2 * x1)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 1)%Z with 2%Z; lia).  (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S2 as (r2 & S2 & P31 & P19 & AG2).
    destruct (col_loop (Z.to_nat (x2 - x1)) r2 m i x1 HRB ltac:(eapply (LC_agree _ r1 _ HL1); [exact AG2 | lc_disjoint]) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(rewrite (AG2 22) by notin_list; exact Q22) P31 P19 ltac:(rewrite (AG2 30) by notin_list; exact Q30))
      as (r3 & m3 & S3 & RB3 & LC3 & AG3).
    exists r3, m3. split; [| split; [exact RB3 | split; [exact LC3 | split]]].
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
    - rewrite (AG3 11), (AG2 11), (AG1 11) by notin_list. exact H11.
    - eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3].
  Qed.

  (* [comment removed for export] *)
  Lemma row_loop : forall k regs m i, RB m -> LC regs -> (Z.of_nat k = y2 - i)%Z -> (0 <= i)%Z ->
    getr regs 11 = Z_to_bv 64 i ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16b48 : word) m rom) (mkst regs' (0x16d28 : word) m' rom)
      /\ RB m' /\ LC regs'
      /\ regs_agree (fun r : reg => In r [11; 19; 22; 23; 24; 25; 26; 27; 30; 31]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs m i HRB HL Hk Hi H11;
      destruct (row_iter regs m i HRB HL ltac:(lia) H11) as (r1 & m1 & S1 & RB1 & LC1 & Q11 & AG1);
      lcd LC1.
    - (* [comment removed for export] *)
      eexists. exists m1. split; [| split; [exact RB1 | split]].
      + eapply msteps_trans; [exact S1|].
        sn F_16c14 D_16c14. fixv (Z_to_bv 64 (i + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; reflexivity).   (* [comment removed for export] *)
        stepb_ft F_16c18 D_16c18 ltac:(condZ).                                                       (* [comment removed for export] *)
        sn F_16c1c D_16c1c.                                                                          (* [comment removed for export] *)
        stepb_ft F_16c20 D_16c20 ltac:(condZ).                                                       (* [comment removed for export] *)
        apply mst_refl.
      + eapply (LC_agree (fun r : reg => In r [11; 19; 22; 23; 24; 25; 26; 27; 30; 31]%list) r1 _ LC1); [solve_regs_agree | lc_disjoint].
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (S2 : exists r2, msteps SEGS (mkst r1 (0x16d18 : word) m1 rom) (mkst r2 (0x16b48 : word) m1 rom)
                              /\ getr r2 11 = Z_to_bv 64 (i + 1) /\ regs_agree (fun r : reg => In r [11; 30]%list) r1 r2).
      { eexists. split.
        - sn F_16c14 D_16c14. fixv (Z_to_bv 64 (i + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; reflexivity). (* [comment removed for export] *)
          stepb_ft F_16c18 D_16c18 ltac:(condZ).                                                     (* [comment removed for export] *)
          sn F_16c1c D_16c1c.                                                                        (* [comment removed for export] *)
          stepb_tk F_16c20 D_16c20 ltac:(condZ).                                                     (* [comment removed for export] *)
          apply mst_refl.
        - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
      destruct S2 as (r2 & S2 & P11 & AG2).
      destruct (IH r2 m1 (i + 1)%Z RB1 ltac:(eapply (LC_agree _ r1 _ LC1); [exact AG2 | lc_disjoint]) ltac:(lia) ltac:(lia) P11)
        as (r3 & m3 & S3 & RB3 & LC3 & AG3).
      exists r3, m3. split; [| split; [exact RB3 | split; [exact LC3|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3].
  Qed.

  Definition loop_clob : list (bv 5) := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

  (* [comment removed for export] *)
  Theorem sel_loop : forall regs m, RB m ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 wpl -> getr regs 8 = Z_to_bv 64 sindex ->
    getr regs 9 = Z_to_bv 64 d -> getr regs 18 = Z_to_bv 64 datas -> getr regs 20 = Z_to_bv 64 x2 -> getr regs 21 = Z_to_bv 64 y2 ->
    exists regs' m',
      msteps SEGS (mkst regs (0x16b14 : word) m rom) (mkst regs' (0x16d64 : word) m' rom)
      /\ RB m' /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r : reg => In r loop_clob) regs regs'.
  Proof.
    intros regs m HRB H2 H10 H8 H9 H18 H20 H21.
    pose proof wpl_bounds as (Hwpl1 & _).
    pose proof (RB_cell m (s - 120) 4 _ HRB ltac:(lia) ltac:(cbn; lia) Cy1) as Cy1'.
    destruct (Z_lt_ge_dec y2 y1) as [EMP|NE].
    { (* [comment removed for export] *)
      eexists. exists m. split; [| split; [exact HRB | split; [| split]]].
      - stepLD F_16a10 D_16a10 (Z_to_le_bytes 4 y1) (Z_to_bv 64 y1) ltac:(rdn_addr (s - 120)%Z; exact Cy1') ltac:(apply lez4; lia). (* [comment removed for export] *)
        rewrite (v_lw_small y1) by lia.
        stepb_tk F_16a14 D_16a14 ltac:(condZ).                                                       (* [comment removed for export] *)
        sn F_16c24 D_16c24. sn F_16c28 D_16c28.                                                      (* [comment removed for export] *)
        apply mst_refl.
      - gres. exact H2.
      - gres. reflexivity.
      - unfold loop_clob. solve_regs_agree. }
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x16b14 : word) m rom) (mkst r1 (0x16b48 : word) m rom)
                            /\ LC r1 /\ getr r1 11 = Z_to_bv 64 y1
                            /\ regs_agree (fun r : reg => In r loop_clob) regs r1).
    { eexists. split; [|split].
      - stepLD F_16a10 D_16a10 (Z_to_le_bytes 4 y1) (Z_to_bv 64 y1) ltac:(rdn_addr (s - 120)%Z; exact Cy1') ltac:(apply lez4; lia). (* [comment removed for export] *)
        rewrite (v_lw_small y1) by lia.
        stepb_ft F_16a14 D_16a14 ltac:(condZ).                                                       (* [comment removed for export] *)
        sn F_16a18 D_16a18. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).                               (* [comment removed for export] *)
        sn F_16a1c D_16a1c. sn F_16a20 D_16a20. sn F_16a24 D_16a24. sn F_16a28 D_16a28.
        sn F_16a2c D_16a2c. sn F_16a30 D_16a30. sn F_16a34 D_16a34. sn F_16a38 D_16a38.
        sn F_16a3c D_16a3c. sn F_16a40 D_16a40.
        apply mst_refl.
      - unfold LC. repeat split; gres; pin; reflexivity.
      - repeat split; gres; pin; try reflexivity. unfold loop_clob. solve_regs_agree. }
    destruct S1 as (r1 & S1 & LC1 & Q11 & AG1).
    destruct (row_loop (Z.to_nat (y2 - y1)) r1 m y1 HRB LC1 ltac:(lia) ltac:(lia) Q11) as (r2 & m2 & S2 & RB2 & LC2 & AG2).
    pose proof LC2 as (L2 & _).
    eexists. exists m2. split; [| split; [exact RB2 | split; [| split]]].
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
      sn F_16c24 D_16c24. sn F_16c28 D_16c28.                                                        (* [comment removed for export] *)
      apply mst_refl.
    - gres. exact L2.
    - gres. reflexivity.
    - eapply regs_agree_trans; [exact AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. unfold loop_clob. solve_regs_agree.
  Qed.

End SelLoop.
