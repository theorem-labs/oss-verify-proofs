(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge FP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrMem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.TUX Require Import DgWalkX_u5 G3PureX_u5 G3LemX_u5 G3WalkX_u5.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma u8arr_rw : forall m A bs, u8arr rsegs m A bs -> rw_cells rsegs m A [CB (length bs) bs].
Proof.
  intros m A bs [Hb Hw]. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* [comment removed for export] *)
Ltac fix_lit8 := lazymatch goal with |- context [write_to_mem _ _ (Z_to_le_bytes 8 ?n)] => change (Z_to_le_bytes 8 n) with (le8 (Z_to_bv 64 n)) end.
Ltac lstep := step; fix_lit8; mem_after_store.

(* [comment removed for export] *)
Lemma fabs_pos : forall a : word, feq_d a (Z_to_bv 64 0) = false -> (1 <= bv_unsigned (fabs_d a) < 2 ^ 63)%Z.
Proof.
  intros a H. unfold fabs_d. pose proof (bv_unsigned_in_range _ a) as Ra. unfold bv_modulus in Ra. cbn -[Z.pow] in Ra.
  assert (Hl : Z.land (bv_unsigned a) (Z.ones 63) = (bv_unsigned a mod 2 ^ 63)%Z) by (apply Z.land_ones; lia).
  rewrite Hl. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned a) (2 ^ 63)); lia).
  pose proof (Z.mod_pos_bound (bv_unsigned a) (2 ^ 63) ltac:(lia)) as Rm. split; [|lia].
  destruct (Z.eq_dec (bv_unsigned a mod 2 ^ 63) 0) as [E|E]; [|lia]. exfalso.
  assert (Ha : bv_unsigned a = 0%Z \/ bv_unsigned a = (2 ^ 63)%Z).
  { pose proof (Z.div_mod (bv_unsigned a) (2 ^ 63) ltac:(lia)) as D. rewrite E in D.
    assert (Q : (0 <= bv_unsigned a / 2 ^ 63 < 2)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). nia. }
  assert (Ea : a = Z_to_bv 64 (bv_unsigned a)) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct Ha as [Ha|Ha]; rewrite Ea, Ha in H; vm_compute in H; discriminate H.
Qed.
Lemma cb4_c4 : forall m A bs, rw_cells rsegs m A [CB 4 bs] -> exists w, rw_cells rsegs m A [C4 w].
Proof.
  intros m A bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hn _].
  destruct bs as [|b0 [|b1 [|b2 [|b3 [|? ?]]]]]; cbn in Hn; try lia.
  destruct (le4_of_bytes b0 b1 b2 b3) as (w & Hw4). exists w. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite Hw4. exact Hb.
  - exact Hw.
Qed.
Ltac peel H := lazymatch type of H with rw_cells _ ?m ?A (?c :: ?rest) =>
  let H1 := fresh "PC" in
  change (c :: rest) with ([c] ++ rest) in H; apply (proj1 (rw_cells_app m A [c] rest)) in H; destruct H as [H1 H]; cbn [cells_size csize Nat.add] in H end.
Lemma rw_glue : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 -> B = (A + Z.of_nat (cells_size cs1))%Z ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 ->. apply rw_cells_app. split; assumption. Qed.
Ltac exs := repeat (lazymatch goal with |- ex _ => eexists end).

Section WH.
(* [comment removed for export] *)
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable SP : Z.
Variables dp SK : Z.
Variable m0 : word -> option byte.
Definition SPB : Z := (SP - 144)%Z.
Hypothesis SPR : (2 ^ 41 + 9344 <= SP /\ SP <= 2 ^ 47)%Z.
Hypothesis DPR : (0 <= dp < 2 ^ 64)%Z.
Hypothesis SKR : (0 <= SK < 2 ^ 64)%Z.
Hypothesis SPA : (SP mod 16 = 0)%Z.
Definition DT_W : list (Z * Z) := [(SP - 9344, SP)]%Z.

(* [comment removed for export] *)
Definition FRZ (ja : list byte) (fs0w : word) : list cell := [CB 112 ja; C8 fs0w; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition FRG (j0 dig j1 : list byte) (K len : Z) (fs0w : word) : list cell :=
  [CB 4 j0; CB 22 dig; CB 78 j1; C4 (Z_to_bv 64 K); C4 (Z_to_bv 64 len); C8 fs0w; C8 s1; C8 s0; C8 ra].

Definition wpZ : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' fs0w (ja : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 SPB) gp tp t0' t1' t2' (Z_to_bv 64 SK) s1 (Z_to_bv 64 dp) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0x456f4) fc' None m' (seg_rom rsegs)
    /\ frm0 fc' /\ rw_cells rsegs m' SPB (FRZ ja fs0w) /\ stk rsegs m' (SP - 9344) SPB
    /\ munch DT_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'.
Definition wpG : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (res len K : Z) fs0w (j0 dig j1 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x45760) (Z_to_bv 64 SPB) gp tp t0' t1' t2' (Z_to_bv 64 SK) (Z_to_bv 64 dp) (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0x45760) fc' None m' (seg_rom rsegs)
    /\ (res = 0 \/ res = 1)%Z /\ (1 <= len <= 21)%Z /\ (-343 <= K <= 309)%Z
    /\ frm0 fc' /\ rw_cells rsegs m' SPB (FRG j0 dig j1 K len fs0w) /\ stk rsegs m' (SP - 9344) SPB
    /\ munch DT_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'.
Definition wpost (ms : machine_state) : Prop := wpZ ms \/ wpG ms.

(* [comment removed for export] *)
Lemma wh_true : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (m : word -> option byte),
  frm0 fc -> stk rsegs m (SP - 9344) SP -> mem_inv rsegs m -> m = m0 ->
  evt rsegs wpost (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dp) (Z_to_bv 64 SK) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x456d0) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros FRM ST MI ->.
  pose proof (munch_refl DT_W m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold DT_W in MU.
  carve_frame 144%nat ST.
  zstep. zstep.
  do 3 zstep.
  do 3 zstep.
  zstep. destruct (feq_d (reg_get F 10) (Z_to_bv 64 0)) eqn:FQ; cbn [bword] in *.
  - (* [comment removed for export] *)
    if_cases K1; [vm_compute in K1; discriminate|].
    replace (Z_to_bv 64 (SP + -144)) with (Z_to_bv 64 SPB) by (unfold SPB; f_equal; lia).
    apply evt_done. left. unfold wpZ. exs. split; [reflexivity|].
    split; [eassumption|]. split; [unfold FRZ, SPB; replace (SP - 144)%Z with (SP + -144)%Z by lia; exact FR|].
    split; [unfold SPB; replace (SP - 144)%Z with (SP + -144)%Z by lia; exact ST|].
    split; [unfold DT_W; exact MU|]. split; [exact WM | exact MI].
  - if_cases K1; [|vm_compute in K1; discriminate].
    do 2 zstep. step.
    do 5 zstep.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB rsegs _ (SP + -144) [] 108 _ _ [4; 22; 78; 4]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    peel FR. peel FR. peel FR. peel FR. peel FR.
    replace (SP + -144 + Z.of_nat 4)%Z with (SP + -140)%Z in PC0 by lia.
    replace (SP + -144 + Z.of_nat 4 + Z.of_nat 22)%Z with (SP + -118)%Z in PC1 by lia.
    replace (SP + -144 + Z.of_nat 4 + Z.of_nat 22 + Z.of_nat 78)%Z with (SP + -40)%Z in PC2 by lia.
    replace (SP + -144 + Z.of_nat 4 + Z.of_nat 22 + Z.of_nat 78 + Z.of_nat 4)%Z with (SP + -36)%Z in PC3 by lia.
    replace (SP + -144 + Z.of_nat 4 + Z.of_nat 22 + Z.of_nat 78 + Z.of_nat 4 + Z.of_nat 4)%Z with (SP + -32)%Z in FR by lia.
    destruct (cb4_c4 _ _ _ PC2) as (kj & KC). clear PC2.
    assert (L22 : length (match PC0 with _ => ltac:(lazymatch type of PC0 with rw_cells _ _ _ [CB _ ?l] => exact l end) end) = 22%nat) by (destruct PC0 as [[W _] _]; cbn in W; tauto).
    apply u8arr_of_rw_cells in PC0 as BU0.
    destruct (stk_split rsegs _ (SP - 9344) (SP + -304) (SP + -144) ST ltac:(lia)) as [STlo SThi]. clear ST.
    pose proof (fabs_pos _ FQ) as Hb.
    assert (USP : bv_unsigned (Z_to_bv 64 (SP + -144)) = (SP + -144)%Z) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (g3_spec (Z_to_bv 64 0x45760) (Z_to_bv 64 (SP + -144)) gp tp (Z_to_bv 64 SK) (Z_to_bv 64 dp) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ (SP + -140) (SP + -36) (SP + -40)).
      all: unfold GSP; rewrite ?USP.
      all: try lia.
      - reflexivity.
      - rewrite freg_get_other by reflexivity. rewrite freg_get_same by reflexivity. exact Hb.
      - eassumption.
      - replace (SP + -144 - 160)%Z with (SP + -304)%Z by lia. exact SThi.
      - exact BU0.
      - exact L22.
      - exact PC3.
      - exact KC.
      - eassumption.
      - reflexivity. }
    cbv beta. intros ms' P. unfold g3_post, G3_W, GSP in P. rewrite USP in P.
    destruct P as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & res & len & K & bs2 & -> & MUc & WMc & MI2 & FRM2 & ST2 & BU2 & BL2 & _ & LE2 & Hlen & KC2 & HK & Hres).
    replace (ret_pc (Z_to_bv 64 0x45760)) with (Z_to_bv 64 0x45760) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    clear BU0 L22 KC PC3 SThi PC0.
    change G3PureX_u5.rsegs with rsegs in *.
    transport_after_call rsegs m m2 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    pose proof (u8arr_rw _ _ _ BU2) as DG. rewrite BL2 in DG.
    lazymatch goal with
    | H0 : rw_cells _ m2 (SP + -144) [CB 4 ?j0], H1 : rw_cells _ m2 (SP + -118) [CB 78 ?x], H2 : rw_cells _ m2 (SP + -32) ?cs8 |- _ =>
      pose proof (rw_glue _ _ _ _ _ H0 (rw_glue _ _ _ _ _ DG (rw_glue _ _ _ _ _ H1 (rw_glue _ _ _ _ _ KC2 (rw_glue _ _ _ _ _ LE2 H2 ltac:(cbn; lia))
                   ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as FRG0;
      clear H0 H1 H2 DG KC2 LE2
    end.
    cbn [app] in FRG0.
    assert (ST3 : stk rsegs m2 (SP - 9344) SPB)
      by (unfold SPB; apply (stk_merge rsegs m2 (SP - 9344) (SP + -304) (SP - 144)); [exact STlo | replace (SP - 144)%Z with (SP + -144)%Z by lia; replace (SP + -304)%Z with (SP + -144 - 160)%Z by lia; exact ST2 | lia]).
    replace (Z_to_bv 64 (SP + -144)) with (Z_to_bv 64 SPB) by (unfold SPB; f_equal; lia).
    apply evt_done. right. unfold wpG. exs. split; [reflexivity|].
    split; [exact Hres|]. split; [exact Hlen|]. split; [exact HK|]. split; [exact FRM2|].
    split; [unfold FRG, SPB; replace (SP - 144)%Z with (SP + -144)%Z by lia; exact FRG0|].
    split; [exact ST3|]. split; [unfold DT_W; exact MU|]. split; [exact WM | exact MI2].
Qed.
End WH.
