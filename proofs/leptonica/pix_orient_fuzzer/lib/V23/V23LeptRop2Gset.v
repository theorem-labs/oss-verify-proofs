(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecW LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUb V23LeptRop2Segs.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23_code_rasteropLow_80000_81000.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition RG_P0 : word := 0x7ff84.
Definition RG_Q1 : word := 0x80140.
Definition RG_Q2 : word := 0x801a4.
Definition RG_Q3 : word := 0x802ac.
Definition RG_Q4 : word := 0x806dc.
Definition RG_Q5 : word := 0x80850.
Definition RG_Q6 : word := 0x80a14.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma swrap32_eq : forall t r k : Z, (- 2 ^ 31 <= r < 2 ^ 31)%Z -> t = (r + k * 2 ^ 32)%Z -> bv_swrap 32 t = r.
Proof. intros t r k Hr ->. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia. Qed.

Lemma zaddw_s : forall a b : Z, (- 2 ^ 31 <= a + b < 2 ^ 31)%Z -> v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b H. unfold v_addw. rewrite !u_Z2bv_mod. f_equal.
  apply swrap32_eq with (k := (- 2 ^ 32 * (a / 2 ^ 64) - 2 ^ 32 * (b / 2 ^ 64))%Z); lia.
Qed.

Lemma zsubw_s : forall a b : Z, (- 2 ^ 31 <= a - b < 2 ^ 31)%Z -> v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b H. unfold v_subw. rewrite !u_Z2bv_mod. f_equal.
  apply swrap32_eq with (k := (- 2 ^ 32 * (a / 2 ^ 64) + 2 ^ 32 * (b / 2 ^ 64))%Z); lia.
Qed.

Lemma zsrlw5 : forall a : Z, (0 <= a < 2 ^ 31)%Z -> v_srlw (Z_to_bv 64 a) (Z_to_bv 64 5) = Z_to_bv 64 (a / 32).
Proof.
  intros a H. unfold v_srlw. rewrite !u_Z2bv_mod. f_equal.
  rewrite Z.shiftr_div_pow2 by lia. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  apply swrap32_eq with (k := 0%Z); [| rewrite (Z.mod_small a) by lia; rewrite (Z.mod_small 5) by lia]; lia.
Qed.

Lemma swrap32_mod : forall t r : Z, (- 2 ^ 31 <= r < 2 ^ 31)%Z -> (t mod 2 ^ 32 = r mod 2 ^ 32)%Z -> bv_swrap 32 t = r.
Proof. intros t r Hr Ht. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia. Qed.

Lemma zmulw_s : forall a b : Z, (- 2 ^ 31 <= a * b < 2 ^ 31)%Z -> v_mulw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b H. unfold v_mulw. rewrite !u_Z2bv_mod. f_equal. apply swrap32_mod; [exact H |].
  assert (Ea : ((a mod 2 ^ 64) mod 2 ^ 32 = a mod 2 ^ 32)%Z) by lia.
  assert (Eb : ((b mod 2 ^ 64) mod 2 ^ 32 = b mod 2 ^ 32)%Z) by lia.
  rewrite (Z.mul_mod (a mod 2 ^ 64) (b mod 2 ^ 64) (2 ^ 32)) by lia. rewrite Ea, Eb.
  rewrite <- (Z.mul_mod a b (2 ^ 32)) by lia. reflexivity.
Qed.

Lemma zsraw5 : forall a : Z, (0 <= a < 2 ^ 31)%Z -> v_sraw (Z_to_bv 64 a) (Z_to_bv 64 5) = Z_to_bv 64 (a / 32).
Proof.
  intros a H. unfold v_sraw. rewrite !u_Z2bv_mod. f_equal.
  rewrite (swrap32_eq (a mod 2 ^ 64) a 0) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite !(Z.mod_small 5) by lia.
  apply swrap32_eq with (k := 0%Z); lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma zand31 : forall x : Z, (0 <= x < 2 ^ 64)%Z -> v_and (Z_to_bv 64 x) (Z_to_bv 64 31) = Z_to_bv 64 (x mod 32).
Proof.
  intros x Hx. unfold v_and. rewrite !u_Z2bv by lia.
  change 31%Z with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma zbv_xor : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lxor a b).
Proof. intros a b Ha Hb. unfold v_xor. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma g_hang_range : forall x : Z, (0 <= g_hang x < 32)%Z.
Proof. intros x. pose proof (Z.mod_pos_bound x 32 ltac:(lia)). unfold g_hang. destruct (Z.eqb_spec (x mod 32) 0); lia. Qed.

Lemma g_sls_range : forall DX SX : Z, (-32 < g_sls DX SX < 64)%Z.
Proof.
  intros DX SX. pose proof (g_hang_range DX). pose proof (g_hang_range SX). unfold g_sls.
  destruct (Z.ltb_spec (g_hang SX) (g_hang DX)); lia.
Qed.

Lemma g_sls_pos : forall DX SX : Z, (1 <= g_sls DX SX <= 32)%Z.
Proof.
  intros DX SX. pose proof (g_hang_range DX). pose proof (g_hang_range SX). unfold g_sls.
  destruct (Z.ltb_spec (g_hang SX) (g_hang DX)); lia.
Qed.

Definition zl32 : list Z := map Z.of_nat (seq 0 32).

Lemma zl32_in : forall a : Z, (0 <= a < 32)%Z -> In a zl32.
Proof. intros a Ha. unfold zl32. apply in_map_iff. exists (Z.to_nat a). split; [lia | apply in_seq; lia]. Qed.

Lemma fin2_w : forall L R : Z -> Z -> word,
  forallb (fun a => forallb (fun b => (bv_unsigned (L a b) =? bv_unsigned (R a b))%Z) zl32) zl32 = true ->
  forall a b : Z, (0 <= a < 32)%Z -> (0 <= b < 32)%Z -> L a b = R a b.
Proof.
  intros L R H a b Ha Hb. rewrite forallb_forall in H. specialize (H a (zl32_in a Ha)).
  rewrite forallb_forall in H. specialize (H b (zl32_in b Hb)). apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma fin2_b : forall L R : Z -> Z -> bool,
  forallb (fun a => forallb (fun b => Bool.eqb (L a b) (R a b)) zl32) zl32 = true ->
  forall a b : Z, (0 <= a < 32)%Z -> (0 <= b < 32)%Z -> L a b = R a b.
Proof.
  intros L R H a b Ha Hb. rewrite forallb_forall in H. specialize (H a (zl32_in a Ha)).
  rewrite forallb_forall in H. specialize (H b (zl32_in b Hb)). apply Bool.eqb_prop. exact H.
Qed.

Ltac gref2 X Y :=
  unfold g_sls, g_hang, RG_MASKS;
  generalize (Z.mod_pos_bound X 32 ltac:(lia)) (Z.mod_pos_bound Y 32 ltac:(lia));
  generalize (X mod 32) as a; generalize (Y mod 32) as b; intros b a Ha Hb; revert a b Ha Hb;
  first [ refine (fin2_w _ _ _) | refine (fin2_b _ _ _) ]; vm_compute; reflexivity.

Ltac glit x := lazymatch x with Z0 => idtac | Zpos _ => idtac end.

Ltac gz1 :=
  first [ rewrite Z.add_0_r | rewrite zbv_add | rewrite zbv_sub | rewrite zbv_mul | rewrite zbv_addi | rewrite zbv_mulw_small by lia | rewrite zmulw_s by lia
        | rewrite zaddw_s by lia | rewrite zsubw_s by lia | rewrite zsrlw5 by lia | rewrite zsraw5 by lia
        | rewrite v_sltu_Z by lia | rewrite v_slt_Z by lia | rewrite zand31 by lia | rewrite zbv_xor by lia
        | rewrite zbv_or by lia
        | match goal with |- context [(?a <? ?b)%Z] =>
            first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ] end
        | match goal with |- context [Z.lxor ?x ?y] =>
            glit x; glit y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v end
        | match goal with |- context [Z.lor ?x ?y] =>
            glit x; glit y; let v := eval vm_compute in (Z.lor x y) in change (Z.lor x y) with v end
        | match goal with |- context [alu64 ALU_ADD ?a ?b] => change (alu64 ALU_ADD a b) with (v_add a b) end
        | match goal with |- context [alu64 ALU_SUB ?a ?b] => change (alu64 ALU_SUB a b) with (v_sub a b) end
        | match goal with |- context [alu64 ALU_SLTU ?a ?b] => change (alu64 ALU_SLTU a b) with (v_sltu a b) end
        | match goal with |- context [alu64 ALU_SLT ?a ?b] => change (alu64 ALU_SLT a b) with (v_slt a b) end
        | match goal with |- context [alu64 ALU_XOR ?a ?b] => change (alu64 ALU_XOR a b) with (v_xor a b) end
        | match goal with |- context [alu64 ALU_AND ?a ?b] => change (alu64 ALU_AND a b) with (v_and a b) end
        | match goal with |- context [alu64 ALU_OR ?a ?b] => change (alu64 ALU_OR a b) with (v_or a b) end
        | match goal with |- context [mul_div M_MUL ?a ?b] => change (mul_div M_MUL a b) with (v_mul a b) end ].

Ltac gz :=
  rewrite ?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor, ?alu_sra, ?alu_srl, ?alu_sll,
          ?w_addw, ?w_subw, ?w_srlw, ?w_sraw, ?w_sllw, ?w_mulw, ?m_mul;
  repeat gz1.

Ltac gsc := lazymatch goal with
  | |- ex _ => idtac
  | _ => (try gz); try first [ ex_br | (rewrite ?u_Z2bv by lia; lia) ]
  end.

Ltac gvc := unfold g_f6, g_f7, g_f3 in *;
  repeat match goal with |- context [(?x <? ?y)%Z] => destruct (x <? y) end; gz;
  first [ (f_equal; lia) | reflexivity ].

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma rgs_RF : forall datad nd datas ns DX SX DW dy sy dh dwpl swpl : Z,
  (datad mod 4 = 0)%Z -> (datas mod 4 = 0)%Z -> (0 <= DX)%Z -> (0 <= SX)%Z -> (1 <= DW)%Z -> (DX + DW <= 32 * dwpl)%Z ->
  g_fw DX = true -> (g_smax DX SX DW <= swpl - 1)%Z ->
  (forall c nw i', 0 <= c -> 0 <= nw -> c + nw <= dwpl -> 0 <= i' < dh ->
      datad <= datad + 4 * (dy * dwpl) + 4 * c + 4 * dwpl * i' /\ datad + 4 * (dy * dwpl) + 4 * c + 4 * dwpl * i' + 4 * nw <= datad + nd)%Z ->
  (forall c nw i', 0 <= c -> 0 <= nw -> c + nw <= swpl -> 0 <= i' < dh ->
      datas <= datas + 4 * (sy * swpl) + 4 * c + 4 * swpl * i' /\ datas + 4 * (sy * swpl) + 4 * c + 4 * swpl * i' + 4 * nw <= datas + ns)%Z ->
  ((datas + 4 * (sy * swpl) + 4 * (SX / 32)) mod 4 = 0 /\ (datad + 4 * (dy * dwpl) + 4 * (DX / 32)) mod 4 = 0)%Z /\
  (forall i, 0 <= i < dh ->
     datad <= datad + 4 * (dy * dwpl) + 4 * (DX / 32) + 4 * dwpl * i /\
     datad + 4 * (dy * dwpl) + 4 * (DX / 32) + 4 * dwpl * i + 4 <= datad + nd /\
     datas <= datas + 4 * (sy * swpl) + 4 * (SX / 32) + 4 * swpl * i /\
     datas + 4 * (sy * swpl) + 4 * (SX / 32) + 4 * swpl * i + 4 <= datas + ns /\
     (g_f6 DX SX = true -> g_f7 SX DW = false -> datas + 4 * (sy * swpl) + 4 * (SX / 32) + 4 * swpl * i + 8 <= datas + ns))%Z.
Proof.
  intros datad nd datas ns DX SX DW dy sy dh dwpl swpl Hd4 Hs4 HDX HSX HDW Hw Hfw Hsm RD RS.
  pose proof (g_col1 DX DW dwpl HDX HDW Hw) as C1. pose proof (g_smax_1 DX SX DW swpl Hsm Hfw) as S1.
  assert (S1' : (SX / 32 + 1 <= swpl)%Z) by (destruct (g_f6 DX SX && negb (g_f7 SX DW)); lia).
  split; [split; lia |]. intros i Hi.
  destruct (RD (DX / 32)%Z 1%Z i ltac:(lia) ltac:(lia) ltac:(lia) Hi) as [D1 D2].
  destruct (RS (SX / 32)%Z 1%Z i ltac:(lia) ltac:(lia) ltac:(lia) Hi) as [T1 T2].
  repeat split; try lia. intros E6 E7. rewrite E6, E7 in S1. cbn in S1.
  destruct (RS (SX / 32)%Z 2%Z i ltac:(lia) ltac:(lia) ltac:(lia) Hi) as [_ T3]. lia.
Qed.

Lemma rgs_RW : forall datad nd datas ns DX SX DW dy sy dh dwpl swpl : Z,
  (datad mod 4 = 0)%Z -> (datas mod 4 = 0)%Z -> (0 <= DX)%Z -> (0 <= SX)%Z -> (1 <= DW)%Z -> (DX + DW <= 32 * dwpl)%Z ->
  (32 <= DW - g_hang DX)%Z -> (g_smax DX SX DW <= swpl - 1)%Z ->
  (forall c nw i', 0 <= c -> 0 <= nw -> c + nw <= dwpl -> 0 <= i' < dh ->
      datad <= datad + 4 * (dy * dwpl) + 4 * c + 4 * dwpl * i' /\ datad + 4 * (dy * dwpl) + 4 * c + 4 * dwpl * i' + 4 * nw <= datad + nd)%Z ->
  (forall c nw i', 0 <= c -> 0 <= nw -> c + nw <= swpl -> 0 <= i' < dh ->
      datas <= datas + 4 * (sy * swpl) + 4 * c + 4 * swpl * i' /\ datas + 4 * (sy * swpl) + 4 * c + 4 * swpl * i' + 4 * nw <= datas + ns)%Z ->
  (1 <= (DW - g_hang DX) / 32)%Z /\
  ((datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32)) mod 4 = 0 /\ (datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32)) mod 4 = 0)%Z /\
  (forall i, 0 <= i < dh ->
     datad <= datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * dwpl * i /\
     datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * dwpl * i + 4 * ((DW - g_hang DX) / 32) <= datad + nd /\
     datas <= datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * swpl * i /\
     datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * swpl * i + 4 * ((DW - g_hang DX) / 32) + 4 <= datas + ns)%Z.
Proof.
  intros datad nd datas ns DX SX DW dy sy dh dwpl swpl Hd4 Hs4 HDX HSX HDW Hw Hfull Hsm RD RS.
  pose proof (LeptRop2Arith.g_hang_range DX) as Hh.
  pose proof (g_col2 DX DW dwpl HDX ltac:(lia) Hw) as (C0 & C1 & C2).
  assert (Edp : g_dp DX DW = false) by (rewrite (g_dp_hang DX DW HDW); apply Z.ltb_ge; lia).
  assert (Enf : g_nfw DX DW = (DW - g_hang DX) / 32) by (apply g_nfw_nodp; exact Edp).
  assert (Hn1 : (1 <= (DW - g_hang DX) / 32)%Z) by lia.
  pose proof (g_smax_2 DX SX DW swpl Hsm ltac:(rewrite Enf; lia)) as S2. rewrite Enf in S2.
  split; [exact Hn1 |]. split; [split; lia |]. intros i Hi.
  destruct (RD ((DX + g_hang DX) / 32)%Z ((DW - g_hang DX) / 32)%Z i ltac:(lia) ltac:(lia) ltac:(lia) Hi) as [D1 D2].
  destruct (RS ((SX + g_hang DX) / 32)%Z ((DW - g_hang DX) / 32 + 1)%Z i ltac:(lia) ltac:(lia) ltac:(lia) Hi) as [T1 T2].
  repeat split; lia.
Qed.

Lemma rgs_RL : forall datad nd datas ns DX SX DW dy sy dh dwpl swpl : Z,
  (datad mod 4 = 0)%Z -> (datas mod 4 = 0)%Z -> (0 <= DX)%Z -> (0 <= SX)%Z -> (1 <= DW)%Z -> (DX + DW <= 32 * dwpl)%Z ->
  (g_hang DX <= DW)%Z -> (g_lwb DX DW <> 0)%Z -> (g_smax DX SX DW <= swpl - 1)%Z ->
  (forall c nw i', 0 <= c -> 0 <= nw -> c + nw <= dwpl -> 0 <= i' < dh ->
      datad <= datad + 4 * (dy * dwpl) + 4 * c + 4 * dwpl * i' /\ datad + 4 * (dy * dwpl) + 4 * c + 4 * dwpl * i' + 4 * nw <= datad + nd)%Z ->
  (forall c nw i', 0 <= c -> 0 <= nw -> c + nw <= swpl -> 0 <= i' < dh ->
      datas <= datas + 4 * (sy * swpl) + 4 * c + 4 * swpl * i' /\ datas + 4 * (sy * swpl) + 4 * c + 4 * swpl * i' + 4 * nw <= datas + ns)%Z ->
  ((datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32)) mod 4 = 0 /\
   (datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32)) mod 4 = 0)%Z /\
  (forall i, 0 <= i < dh ->
     datad <= datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32) + 4 * dwpl * i /\
     datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32) + 4 * dwpl * i + 4 <= datad + nd /\
     datas <= datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32) + 4 * swpl * i /\
     datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32) + 4 * swpl * i + 4 <= datas + ns /\
     (g_f3 DX SX DW = false ->
        datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32) + 4 * swpl * i + 8 <= datas + ns))%Z.
Proof.
  intros datad nd datas ns DX SX DW dy sy dh dwpl swpl Hd4 Hs4 HDX HSX HDW Hw Hhg Hlw Hsm RD RS.
  pose proof (LeptRop2Arith.g_hang_range DX) as Hh.
  pose proof (g_col2 DX DW dwpl HDX Hhg Hw) as (C0 & C1 & _).
  pose proof (g_col3 DX DW dwpl HDX Hhg Hw Hlw) as C3.
  assert (Edp : g_dp DX DW = false) by (rewrite (g_dp_hang DX DW HDW); apply Z.ltb_ge; lia).
  assert (Enf : g_nfw DX DW = (DW - g_hang DX) / 32) by (apply g_nfw_nodp; exact Edp).
  assert (Enl : g_nolast DX DW = false) by (rewrite (g_nolast_nodp DX DW Edp); apply Z.eqb_neq; exact Hlw).
  pose proof (g_smax_3 DX SX DW swpl Hsm Enl) as S3. rewrite Enf in S3.
  assert (S3' : ((SX + g_hang DX) / 32 + (DW - g_hang DX) / 32 + 1 <= swpl)%Z) by (destruct (g_f3 DX SX DW); lia).
  split; [split; lia |]. intros i Hi.
  destruct (RD ((DX + g_hang DX) / 32 + (DW - g_hang DX) / 32)%Z 1%Z i ltac:(lia) ltac:(lia) ltac:(lia) Hi) as [D1 D2].
  destruct (RS ((SX + g_hang DX) / 32 + (DW - g_hang DX) / 32)%Z 1%Z i ltac:(lia) ltac:(lia) ltac:(lia) Hi) as [T1 T2].
  repeat split; try lia. intros E3. rewrite E3 in S3.
  destruct (RS ((SX + g_hang DX) / 32 + (DW - g_hang DX) / 32)%Z 2%Z i ltac:(lia) ltac:(lia) ltac:(lia) Hi) as [_ T3]. lia.
Qed.

Lemma rgs_rows_eq : forall dy dh dpixh sy spixh : Z, (dy + dh <= dpixh)%Z -> (sy + dh <= spixh)%Z ->
  (sy - spixh - Z.min 0 (sy + dpixh - spixh - dy + Z.min 0 (dy + dh - dpixh)) = - dh)%Z.
Proof. intros. lia. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Gset.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma and31 : forall x : Z, (0 <= x < 2 ^ 64)%Z -> alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 31) = Z_to_bv 64 (x mod 32).
Proof. intros x Hx. rewrite alu_and. apply zand31. exact Hx. Qed.

Lemma lor_mod32_ne0 : forall a b : Z, (0 <= a)%Z -> (0 <= b)%Z -> (a mod 32 <> b mod 32)%Z -> (Z.lor a b mod 32 <> 0)%Z.
Proof.
  intros a b Ha Hb Hne Hz. apply Hne.
  assert (E : forall x, (x mod 32 = Z.land x (Z.ones 5))%Z) by (intro x; rewrite Z.land_ones by lia; reflexivity).
  rewrite !E in Hz. rewrite !E. rewrite Z.land_lor_distr_l in Hz.
  apply Z.lor_eq_0_iff in Hz. destruct Hz as [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

Ltac grd Hbs J :=
  lazymatch type of Hbs with rdn _ _ _ _ = Some ?bs =>
    lazymatch goal with |- exists _, rdn _ _ _ _ = Some _ /\ _ =>
      exists bs; split; [ gz; match goal with |- rdn _ _ (Z_to_bv 64 ?A) _ = _ => replace A with J by (unfold RG_MASKS; lia) end;
                          exact Hbs
                        | reflexivity ]
    end
  end.

Ltac gval regs :=
  try unfold ex_env; ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
  repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
  unfold g_f6, g_f7; gz; gvc.

Ltac gmem regs Hms :=
  eapply ex_msteps_mem; [exact Hms|]; cbn [mem_denot s_log e_addr e_width e_val];
  repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | first [ solve [ex_bytes_eq regs] | (f_equal; try gval regs) ] ]);
  try reflexivity.

Ltac gimp := lazymatch goal with
  | |- true = false -> _ => let H := fresh in intro H; discriminate H
  | |- false = true -> _ => let H := fresh in intro H; discriminate H
  | |- true = true -> _ => intros _
  | |- false = false -> _ => intros _
  | _ => idtac
  end.

Ltac gend regs Hms HR HR' :=
  split; [ first [ex_mem regs Hms | gmem regs Hms]
         | repeat split; gimp; try (ex_reg regs HR'); [..| ex_agree HR HR'] ];
  try (gz; gvc).


(* [comment removed for export] *)
Lemma rg_P0 : forall regs m (s DX SX : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= DX < 2 ^ 31)%Z -> (0 <= SX < 2 ^ 31)%Z -> (DX mod 32 <> SX mod 32)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 25 = Z_to_bv 64 DX -> getr regs 27 = Z_to_bv 64 SX ->
  exists regs',
    msteps SEGS (mkst regs RG_P0 m rom)
                (mkst regs' RG_Q1
                   (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
                      (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (getr regs 6)))
                      (Z_to_bv 64 (s - 200)) (word_to_le_bytes 8 (getr regs 1)))
                      (Z_to_bv 64 (s - 192)) (word_to_le_bytes 8 (getr regs 26)))
                      (Z_to_bv 64 (s - 176)) (word_to_le_bytes 8 (getr regs 16)))
                      (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (getr regs 28)))
                      (Z_to_bv 64 (s - 168)) (word_to_le_bytes 8 (getr regs 18)))
                      (Z_to_bv 64 (s - 184)) (word_to_le_bytes 8 (getr regs 23))) rom)
    /\ getr regs' 1 = Z_to_bv 64 (DX mod 32) /\ getr regs' 12 = Z_to_bv 64 (SX mod 32)
    /\ regs_agree (fun r => In r [1; 12]%list) regs regs'.
Proof.
  intros regs m s DX SX Hs1 Hs2 HDX HSX Hne Hso H2 H25 H27.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)). pose proof (Z.mod_pos_bound SX 32 ltac:(lia)).
  unfold RG_P0, RG_Q1.
  replace (0x7ff84 : word) with (Z_to_bv 64 0x7ff84) by (apply bv_eq; reflexivity).
  replace (0x80140 : word) with (Z_to_bv 64 0x80140) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KWr (SA (EVar 32) (-240)) 240]) by (ex_know regs).
  ex_run 60%nat [0x80140%Z] (SCR [false; true] [] []) HR HK R' HR' Hms.
  - rewrite !and31 by lia. ex_br.
  - rewrite alu_or, zbv_or by lia. rewrite and31 by (apply Z_lor_range64; lia).
    pose proof (lor_mod32_ne0 DX SX ltac:(lia) ltac:(lia) Hne). pose proof (Z.mod_pos_bound (Z.lor DX SX) 32 ltac:(lia)).
    ex_br.
  - exists R'. split; [ex_mem regs Hms |]. repeat split; try (ex_reg regs HR'); [..| ex_agree HR HR'].
    all: apply zand31; lia.
Qed.

(* [comment removed for export] *)
Lemma rg_Q1 : forall regs m (DX SX : Z),
  (0 <= DX < 2 ^ 31)%Z -> (0 <= SX < 2 ^ 31)%Z -> (DX mod 32 <> SX mod 32)%Z ->
  getr regs 1 = Z_to_bv 64 (DX mod 32) -> getr regs 12 = Z_to_bv 64 (SX mod 32) ->
  exists regs',
    msteps SEGS (mkst regs RG_Q1 m rom) (mkst regs' RG_Q2 m rom)
    /\ getr regs' 23 = Z_to_bv 64 (g_hang DX) /\ getr regs' 21 = Z_to_bv 64 (32 - DX mod 32) /\ getr regs' 20 = Z_to_bv 64 32
    /\ getr regs' 17 = Z_to_bv 64 (32 - SX mod 32) /\ getr regs' 29 = Z_to_bv 64 (g_sls DX SX) /\ getr regs' 30 = Z_to_bv 64 (g_sls DX SX)
    /\ getr regs' 16 = Z_to_bv 64 RG_MASKS /\ getr regs' 15 = Z_to_bv 64 (2 ^ 64 - 1 - RG_MASKS)
    /\ regs_agree (fun r => In r [6; 15; 16; 17; 20; 21; 23; 29; 30; 31]%list) regs regs'.
Proof.
  intros regs m DX SX HDX HSX Hne H1 H12.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)). pose proof (Z.mod_pos_bound SX 32 ltac:(lia)).
  pose proof (g_sls_pos DX SX) as Hsls.
  assert (HM : exists (bs : list byte) (v : word),
             rdn SEGS m (Z_to_bv 64 (RG_MASKS + 4 * g_sls DX SX)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v)
    by (unshelve eapply masks_any; first [lia | exact rom]).
  destruct HM as (bs & v & Hbs & _).
  unfold RG_Q1, RG_Q2.
  replace (0x80140 : word) with (Z_to_bv 64 0x80140) by (apply bv_eq; reflexivity).
  replace (0x801a4 : word) with (Z_to_bv 64 0x801a4) by (apply bv_eq; reflexivity).
  ex_entry regs [extz true 4 (lez bs)] HR.
  assert (HK : know_ok SEGS (ex_env regs [extz true 4 (lez bs)]) m []) by (ex_know regs).
  ex_run 60%nat [0x801a4%Z] (SCR [true; true] [EVar 32] []) HR HK R' HR' Hms.
  - exists bs. split; [| reflexivity].
    match goal with |- rdn _ _ ?A _ = _ => replace A with (Z_to_bv 64 (RG_MASKS + 4 * g_sls DX SX)) by (gref2 DX SX) end.
    exact Hbs.
  - match goal with |- context [bv_unsigned (mul_div M_MUL (Z_to_bv 64 4) ?t)] =>
      replace (mul_div M_MUL (Z_to_bv 64 4) t) with (Z_to_bv 64 (4 * g_sls DX SX)) by (gref2 DX SX) end.
    rewrite !u_Z2bv by lia. lia.
  - gref2 DX SX.
  - gref2 DX SX.
  - exists R'. split; [ex_mem regs Hms |]. repeat split; try (ex_reg regs HR'); [..| ex_agree HR HR'].
    all: gref2 DX SX.
Qed.

(* [comment removed for export] *)
Lemma rg_Q2 : forall regs m (s DX SX DW dy sy dwpl swpl datad datas : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= DX < 2 ^ 31)%Z -> (0 <= SX < 2 ^ 31)%Z -> (0 <= DW < 2 ^ 31)%Z -> (DX mod 32 <> 0)%Z ->
  (0 <= dy * dwpl < 2 ^ 31)%Z -> (0 <= sy * swpl < 2 ^ 31)%Z -> (1 <= datad)%Z -> (1 <= datas)%Z ->
  (datad + 4 * (dy * dwpl) + 4 * (DX / 32) < 2 ^ 64)%Z -> (datas + 4 * (sy * swpl) + 4 * (SX / 32) < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) ->
  getr regs 1 = Z_to_bv 64 (DX mod 32) -> getr regs 21 = Z_to_bv 64 (32 - DX mod 32) -> getr regs 12 = Z_to_bv 64 (SX mod 32) ->
  getr regs 17 = Z_to_bv 64 (32 - SX mod 32) -> getr regs 9 = Z_to_bv 64 DW -> getr regs 25 = Z_to_bv 64 DX -> getr regs 27 = Z_to_bv 64 SX ->
  getr regs 7 = Z_to_bv 64 dy -> getr regs 5 = Z_to_bv 64 sy -> getr regs 14 = Z_to_bv 64 dwpl ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 19 = Z_to_bv 64 datas ->
  getr regs 16 = Z_to_bv 64 RG_MASKS -> getr regs 15 = Z_to_bv 64 (2 ^ 64 - 1 - RG_MASKS) ->
  exists regs',
    msteps SEGS (mkst regs RG_Q2 m rom)
                (mkst regs' RG_Q3 (wbytes m (Z_to_bv 64 (s - 224)) (word_to_le_bytes 8 (Z_to_bv 64 (if g_f6 DX SX then 1 else 0)))) rom)
    /\ getr regs' 25 = Z_to_bv 64 (datad + 4 * (dy * dwpl) + 4 * (DX / 32)) /\ getr regs' 15 = Z_to_bv 64 (datas + 4 * (sy * swpl) + 4 * (SX / 32))
    /\ getr regs' 26 = Z_to_bv 64 (if g_f7 SX DW then 1 else 0)
    /\ regs_agree (fun r => In r [6; 12; 15; 16; 22; 25; 26; 27; 28]%list) regs regs'.
Proof.
  intros regs m s DX SX DW dy sy dwpl swpl datad datas Hs1 Hs2 HDX HSX HDW Hfw Hdd Hss Hd1 Hs1' Hpd Hps Hso Csw
    H2 H1 H21 H12 H17 H9 H25 H27 H7 H5 H14 H10 H19 H16 H15.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)). pose proof (Z.mod_pos_bound SX 32 ltac:(lia)).
  pose proof (Z.div_pos DX 32 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le DX 32 ltac:(lia)).
  pose proof (Z.div_pos SX 32 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le SX 32 ltac:(lia)).
  assert (HM : exists (bs : list byte) (v : word),
             rdn SEGS m (Z_to_bv 64 (RG_MASKS + 4 * (32 - DX mod 32))) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v)
    by (unshelve eapply masks_any; first [lia | exact rom]).
  destruct HM as (bs & v & Hbs & _).
  unfold RG_Q2, RG_Q3.
  replace (0x801a4 : word) with (Z_to_bv 64 0x801a4) by (apply bv_eq; reflexivity).
  replace (0x802ac : word) with (Z_to_bv 64 0x802ac) by (apply bv_eq; reflexivity).
  ex_entry regs [s; swpl; extz true 4 (lez bs)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; swpl; extz true 4 (lez bs)]) m
                 [KWr (SA (EVar 32) (-240)) 240; KWord (SA (EVar 32) (-152)) 8 (EVar 33)]) by (ex_know regs).
  ex_run 120%nat [0x802ac%Z] (SCR [false; true; true; true; true; true; true; true; true; true; true; true] [EVar 34] []) HR HK R' HR' Hms.
  all: gsc.
  all: try (grd Hbs (RG_MASKS + 4 * (32 - DX mod 32))%Z).
  all: lazymatch goal with |- @ex (bvmap 5 word) _ => exists R'; gend regs Hms HR HR' | _ => idtac end.
Qed.

(* [comment removed for export] *)
Lemma rg_Q3 : forall regs m (s DX SX DW : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (RG_MASKS + 264 <= s - 240)%Z -> (0 <= DX < 2 ^ 30)%Z -> (0 <= SX < 2 ^ 31)%Z -> (1 <= DW)%Z -> (DX mod 32 <> 0)%Z ->
  (DW < 32 - DX mod 32)%Z -> (DX mod 32 <> SX mod 32)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 8 = Z_to_bv 64 DW -> getr regs 9 = Z_to_bv 64 DW -> getr regs 13 = Z_to_bv 64 DX ->
  getr regs 21 = Z_to_bv 64 (32 - DX mod 32) -> getr regs 20 = Z_to_bv 64 32 -> getr regs 29 = Z_to_bv 64 (g_sls DX SX) ->
  exists regs',
    msteps SEGS (mkst regs RG_Q3 m rom)
                (mkst regs' RG_Q6
                   (wbytes (wbytes (wbytes (wbytes m
                      (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                      (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
                      (Z_to_bv 64 (s - 216)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
                      (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
    /\ getr regs' 8 = Z_to_bv 64 (32 - g_sls DX SX) /\ getr regs' 10 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [6; 8; 9; 10; 12; 16; 17; 18; 22; 27]%list) regs regs'.
Proof.
  intros regs m s DX SX DW Hs1 Hs2 Hmk HDX HSX HDW Hfw Hdp Hne Hso H2 H8 H9 H13 H21 H20 H29.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)). pose proof (Z.mod_pos_bound SX 32 ltac:(lia)).
  pose proof (g_sls_range DX SX). pose proof (Z.mod_pos_bound (DW + DX) 32 ltac:(lia)). unfold RG_MASKS in Hmk.
  assert (HM : exists (bs : list byte) (v : word),
             rdn SEGS m (Z_to_bv 64 (RG_MASKS + 4 * (33 + DW + DX mod 32))) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v)
    by (unshelve eapply masks_any; first [lia | exact rom]).
  destruct HM as (bs & v & Hbs & _).
  unfold RG_Q3, RG_Q6.
  replace (0x802ac : word) with (Z_to_bv 64 0x802ac) by (apply bv_eq; reflexivity).
  replace (0x80a14 : word) with (Z_to_bv 64 0x80a14) by (apply bv_eq; reflexivity).
  ex_entry regs [s; extz true 4 (lez bs)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; extz true 4 (lez bs)]) m [KWr (SA (EVar 32) (-240)) 240]) by (ex_know regs).
  ex_run 80%nat [0x80a14%Z] (SCR [false; true; true; true; false] [EVar 33] []) HR HK R' HR' Hms.
  all: gsc.
  all: try (grd Hbs (RG_MASKS + 4 * (33 + DW + DX mod 32))%Z).
  all: lazymatch goal with |- @ex (bvmap 5 word) _ => exists R'; gend regs Hms HR HR' | _ => idtac end.
Qed.

(* [comment removed for export] *)
Lemma rg_Q3n : forall regs m (DX DW : Z),
  (0 <= DX < 2 ^ 31)%Z -> (0 <= DW < 2 ^ 31)%Z -> (32 - DX mod 32 <= DW)%Z ->
  getr regs 9 = Z_to_bv 64 DW -> getr regs 21 = Z_to_bv 64 (32 - DX mod 32) ->
  exists regs',
    msteps SEGS (mkst regs RG_Q3 m rom) (mkst regs' RG_Q4 m rom)
    /\ regs_agree (fun r => In r (@nil (bv 5))) regs regs'.
Proof.
  intros regs m DX DW HDX HDW Hc H9 H21.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)).
  unfold RG_Q3, RG_Q4.
  replace (0x802ac : word) with (Z_to_bv 64 0x802ac) by (apply bv_eq; reflexivity).
  replace (0x806dc : word) with (Z_to_bv 64 0x806dc) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs (@nil Z)) m []) by (ex_know regs).
  ex_run 10%nat [0x806dc%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms | ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma rg_Q3b : forall regs m (DX : Z),
  (0 <= DX < 2 ^ 31)%Z -> (DX mod 32 = 0)%Z -> getr regs 1 = Z_to_bv 64 (DX mod 32) ->
  exists regs',
    msteps SEGS (mkst regs RG_Q2 m rom) (mkst regs' RG_Q4 m rom)
    /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 0 /\ getr regs' 21 = Z_to_bv 64 0 /\ getr regs' 27 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [15; 21; 25; 27]%list) regs regs'.
Proof.
  intros regs m DX HDX H0 H1.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)).
  unfold RG_Q2, RG_Q4.
  replace (0x801a4 : word) with (Z_to_bv 64 0x801a4) by (apply bv_eq; reflexivity).
  replace (0x806dc : word) with (Z_to_bv 64 0x806dc) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs (@nil Z)) m []) by (ex_know regs).
  ex_run 10%nat [0x806dc%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms |]; repeat split; try (ex_reg regs HR'); [..| ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma rg_Q4 : forall (full : bool) regs m (s DX SX DW dy sy dwpl swpl datad datas : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= DX < 2 ^ 30)%Z -> (0 <= SX < 2 ^ 30)%Z -> (0 <= DW < 2 ^ 30)%Z -> (g_hang DX <= DW)%Z ->
  (if full then 32 <= DW - g_hang DX else DW - g_hang DX < 32)%Z ->
  (full = true -> 0 <= dy * dwpl < 2 ^ 31 /\ 0 <= sy * swpl < 2 ^ 31 /\ 1 <= datad /\ 1 <= datas /\
                  datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32) < 2 ^ 64 /\
                  datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32) < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 8 = Z_to_bv 64 DW ->
  getr regs 21 = Z_to_bv 64 (g_hang DX) -> getr regs 23 = Z_to_bv 64 (g_hang DX) -> getr regs 13 = Z_to_bv 64 DX -> getr regs 24 = Z_to_bv 64 SX ->
  getr regs 7 = Z_to_bv 64 dy -> getr regs 5 = Z_to_bv 64 sy -> getr regs 14 = Z_to_bv 64 dwpl ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 19 = Z_to_bv 64 datas ->
  exists regs',
    msteps SEGS (mkst regs RG_Q4 m rom)
                (mkst regs' RG_Q5
                   (if full
                    then wbytes (wbytes m
                           (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 ((DW - g_hang DX) / 32))))
                           (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 0))
                    else wbytes (wbytes (wbytes m
                           (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 ((DW - g_hang DX) / 32))))
                           (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                           (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 1))) rom)
    /\ getr regs' 16 = Z_to_bv 64 0
    /\ (full = true -> getr regs' 18 = Z_to_bv 64 (datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32))
                    /\ getr regs' 6 = Z_to_bv 64 (datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32)))
    /\ regs_agree (fun r => In r [6; 8; 12; 16; 17; 18; 28]%list) regs regs'.
Proof.
  intros full regs m s DX SX DW dy sy dwpl swpl datad datas Hs1 Hs2 HDX HSX HDW Hhang Hfull Hfc Hso Csw
    H2 H8 H21 H23 H13 H24 H7 H5 H14 H10 H19.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)).
  pose proof (g_hang_range DX) as Hh.
  assert (Hdv : (0 <= (DW - g_hang DX) / 32 <= DW)%Z) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold RG_Q4, RG_Q5.
  replace (0x806dc : word) with (Z_to_bv 64 0x806dc) by (apply bv_eq; reflexivity).
  replace (0x80850 : word) with (Z_to_bv 64 0x80850) by (apply bv_eq; reflexivity).
  ex_entry regs [s; swpl] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; swpl]) m
                 [KWr (SA (EVar 32) (-240)) 240; KWord (SA (EVar 32) (-152)) 8 (EVar 33)]) by (ex_know regs).
  destruct full; cbn iota in Hfull |- *.
  - destruct (Hfc eq_refl) as (Hdd & Hss & Hd1 & Hs1' & Hpd & Hps). clear Hfc.
    assert (Hd1v : (1 <= (DW - g_hang DX) / 32)%Z) by (apply Z.div_le_lower_bound; lia).
    ex_run 120%nat [0x80850%Z] (SCR [false; true; true; true; true; true; true; true; true; true; true; true; true] [] []) HR HK R' HR' Hms.
    all: gsc.
    all: lazymatch goal with |- @ex (bvmap 5 word) _ => exists R'; gend regs Hms HR HR' | _ => idtac end.
  - clear Hfc.
    assert (E0 : ((DW - g_hang DX) / 32 = 0)%Z) by (apply Z.div_small; lia).
    ex_run 40%nat [0x80850%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    all: try rewrite E0.
    all: gsc.
    all: lazymatch goal with |- @ex (bvmap 5 word) _ => exists R'; gend regs Hms HR HR' | _ => idtac end.
Qed.

(* [comment removed for export] *)
Lemma rg_Q5 : forall (nl : bool) regs m (s DX SX DW dy sy dwpl swpl datad datas nfw sls : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (RG_MASKS + 264 <= s - 240)%Z -> (0 <= DX < 2 ^ 30)%Z -> (0 <= SX < 2 ^ 30)%Z -> (0 <= DW < 2 ^ 30)%Z -> (g_hang DX <= DW)%Z ->
  (0 <= nfw < 2 ^ 26)%Z -> (0 <= sls <= 32)%Z -> (if nl then g_lwb DX DW = 0 else g_lwb DX DW <> 0)%Z ->
  (nl = false -> 0 <= dy * dwpl < 2 ^ 31 /\ 0 <= sy * swpl < 2 ^ 31 /\ 1 <= datad /\ 1 <= datas /\
                 datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * nfw < 2 ^ 64 /\
                 datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * nfw < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 13 = Z_to_bv 64 DX -> getr regs 9 = Z_to_bv 64 DW -> getr regs 24 = Z_to_bv 64 SX ->
  getr regs 23 = Z_to_bv 64 (g_hang DX) -> getr regs 16 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 32 -> getr regs 29 = Z_to_bv 64 sls ->
  getr regs 7 = Z_to_bv 64 dy -> getr regs 5 = Z_to_bv 64 sy -> getr regs 14 = Z_to_bv 64 dwpl ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 19 = Z_to_bv 64 datas ->
  exists regs' (mk : word),
    msteps SEGS (mkst regs RG_Q5 m rom)
                (mkst regs' RG_Q6
                   (if nl
                    then wbytes (wbytes m
                           (Z_to_bv 64 (s - 216)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
                           (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0))
                    else wbytes (wbytes (wbytes (wbytes m
                           (Z_to_bv 64 (s - 216)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                           (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 mk))
                           (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (Z_to_bv 64 (datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * nfw))))
                           (Z_to_bv 64 (s - 232)) (word_to_le_bytes 8 (Z_to_bv 64 (if (32 - sls <? g_lwb DX DW)%Z then 0 else 1)))) rom)
    /\ getr regs' 8 = Z_to_bv 64 (32 - sls)
    /\ (nl = true -> getr regs' 10 = Z_to_bv 64 0)
    /\ (nl = false -> getr regs' 10 = Z_to_bv 64 (datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * nfw))
    /\ regs_agree (fun r => In r [5; 7; 8; 9; 10; 12; 13; 16; 20; 22; 23; 28]%list) regs regs'.
Proof.
  intros nl regs m s DX SX DW dy sy dwpl swpl datad datas nfw sls Hs1 Hs2 Hmk HDX HSX HDW Hhang Hnfw Hsls Hnl Hnlc Hso Csw Cnfw
    H2 H13 H9 H24 H23 H16 H20 H29 H7 H5 H14 H10 H19.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)). pose proof (Z.mod_pos_bound (DW + DX) 32 ltac:(lia)).
  unfold RG_MASKS in Hmk.
  pose proof (g_hang_range DX) as Hh.
  unfold g_lwb in *.
  unfold RG_Q5, RG_Q6.
  replace (0x80850 : word) with (Z_to_bv 64 0x80850) by (apply bv_eq; reflexivity).
  replace (0x80a14 : word) with (Z_to_bv 64 0x80a14) by (apply bv_eq; reflexivity).
  destruct nl; cbn iota in Hnl |- *.
  - clear Hnlc.
    ex_entry regs [s; swpl; nfw] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; swpl; nfw]) m
                   [KWr (SA (EVar 32) (-240)) 240; KWord (SA (EVar 32) (-152)) 8 (EVar 33);
                    KWord (SA (EVar 32) (-128)) 8 (EVar 34)]) by (ex_know regs).
    ex_run 40%nat [0x80a14%Z] (SCR [true; false] [] []) HR HK R' HR' Hms.
    all: gsc.
    all: lazymatch goal with |- @ex (bvmap 5 word) _ => exists R', (Z_to_bv 64 0); gend regs Hms HR HR' | _ => idtac end.
  - destruct (Hnlc eq_refl) as (Hdd & Hss & Hd1 & Hs1' & Hpd & Hps). clear Hnlc.
    assert (HM : exists (bs : list byte) (v : word),
               rdn SEGS m (Z_to_bv 64 (RG_MASKS + 4 * (33 + (DW + DX) mod 32))) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v)
      by (unshelve eapply masks_any; first [lia | exact rom]).
    destruct HM as (bs & v & Hbs & _).
    ex_entry regs [s; swpl; nfw; extz true 4 (lez bs)] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; swpl; nfw; extz true 4 (lez bs)]) m
                   [KWr (SA (EVar 32) (-240)) 240; KWord (SA (EVar 32) (-152)) 8 (EVar 33);
                    KWord (SA (EVar 32) (-128)) 8 (EVar 34)]) by (ex_know regs).
    ex_run 160%nat [0x80a14%Z] (SCR [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] [EVar 35] []) HR HK R' HR' Hms.
    all: gsc.
    all: try (grd Hbs (RG_MASKS + 4 * (33 + (DW + DX) mod 32))%Z).
    all: lazymatch goal with |- @ex (bvmap 5 word) _ => exists R', (Z_to_bv 64 (extz true 4 (lez bs))); gend regs Hms HR HR' | _ => idtac end.
Qed.

Lemma rg_Q6g : forall regs m (s swpl op tv : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= swpl < 2 ^ 63)%Z -> (1 <= op <= 14)%Z -> (0 <= tv < 2 ^ 31)%Z -> (tv mod 2 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (RG_JT + 4 * (op - 1))) 4 = Some (Z_to_le_bytes 4 tv) ->
  store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 11 = Z_to_bv 64 op ->
  exists regs',
    msteps SEGS (mkst regs RG_Q6 m rom)
                (mkst regs' (Z_to_bv 64 (RG_JT + tv)) (wbytes m (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
    /\ regs_agree (fun r => In r [12; 13; 16]%list) regs regs'.
Proof.
  intros regs m s swpl op tv Hs1 Hs2 Hsw Hop Htv Hev Hjt Hso Csw H2 H11.
  unfold RG_Q6.
  replace (0x80a14 : word) with (Z_to_bv 64 0x80a14) by (apply bv_eq; reflexivity).
  ex_entry regs [s; swpl; tv] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; swpl; tv]) m
                 [KWr (SA (EVar 32) (-240)) 240; KWord (SA (EVar 32) (-152)) 8 (EVar 33);
                  KRange (EVar 33) 0 (2 ^ 63 - 1); KRange (EVar 11) 1 14]) by (ex_know regs).
  ex_run 60%nat (@nil Z) (SCR [false] [EVar 34] []) HR HK R' HR' Hms.
  all: gsc.
  - exists (Z_to_le_bytes 4 tv). split.
    + gz. match goal with |- rdn _ _ (Z_to_bv 64 ?A) _ = _ => replace A with (RG_JT + 4 * (op - 1))%Z by (unfold RG_JT; lia) end.
      exact Hjt.
    + rewrite lez4 by lia. rewrite u_Z2bv by lia. unfold extz. change (8 * N.of_nat 4)%N with 32%N.
      rewrite (swrap32_eq tv tv 0) by lia. reflexivity.
  - assert (Hms2 : msteps SEGS (mkst regs (Z_to_bv 64 0x80a14) m rom)
                     (mkst R' (0x80a4c : word) (wbytes m (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)).
    { replace (0x80a4c : word) with (Z_to_bv 64 0x80a4c) by (apply bv_eq; reflexivity). gmem regs Hms. }
    exists R'. split; [| ex_agree HR HR'].
    eapply msteps_trans; [exact Hms2 |].
    stepjr F_80a4c D_80a4c (Z_to_bv 64 (RG_JT + tv)) ltac:(ex_reg regs HR'; try (unfold RG_JT; gz; gvc)).
    match goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (Z_to_bv 64 (RG_JT + tv)); [apply mst_refl |] end.
    unfold v_jalr, jalr_tgtZ. f_equal. unfold RG_JT in *. rewrite u_Z2bv by lia.
    cbn [bv_signed]. rewrite Z.add_0_r. symmetry. apply land_m2_even.
    rewrite Z.add_mod by lia. rewrite Hev. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rg_Q6 : forall regs m (s swpl : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= swpl < 2 ^ 63)%Z ->
  rdn SEGS m (Z_to_bv 64 RG_JT12) 4 = Some (Z_to_le_bytes 4 RG_JT12V) ->
  store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 11 = Z_to_bv 64 12 ->
  exists regs',
    msteps SEGS (mkst regs RG_Q6 m rom)
                (mkst regs' RG_S1 (wbytes m (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
    /\ regs_agree (fun r => In r [12; 13; 16]%list) regs regs'.
Proof.
  intros regs m s swpl Hs1 Hs2 Hsw Hjt Hso Csw H2 H11.
  unfold RG_Q6, RG_S1.
  replace (0x80a14 : word) with (Z_to_bv 64 0x80a14) by (apply bv_eq; reflexivity).
  replace (0x86d0c : word) with (Z_to_bv 64 0x86d0c) by (apply bv_eq; reflexivity).
  ex_entry regs [s; swpl] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; swpl]) m
                 [KWr (SA (EVar 32) (-240)) 240; KWord (SA (EVar 32) (-152)) 8 (EVar 33);
                  KWord (SA (ELit 0) RG_JT12) 4 (ELit RG_JT12V); KRange (EVar 33) 0 (2 ^ 63 - 1)])
    by (unfold RG_JT12, RG_JT12V in *; ex_know regs).
  ex_run 60%nat [0x86d0c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [gmem regs Hms | ex_agree HR HR'].
Qed.

Definition rgs_out (m M1 : word -> option byte) (regs' : bvmap 5 word) (s datad nd datas ns dh dwpl swpl : Z)
  (fw f6 f7 nofull nolast f3 : bool) (dxb sls nfw psf pdf psF pdF psl pdl : Z) : Prop :=
    (forall x : word, (u x < s - 240 \/ s - 112 <= u x)%Z -> M1 x = m x) /\ mem_grows m M1
    /\ (1 <= dh < 2 ^ 24 /\ 0 <= swpl < 2 ^ 24 /\ 0 <= dwpl < 2 ^ 24 /\ 1 <= sls <= 31 /\ 0 <= nfw < 2 ^ 26)%Z
    /\ ((0 <= dxb < 32)%Z /\ (if fw then dxb <> 0 else dxb = 0)%Z)
    /\ (nofull = false -> (1 <= nfw)%Z)
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 216)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nolast then 1 else 0)))
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nofull then 1 else 0)))
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl))
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh))
    /\ (fw = true \/ nolast = false -> rg_rows M1 s dh)
    /\ (fw = true -> rdn SEGS M1 (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f6 then 1 else 0))))
    /\ (nofull = false -> rdn SEGS M1 (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)))
    /\ (nolast = false -> rdn SEGS M1 (Z_to_bv 64 (s - 232)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f3 then 1 else 0))))
    /\ (nolast = false -> rdn SEGS M1 (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)))
    /\ (nolast = false -> exists mk : word, rdn SEGS M1 (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk))
    /\ (fw = true -> (psf mod 4 = 0 /\ pdf mod 4 = 0)%Z /\
          (forall i, 0 <= i < dh -> datad <= pdf + 4 * dwpl * i /\ pdf + 4 * dwpl * i + 4 <= datad + nd /\
                                    datas <= psf + 4 * swpl * i /\ psf + 4 * swpl * i + 4 <= datas + ns /\
                                    (f6 = true -> f7 = false -> psf + 4 * swpl * i + 8 <= datas + ns))%Z)
    /\ (nofull = false -> (psF mod 4 = 0 /\ pdF mod 4 = 0)%Z /\
          (forall i, 0 <= i < dh -> datad <= pdF + 4 * dwpl * i /\ pdF + 4 * dwpl * i + 4 * nfw <= datad + nd /\
                                    datas <= psF + 4 * swpl * i /\ psF + 4 * swpl * i + 4 * nfw + 4 <= datas + ns)%Z)
    /\ (nolast = false -> (psl mod 4 = 0 /\ pdl mod 4 = 0)%Z /\
          (forall i, 0 <= i < dh -> datad <= pdl + 4 * dwpl * i /\ pdl + 4 * dwpl * i + 4 <= datad + nd /\
                                    datas <= psl + 4 * swpl * i /\ psl + 4 * swpl * i + 4 <= datas + ns /\
                                    (f3 = false -> psl + 4 * swpl * i + 8 <= datas + ns))%Z)
    /\ getr regs' 2 = Z_to_bv 64 (s - 240) /\ getr regs' 1 = Z_to_bv 64 dxb /\ getr regs' 14 = Z_to_bv 64 dwpl
    /\ getr regs' 30 = Z_to_bv 64 sls /\ getr regs' 8 = Z_to_bv 64 (32 - sls)
    /\ (fw = true -> getr regs' 15 = Z_to_bv 64 psf /\ getr regs' 25 = Z_to_bv 64 pdf /\ getr regs' 26 = Z_to_bv 64 (if f7 then 1 else 0))
    /\ (nofull = false -> getr regs' 6 = Z_to_bv 64 psF /\ getr regs' 18 = Z_to_bv 64 pdF)
    /\ (nolast = false -> getr regs' 10 = Z_to_bv 64 pdl).

Ltac ggrows := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
Ltac lastmem S := match type of S with msteps _ _ (mkst _ _ ?M _) => M end.
Ltac greg_fin := first [ reflexivity | (f_equal; lia) ].
Ltac greg :=
  lazymatch goal with
  | |- getr ?rb ?k = _ =>
    first [ match goal with H : getr rb k = _ |- _ => rewrite H; greg_fin end
          | match goal with AG : regs_agree _ ?ra rb |- _ => rewrite (AG k ltac:(notin_list)); greg end ]
  end.
Ltac gsok := eapply store_ok_mono; [ ggrows | eassumption ].
Ltac growsc :=
  match goal with R : rg_rows _ _ _ |- rg_rows _ _ _ =>
    let c1 := fresh "c" in let c2 := fresh "c" in let c3 := fresh "c" in let c4 := fresh "c" in let c5 := fresh "c" in
    let c6 := fresh "c" in let R1 := fresh "R" in let R2 := fresh "R" in let R3 := fresh "R" in let R4 := fresh "R" in
    let R5 := fresh "R" in let R6 := fresh "R" in let B := fresh "B" in
    destruct R as (c1 & c2 & c3 & c4 & c5 & c6 & R1 & R2 & R3 & R4 & R5 & R6 & B);
    exists c1, c2, c3, c4, c5, c6; do 6 (split; [solve [rdn_chain; assumption] |]); exact B
  end.
Ltac gasm := match goal with H : ?g |- ?g => exact H end.
Ltac gp :=
  lazymatch goal with
  | |- forall x : word, _ -> _ = _ =>
      let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
      repeat (rewrite wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia)); solve [eauto]
  | |- mem_grows _ _ => first [ ggrows | (eapply mem_grows_trans; [eassumption | ggrows]) ]
  | |- rdn _ _ _ _ = _ => try (unfold g_f3; rewrite if_negb); rdn_chain; try assumption
  | |- rg_rows _ _ _ => first [ solve [gasm] | growsc ]
  | |- getr _ _ = _ => greg
  | |- exists mk : word, _ => eexists; rdn_chain
  | |- true = false -> _ => let H := fresh in intro H; discriminate H
  | |- false = true -> _ => let H := fresh in intro H; discriminate H
  | |- true = true -> _ => intros _; gp
  | |- false = false -> _ => intros _; gp
  | |- true = true \/ _ -> _ => intros _; gp
  | |- false = true \/ false = false -> _ => intros _; gp
  | |- false = true \/ true = false -> _ => let H := fresh in intros [H | H]; discriminate H
  | |- _ /\ _ => first [ solve [assumption] | split; gp ]
  | |- _ => first [ solve [assumption] | lia ]
  end.

Ltac grows0 sy dpixh dy dh spixh :=
  unfold rg_rows; exists sy, sy, dpixh, dy, (dy + dh - dpixh)%Z, spixh;
  do 6 (split; [solve [rdn_chain] |]); do 6 (split; [lia |]); lia.

Ltac gleaf DX Cf6 Hfwr RFx Hsm RD RS :=
  let Efw := fresh "Efw" in
  destruct (g_fw DX) eqn:Efw;
  [ pose proof (Cf6 ltac:(first [exact Efw | reflexivity])) as Cf6';
    pose proof (Hfwr ltac:(first [exact Efw | reflexivity])) as (G15 & G25 & G26);
    pose proof (RFx ltac:(first [exact Efw | reflexivity]) Hsm RD RS) as RF';
    pose proof (g_fw_true DX Efw) as (Hnz & _);
    unfold rgs_out; cbn iota; gp
  | pose proof (g_fw_hang DX Efw) as Ehg0;
    assert (Hz : (DX mod 32 = 0)%Z) by (unfold g_fw in Efw; apply negb_false_iff, Z.eqb_eq in Efw; exact Efw);
    unfold rgs_out; cbn iota; gp ].

Lemma rgs_q4 : forall regs m m4 (s datad nd datas ns DX SX DW dy sy dh dwpl swpl : Z),
  (250000 <= s /\ s + 64 < 2 ^ 64)%Z ->
  (4096 <= datad /\ 0 < nd /\ datad + nd + 2 ^ 27 <= 2 ^ 64 /\ datad mod 4 = 0)%Z ->
  (4096 <= datas /\ 0 < ns /\ datas + ns + 2 ^ 27 <= 2 ^ 64 /\ datas mod 4 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true ->
  rdn SEGS m (Z_to_bv 64 RG_JT12) 4 = Some (Z_to_le_bytes 4 RG_JT12V) ->
  (forall x : word, (u x < s - 240 \/ s - 112 <= u x)%Z -> m4 x = m x) -> mem_grows m m4 ->
  rdn SEGS m4 (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m4 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rg_rows m4 s dh ->
  (g_fw DX = true -> rdn SEGS m4 (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if g_f6 DX SX then 1 else 0)))) ->
  (1 <= dh < 2 ^ 24)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  (0 <= DX < 2 ^ 30)%Z -> (0 <= SX < 2 ^ 30)%Z -> (1 <= DW < 2 ^ 30)%Z -> (0 <= dy * dwpl < 2 ^ 24)%Z -> (0 <= sy * swpl < 2 ^ 24)%Z ->
  (DX mod 32 <> SX mod 32)%Z -> (g_smax DX SX DW <= swpl - 1)%Z -> (DX + DW <= 32 * dwpl)%Z -> (g_hang DX <= DW)%Z ->
  (forall c nw i', 0 <= c -> 0 <= nw -> c + nw <= dwpl -> 0 <= i' < dh ->
      datad <= datad + 4 * (dy * dwpl) + 4 * c + 4 * dwpl * i' /\ datad + 4 * (dy * dwpl) + 4 * c + 4 * dwpl * i' + 4 * nw <= datad + nd)%Z ->
  (forall c nw i', 0 <= c -> 0 <= nw -> c + nw <= swpl -> 0 <= i' < dh ->
      datas <= datas + 4 * (sy * swpl) + 4 * c + 4 * swpl * i' /\ datas + 4 * (sy * swpl) + 4 * c + 4 * swpl * i' + 4 * nw <= datas + ns)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 1 = Z_to_bv 64 (DX mod 32) -> getr regs 5 = Z_to_bv 64 sy ->
  getr regs 7 = Z_to_bv 64 dy -> getr regs 8 = Z_to_bv 64 DW -> getr regs 9 = Z_to_bv 64 DW -> getr regs 10 = Z_to_bv 64 datad ->
  getr regs 11 = Z_to_bv 64 12 -> getr regs 13 = Z_to_bv 64 DX -> getr regs 14 = Z_to_bv 64 dwpl -> getr regs 19 = Z_to_bv 64 datas ->
  getr regs 20 = Z_to_bv 64 32 -> getr regs 21 = Z_to_bv 64 (g_hang DX) -> getr regs 23 = Z_to_bv 64 (g_hang DX) ->
  getr regs 24 = Z_to_bv 64 SX -> getr regs 29 = Z_to_bv 64 (g_sls DX SX) -> getr regs 30 = Z_to_bv 64 (g_sls DX SX) ->
  (g_fw DX = true -> getr regs 15 = Z_to_bv 64 (datas + 4 * (sy * swpl) + 4 * (SX / 32))
                     /\ getr regs 25 = Z_to_bv 64 (datad + 4 * (dy * dwpl) + 4 * (DX / 32))
                     /\ getr regs 26 = Z_to_bv 64 (if g_f7 SX DW then 1 else 0)) ->
  exists regs' M1 (nofull nolast f3 : bool) (nfw psF pdF psl pdl : Z),
    msteps SEGS (mkst regs RG_Q4 m4 rom) (mkst regs' RG_S1 M1 rom)
    /\ rgs_out m M1 regs' s datad nd datas ns dh dwpl swpl (g_fw DX) (g_f6 DX SX) (g_f7 SX DW) nofull nolast f3 (DX mod 32) (g_sls DX SX) nfw
         (datas + 4 * (sy * swpl) + 4 * (SX / 32)) (datad + 4 * (dy * dwpl) + 4 * (DX / 32)) psF pdF psl pdl
    /\ regs_agree (fun r : reg => In r [5; 6; 7; 8; 9; 10; 12; 13; 16; 17; 18; 20; 22; 23; 28]%list) regs regs'.
Proof.
  intros regs m m4 s datad nd datas ns DX SX DW dy sy dh dwpl swpl Hs Hdd Hds SOKf JT OUT4 GR4 Cdh Csw Crows Cf6
    Hdh Hsw Hdw HDX HSX HDW Hdyw Hsyw Hne Hsm Hw Hhd RD RS
    H2 H1 H5 H7 H8 H9 H10 H11 H13 H14 H19 H20 H21 H23 H24 H29 H30 Hfwr.
  pose proof (LeptRop2Arith.g_hang_range DX) as Hhg. pose proof (LeptRop2Arith.g_sls_range DX SX Hne) as Hsl.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)) as HmD. pose proof (Z.mod_pos_bound (DW + DX) 32 ltac:(lia)) as HmW.
  pose proof (g_col2 DX DW dwpl ltac:(lia) Hhd Hw) as (C0 & C1 & C2).
  assert (SOK4 : store_ok SEGS m4 (Z_to_bv 64 (s - 240)) 240 = true) by (eapply store_ok_mono; [exact GR4 | exact SOKf]).
  assert (JT4 : rdn SEGS m4 (Z_to_bv 64 RG_JT12) 4 = Some (Z_to_le_bytes 4 RG_JT12V)).
  { rewrite <- JT. unfold RG_JT12. apply rdn_ext; rewrite ?u_Z2bv by lia; [lia |]. intros x Hx. apply OUT4. lia. }
  pose proof (rgs_RF datad nd datas ns DX SX DW dy sy dh dwpl swpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hw) as RFx.
  assert (Hmk : (RG_MASKS + 264 <= s - 240)%Z) by (unfold RG_MASKS; lia).
  unfold g_lwb in *.
  destruct (Z_le_gt_dec 32 (DW - g_hang DX)) as [Hfull | Hnfull].
  -
    destruct (rgs_RW datad nd datas ns DX SX DW dy sy dh dwpl swpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hw Hfull Hsm RD RS)
      as (Hq1 & RWm & RWr).
    destruct (RWr 0%Z ltac:(lia)) as (W1 & W2 & W3 & W4).
    destruct (rg_Q4 true regs m4 s DX SX DW dy sy dwpl swpl datad datas ltac:(lia) ltac:(lia) HDX HSX ltac:(lia) Hhd
                ltac:(cbn iota; lia) ltac:(intros _; repeat split; lia) SOK4 Csw H2 H8 H21 H23 H13 H24 H7 H5 H14 H10 H19)
      as (r5 & S5 & E16 & E6 & AG5).
    cbn iota in S5. destruct (E6 eq_refl) as (E18 & E6'). clear E6.
    let M5 := lastmem S5 in
    assert (C5nf : rdn SEGS M5 (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ((DW - g_hang DX) / 32)))) by rdn_chain;
    assert (C5sw : rdn SEGS M5 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl))) by (rdn_chain; exact Csw);
    assert (SOK5 : store_ok SEGS M5 (Z_to_bv 64 (s - 240)) 240 = true) by gsok.
    destruct (Z.eq_dec ((DW + DX) mod 32) 0) as [Hl0 | Hl].
    +
      let M5 := lastmem S5 in
      destruct (rg_Q5 true r5 M5 s DX SX DW dy sy dwpl swpl datad datas ((DW - g_hang DX) / 32) (g_sls DX SX)
                  ltac:(lia) ltac:(lia) Hmk HDX HSX ltac:(lia) Hhd ltac:(lia) ltac:(lia) ltac:(unfold g_lwb; cbn iota; exact Hl0)
                  ltac:(intro X; discriminate X) SOK5 C5sw C5nf ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) E16
                  ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg))
        as (r6 & mk & S6 & F8 & F10 & _ & AG6).
      cbn iota in S6.
      let M6 := lastmem S6 in
      destruct (rg_Q6 r6 M6 s swpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RG_JT12 in *; rdn_chain; exact JT4)
                  ltac:(gsok) ltac:(rdn_chain; exact Csw) ltac:(greg) ltac:(greg))
        as (r7 & S7 & AG7).
      let M7 := lastmem S7 in
      exists r7, M7, false, true, true, ((DW - g_hang DX) / 32)%Z,
        (datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32))%Z, (datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32))%Z, 0%Z, 0%Z.
      split; [eapply msteps_trans; [exact S5 |]; eapply msteps_trans; [exact S6 | exact S7] |].
      split; [| eapply regs_agree_trans; [regs_agree_weaken AG5 |]; eapply regs_agree_trans; [regs_agree_weaken AG6 | regs_agree_weaken AG7]].
      gleaf DX Cf6 Hfwr RFx Hsm RD RS.
    +
      destruct (rgs_RL datad nd datas ns DX SX DW dy sy dh dwpl swpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hw Hhd
                  ltac:(unfold g_lwb; exact Hl) Hsm RD RS) as (RLm & RLr).
      destruct (RLr 0%Z ltac:(lia)) as (L1 & L2 & L3 & L4 & _).
      let M5 := lastmem S5 in
      destruct (rg_Q5 false r5 M5 s DX SX DW dy sy dwpl swpl datad datas ((DW - g_hang DX) / 32) (g_sls DX SX)
                  ltac:(lia) ltac:(lia) Hmk HDX HSX ltac:(lia) Hhd ltac:(lia) ltac:(lia) ltac:(unfold g_lwb; cbn iota; exact Hl)
                  ltac:(intros _; repeat split; lia) SOK5 C5sw C5nf ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) E16
                  ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg))
        as (r6 & mk & S6 & F8 & _ & F10 & AG6).
      cbn iota in S6. specialize (F10 eq_refl).
      let M6 := lastmem S6 in
      destruct (rg_Q6 r6 M6 s swpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RG_JT12 in *; rdn_chain; exact JT4)
                  ltac:(gsok) ltac:(rdn_chain; exact Csw) ltac:(greg) ltac:(greg))
        as (r7 & S7 & AG7).
      let M7 := lastmem S7 in
      exists r7, M7, false, false, (g_f3 DX SX DW), ((DW - g_hang DX) / 32)%Z,
        (datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32))%Z, (datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32))%Z,
        (datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32))%Z,
        (datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32))%Z.
      split; [eapply msteps_trans; [exact S5 |]; eapply msteps_trans; [exact S6 | exact S7] |].
      split; [| eapply regs_agree_trans; [regs_agree_weaken AG5 |]; eapply regs_agree_trans; [regs_agree_weaken AG6 | regs_agree_weaken AG7]].
      gleaf DX Cf6 Hfwr RFx Hsm RD RS.
  -
    assert (Eq0 : ((DW - g_hang DX) / 32 = 0)%Z) by (apply Z.div_small; lia).
    destruct (rg_Q4 false regs m4 s DX SX DW dy sy dwpl swpl datad datas ltac:(lia) ltac:(lia) HDX HSX ltac:(lia) Hhd
                ltac:(cbn iota; lia) ltac:(intro X; discriminate X) SOK4 Csw H2 H8 H21 H23 H13 H24 H7 H5 H14 H10 H19)
      as (r5 & S5 & E16 & _ & AG5).
    cbn iota in S5.
    let M5 := lastmem S5 in
    assert (C5nf : rdn SEGS M5 (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by rdn_chain;
    assert (C5sw : rdn SEGS M5 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl))) by (rdn_chain; exact Csw);
    assert (SOK5 : store_ok SEGS M5 (Z_to_bv 64 (s - 240)) 240 = true) by gsok.
    destruct (Z.eq_dec ((DW + DX) mod 32) 0) as [Hl0 | Hl].
    +
      let M5 := lastmem S5 in
      destruct (rg_Q5 true r5 M5 s DX SX DW dy sy dwpl swpl datad datas 0 (g_sls DX SX)
                  ltac:(lia) ltac:(lia) Hmk HDX HSX ltac:(lia) Hhd ltac:(lia) ltac:(lia) ltac:(unfold g_lwb; cbn iota; exact Hl0)
                  ltac:(intro X; discriminate X) SOK5 C5sw C5nf ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) E16
                  ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg))
        as (r6 & mk & S6 & F8 & F10 & _ & AG6).
      cbn iota in S6.
      let M6 := lastmem S6 in
      destruct (rg_Q6 r6 M6 s swpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RG_JT12 in *; rdn_chain; exact JT4)
                  ltac:(gsok) ltac:(rdn_chain; exact Csw) ltac:(greg) ltac:(greg))
        as (r7 & S7 & AG7).
      let M7 := lastmem S7 in
      exists r7, M7, true, true, true, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z.
      split; [eapply msteps_trans; [exact S5 |]; eapply msteps_trans; [exact S6 | exact S7] |].
      split; [| eapply regs_agree_trans; [regs_agree_weaken AG5 |]; eapply regs_agree_trans; [regs_agree_weaken AG6 | regs_agree_weaken AG7]].
      gleaf DX Cf6 Hfwr RFx Hsm RD RS.
    +
      destruct (rgs_RL datad nd datas ns DX SX DW dy sy dh dwpl swpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hw Hhd
                  ltac:(unfold g_lwb; exact Hl) Hsm RD RS) as (RLm & RLr).
      rewrite Eq0 in RLm, RLr.
      destruct (RLr 0%Z ltac:(lia)) as (L1 & L2 & L3 & L4 & _).
      let M5 := lastmem S5 in
      destruct (rg_Q5 false r5 M5 s DX SX DW dy sy dwpl swpl datad datas 0 (g_sls DX SX)
                  ltac:(lia) ltac:(lia) Hmk HDX HSX ltac:(lia) Hhd ltac:(lia) ltac:(lia) ltac:(unfold g_lwb; cbn iota; exact Hl)
                  ltac:(intros _; repeat split; lia) SOK5 C5sw C5nf ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) E16
                  ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg))
        as (r6 & mk & S6 & F8 & _ & F10 & AG6).
      cbn iota in S6. specialize (F10 eq_refl).
      let M6 := lastmem S6 in
      destruct (rg_Q6 r6 M6 s swpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RG_JT12 in *; rdn_chain; exact JT4)
                  ltac:(gsok) ltac:(rdn_chain; exact Csw) ltac:(greg) ltac:(greg))
        as (r7 & S7 & AG7).
      let M7 := lastmem S7 in
      exists r7, M7, true, false, (g_f3 DX SX DW), 0%Z, 0%Z, 0%Z,
        (datas + 4 * (sy * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * 0)%Z,
        (datad + 4 * (dy * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * 0)%Z.
      split; [eapply msteps_trans; [exact S5 |]; eapply msteps_trans; [exact S6 | exact S7] |].
      split; [| eapply regs_agree_trans; [regs_agree_weaken AG5 |]; eapply regs_agree_trans; [regs_agree_weaken AG6 | regs_agree_weaken AG7]].
      gleaf DX Cf6 Hfwr RFx Hsm RD RS.
Qed.

Lemma rgs_out_fin : forall (m M1 : word -> option byte) (regs' : bvmap 5 word) (s datad nd datas ns dh dwpl swpl : Z)
  (fw f6 f7 nofull nolast f3 : bool) (dxb sls nfw psf pdf psF pdF psl pdl : Z),
  store_ok SEGS m (Z_to_bv 64 datad) (Z.to_nat nd) = true -> store_ok SEGS m (Z_to_bv 64 datas) (Z.to_nat ns) = true ->
  rgs_out m M1 regs' s datad nd datas ns dh dwpl swpl fw f6 f7 nofull nolast f3 dxb sls nfw psf pdf psF pdF psl pdl ->
    (forall x : word, (u x < s - 240 \/ s - 112 <= u x)%Z -> M1 x = m x) /\ mem_grows m M1
    /\ store_ok SEGS M1 (Z_to_bv 64 datad) (Z.to_nat nd) = true /\ store_ok SEGS M1 (Z_to_bv 64 datas) (Z.to_nat ns) = true
    /\ (1 <= dh < 2 ^ 24 /\ 0 <= swpl < 2 ^ 24 /\ 0 <= dwpl < 2 ^ 24 /\ 1 <= sls <= 31 /\ 0 <= nfw < 2 ^ 26)%Z
    /\ ((0 <= dxb < 32)%Z /\ (if fw then dxb <> 0 else dxb = 0)%Z)
    /\ (nofull = false -> (1 <= nfw)%Z)
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 216)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nolast then 1 else 0)))
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nofull then 1 else 0)))
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl))
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh))
    /\ (fw = true \/ nolast = false -> rg_rows M1 s dh)
    /\ (fw = true -> rdn SEGS M1 (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f6 then 1 else 0))))
    /\ (nofull = false -> rdn SEGS M1 (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)))
    /\ (nolast = false -> rdn SEGS M1 (Z_to_bv 64 (s - 232)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f3 then 1 else 0))))
    /\ (nolast = false -> rdn SEGS M1 (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)))
    /\ (nolast = false -> exists mk : word, rdn SEGS M1 (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk))
    /\ (fw = true -> (psf mod 4 = 0 /\ pdf mod 4 = 0)%Z /\
          (forall i, 0 <= i < dh -> datad <= pdf + 4 * dwpl * i /\ pdf + 4 * dwpl * i + 4 <= datad + nd /\
                                    datas <= psf + 4 * swpl * i /\ psf + 4 * swpl * i + 4 + (if f6 && negb f7 then 4 else 0) <= datas + ns)%Z)
    /\ (nofull = false -> (psF mod 4 = 0 /\ pdF mod 4 = 0)%Z /\
          (forall i, 0 <= i < dh -> datad <= pdF + 4 * dwpl * i /\ pdF + 4 * dwpl * i + 4 * nfw <= datad + nd /\
                                    datas <= psF + 4 * swpl * i /\ psF + 4 * swpl * i + 4 * nfw + 4 <= datas + ns)%Z)
    /\ (nolast = false -> (psl mod 4 = 0 /\ pdl mod 4 = 0)%Z /\
          (forall i, 0 <= i < dh -> datad <= pdl + 4 * dwpl * i /\ pdl + 4 * dwpl * i + 4 <= datad + nd /\
                                    datas <= psl + 4 * swpl * i /\ psl + 4 * swpl * i + 4 + (if f3 then 0 else 4) <= datas + ns)%Z)
    /\ getr regs' 2 = Z_to_bv 64 (s - 240) /\ getr regs' 1 = Z_to_bv 64 dxb /\ getr regs' 14 = Z_to_bv 64 dwpl
    /\ getr regs' 30 = Z_to_bv 64 sls /\ getr regs' 8 = Z_to_bv 64 (32 - sls)
    /\ (fw = true -> getr regs' 15 = Z_to_bv 64 psf /\ getr regs' 25 = Z_to_bv 64 pdf /\ getr regs' 26 = Z_to_bv 64 (if f7 then 1 else 0))
    /\ (nofull = false -> getr regs' 6 = Z_to_bv 64 psF /\ getr regs' 18 = Z_to_bv 64 pdF)
    /\ (nolast = false -> getr regs' 10 = Z_to_bv 64 pdl).
Proof.
  intros m M1 regs' s datad nd datas ns dh dwpl swpl fw f6 f7 nofull nolast f3 dxb sls nfw psf pdf psF pdF psl pdl SKd SKs O.
  unfold rgs_out in O.
  destruct O as (OUT & GR & GEO & DXB & NF & C1 & C2 & C3 & C4 & C5 & ROWS & CF6 & CNFW & CF3 & CPSL & CMK & RF & RW & RL
                 & G2 & G1 & G14 & G30 & G8 & GF & GN & GL).
  split; [exact OUT |]. split; [exact GR |].
  split; [eapply store_ok_mono; [exact GR | exact SKd] |].
  split; [eapply store_ok_mono; [exact GR | exact SKs] |].
  split; [exact GEO |]. split; [exact DXB |]. split; [exact NF |].
  split; [exact C1 |]. split; [exact C2 |]. split; [exact C3 |]. split; [exact C4 |]. split; [exact C5 |].
  split; [exact ROWS |]. split; [exact CF6 |]. split; [exact CNFW |]. split; [exact CF3 |]. split; [exact CPSL |].
  split; [exact CMK |].
  split.
  { intros Hf. destruct (RF Hf) as (Ha & Hb). split; [exact Ha |]. intros i Hi.
    destruct (Hb i Hi) as (B1 & B2 & B3 & B4 & B5). split; [exact B1 |]. split; [exact B2 |]. split; [exact B3 |].
    destruct f6, f7; cbn [andb negb]; try lia; specialize (B5 eq_refl eq_refl); lia. }
  split; [exact RW |].
  split.
  { intros Hl. destruct (RL Hl) as (Ha & Hb). split; [exact Ha |]. intros i Hi.
    destruct (Hb i Hi) as (B1 & B2 & B3 & B4 & B5). split; [exact B1 |]. split; [exact B2 |]. split; [exact B3 |].
    destruct f3; cbn [andb negb]; try lia; specialize (B5 eq_refl); lia. }
  exact (conj G2 (conj G1 (conj G14 (conj G30 (conj G8 (conj GF (conj GN GL))))))).
Qed.

Lemma rg_setup : forall regs m (s datad nd datas ns DX SX DW dy sy dh dwpl swpl dpixh spixh : Z),
  (250000 <= s /\ s + 64 < 2 ^ 64)%Z ->
  (4096 <= datad /\ 0 < nd /\ datad + nd + 2 ^ 27 <= 2 ^ 64 /\ datad mod 4 = 0)%Z ->
  (4096 <= datas /\ 0 < ns /\ datas + ns + 2 ^ 27 <= 2 ^ 64 /\ datas mod 4 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 datad) (Z.to_nat nd) = true ->
  store_ok SEGS m (Z_to_bv 64 datas) (Z.to_nat ns) = true ->
  disj_apart datad nd (s - 240) 240 ->
  store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true ->
  rdn SEGS m (Z_to_bv 64 RG_JT12) 4 = Some (Z_to_le_bytes 4 RG_JT12V) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  (1 <= dh < 2 ^ 24)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  (0 <= DX < 2 ^ 30)%Z -> (0 <= SX < 2 ^ 30)%Z -> (1 <= DW < 2 ^ 30)%Z -> (0 <= dy * dwpl < 2 ^ 24)%Z -> (0 <= sy * swpl < 2 ^ 24)%Z ->
  (DX mod 32 <> SX mod 32)%Z -> (g_smax DX SX DW <= swpl - 1)%Z -> (DX + DW <= 32 * dwpl)%Z ->
  (0 <= dy)%Z -> (0 <= sy)%Z -> (dy + dh <= dpixh < 2 ^ 24)%Z -> (sy + dh <= spixh < 2 ^ 24)%Z ->
  (forall c nw i', 0 <= c -> 0 <= nw -> c + nw <= dwpl -> 0 <= i' < dh ->
      datad <= datad + 4 * (dy * dwpl) + 4 * c + 4 * dwpl * i' /\ datad + 4 * (dy * dwpl) + 4 * c + 4 * dwpl * i' + 4 * nw <= datad + nd)%Z ->
  (forall c nw i', 0 <= c -> 0 <= nw -> c + nw <= swpl -> 0 <= i' < dh ->
      datas <= datas + 4 * (sy * swpl) + 4 * c + 4 * swpl * i' /\ datas + 4 * (sy * swpl) + 4 * c + 4 * swpl * i' + 4 * nw <= datas + ns)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 1 = Z_to_bv 64 sy -> getr regs 5 = Z_to_bv 64 sy -> getr regs 6 = Z_to_bv 64 swpl ->
  getr regs 7 = Z_to_bv 64 dy -> getr regs 8 = Z_to_bv 64 DW -> getr regs 9 = Z_to_bv 64 DW -> getr regs 10 = Z_to_bv 64 datad ->
  getr regs 11 = Z_to_bv 64 12 -> getr regs 13 = Z_to_bv 64 DX -> getr regs 14 = Z_to_bv 64 dwpl -> getr regs 16 = Z_to_bv 64 dy ->
  getr regs 18 = Z_to_bv 64 (dy + dh - dpixh) -> getr regs 19 = Z_to_bv 64 datas -> getr regs 23 = Z_to_bv 64 dpixh ->
  getr regs 24 = Z_to_bv 64 SX -> getr regs 25 = Z_to_bv 64 DX -> getr regs 26 = Z_to_bv 64 sy -> getr regs 27 = Z_to_bv 64 SX ->
  getr regs 28 = Z_to_bv 64 spixh ->
  exists regs' M1 (fw f6 f7 nofull nolast f3 : bool) (dxb sls nfw psf pdf psF pdF psl pdl : Z),
    msteps SEGS (mkst regs RG_P0 m rom) (mkst regs' RG_S1 M1 rom)
    /\ regs_agree (fun r : reg => In r [1; 5; 6; 7; 8; 9; 10; 12; 13; 15; 16; 17; 18; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'
    /\ (forall x : word, (u x < s - 240 \/ s - 112 <= u x)%Z -> M1 x = m x) /\ mem_grows m M1
    /\ store_ok SEGS M1 (Z_to_bv 64 datad) (Z.to_nat nd) = true /\ store_ok SEGS M1 (Z_to_bv 64 datas) (Z.to_nat ns) = true
    /\ (1 <= dh < 2 ^ 24 /\ 0 <= swpl < 2 ^ 24 /\ 0 <= dwpl < 2 ^ 24 /\ 1 <= sls <= 31 /\ 0 <= nfw < 2 ^ 26)%Z
    /\ ((0 <= dxb < 32)%Z /\ (if fw then dxb <> 0 else dxb = 0)%Z)
    /\ (nofull = false -> (1 <= nfw)%Z)
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 216)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nolast then 1 else 0)))
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nofull then 1 else 0)))
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl))
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn SEGS M1 (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh))
    /\ (fw = true \/ nolast = false -> rg_rows M1 s dh)
    /\ (fw = true -> rdn SEGS M1 (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f6 then 1 else 0))))
    /\ (nofull = false -> rdn SEGS M1 (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)))
    /\ (nolast = false -> rdn SEGS M1 (Z_to_bv 64 (s - 232)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f3 then 1 else 0))))
    /\ (nolast = false -> rdn SEGS M1 (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)))
    /\ (nolast = false -> exists mk : word, rdn SEGS M1 (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk))
    /\ (fw = true -> (psf mod 4 = 0 /\ pdf mod 4 = 0)%Z /\
          (forall i, 0 <= i < dh -> datad <= pdf + 4 * dwpl * i /\ pdf + 4 * dwpl * i + 4 <= datad + nd /\
                                    datas <= psf + 4 * swpl * i /\ psf + 4 * swpl * i + 4 + (if f6 && negb f7 then 4 else 0) <= datas + ns)%Z)
    /\ (nofull = false -> (psF mod 4 = 0 /\ pdF mod 4 = 0)%Z /\
          (forall i, 0 <= i < dh -> datad <= pdF + 4 * dwpl * i /\ pdF + 4 * dwpl * i + 4 * nfw <= datad + nd /\
                                    datas <= psF + 4 * swpl * i /\ psF + 4 * swpl * i + 4 * nfw + 4 <= datas + ns)%Z)
    /\ (nolast = false -> (psl mod 4 = 0 /\ pdl mod 4 = 0)%Z /\
          (forall i, 0 <= i < dh -> datad <= pdl + 4 * dwpl * i /\ pdl + 4 * dwpl * i + 4 <= datad + nd /\
                                    datas <= psl + 4 * swpl * i /\ psl + 4 * swpl * i + 4 + (if f3 then 0 else 4) <= datas + ns)%Z)
    /\ getr regs' 2 = Z_to_bv 64 (s - 240) /\ getr regs' 1 = Z_to_bv 64 dxb /\ getr regs' 14 = Z_to_bv 64 dwpl
    /\ getr regs' 30 = Z_to_bv 64 sls /\ getr regs' 8 = Z_to_bv 64 (32 - sls)
    /\ (fw = true -> getr regs' 15 = Z_to_bv 64 psf /\ getr regs' 25 = Z_to_bv 64 pdf /\ getr regs' 26 = Z_to_bv 64 (if f7 then 1 else 0))
    /\ (nofull = false -> getr regs' 6 = Z_to_bv 64 psF /\ getr regs' 18 = Z_to_bv 64 pdF)
    /\ (nolast = false -> getr regs' 10 = Z_to_bv 64 pdl).
Proof.
  intros regs m s datad nd datas ns DX SX DW dy sy dh dwpl swpl dpixh spixh Hs Hdd Hds SOKd SOKs FR SOKf JT Cdh
    Hdh Hsw Hdw HDX HSX HDW Hdyw Hsyw Hne Hsm Hw Hdy Hsy Hdp Hsp RD RS
    H2 H1 H5 H6 H7 H8 H9 H10 H11 H13 H14 H16 H18 H19 H23 H24 H25 H26 H27 H28.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)) as HmD.
  pose proof (LeptRop2Arith.g_sls_range DX SX Hne) as Hsl.
  pose proof (LeptRop2Arith.g_hang_range DX) as Hhg.
  destruct (rg_P0 regs m s DX SX ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hne SOKf H2 H25 H27) as (r1 & S1 & E1 & E12 & AG1).
  rewrite H6, H1, H26, H16, H28, H18, H23 in S1.
  let M1 := lastmem S1 in
  assert (ROWS1 : rg_rows M1 s dh).
  { unfold rg_rows. exists sy, sy, dpixh, dy, (dy + dh - dpixh)%Z, spixh.
    do 6 (split; [solve [rdn_chain] |]). do 6 (split; [lia |]). lia. }
  let M1 := lastmem S1 in
  destruct (rg_Q1 r1 M1 DX SX ltac:(lia) ltac:(lia) Hne E1 E12) as (r2 & S2 & F23 & F21 & F20 & F17 & F29 & F30 & F16 & F15 & AG2).
  destruct (Z.eq_dec (DX mod 32) 0) as [Hz | Hnz].
  - assert (Efw : g_fw DX = false) by (unfold g_fw; rewrite Hz; reflexivity).
    pose proof (g_fw_hang DX Efw) as Eh.
    let M1 := lastmem S1 in
    destruct (rg_Q3b r2 M1 DX ltac:(lia) Hz ltac:(greg)) as (r3 & S3 & G15 & G25 & G21 & G27 & AG3).
    let M1 := lastmem S1 in
    destruct (rgs_q4 r3 m M1 s datad nd datas ns DX SX DW dy sy dh dwpl swpl Hs Hdd Hds SOKf JT
                ltac:(gp) ltac:(gp) ltac:(rdn_chain; exact Cdh) ltac:(rdn_chain) ROWS1 ltac:(rewrite Efw; intro X; discriminate X)
                Hdh Hsw Hdw HDX HSX HDW Hdyw Hsyw Hne Hsm Hw ltac:(rewrite Eh; lia) RD RS
                ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg)
                ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(rewrite Eh; greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg)
                ltac:(rewrite Efw; intro X; discriminate X))
      as (r4 & M4 & nofull & nolast & f3 & nfw & psF & pdF & psl & pdl & S4 & O4 & AG4).
    exists r4, M4, (g_fw DX), (g_f6 DX SX), (g_f7 SX DW), nofull, nolast, f3, (DX mod 32)%Z, (g_sls DX SX), nfw,
      (datas + 4 * (sy * swpl) + 4 * (SX / 32))%Z, (datad + 4 * (dy * dwpl) + 4 * (DX / 32))%Z, psF, pdF, psl, pdl.
    split; [eapply msteps_trans; [exact S1 |]; eapply msteps_trans; [exact S2 |]; eapply msteps_trans; [exact S3 | exact S4] |].
    split; [eapply regs_agree_trans; [regs_agree_weaken AG1 |]; eapply regs_agree_trans; [regs_agree_weaken AG2 |];
            eapply regs_agree_trans; [regs_agree_weaken AG3 | regs_agree_weaken AG4] |].
    eapply rgs_out_fin; [exact SOKd | exact SOKs | exact O4].
  - assert (Efw : g_fw DX = true) by (unfold g_fw; apply negb_true_iff, Z.eqb_neq; exact Hnz).
    pose proof (g_fw_true DX Efw) as (_ & Eh).
    destruct (rgs_RF datad nd datas ns DX SX DW dy sy dh dwpl swpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hw Efw Hsm RD RS)
      as (RFm & RFr).
    destruct (RFr 0%Z ltac:(lia)) as (K1 & K2 & K3 & K4 & _).
    let M1 := lastmem S1 in
    destruct (rg_Q2 r2 M1 s DX SX DW dy sy dwpl swpl datad datas ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hnz
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(gsok) ltac:(rdn_chain)
                ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg)
                ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg))
      as (r3 & S3 & G25 & G15 & G26 & AG3).
    destruct (Z_lt_ge_dec DW (32 - DX mod 32)) as [Hdpc | Hndp].
    + let M2 := lastmem S3 in
      destruct (rg_Q3 r3 M2 s DX SX DW ltac:(lia) ltac:(lia) ltac:(unfold RG_MASKS; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hnz Hdpc Hne
                  ltac:(gsok) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg))
        as (r4 & S4 & G8 & G10 & AG4).
      let M3 := lastmem S4 in
      destruct (rg_Q6 r4 M3 s swpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RG_JT12 in *; rdn_chain; exact JT)
                  ltac:(gsok) ltac:(rdn_chain) ltac:(greg) ltac:(greg))
        as (r5 & S5 & AG5).
      let M5 := lastmem S5 in
      exists r5, M5, true, (g_f6 DX SX), (g_f7 SX DW), true, true, false, (DX mod 32)%Z, (g_sls DX SX), 0%Z,
        (datas + 4 * (sy * swpl) + 4 * (SX / 32))%Z, (datad + 4 * (dy * dwpl) + 4 * (DX / 32))%Z, 0%Z, 0%Z, 0%Z, 0%Z.
      split; [eapply msteps_trans; [exact S1 |]; eapply msteps_trans; [exact S2 |]; eapply msteps_trans; [exact S3 |];
              eapply msteps_trans; [exact S4 | exact S5] |].
      split; [eapply regs_agree_trans; [regs_agree_weaken AG1 |]; eapply regs_agree_trans; [regs_agree_weaken AG2 |];
              eapply regs_agree_trans; [regs_agree_weaken AG3 |]; eapply regs_agree_trans; [regs_agree_weaken AG4 | regs_agree_weaken AG5] |].
      refine (rgs_out_fin m _ r5 s datad nd datas ns dh dwpl swpl true (g_f6 DX SX) (g_f7 SX DW) true true false
                (DX mod 32)%Z (g_sls DX SX) 0%Z _ _ 0%Z 0%Z 0%Z 0%Z SOKd SOKs _).
      let M5 := lastmem S5 in
      assert (ROWS5 : rg_rows M5 s dh) by (grows0 sy dpixh dy dh spixh).
      clear ROWS1.
      unfold rgs_out; cbn iota; gp.
    + let M2 := lastmem S3 in
      destruct (rg_Q3n r3 M2 DX DW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(greg) ltac:(greg)) as (r4 & S4 & AG4).
      let M2 := lastmem S3 in
      destruct (rgs_q4 r4 m M2 s datad nd datas ns DX SX DW dy sy dh dwpl swpl Hs Hdd Hds SOKf JT
                  ltac:(gp) ltac:(gp) ltac:(rdn_chain; exact Cdh) ltac:(rdn_chain) ltac:(grows0 sy dpixh dy dh spixh) ltac:(intros _; rdn_chain)
                  Hdh Hsw Hdw HDX HSX HDW Hdyw Hsyw Hne Hsm Hw ltac:(rewrite Eh; lia) RD RS
                  ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg)
                  ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(rewrite Eh; greg) ltac:(greg) ltac:(greg) ltac:(greg) ltac:(greg)
                  ltac:(intros _; split; [greg | split; greg]))
        as (r5 & M5 & nofull & nolast & f3 & nfw & psF & pdF & psl & pdl & S5 & O5 & AG5).
      exists r5, M5, (g_fw DX), (g_f6 DX SX), (g_f7 SX DW), nofull, nolast, f3, (DX mod 32)%Z, (g_sls DX SX), nfw,
        (datas + 4 * (sy * swpl) + 4 * (SX / 32))%Z, (datad + 4 * (dy * dwpl) + 4 * (DX / 32))%Z, psF, pdF, psl, pdl.
      split; [eapply msteps_trans; [exact S1 |]; eapply msteps_trans; [exact S2 |]; eapply msteps_trans; [exact S3 |];
              eapply msteps_trans; [exact S4 | exact S5] |].
      split; [eapply regs_agree_trans; [regs_agree_weaken AG1 |]; eapply regs_agree_trans; [regs_agree_weaken AG2 |];
              eapply regs_agree_trans; [regs_agree_weaken AG3 |]; eapply regs_agree_trans; [regs_agree_weaken AG4 | regs_agree_weaken AG5] |].
      eapply rgs_out_fin; [exact SOKd | exact SOKs | exact O5].
Qed.

End Gset.
