(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV FPStepsB Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith GrayLib DitherLib DitherLoop LeptExec LeptExecFP LeptExecX LeptExecB LeptFPB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpReal FpBound FpSiteB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2_code_bilateralApply.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
#[local] Opaque RiscvSemantics.store_ok.

Ltac cellz regs HK Hlf off n a z :=
  let C := fresh "C" in
  exB_cell HK Hlf (EVar 32) off n a z C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact C.

Lemma v_divw_1 : forall x, (0 <= x < 2 ^ 31)%Z -> v_divw (Z_to_bv 64 x) (Z_to_bv 64 1) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold v_divw. rewrite !u_Z2bv by lia. rewrite (wrap32_small 1) by lia.
  replace (1 =? 0)%Z with false by reflexivity.
  rewrite (swrap32_small x) by lia. rewrite (swrap32_small 1) by lia. rewrite Z.quot_1_r. rewrite (swrap32_small x) by lia. reflexivity.
Qed.
Lemma zb_divw1 : forall a, (0 <= a < 2 ^ 31)%Z -> sext 64 (mul_div M_DIV (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 a.
Proof. intros a Ha. rewrite w_divw. apply v_divw_1; exact Ha. Qed.
Lemma zb_add : forall a b : Z, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. exact ex_ptr_val. Qed.
Lemma zb_mul : forall a b : Z, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof. intros a b. rewrite m_mul. apply zbv_mul. Qed.
Lemma zb_mulw : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> (0 <= a * b < 2 ^ 31)%Z ->
  sext 64 (mul_div M_MUL (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 b))) = Z_to_bv 64 (a * b).
Proof. intros a b Ha Hb Hab. rewrite w_mulw. apply zbv_mulw_small; lia. Qed.
Lemma zb_addw : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> (0 <= a + b < 2 ^ 31)%Z ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 b))) = Z_to_bv 64 (a + b).
Proof. intros a b Ha Hb Hab. rewrite w_addw. apply zbv_addw_small; lia. Qed.
Lemma zb_sltu1 : forall a b, (0 <= a < b)%Z -> (b < 2 ^ 64)%Z -> alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof.
  intros a b Hab Hb. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite !u_Z2bv by lia.
  replace (a <? b)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma zb_sltu0 : forall a b, (0 <= b <= a)%Z -> (a < 2 ^ 64)%Z -> alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof. intros a b Hab Ha. rewrite alu_sltu. apply zbv_sltu_ge; lia. Qed.
Lemma zb_slt0 : forall a b, (0 <= b <= a)%Z -> (a < 2 ^ 63)%Z -> alu64 ALU_SLT (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
  intros a b Hab Ha. rewrite alu_slt. unfold v_slt, c_lts, bv_lts. rewrite !bv_signed_Zs by lia.
  replace (a <? b)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma zb_xor3 : forall a, (0 <= a < 2 ^ 64)%Z -> alu64 ALU_XOR (Z_to_bv 64 a) (Z_to_bv 64 3) = Z_to_bv 64 (Z.lxor a 3).
Proof. intros a Ha. rewrite alu_xor. unfold v_xor. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma rb_zx : forall (M : word -> option byte) (a b : Z) (n : nat) (z : Z), a = b ->
  rdn Ubsan.M.loaded_segments M (Z_to_bv 64 b) n = Some (Z_to_le_bytes n z) -> (0 <= z < 2 ^ (8 * Z.of_nat n))%Z ->
  exists bs, rdn Ubsan.M.loaded_segments M (Z_to_bv 64 a) n = Some bs /\ Z_to_bv 64 (extz false n (bytes_le_to_Z bs)) = Z_to_bv 64 z.
Proof.
  intros M a b n z -> R Hz. exists (Z_to_le_bytes n z). split; [exact R|].
  unfold extz. rewrite bytes_le_Z_to_le by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma rb_sx4 : forall (M : word -> option byte) (a b : Z) (z : Z), a = b ->
  rdn Ubsan.M.loaded_segments M (Z_to_bv 64 b) 4 = Some (Z_to_le_bytes 4 z) -> (0 <= z < 2 ^ 31)%Z ->
  exists bs, rdn Ubsan.M.loaded_segments M (Z_to_bv 64 a) 4 = Some bs /\ Z_to_bv 64 (extz true 4 (bytes_le_to_Z bs)) = Z_to_bv 64 z.
Proof.
  intros M a b z -> R Hz. exists (Z_to_le_bytes 4 z). split; [exact R|].
  unfold extz. rewrite bytes_le_Z_to_le by lia. rewrite Z.mod_small by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  change (8 * N.of_nat 4)%N with 32%N. rewrite swrap32_small by lia. reflexivity.
Qed.

Ltac zb_norm :=
  repeat first [ rewrite zb_add | rewrite zb_mul | rewrite zb_mulw by lia | rewrite zb_addw by lia | rewrite zb_divw1 by lia
               | rewrite zb_sltu1 by lia | rewrite zb_sltu0 by lia | rewrite zb_slt0 by lia | rewrite zb_xor3 by lia
               | rewrite ext_val_sx_id by (first [ lia | (rewrite ?u_Z2bv by lia; ex_pow2; lia) ])
               | rewrite ext_val_zx_id by (rewrite ?u_Z2bv by lia; ex_pow2; lia) ].
Ltac zb_br := zb_norm; first [ ex_br | (vm_compute; reflexivity) ].
Ltac rb_tac :=
  zb_norm; rewrite ?zbv_addi;
  first [ (eapply rb_sx4; [ | eassumption | ]; [ lia | lia ])
        | (eapply rb_zx; [ | eassumption | ]; [ lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ]) ].
Ltac xreg regs HR' :=
  lazymatch goal with
  | |- getr _ ?k = _ =>
      rewrite (reg_val _ _ _ k HR');
      match goal with |- context [sr_get ?sr k] => let e := eval vm_compute in (sr_get sr k) in change (sr_get sr k) with e end;
      ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
      repeat match goal with H : getr regs _ = _ |- _ => rewrite H end;
      zb_norm; first [ reflexivity | (f_equal; lia) ]
  end.

Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma ap_B2 : forall (fx : FPState) regs (m : word -> option byte) (s pixd datas wpl datad : Z),
  (4096 + 160 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (4096 <= datas < 2 ^ 64)%Z -> (4096 <= datad < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z -> (0 <= wpl < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 datas ->
  getr regs 18 = Z_to_bv 64 wpl -> getr regs 19 = Z_to_bv 64 datad ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3a650) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x3a6a0) M' rom /\
      rinv [((s - 160)%Z, 16%Z); ((s - 136)%Z, 24%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixd) /\
      rdn SEGS M' (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wpl) /\
      rdn SEGS M' (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 0) /\
      rdn SEGS M' (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 datad) /\
      rdn SEGS M' (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 datas) /\
      getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1 /\
      getr regs' 14 = Z_to_bv 64 1 /\ getr regs' 15 = Z_to_bv 64 3 /\
      regs_agree (fun r => In r [11; 12; 13; 14; 15]%list) regs regs').
Proof.
  intros fx regs m s pixd datas wpl datad Hs As Hds Hdd Hpd Hw SOK H2 H8 H9 H18 H19.
  assert (As' : ((s - 160) mod 16 = 0)%Z) by (rewrite Zminus_mod, As; reflexivity).
  ex_entry regs [(s - 160)%Z; pixd; datas; wpl; datad] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 160)%Z; pixd; datas; wpl; datad]) m
    [KWr (SA (EVar 32) 0) 160; KAlign (EVar 32) 16; KRange (EVar 32) 4096 (2 ^ 47);
     KRange (EVar 34) 4096 (2 ^ 64 - 1); KRange (EVar 36) 4096 (2 ^ 64 - 1)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 100%nat [0x3a6a0%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 160)%Z, 16%Z); ((s - 136)%Z, 24%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (ex_reg regs HR); try (ex_agree HRo HR).
  - cellz regs HK Hlf 0%Z 8%nat (s - 160)%Z pixd.
  - cellz regs HK Hlf 8%Z 8%nat (s - 152)%Z wpl.
  - cellz regs HK Hlf 24%Z 8%nat (s - 136)%Z 0%Z.
  - cellz regs HK Hlf 32%Z 8%nat (s - 128)%Z datad.
  - cellz regs HK Hlf 40%Z 8%nat (s - 120)%Z datas.
  - apply zbv_snez; lia.
  - apply zbv_snez; lia.
Qed.

Lemma ap_row : forall (fx : FPState) regs (m : word -> option byte) (s datas dd wpl h w i : Z),
  (4096 + 160 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (0 <= i < h)%Z -> (h <= 20000)%Z -> (0 <= wpl <= 20000)%Z -> (1 <= w < 2 ^ 31)%Z ->
  (4096 <= datas)%Z -> (datas + 4 * wpl * h <= 2 ^ 47)%Z -> (4096 <= dd)%Z -> (dd + 4 * wpl * h <= 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 wpl) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 (i * wpl)) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 dd) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 datas) ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 11 = Z_to_bv 64 (i * wpl) -> getr regs 12 = Z_to_bv 64 i ->
  getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 3 ->
  getr regs 18 = Z_to_bv 64 wpl -> getr regs 22 = Z_to_bv 64 1 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3a6a0) m rom)
    (fun fin => exists regs', fin = @mkst fx regs' (Z_to_bv 64 0x3a75c) m rom /\
      getr regs' 5 = Z_to_bv 64 0 /\ getr regs' 6 = Z_to_bv 64 0 /\
      getr regs' 7 = Z_to_bv 64 (datas + 4 * wpl * i) /\ getr regs' 21 = Z_to_bv 64 (datas + 4 * wpl * i) /\
      getr regs' 28 = Z_to_bv 64 (dd + 4 * wpl * i) /\ getr regs' 31 = Z_to_bv 64 (dd + 4 * wpl * i) /\
      getr regs' 16 = Z_to_bv 64 (datas + 4 * wpl * i) /\ getr regs' 17 = Z_to_bv 64 (dd + 4 * wpl * i) /\
      getr regs' 29 = Z_to_bv 64 i /\ getr regs' 30 = Z_to_bv 64 (8 * i) /\
      regs_agree (fun r => In r [5; 6; 7; 10; 16; 17; 21; 28; 29; 30; 31]%list) regs regs').
Proof.
  intros fx regs m s datas dd wpl h w i Hs As Hi Hh Hwpl Hw Hds Hds' Hdd Hdd' R144 R136 R128 R120 R108 H2 H11 H12 H13 H14 H15 H18 H22.
  assert (As' : ((s - 160) mod 16 = 0)%Z) by (rewrite Zminus_mod, As; reflexivity).
  assert (Hiw : (0 <= i * wpl <= 20000 * 20000)%Z) by nia.
  assert (Hwh : (0 <= wpl * h)%Z) by nia.
  assert (Hiw2 : (i * wpl + wpl <= wpl * h)%Z) by nia.
  ex_entry regs [(s - 160)%Z; i; wpl; (i * wpl)%Z; datas; dd; w] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 160)%Z; i; wpl; (i * wpl)%Z; datas; dd; w]) m
    [KAlign (EVar 32) 16; KRange (EVar 32) 4096 (2 ^ 47);
     KWord (SA (EVar 32) 16) 8 (EVar 34); KWord (SA (EVar 32) 24) 8 (EVar 35); KWord (SA (EVar 32) 32) 8 (EVar 37);
     KWord (SA (EVar 32) 40) 8 (EVar 36); KWord (SA (EVar 32) 52) 4 (EVar 38)]).
  { ex_know regs. }
  ex_open HR HK Hms Hlf.
  ex_cont 100%nat [0x3a75c%Z] (SCR [false; false; false; false; false; false; false; false; false; false; false; false] [] []) HR Hlf HK Hms.
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => zb_br end).
  eexists; split; [exact Hms|].
  eexists; split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (xreg regs HR); try (ex_agree HRo HR).
Qed.
End Segs.

Ltac bytes_eq := vm_compute; apply (f_equal Some); repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]); reflexivity.
Lemma ro_one : rdn SEGS (fun _ => None) (Z_to_bv 64 0x12590) 8 = Some (Z_to_le_bytes 8 p_one_d).
Proof. bytes_eq. Qed.
Lemma ro_half : rdn SEGS (fun _ => None) (Z_to_bv 64 0x125b8) 8 = Some (Z_to_le_bytes 8 p_half_d).
Proof. bytes_eq. Qed.
Lemma ro_lo : rdn SEGS (fun _ => None) (Z_to_bv 64 0x125d0) 8 = Some (Z_to_le_bytes 8 p_lo_d).
Proof. bytes_eq. Qed.
Lemma ro_hi : rdn SEGS (fun _ => None) (Z_to_bv 64 0x12588) 8 = Some (Z_to_le_bytes 8 p_hi_d).
Proof. bytes_eq. Qed.

(* [comment removed for export] *)
#[local] Instance ap_fxd : FPState | 100 := mkFP bvmap_empty (Z_to_bv 32 0).

(* [comment removed for export] *)
Definition ap_rds (M : word -> option byte) (kx kf ls W h : Z) (linesf datak : Z -> Z) : Prop :=
  (forall v, (0 <= v < 256)%Z -> exists k, rdn SEGS M (Z_to_bv 64 (kx + 4 * v)) 4 = Some (Z_to_le_bytes 4 k) /\ (0 <= k <= 8)%Z) /\
  (forall v, (0 <= v < 256)%Z -> exists x, rdn SEGS M (Z_to_bv 64 (kf + 4 * v)) 4 = Some (Z_to_le_bytes 4 x) /\ FpSiteB.kfr_le1 x) /\
  (forall k, (0 <= k < 10)%Z -> rdn SEGS M (Z_to_bv 64 (ls + 8 * k)) 8 = Some (Z_to_le_bytes 8 (linesf k))) /\
  (forall k i, (0 <= k < 10)%Z -> (0 <= i < h)%Z -> rdn SEGS M (Z_to_bv 64 (linesf k + 8 * i)) 8 = Some (Z_to_le_bytes 8 (datak k + W * i))) /\
  (forall k p, (0 <= k < 10)%Z -> (datak k <= p < datak k + W * h)%Z -> exists b, rdn SEGS M (Z_to_bv 64 p) 1 = Some [b]) /\
  (forall k, (0 <= k < 10)%Z -> (linesf k mod 8 = 0)%Z /\ (4096 <= linesf k)%Z /\ (linesf k + 8 * h <= 2 ^ 47)%Z /\
                                (datak k mod 4 = 0)%Z /\ (4096 <= datak k)%Z /\ (datak k + W * h <= 2 ^ 47)%Z).

Definition ap_ro (M : word -> option byte) : Prop :=
  rdn SEGS M (Z_to_bv 64 0x12588) 8 = Some (Z_to_le_bytes 8 p_hi_d) /\
  rdn SEGS M (Z_to_bv 64 0x12590) 8 = Some (Z_to_le_bytes 8 p_one_d) /\
  rdn SEGS M (Z_to_bv 64 0x125b8) 8 = Some (Z_to_le_bytes 8 p_half_d) /\
  rdn SEGS M (Z_to_bv 64 0x125d0) 8 = Some (Z_to_le_bytes 8 p_lo_d).

(* [comment removed for export] *)
Definition ap_fp (fr fr' : bvmap 5 word) : Prop :=
  forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> reg_get fr' r = reg_get fr r.

(* [comment removed for export] *)
Definition ap_apart (dd n kx kf ls W h : Z) (linesf datak : Z -> Z) : Prop :=
  (kx + 1024 <= dd \/ dd + n <= kx)%Z /\ (kf + 1024 <= dd \/ dd + n <= kf)%Z /\ (ls + 80 <= dd \/ dd + n <= ls)%Z /\
  (forall k, (0 <= k < 10)%Z -> (linesf k + 8 * h <= dd \/ dd + n <= linesf k)%Z /\ (datak k + W * h <= dd \/ dd + n <= datak k)%Z) /\
  (dd + n <= 0x12588 \/ 0x125d8 <= dd)%Z.

Definition APJ : list reg := [1; 5; 6; 7; 8; 9; 10; 18; 19; 20; 21; 26; 27; 28; 31]%bv.
Definition API : list reg := [1; 5; 6; 7; 8; 9; 10; 11; 12; 16; 17; 18; 19; 20; 21; 26; 27; 28; 29; 30; 31]%bv.

Ltac zl := cbn [Z.of_nat Pos.of_succ_nat Pos.succ fst snd]; lia.

Lemma ap_apart_sub : forall dd n dd' n' kx kf ls W h linesf datak, ap_apart dd n kx kf ls W h linesf datak -> (dd <= dd')%Z -> (dd' + n' <= dd + n)%Z ->
  ap_apart dd' n' kx kf ls W h linesf datak.
Proof.
  intros dd n dd' n' kx kf ls W h linesf datak HA H1 H2. unfold ap_apart in *.
  destruct HA as [A1 [A2 [A3 [A4 A5]]]].
  split; [lia|split; [lia|split; [lia|split; [|lia]]]].
  intros k Hk. destruct (A4 k Hk) as [B1 B2]. split; lia.
Qed.

Lemma rdn_rinv1 : forall (lo n : Z) (M0 M : word -> option byte) (a : Z) (k : nat), rinv [(lo, n)] M0 M -> (0 <= a)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
  (a + Z.of_nat k <= lo \/ lo + n <= a)%Z -> rdn SEGS M (Z_to_bv 64 a) k = rdn SEGS M0 (Z_to_bv 64 a) k.
Proof.
  intros lo n M0 M a k HR Ha Hk Hd.
  eapply rinv_rdn; [exact HR|exact Ha|exact Hk|].
  intros r [<-|[]]. cbn [fst snd]. exact Hd.
Qed.

Lemma ap_rdn_keepG : forall (R : list (Z * Z)) (M0 M : word -> option byte) (z : Z) (k : nat), rinv R M0 M -> (0 <= z)%Z -> (z + Z.of_nat k <= 2 ^ 64)%Z ->
  (forall r, In r R -> z + Z.of_nat k <= fst r \/ fst r + snd r <= z)%Z -> rdn SEGS M (Z_to_bv 64 z) k = rdn SEGS M0 (Z_to_bv 64 z) k.
Proof.
  intros R M0 M z k HR Hz Hzk Hd.
  eapply rinv_rdn; [exact HR|exact Hz|exact Hzk|exact Hd].
Qed.

Lemma ap_rds_keepG : forall (R : list (Z * Z)) (M0 M : word -> option byte) (kx kf ls W h : Z) (linesf datak : Z -> Z), rinv R M0 M ->
  (forall r, In r R -> ap_apart (fst r) (snd r) kx kf ls W h linesf datak) ->
  (0 <= kx)%Z -> (kx + 1024 <= 2 ^ 47)%Z -> (0 <= kf)%Z -> (kf + 1024 <= 2 ^ 47)%Z -> (0 <= ls)%Z -> (ls + 80 <= 2 ^ 47)%Z -> (0 <= W)%Z ->
  ap_rds M0 kx kf ls W h linesf datak -> ap_rds M kx kf ls W h linesf datak.
Proof.
  intros R M0 M kx kf ls W h linesf datak HR HA Hkx0 Hkx1 Hkf0 Hkf1 Hls0 Hls1 HW HD.
  unfold ap_rds in *. destruct HD as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  split; [|split; [|split; [|split; [|split]]]].
  - intros v Hv. destruct (H1 v Hv) as [x [Hx Hx']]. exists x. split; [|exact Hx'].
    rewrite (ap_rdn_keepG R M0 M _ _ HR); [exact Hx|lia|zl|].
    intros r Hr. destruct (HA r Hr) as [A1 _]. zl.
  - intros v Hv. destruct (H2 v Hv) as [x [Hx Hx']]. exists x. split; [|exact Hx'].
    rewrite (ap_rdn_keepG R M0 M _ _ HR); [exact Hx|lia|zl|].
    intros r Hr. destruct (HA r Hr) as [_ [A2 _]]. zl.
  - intros k Hk.
    rewrite (ap_rdn_keepG R M0 M _ _ HR); [exact (H3 k Hk)|lia|zl|].
    intros r Hr. destruct (HA r Hr) as [_ [_ [A3 _]]]. zl.
  - intros k i Hk Hi. destruct (H6 k Hk) as [L1 [L2 [L3 [L4 [L5 L6]]]]].
    rewrite (ap_rdn_keepG R M0 M _ _ HR); [exact (H4 k i Hk Hi)|lia|zl|].
    intros r Hr. destruct (HA r Hr) as [_ [_ [_ [A4 _]]]]. destruct (A4 k Hk) as [B1 _]. zl.
  - intros k p Hk Hp. destruct (H6 k Hk) as [L1 [L2 [L3 [L4 [L5 L6]]]]].
    destruct (H5 k p Hk Hp) as [b Hb]. exists b.
    rewrite (ap_rdn_keepG R M0 M _ _ HR); [exact Hb|lia|zl|].
    intros r Hr. destruct (HA r Hr) as [_ [_ [_ [A4 _]]]]. destruct (A4 k Hk) as [_ B2]. zl.
  - exact H6.
Qed.

Lemma ap_ro_keepG : forall (R : list (Z * Z)) (M0 M : word -> option byte), rinv R M0 M -> (forall r, In r R -> (fst r + snd r <= 0x12588 \/ 0x125d8 <= fst r)%Z) ->
  ap_ro M0 -> ap_ro M.
Proof.
  intros R M0 M HR HF HO. unfold ap_ro in *. destruct HO as [A1 [A2 [A3 A4]]].
  split; [|split; [|split]];
    (rewrite (ap_rdn_keepG R M0 M _ _ HR); [assumption|lia|zl|intros r Hr; specialize (HF r Hr); zl]).
Qed.

Lemma ap_rds_keep : forall (M0 M : word -> option byte) (dd n kx kf ls W h : Z) (linesf datak : Z -> Z), rinv [(dd, n)] M0 M -> ap_apart dd n kx kf ls W h linesf datak ->
  (0 <= kx)%Z -> (kx + 1024 <= 2 ^ 47)%Z -> (0 <= kf)%Z -> (kf + 1024 <= 2 ^ 47)%Z -> (0 <= ls)%Z -> (ls + 80 <= 2 ^ 47)%Z -> (0 <= W)%Z ->
  ap_rds M0 kx kf ls W h linesf datak -> ap_rds M kx kf ls W h linesf datak.
Proof.
  intros M0 M dd n kx kf ls W h linesf datak HR HA Hkx0 Hkx1 Hkf0 Hkf1 Hls0 Hls1 HW HD.
  apply (ap_rds_keepG [(dd, n)] M0 M kx kf ls W h linesf datak HR); try assumption.
  intros r [<-|[]]. exact HA.
Qed.

Lemma ap_ro_keep : forall (M0 M : word -> option byte) (dd n : Z), rinv [(dd, n)] M0 M -> (dd + n <= 0x12588 \/ 0x125d8 <= dd)%Z -> ap_ro M0 -> ap_ro M.
Proof.
  intros M0 M dd n HR Hd HO.
  apply (ap_ro_keepG [(dd, n)] M0 M HR); [|exact HO].
  intros r [<-|[]]. exact Hd.
Qed.

Lemma ap_rds_keepR : forall (R : list (Z * Z)) (M0 M : word -> option byte) (kx kf ls W h : Z) (linesf datak : Z -> Z), rinv R M0 M ->
  Forall (fun r => ap_apart (fst r) (snd r) kx kf ls W h linesf datak /\ (0 <= snd r)%Z) R ->
  (0 <= kx)%Z -> (kx + 1024 <= 2 ^ 47)%Z -> (0 <= kf)%Z -> (kf + 1024 <= 2 ^ 47)%Z -> (0 <= ls)%Z -> (ls + 80 <= 2 ^ 47)%Z -> (0 <= W)%Z ->
  ap_rds M0 kx kf ls W h linesf datak -> ap_rds M kx kf ls W h linesf datak.
Proof.
  intros R M0 M kx kf ls W h linesf datak HR HF Hkx0 Hkx1 Hkf0 Hkf1 Hls0 Hls1 HW HD.
  apply (ap_rds_keepG R M0 M kx kf ls W h linesf datak HR); try assumption.
  rewrite Forall_forall in HF. intros r Hr. exact (proj1 (HF r Hr)).
Qed.

Lemma ap_ro_keepR : forall (R : list (Z * Z)) (M0 M : word -> option byte), rinv R M0 M -> Forall (fun r => (fst r + snd r <= 0x12588 \/ 0x125d8 <= fst r)%Z) R ->
  ap_ro M0 -> ap_ro M.
Proof.
  intros R M0 M HR HF HO.
  apply (ap_ro_keepG R M0 M HR); [|exact HO].
  rewrite Forall_forall in HF. exact HF.
Qed.

(* [comment removed for export] *)
Lemma ap_rd_const : forall (m : word -> option byte) (a : Z), In a [0x12590; 0x125b8]%Z -> exists bs, rdn SEGS m (Z_to_bv 64 a) 8 = Some bs /\ length bs = 8%nat.
Proof. intros m a [<- | [<- | []]]; eapply rdn_rom_any; [exact ro_one | exact ro_half]. Qed.

Section Segs.
Variable rom : word -> option byte.

Lemma ap_rowinc : forall (fx : FPState) regs (M : word -> option byte) (s wpl h i : Z),
  (4096 + 160 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z -> (0 <= i)%Z -> (i + 1 < h)%Z -> (h <= 20000)%Z -> (0 <= wpl <= 20000)%Z ->
  store_ok SEGS M (Z_to_bv 64 (s - 136)) 8 = true ->
  rdn SEGS M (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wpl) ->
  rdn SEGS M (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 wpl) ->
  rdn SEGS M (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 (i * wpl)) ->
  rdn SEGS M (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 11 = Z_to_bv 64 (i * wpl) -> getr regs 12 = Z_to_bv 64 i ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3a67c) M rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x3a6a0) M' rom /\
       rinv [((s - 136)%Z, 8%Z)] M M' /\ rdn SEGS M' (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 ((i + 1) * wpl)) /\
       getr regs' 11 = Z_to_bv 64 ((i + 1) * wpl) /\ getr regs' 12 = Z_to_bv 64 (i + 1) /\ getr regs' 18 = Z_to_bv 64 wpl /\
       regs_agree (fun r => In r [10; 11; 12; 16; 17; 18]%list) regs regs').
Proof.
  intros fx regs M s wpl h i Hs As Hi Hih Hh Hw SOK R152 R144 R136 R112 H2 H11 H12.
  assert (As' : ((s - 160) mod 16 = 0)%Z) by (rewrite Zminus_mod, As; reflexivity).
  assert (Hiw : (0 <= i * wpl <= 20000 * 20000)%Z) by nia.
  assert (Hiw1 : (0 <= i * wpl + wpl <= 20000 * 20000)%Z) by nia.
  ex_entry regs [(s - 160)%Z; i; wpl; (i * wpl)%Z; h] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 160)%Z; i; wpl; (i * wpl)%Z; h]) M
    [KWr (SA (EVar 32) 24) 8; KAlign (EVar 32) 16; KRange (EVar 32) 4096 (2 ^ 47);
     KRange (EVar 33) 0 20000; KRange (EVar 34) 0 20000; KRange (EVar 35) 0 (20000 * 20000); KRange (EVar 36) 0 20000;
     KWord (SA (EVar 32) 8) 8 (EVar 34); KWord (SA (EVar 32) 16) 8 (EVar 34); KWord (SA (EVar 32) 24) 8 (EVar 35);
     KWord (SA (EVar 32) 48) 4 (EVar 36)]).
  { ex_know regs. }
  ex_open HR HK Hms Hlf.
  ex_cont 100%nat [0x3a6a0%Z] (SCR [false] [] []) HR Hlf HK Hms.
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => zb_br end).
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 136)%Z, 8%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (xreg regs HR); try (ex_agree HRo HR).
  cellz regs HK Hlf 24%Z 8%nat (s - 136)%Z ((i + 1) * wpl)%Z.
Qed.

Lemma ap_iexit : forall (fx : FPState) regs (M : word -> option byte) (s wpl h i pixd : Z),
  (4096 + 160 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z -> (0 <= i)%Z -> (i + 1 = h)%Z -> (h <= 20000)%Z -> (0 <= wpl <= 20000)%Z ->
  (0 <= pixd < 2 ^ 64)%Z ->
  store_ok SEGS M (Z_to_bv 64 (s - 136)) 8 = true ->
  rdn SEGS M (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixd) ->
  rdn SEGS M (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wpl) ->
  rdn SEGS M (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 wpl) ->
  rdn SEGS M (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 (i * wpl)) ->
  rdn SEGS M (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 11 = Z_to_bv 64 (i * wpl) -> getr regs 12 = Z_to_bv 64 i ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3a67c) M rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x3aa18) M' rom /\
       rinv [((s - 136)%Z, 8%Z)] M M' /\ getr regs' 8 = Z_to_bv 64 pixd /\
       regs_agree (fun r => In r [8; 10; 11; 12; 16; 17; 18]%list) regs regs').
Proof.
  intros fx regs M s wpl h i pixd Hs As Hi Hih Hh Hw Hpd SOK R160 R152 R144 R136 R112 H2 H11 H12.
  assert (As' : ((s - 160) mod 16 = 0)%Z) by (rewrite Zminus_mod, As; reflexivity).
  assert (Hiw : (0 <= i * wpl <= 20000 * 20000)%Z) by nia.
  assert (Hiw1 : (0 <= i * wpl + wpl <= 20000 * 20000)%Z) by nia.
  ex_entry regs [(s - 160)%Z; i; wpl; (i * wpl)%Z; h; pixd] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 160)%Z; i; wpl; (i * wpl)%Z; h; pixd]) M
    [KWr (SA (EVar 32) 24) 8; KAlign (EVar 32) 16; KRange (EVar 32) 4096 (2 ^ 47);
     KRange (EVar 33) 0 20000; KRange (EVar 34) 0 20000; KRange (EVar 35) 0 (20000 * 20000); KRange (EVar 36) 0 20000;
     KWord (SA (EVar 32) 0) 8 (EVar 37);
     KWord (SA (EVar 32) 8) 8 (EVar 34); KWord (SA (EVar 32) 16) 8 (EVar 34); KWord (SA (EVar 32) 24) 8 (EVar 35);
     KWord (SA (EVar 32) 48) 4 (EVar 36)]).
  { ex_know regs. }
  ex_open HR HK Hms Hlf.
  ex_cont 100%nat [0x3aa18%Z] (SCR [true] [] []) HR Hlf HK Hms.
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => zb_br end).
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 136)%Z, 8%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (xreg regs HR); try (ex_agree HRo HR).
Qed.

End Segs.

Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma ap_pxA : forall (fx : FPState) regs (M : word -> option byte) (s kx kf ls W h i j rs rd v k lk pk lk1 pk1 : Z),
  (4096 + 160 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (0 <= j < W)%Z -> (W <= 80000)%Z -> (W mod 4 = 0)%Z -> (0 <= i < h)%Z -> (h <= 20000)%Z ->
  (rs mod 4 = 0)%Z -> (4096 <= rs)%Z -> (rs + W <= 2 ^ 47)%Z -> (4096 <= rd)%Z -> (rd + W <= 2 ^ 47)%Z ->
  (kx mod 4 = 0)%Z -> (4096 <= kx)%Z -> (kx + 1024 <= 2 ^ 47)%Z ->
  (kf mod 4 = 0)%Z -> (4096 <= kf)%Z -> (kf + 1024 <= 2 ^ 47)%Z ->
  (ls mod 8 = 0)%Z -> (4096 <= ls)%Z -> (ls + 80 <= 2 ^ 47)%Z ->
  (0 <= v < 256)%Z -> (0 <= k <= 8)%Z ->
  (lk mod 8 = 0)%Z -> (4096 <= lk)%Z -> (lk + 8 * h <= 2 ^ 47)%Z ->
  (lk1 mod 8 = 0)%Z -> (4096 <= lk1)%Z -> (lk1 + 8 * h <= 2 ^ 47)%Z ->
  (4096 <= pk)%Z -> (pk + W <= 2 ^ 47)%Z -> (4096 <= pk1)%Z -> (pk1 + W <= 2 ^ 47)%Z ->
  rdn SEGS M (Z_to_bv 64 (Z.lxor (rs + j) 3)) 1 = Some (Z_to_le_bytes 1 v) ->
  rdn SEGS M (Z_to_bv 64 (kx + 4 * v)) 4 = Some (Z_to_le_bytes 4 k) ->
  rdn SEGS M (Z_to_bv 64 (ls + 8 * k)) 8 = Some (Z_to_le_bytes 8 lk) ->
  rdn SEGS M (Z_to_bv 64 (lk + 8 * i)) 8 = Some (Z_to_le_bytes 8 pk) ->
  rdn SEGS M (Z_to_bv 64 (ls + 8 * (k + 1))) 8 = Some (Z_to_le_bytes 8 lk1) ->
  rdn SEGS M (Z_to_bv 64 (lk1 + 8 * i)) 8 = Some (Z_to_le_bytes 8 pk1) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 5 = Z_to_bv 64 j -> getr regs 7 = Z_to_bv 64 (rs + j) -> getr regs 21 = Z_to_bv 64 (rs + j) ->
  getr regs 16 = Z_to_bv 64 rs -> getr regs 28 = Z_to_bv 64 (rd + j) -> getr regs 31 = Z_to_bv 64 (rd + j) ->
  getr regs 29 = Z_to_bv 64 i -> getr regs 30 = Z_to_bv 64 (8 * i) ->
  getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 3 -> getr regs 22 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 kx -> getr regs 24 = Z_to_bv 64 kf -> getr regs 25 = Z_to_bv 64 ls ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3a75c) M rom)
    (fun fin => exists regs', fin = @mkst fx regs' (Z_to_bv 64 0x3a8e8) M rom /\
       getr regs' 26 = Z_to_bv 64 (kf + 4 * v) /\ getr regs' 10 = Z_to_bv 64 (Z.lxor (pk + j) 3) /\
       getr regs' 8 = Z_to_bv 64 (Z.lxor (pk1 + j) 3) /\
       regs_agree (fun r => In r [1; 8; 9; 10; 18; 19; 20; 26; 27]%list) regs regs').
Proof.
  intros fx regs M s kx kf ls W h i j rs rd v k lk pk lk1 pk1 Hs As Hj HW AW Hi Hh Ars Hrs Hrs' Hrd Hrd' Akx Hkx Hkx' Akf Hkf Hkf' Als Hls Hls'
    Hv Hk Alk Hlk Hlk' Alk1 Hlk1 Hlk1' Hpk Hpk' Hpk1 Hpk1' Rv Rk Rlk Rpk Rlk1 Rpk1 H2 H5 H7 H21 H16 H28 H31 H29 H30 H13 H14 H15 H22 H23 H24 H25.
  assert (As' : ((s - 160) mod 16 = 0)%Z) by (rewrite Zminus_mod, As; reflexivity).
  ex_entry regs [(s - 160)%Z; kx; kf; ls; i; j; rs; rd; (rs + j)%Z; (rd + j)%Z; (8 * i)%Z; v; k; lk; pk; lk1; pk1] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 160)%Z; kx; kf; ls; i; j; rs; rd; (rs + j)%Z; (rd + j)%Z; (8 * i)%Z; v; k; lk; pk; lk1; pk1]) M
    [KAlign (EVar 33) 4; KAlign (EVar 34) 4; KAlign (EVar 35) 8; KAlign (EVar 42) 8; KAlign (EVar 45) 8; KAlign (EVar 47) 8;
     KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 35) 4096 (2 ^ 47);
     KRange (EVar 36) 0 20000; KRange (EVar 37) 0 80000; KRange (EVar 40) 4096 (2 ^ 47); KRange (EVar 41) 4096 (2 ^ 47);
     KRange (EVar 42) 0 160000; KRange (EVar 43) 0 255; KRange (EVar 44) 0 8;
     KRange (EVar 45) 4096 (2 ^ 47); KRange (EVar 46) 4096 (2 ^ 47); KRange (EVar 47) 4096 (2 ^ 47); KRange (EVar 48) 4096 (2 ^ 47)]).
  { assert (A8 : ((8 * i) mod 8 = 0)%Z) by (rewrite Z.mul_comm; apply Z_mod_mult). ex_know regs. }
  ex_open HR HK Hms Hlf.
  ex_cont 300%nat [0x3a8e8%Z]
    (SCR (repeat false 40) [EVar 43; EVar 44; EVar 45; EVar 46; EVar 47; EVar 48] []) HR Hlf HK Hms.
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => zb_br end).
  all: try (lazymatch goal with |- exists bs, _ => rb_tac end).
  eexists; split; [exact Hms|].
  eexists; split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (xreg regs HR); try (ex_agree HRo HR).
Qed.
End Segs.

Lemma apf_cell : forall z, (0 <= z < 2 ^ 32)%Z -> bv_extract 0%N 32%N (le_bytes_to_word (Z_to_le_bytes 4 z)) = Z_to_bv 32 z.
Proof.
  intros z Hz. unfold le_bytes_to_word. rewrite (lez4 z Hz).
  apply bv_eq. rewrite bv_extract_unsigned, !Z_to_bv_unsigned. change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z. change (Z.of_N 32) with 32%Z.
  rewrite (Z.mod_small z (2 ^ 64)) by lia. rewrite (Z.mod_small z (2 ^ 64)) by lia. reflexivity.
Qed.

Lemma apf_ld8 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_extract 0%N 64%N (le_bytes_to_word (Z_to_le_bytes 8 z)) = Z_to_bv 64 z.
Proof. intros z Hz. rewrite exf_extract64. unfold le_bytes_to_word. rewrite (lez8 z Hz). rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma apf_u8 : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 8) with 8%Z.
  change (2 ^ 8)%Z with 256%Z. apply Z.mod_small. lia.
Qed.

Lemma apf_sltiu1 : forall a, (1 <= a < 2 ^ 64)%Z -> v_sltiu (Z_to_bv 64 a) 1 = Z_to_bv 64 0.
Proof.
  intros a Ha. unfold v_sltiu. rewrite u_Z2bv by lia. change (bv_wrap 64 1) with 1%Z.
  destruct (Z.ltb_spec a 1); [lia | reflexivity].
Qed.

Lemma apf_xori3 : forall a, (0 <= a < 2 ^ 64)%Z -> v_xori (Z_to_bv 64 a) 3 = Z_to_bv 64 (Z.lxor a 3).
Proof. intros a Ha. unfold v_xori. rewrite u_Z2bv by lia. change (bv_wrap 64 3) with 3%Z. reflexivity. Qed.

Lemma apf_lw : forall z, (0 <= z < 2 ^ 31)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold v_lw. rewrite u_Z2bv by lia. rewrite swrap32_small by lia. reflexivity. Qed.

Lemma apf_x3 : forall rd j W, (rd mod 4 = 0)%Z -> (W mod 4 = 0)%Z -> (0 <= j < W)%Z -> (0 <= rd)%Z ->
  (rd <= Z.lxor (rd + j) 3 < rd + W)%Z.
Proof.
  intros rd j W A1 A2 Hj Hr. rewrite lxor3_eq by lia.
  pose proof (Z.mod_pos_bound (rd + j) 4 ltac:(lia)) as B.
  pose proof (Z.div_mod (rd + j) 4 ltac:(lia)) as E1.
  pose proof (Z.div_mod rd 4 ltac:(lia)) as E2.
  pose proof (Z.div_mod W 4 ltac:(lia)) as E3.
  rewrite A1 in E2. rewrite A2 in E3. lia.
Qed.

Lemma apf_iw : forall z, (0 <= z < 256)%Z -> int_wrap 32 z = z.
Proof. intros z Hz. unfold int_wrap. rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma apf_c64 : forall c, Z.leb 0 c = true -> Z.ltb c (2 ^ 64) = true -> (0 <= c < 2 ^ 64)%Z.
Proof. intros c A B. apply Z.leb_le in A. apply Z.ltb_lt in B. lia. Qed.

Definition apf_lit (n : N) (z : Z) : bv n := Z_to_bv n z.

Local Ltac canon1 t :=
  match t with
  | context C [@BV ?n ?z _] => let t' := context C [apf_lit n z] in canon1 t'
  | _ => t
  end.
Local Ltac canon2 t :=
  match t with
  | context C [apf_lit ?n ?z] => let t' := context C [@BV n z (I <: BvWf n z)] in canon2 t'
  | _ => t
  end.
Local Ltac canon t := let t1 := canon1 t in canon2 t1.

Local Ltac here Fw Dw :=
  lazymatch goal with |- reach ?sg (@mkst _ _ ?p _ _) _ =>
    let f := eval vm_compute in (fetch_word sg p) in
    lazymatch f with Some ?w =>
      assert (Fw : fetch_word sg p = Some w) by (vm_cast_no_check (eq_refl (Some w)));
      let d0 := eval vm_compute in (decode_any w) in
      let d := canon d0 in
      assert (Dw : decode_any w = d) by vm_refl_bv
    end
  end.

Local Ltac pcn :=
  lazymatch goal with |- reach _ (@mkst _ _ ?p _ _) _ =>
    lazymatch p with
    | Z_to_bv 64 _ => idtac
    | _ => tryif check_closed_term p then
             (let z := eval vm_compute in (bv_unsigned p) in
              let E := fresh "E" in
              assert (E : p = Z_to_bv 64 z) by (apply bv_eq; vm_compute; reflexivity);
              rewrite E; clear E)
           else idtac
    end
  end.

Local Ltac lits :=
  repeat match goal with
  | |- context [bv_signed (@BV ?n ?z ?pf)] =>
      let v := eval vm_compute in (bv_signed (@BV n z pf)) in change (bv_signed (@BV n z pf)) with v
  | |- context [bv_unsigned (@BV ?n ?z ?pf)] => change (bv_unsigned (@BV n z pf)) with z
  end.

Local Ltac rneq := let Hc := fresh "Hc" in intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate Hc.

Local Ltac gsimp :=
  repeat match goal with
  | |- context [getr (regupd ?R ?r ?v) ?r'] =>
      first [ (let E := fresh "E" in
               assert (E : getr (regupd R r v) r' = v) by (replace r' with r by bveq; apply getr_same; rneq);
               rewrite E; clear E)
            | (let E := fresh "E" in
               assert (E : getr (regupd R r v) r' = getr R r') by (apply getr_other; rneq);
               rewrite E; clear E) ]
  | |- context [getr ?R ?r] =>
      lazymatch r with @BV _ _ _ =>
        let b := eval vm_compute in (bv_eqb r (Z_to_bv 5 0)) in
        lazymatch b with true => change (getr R r) with (Z_to_bv 64 0) end
      end
  end.

Local Ltac hregs :=
  repeat match goal with
  | |- context [getr ?R ?r] =>
      is_var R;
      match goal with
      | H : getr R ?r0 = ?val |- _ =>
          let b := eval vm_compute in (bv_eqb r r0) in
          lazymatch b with
          | true => let E := fresh "E" in
                    assert (E : getr R r = val) by (replace r with r0 by bveq; exact H);
                    rewrite E; clear E
          end
      end
  end.

Local Ltac fsimp := cbn [fp_regs fp_csr]; cbn [fpv_box];
  repeat first [ rewrite fpv_read_S_box | rewrite fpv_read_D_same | rewrite fpv_read_other by rneq
               | rewrite fpv_get_same | rewrite fpv_get_other by rneq ].

Local Ltac csgen FZ :=
  repeat lazymatch goal with |- context [mkFP _ (fpv_acc ?c ?fl)] =>
    let H := fresh "FZ" in
    pose proof (fpv_frm_acc c fl FZ) as H;
    let c' := fresh "cs" in
    set (c' := fpv_acc c fl) in *; clearbody c'; clear FZ; rename H into FZ
  end.

Local Ltac wcl :=
  repeat match goal with
  | |- context [v_auipc ?a ?b] => wlit_closed (v_auipc a b)
  | |- context [v_addi ?a ?b] => wlit_closed (v_addi a b)
  | |- context [v_xor ?a ?b] => wlit_closed (v_xor a b)
  end.

Local Ltac vsimp :=
  repeat match goal with
  | |- context [bv_extract _ _ (le_bytes_to_word (Z_to_le_bytes 4 ?z))] => rewrite (apf_cell z) by lia
  | |- context [bv_extract _ _ (le_bytes_to_word (Z_to_le_bytes 8 ?z))] => rewrite (apf_ld8 z) by lia
  | |- context [v_addi (Z_to_bv 64 ?a) ?i] => rewrite (zbv_addi a i)
  | |- context [v_xori (Z_to_bv 64 ?a) 3] => rewrite (apf_xori3 a) by lia
  | |- context [v_sltiu (Z_to_bv 64 ?a) 1] => rewrite (apf_sltiu1 a) by lia
  | |- context [v_lw (Z_to_bv 64 ?a)] => rewrite (apf_lw a) by lia
  end.

Local Ltac unorm2 :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (u_Z2bv z) by lia
  | |- context [bv_unsigned (Z_to_bv 32 ?z)] => rewrite (fp_u_Z2bv32 z) by lia
  | |- context [bv_unsigned (Z_to_bv 8 ?z)] => rewrite (apf_u8 z) by lia
  end.

Local Ltac fold_all :=
  repeat match goal with
  | n := ?b |- _ => progress change b with n
  end.

Local Ltac disj := first [ (repeat split; reflexivity) | (left; disj) | (right; disj) ].

Local Ltac ldt := gsimp; hregs; lits; wcl; rewrite ?zbv_addi, ?Z.add_0_r; eassumption.

Local Ltac brt := gsimp; hregs; lits; wcl; vsimp; unorm2;
  first [ cond_compute
        | (unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_Z2bv by lia; first [apply Z.eqb_neq | apply Z.ltb_ge]; lia) ].

Local Ltac stp FZ :=
  let Fw := fresh "Fw" in let Dw := fresh "Dw" in
  here Fw Dw;
  eapply reach_step; [ reflexivity |
    lazymatch type of Dw with
    | _ = Some (OpImm ALU_ADD _ _ _, _) => eapply step_addi; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm ALU_XOR _ _ _, _) => eapply step_xori; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm ALU_SLTU _ _ _, _) => eapply step_sltiu; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op ALU_XOR _ _ _, _) => eapply step_xor; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Auipc _ _, _) => eapply step_auipc; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu; [exact Fw | reflexivity | exact Dw | ldt]
    | _ = Some (Branch BC_EQ _ _ _, _) => eapply step_beq_ft; [exact Fw | reflexivity | exact Dw | brt]
    | _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft; [exact Fw | reflexivity | exact Dw | brt]
    | _ = Some (Fcmp _ _ _ _ _, _) => eapply fpv_step_fcmp; [exact Fw | reflexivity | exact Dw]
    | _ = Some (FLoad FMT_D _ _ _, _) => eapply fp_step_fld; [exact Fw | reflexivity | exact Dw | reflexivity | ldt]
    | _ = Some (FLoad FMT_S _ _ _, _) => eapply fp_step_flw; [exact Fw | reflexivity | exact Dw | reflexivity | ldt]
    | _ = Some (Fari _ _ _ _ _ _, _) => eapply fpv_step_fari; [exact Fw | reflexivity | exact Dw | exact FZ | reflexivity]
    | _ = Some (Fma _ _ _ _ _ _ _, _) => eapply fpv_step_fma; [exact Fw | reflexivity | exact Dw | exact FZ | reflexivity]
    | _ = Some (Fcvt FC_W _ _ _ _, _) =>
        eapply fpv_step_fcvt_x_of_f; [exact Fw | reflexivity | exact Dw | disj | disj | exact FZ | reflexivity]
    | _ = Some (Fcvt _ FC_WU _ _ _, _) =>
        eapply fpv_step_fcvt_f_of_x; [exact Fw | reflexivity | exact Dw | disj | disj | exact FZ | reflexivity]
    | _ = Some (Fcvt _ _ _ _ _, _) =>
        eapply fpv_step_fcvt_f_of_f; [exact Fw | reflexivity | exact Dw | disj | disj | exact FZ | reflexivity]
    end | ];
  clear Fw Dw.

Local Ltac cmps :=
  repeat match goal with
  | H : fst (fpv_cmp _ _ _ _) = _ |- context [fst (fpv_cmp _ _ _ _)] => rewrite H
  end;
  repeat match goal with |- context [if true then ?A else ?B] => change (if true then A else B) with A end.

Local Ltac nrm FZ :=
  cbn [fp_regs fp_csr]; reduce_bv_eqb_ifs; pcn; fsimp; gsimp; hregs; lits; wcl; vsimp; unorm2; fold_all; cmps; csgen FZ.

Local Ltac sn FZ := stp FZ; nrm FZ.

Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma ap_pxF : forall fr cs regs (M : word -> option byte) (s kf v x rs rd W w j pk pk1 lo hi : Z),
  frm_zero cs -> (4096 + 160 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (0 <= j < w)%Z -> (w <= W)%Z -> (W <= 80000)%Z -> (W mod 4 = 0)%Z ->
  (4096 <= rs)%Z -> (rs + W <= 2 ^ 47)%Z -> (rd mod 4 = 0)%Z -> (4096 <= rd)%Z -> (rd + W <= 2 ^ 47)%Z -> (rd + W <= s - 160 \/ s <= rd)%Z ->
  (kf mod 4 = 0)%Z -> (4096 <= kf)%Z -> (kf + 1024 <= 2 ^ 47)%Z -> (0 <= v < 256)%Z ->
  rdn SEGS M (Z_to_bv 64 (kf + 4 * v)) 4 = Some (Z_to_le_bytes 4 x) -> FpSiteB.kfr_le1 x ->
  (4096 <= pk)%Z -> (pk + W <= 2 ^ 47)%Z -> (4096 <= pk1)%Z -> (pk1 + W <= 2 ^ 47)%Z ->
  rdn SEGS M (Z_to_bv 64 (Z.lxor (pk + j) 3)) 1 = Some (Z_to_le_bytes 1 lo) -> (0 <= lo < 256)%Z ->
  rdn SEGS M (Z_to_bv 64 (Z.lxor (pk1 + j) 3)) 1 = Some (Z_to_le_bytes 1 hi) -> (0 <= hi < 256)%Z ->
  ap_ro M -> store_ok SEGS M (Z_to_bv 64 (Z.lxor (rd + j) 3)) 1 = true ->
  rdn SEGS M (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 5 = Z_to_bv 64 j -> getr regs 6 = Z_to_bv 64 j ->
  getr regs 7 = Z_to_bv 64 (rs + j) -> getr regs 21 = Z_to_bv 64 (rs + j) ->
  getr regs 8 = Z_to_bv 64 (Z.lxor (pk1 + j) 3) -> getr regs 10 = Z_to_bv 64 (Z.lxor (pk + j) 3) -> getr regs 26 = Z_to_bv 64 (kf + 4 * v) ->
  getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 3 -> getr regs 17 = Z_to_bv 64 rd ->
  getr regs 28 = Z_to_bv 64 (rd + j) -> getr regs 31 = Z_to_bv 64 (rd + j) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a8e8) M rom)
    (fun fin => exists fr' cs' regs' M' bs, fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a980) M' rom /\ frm_zero cs' /\
       length bs = 1%nat /\ M' = wbytes M (Z_to_bv 64 (Z.lxor (rd + j) 3)) bs /\ ap_fp fr fr' /\
       getr regs' 5 = Z_to_bv 64 (j + 1) /\ getr regs' 6 = Z_to_bv 64 (j + 1) /\
       getr regs' 7 = Z_to_bv 64 (rs + (j + 1)) /\ getr regs' 21 = Z_to_bv 64 (rs + (j + 1)) /\
       getr regs' 28 = Z_to_bv 64 (rd + (j + 1)) /\ getr regs' 31 = Z_to_bv 64 (rd + (j + 1)) /\
       getr regs' 10 = Z_to_bv 64 w /\
       regs_agree (fun r => In r [5; 6; 7; 8; 9; 10; 21; 28; 31]%list) regs regs').
Proof.
  intros fr cs regs M s kf v x rs rd W w j pk pk1 lo hi FZ Hs1 As Hj HwW HW AW Hrs Hrs' Ard Hrd Hrd' Hsep
    Akf Hkf Hkf' Hv Rx Kx Hpk Hpk' Hpk1 Hpk1' Rlo Hlo Rhi Hhi Hro Sok Rw H2 H5 H6 H7 H21 H8 H10 H26 H14 H15 H17 H28 H31.
  assert (Rx32 : (0 <= x < 2 ^ 32)%Z) by (apply FpSiteB.kfr_le1_range; exact Kx).
  destruct Hro as (Ro1 & Ro2 & Ro3 & Ro4).
  cbn [Z_to_le_bytes] in Rlo, Rhi.
  assert (Kone : (0 <= p_one_d < 2 ^ 64)%Z) by (apply apf_c64; vm_compute; reflexivity).
  assert (Khalf : (0 <= p_half_d < 2 ^ 64)%Z) by (apply apf_c64; vm_compute; reflexivity).
  assert (Klo : (0 <= p_lo_d < 2 ^ 64)%Z) by (apply apf_c64; vm_compute; reflexivity).
  assert (Khi : (0 <= p_hi_d < 2 ^ 64)%Z) by (apply apf_c64; vm_compute; reflexivity).
  pose (frd := fst (fp_convert (fp_format FMT_S) (fp_format FMT_D) RNE x)).
  pose (t1 := fst (fpv_ari F_SUB FMT_D RNE p_one_d frd)).
  pose (lod := fst (fp_of_int (fp_format FMT_D) RNE false 32 lo)).
  pose (his := fst (fp_of_int (fp_format FMT_S) RNE false 32 hi)).
  pose (t2 := fst (fpv_ari F_MUL FMT_S RNE x his)).
  pose (t2d := fst (fp_convert (fp_format FMT_S) (fp_format FMT_D) RNE t2)).
  pose (t3 := fst (fpv_fma F_MADD FMT_D RNE t1 lod t2d)).
  pose (vr := fst (fpv_ari F_ADD FMT_D RNE t3 p_half_d)).
  assert (Hst : (0 <= x < 2 ^ 32)%Z /\ (0 <= frd < 2 ^ 64)%Z /\ (0 <= t1 < 2 ^ 64)%Z /\ (0 <= lod < 2 ^ 64)%Z /\
                (0 <= his < 2 ^ 32)%Z /\ (0 <= t2 < 2 ^ 32)%Z /\ (0 <= t2d < 2 ^ 64)%Z /\
                (0 <= t3 < 2 ^ 64)%Z /\ (0 <= vr < 2 ^ 64)%Z /\
                fst (fpv_cmp F_LT FMT_D p_lo_d vr) = true /\ fst (fpv_cmp F_LT FMT_D vr p_hi_d) = true /\
                (0 <= fst (fp_to_int (fp_format FMT_D) RTZ true 32 vr) < 512)%Z)
    by exact (FpSiteB.apply_site_full RNE RNE RNE RNE RNE RNE RNE RNE x lo hi lo hi Kx (apf_iw lo Hlo) ltac:(lia) (apf_iw hi Hhi) ltac:(lia)).
  destruct Hst as (_ & Rfrd & Rt1 & Rlod & Rhis & Rt2 & Rt2d & Rt3 & Rvr & Lt1 & Lt2 & _).
  sn FZ.
  do 7 sn FZ.
  do 9 sn FZ.
  do 12 sn FZ.
  do 2 sn FZ.
  let Fw := fresh "Fw" in let Dw := fresh "Dw" in
  here Fw Dw;
  eapply reach_step; [ reflexivity
    | eapply MmapSim.step_sb_at with (a := Z_to_bv 64 (Z.lxor (rd + j) 3));
      [ exact Fw | reflexivity | exact Dw | gsimp; hregs; lits; vsimp; rewrite ?Z.add_0_r; reflexivity
      | gsimp; reflexivity | reflexivity | exact Sok ] | ];
  clear Fw Dw.
  nrm FZ.
  pose proof (apf_x3 rd j W Ard AW ltac:(lia) ltac:(lia)) as X3.
  let Fw := fresh "Fw" in let Dw := fresh "Dw" in
  here Fw Dw;
  eapply reach_step; [ reflexivity
    | eapply step_lw with (v := Z_to_bv 64 w);
      [ exact Fw | reflexivity | exact Dw
      | gsimp; hregs; lits; vsimp; replace (s - 160 + 52)%Z with (s - 108)%Z by lia;
        rewrite rdn_wbytes_out_Z by (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Rw
      | apply lez4; lia ] | ];
  clear Fw Dw.
  nrm FZ.
  do 5 sn FZ.
  apply reach_done. cbv beta.
  lazymatch goal with |- exists _ _ _ _ _, @mkst (mkFP ?F ?C) ?R _ (wbytes ?m ?a ?bs0) _ = _ /\ _ =>
    exists F, C, R, (wbytes m a bs0), bs0 end.
  split; [reflexivity|].
  split; [exact FZ|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [ intros r N10 N11 N12 N13 N14 N15; rewrite ?fpv_get_other by assumption; reflexivity |].
  repeat match goal with |- _ /\ _ => split end.
  all: try (gsimp; hregs; f_equal; lia).
  solve_regs_agree.
Qed.

End Segs.

Lemma apx_lx3 : forall a W j : Z, (0 <= a)%Z -> (a mod 4 = 0)%Z -> (W mod 4 = 0)%Z -> (0 <= j < W)%Z ->
  (a <= Z.lxor (a + j) 3 < a + W)%Z.
Proof.
  intros a W j Ha Aa AW Hj.
  rewrite lxor3_eq by lia.
  assert (E : ((a + j) mod 4 = j mod 4)%Z) by (rewrite Zplus_mod, Aa, Z.add_0_l, Zmod_mod; reflexivity).
  rewrite E.
  pose proof (Z.mod_pos_bound j 4 ltac:(lia)) as B.
  pose proof (Z_div_mod_eq_full j 4) as Dj.
  pose proof (Z_div_mod_eq_full W 4) as DW.
  rewrite AW in DW.
  lia.
Qed.

Lemma apx_al4 : forall a b c : Z, (a mod 4 = 0)%Z -> (b mod 4 = 0)%Z -> ((a + b * c) mod 4 = 0)%Z.
Proof.
  intros a b c Ha Hb. rewrite Zplus_mod, Ha, Zmult_mod, Hb. reflexivity.
Qed.

Lemma apx_b1 : forall (M : word -> option byte) (p : Z), (exists b, rdn SEGS M (Z_to_bv 64 p) 1 = Some [b]) ->
  exists v, rdn SEGS M (Z_to_bv 64 p) 1 = Some (Z_to_le_bytes 1 v) /\ (0 <= v < 256)%Z.
Proof.
  intros M p [b Hb]. exists (lez [b]). split.
  - rewrite Hb. f_equal. exact (eq_sym (Z_to_le_bytes_lez [b])).
  - pose proof (lez_bound_len [b] 1%nat eq_refl) as HB.
    change (2 ^ (8 * Z.of_nat 1))%Z with 256%Z in HB. exact HB.
Qed.

Section Segs.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Lemma ap_px : forall fr cs regs (M : word -> option byte) (s kx kf ls W h w i j rs rd : Z) (linesf datak : Z -> Z),
  frm_zero cs -> (4096 + 160 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (0 <= j < w)%Z -> (w <= W)%Z -> (W <= 80000)%Z -> (W mod 4 = 0)%Z -> (0 <= i < h)%Z -> (h <= 20000)%Z ->
  (rs mod 4 = 0)%Z -> (4096 <= rs)%Z -> (rs + W <= 2 ^ 47)%Z -> (rd mod 4 = 0)%Z -> (4096 <= rd)%Z -> (rd + W <= 2 ^ 47)%Z -> (rd + W <= s - 160 \/ s <= rd)%Z ->
  (kx mod 4 = 0)%Z -> (4096 <= kx)%Z -> (kx + 1024 <= 2 ^ 47)%Z -> (kf mod 4 = 0)%Z -> (4096 <= kf)%Z -> (kf + 1024 <= 2 ^ 47)%Z ->
  (ls mod 8 = 0)%Z -> (4096 <= ls)%Z -> (ls + 80 <= 2 ^ 47)%Z ->
  (forall p, (rs <= p < rs + W)%Z -> exists b, rdn SEGS M (Z_to_bv 64 p) 1 = Some [b]) ->
  ap_rds M kx kf ls W h linesf datak -> ap_ro M ->
  (forall p, (rd <= p < rd + W)%Z -> store_ok SEGS M (Z_to_bv 64 p) 1 = true) ->
  rdn SEGS M (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 5 = Z_to_bv 64 j -> getr regs 6 = Z_to_bv 64 j ->
  getr regs 7 = Z_to_bv 64 (rs + j) -> getr regs 21 = Z_to_bv 64 (rs + j) -> getr regs 16 = Z_to_bv 64 rs ->
  getr regs 28 = Z_to_bv 64 (rd + j) -> getr regs 31 = Z_to_bv 64 (rd + j) -> getr regs 17 = Z_to_bv 64 rd ->
  getr regs 29 = Z_to_bv 64 i -> getr regs 30 = Z_to_bv 64 (8 * i) ->
  getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 3 -> getr regs 22 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 kx -> getr regs 24 = Z_to_bv 64 kf -> getr regs 25 = Z_to_bv 64 ls ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a75c) M rom)
    (fun fin => exists fr' cs' regs' M' p bs, fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a980) M' rom /\ frm_zero cs' /\
       (rd <= p < rd + W)%Z /\ length bs = 1%nat /\ M' = wbytes M (Z_to_bv 64 p) bs /\ ap_fp fr fr' /\
       getr regs' 5 = Z_to_bv 64 (j + 1) /\ getr regs' 6 = Z_to_bv 64 (j + 1) /\
       getr regs' 7 = Z_to_bv 64 (rs + (j + 1)) /\ getr regs' 21 = Z_to_bv 64 (rs + (j + 1)) /\
       getr regs' 28 = Z_to_bv 64 (rd + (j + 1)) /\ getr regs' 31 = Z_to_bv 64 (rd + (j + 1)) /\
       getr regs' 10 = Z_to_bv 64 w /\
       regs_agree (fun r => In r APJ) regs regs').
Proof.
  intros fr cs regs M s kx kf ls W h w i j rs rd linesf datak Hcs Hs As Hj HwW HW AW Hi Hh Ars Hrs Hrs' Ard Hrd Hrd' Hsep
    Akx Hkx Hkx' Akf Hkf Hkf' Als Hls Hls' Hsrc Hrds Hro Hst Rw H2 H5 H6 H7 H21 H16 H28 H31 H17 H29 H30
    H13 H14 H15 H22 H23 H24 H25.
  assert (HjW : (0 <= j < W)%Z) by lia.
  assert (WiH : (0 <= W * i /\ W * i + W <= W * h)%Z) by (split; nia).
  pose proof (apx_lx3 rs W j ltac:(lia) Ars AW HjW) as Lrs.
  pose proof (apx_lx3 rd W j ltac:(lia) Ard AW HjW) as Lrd.
  destruct (apx_b1 M _ (Hsrc _ Lrs)) as (v & Rv & Hv).
  destruct Hrds as (R1 & R2 & R3 & R4 & R5 & R6).
  destruct (R1 v Hv) as (k & Rk & Hk).
  destruct (R2 v Hv) as (x & Rx & Hx).
  assert (Hk0 : (0 <= k < 10)%Z) by lia.
  assert (Hk1 : (0 <= k + 1 < 10)%Z) by lia.
  destruct (R6 k Hk0) as (Alk & Hlk & Hlk' & Adk & Hdk & Hdk').
  destruct (R6 (k + 1)%Z Hk1) as (Alk1 & Hlk1 & Hlk1' & Adk1 & Hdk1 & Hdk1').
  assert (Hpk : (4096 <= datak k + W * i)%Z) by lia.
  assert (Hpk' : (datak k + W * i + W <= 2 ^ 47)%Z) by lia.
  assert (Hpk1 : (4096 <= datak (k + 1)%Z + W * i)%Z) by lia.
  assert (Hpk1' : (datak (k + 1)%Z + W * i + W <= 2 ^ 47)%Z) by lia.
  pose proof (apx_lx3 (datak k + W * i) W j ltac:(lia) (apx_al4 _ _ i Adk AW) AW HjW) as Llo.
  pose proof (apx_lx3 (datak (k + 1)%Z + W * i) W j ltac:(lia) (apx_al4 _ _ i Adk1 AW) AW HjW) as Lhi.
  assert (Plo : (datak k <= Z.lxor (datak k + W * i + j) 3 < datak k + W * h)%Z) by lia.
  assert (Phi : (datak (k + 1)%Z <= Z.lxor (datak (k + 1)%Z + W * i + j) 3 < datak (k + 1)%Z + W * h)%Z) by lia.
  destruct (apx_b1 M _ (R5 k _ Hk0 Plo)) as (lo & Rlo & Hlo).
  destruct (apx_b1 M _ (R5 (k + 1)%Z _ Hk1 Phi)) as (hi & Rhi & Hhi).
  eapply reach_bind.
  { exact (ap_pxA rom (mkFP fr cs) regs M s kx kf ls W h i j rs rd v k (linesf k) (datak k + W * i)
      (linesf (k + 1)%Z) (datak (k + 1)%Z + W * i)
      Hs As HjW HW AW Hi Hh Ars Hrs Hrs' Hrd Hrd' Akx Hkx Hkx' Akf Hkf Hkf' Als Hls Hls' Hv Hk
      Alk Hlk Hlk' Alk1 Hlk1 Hlk1' Hpk Hpk' Hpk1 Hpk1'
      Rv Rk (R3 k Hk0) (R4 k i Hk0 Hi) (R3 (k + 1)%Z Hk1) (R4 (k + 1)%Z i Hk1 Hi)
      H2 H5 H7 H21 H16 H28 H31 H29 H30 H13 H14 H15 H22 H23 H24 H25). }
  intros fin (regs' & -> & R26 & R10 & R8 & HagA).
  assert (G2 : getr regs' 2 = Z_to_bv 64 (s - 160)) by (rewrite (HagA 2%bv ltac:(notin_list)); exact H2).
  assert (G5 : getr regs' 5 = Z_to_bv 64 j) by (rewrite (HagA 5%bv ltac:(notin_list)); exact H5).
  assert (G6 : getr regs' 6 = Z_to_bv 64 j) by (rewrite (HagA 6%bv ltac:(notin_list)); exact H6).
  assert (G7 : getr regs' 7 = Z_to_bv 64 (rs + j)) by (rewrite (HagA 7%bv ltac:(notin_list)); exact H7).
  assert (G21 : getr regs' 21 = Z_to_bv 64 (rs + j)) by (rewrite (HagA 21%bv ltac:(notin_list)); exact H21).
  assert (G14 : getr regs' 14 = Z_to_bv 64 1) by (rewrite (HagA 14%bv ltac:(notin_list)); exact H14).
  assert (G15 : getr regs' 15 = Z_to_bv 64 3) by (rewrite (HagA 15%bv ltac:(notin_list)); exact H15).
  assert (G17 : getr regs' 17 = Z_to_bv 64 rd) by (rewrite (HagA 17%bv ltac:(notin_list)); exact H17).
  assert (G28 : getr regs' 28 = Z_to_bv 64 (rd + j)) by (rewrite (HagA 28%bv ltac:(notin_list)); exact H28).
  assert (G31 : getr regs' 31 = Z_to_bv 64 (rd + j)) by (rewrite (HagA 31%bv ltac:(notin_list)); exact H31).
  eapply reach_weaken; [| exact (ap_pxF rom fr cs regs' M s kf v x rs rd W w j (datak k + W * i) (datak (k + 1)%Z + W * i) lo hi
       Hcs Hs As Hj HwW HW AW Hrs Hrs' Ard Hrd Hrd' Hsep Akf Hkf Hkf' Hv Rx Hx Hpk Hpk' Hpk1 Hpk1' Rlo Hlo Rhi Hhi Hro (Hst _ Lrd) Rw
       G2 G5 G6 G7 G21 R8 R10 R26 G14 G15 G17 G28 G31)].
  intros fin (fr' & cs' & regs'' & M' & bs & -> & Hcs' & Hbs & HM' & Hfp & Q5 & Q6 & Q7 & Q21 & Q28 & Q31 & Q10 & HagF).
  exists fr', cs', regs'', M', (Z.lxor (rd + j) 3), bs.
  split; [reflexivity|]. split; [exact Hcs'|]. split; [exact Lrd|]. split; [exact Hbs|]. split; [exact HM'|].
  split; [exact Hfp|].
  do 7 (split; [assumption|]).
  apply (regs_agree_trans _ regs regs' regs'').
  - eapply regs_agree_mono; [| exact HagA]; unfold APJ; incl_list.
  - eapply regs_agree_mono; [| exact HagF]; unfold APJ; incl_list.
Qed.
End Segs.

Lemma ap_fp_trans : forall fr1 fr2 fr3, ap_fp fr1 fr2 -> ap_fp fr2 fr3 -> ap_fp fr1 fr3.
Proof.
  unfold ap_fp. intros fr1 fr2 fr3 H12 H23 r a b c d e f.
  rewrite (H23 r a b c d e f). apply H12; assumption.
Qed.

Ltac agr Hag := rewrite (Hag _) by (cbv beta; unfold APJ; notin_list).
Ltac set_pc v :=
  lazymatch goal with
  | |- reach _ (@mkst _ _ ?pc _ _) _ => replace pc with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
  end.

Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma ap_jloop : forall (n : nat) fr cs regs (Mj M : word -> option byte) (s kx kf ls W h w i j rs rd : Z) (linesf datak : Z -> Z),
  Z.of_nat n = (w - j)%Z -> (0 <= j < w)%Z -> frm_zero cs -> rinv [(rd, W)] Mj M ->
  (4096 + 160 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (w <= W)%Z -> (W <= 80000)%Z -> (W mod 4 = 0)%Z -> (0 <= i < h)%Z -> (h <= 20000)%Z ->
  (rs mod 4 = 0)%Z -> (4096 <= rs)%Z -> (rs + W <= 2 ^ 47)%Z ->
  (rd mod 4 = 0)%Z -> (4096 <= rd)%Z -> (rd + W <= 2 ^ 47)%Z -> (rd + W <= s - 160 \/ s <= rd)%Z ->
  (kx mod 4 = 0)%Z -> (4096 <= kx)%Z -> (kx + 1024 <= 2 ^ 47)%Z -> (kf mod 4 = 0)%Z -> (4096 <= kf)%Z -> (kf + 1024 <= 2 ^ 47)%Z ->
  (ls mod 8 = 0)%Z -> (4096 <= ls)%Z -> (ls + 80 <= 2 ^ 47)%Z ->
  (forall p, (rs <= p < rs + W)%Z -> exists b, rdn SEGS Mj (Z_to_bv 64 p) 1 = Some [b]) ->
  (forall p, (rd <= p < rd + W)%Z -> store_ok SEGS Mj (Z_to_bv 64 p) 1 = true) ->
  ap_rds Mj kx kf ls W h linesf datak -> ap_ro Mj -> ap_apart rd W kx kf ls W h linesf datak ->
  rdn SEGS Mj (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 5 = Z_to_bv 64 j -> getr regs 6 = Z_to_bv 64 j ->
  getr regs 7 = Z_to_bv 64 (rs + j) -> getr regs 21 = Z_to_bv 64 (rs + j) -> getr regs 16 = Z_to_bv 64 rs ->
  getr regs 28 = Z_to_bv 64 (rd + j) -> getr regs 31 = Z_to_bv 64 (rd + j) -> getr regs 17 = Z_to_bv 64 rd ->
  getr regs 29 = Z_to_bv 64 i -> getr regs 30 = Z_to_bv 64 (8 * i) ->
  getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 3 -> getr regs 22 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 kx -> getr regs 24 = Z_to_bv 64 kf -> getr regs 25 = Z_to_bv 64 ls ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a75c) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a67c) M' rom /\ frm_zero cs' /\
       rinv [(rd, W)] Mj M' /\ regs_agree (fun r => In r APJ) regs regs' /\ ap_fp fr fr').
Proof.
  intros n. induction n as [|n IH];
  intros fr cs regs Mj M s kx kf ls W h w i j rs rd linesf datak
    Hn Hj Hcs HM Hs As HwW HW AW Hi Hh Ars Hrs Hrs' Ard Hrd Hrd' Hsep Akx Hkx Hkx' Akf Hkf Hkf' Als Hls Hls'
    Rsrc Sdst Hrds Hro Hap R108 H2 H5 H6 H7 H21 H16 H28 H31 H17 H29 H30 H13 H14 H15 H22 H23 H24 H25.
  { cbn [Z.of_nat] in Hn. lia. }
  assert (Hlo : (rd + W <= 0x12588 \/ 0x125d8 <= rd)%Z) by (destruct Hap as (_ & _ & _ & _ & X); exact X).
  pose proof HM as [Hgrow _].
  eapply reach_bind.
  { eapply (ap_px rom fr cs regs M s kx kf ls W h w i j rs rd linesf datak); try eassumption; try lia.
    - intros p Hp. destruct (Rsrc p Hp) as [b Rb].
      destruct (rdn_grows _ _ _ _ _ _ Hgrow Rb) as (bs' & Rb' & Lb').
      destruct bs' as [|b' [|]]; try discriminate Lb'. exists b'; exact Rb'.
    - eapply ap_rds_keep; [exact HM | exact Hap | lia | lia | lia | lia | lia | lia | lia | exact Hrds].
    - eapply ap_ro_keep; [exact HM | exact Hlo | exact Hro].
    - intros p Hp. eapply reg_sok; [exact Hgrow | exact (Sdst p Hp) | lia | lia | lia | lia].
    - rewrite (rdn_rinv1 rd W Mj M (s - 108) 4 HM) by lia. exact R108. }
  intros fin (fr' & cs' & regs' & M' & p & bs & -> & Hcs' & Hp & Hbs & -> & Hfp & H5' & H6' & H7' & H21' & H28' & H31' & H10' & Hag).
  assert (HM' : rinv [(rd, W)] Mj (wbytes M (Z_to_bv 64 p) bs)).
  { eapply rinv_wbytes; [exact HM | rewrite Hbs; reflexivity | lia | lia | ].
    exists (rd, W). split; [left; reflexivity | cbn [fst snd]; lia]. }
  destruct (Z_lt_ge_dec (j + 1) w) as [Hlt|Hge].
  - eapply reach_step; [reflexivity | | ].
    { eapply step_branch_tk_gen; [exact F_3a980 | reflexivity | exact D_3a980 | ].
      rewrite H6', H10'. ex_br. }
    set_pc 0x3a75c%Z.
    eapply reach_weaken.
    2: { eapply (IH fr' cs' regs' Mj (wbytes M (Z_to_bv 64 p) bs) s kx kf ls W h w i (j + 1)%Z rs rd linesf datak);
         try eassumption; try lia; agr Hag; assumption. }
    intros fin (fr'' & cs'' & regs'' & M'' & -> & Hcs'' & HM'' & Hag' & Hfp').
    exists fr'', cs'', regs'', M''. split; [reflexivity|]. split; [exact Hcs''|]. split; [exact HM''|]. split.
    + eapply regs_agree_trans; eassumption.
    + eapply ap_fp_trans; eassumption.
  - eapply reach_step; [reflexivity | | ].
    { eapply step_branch_ft_gen; [exact F_3a980 | reflexivity | exact D_3a980 | ].
      rewrite H6', H10'. ex_br. }
    set_pc 0x3a984%Z.
    eapply reach_step; [reflexivity | eapply step_jal_x0; [exact F_3a984 | reflexivity | exact D_3a984] | ].
    set_pc 0x3a67c%Z.
    apply reach_done.
    exists fr', cs', regs', (wbytes M (Z_to_bv 64 p) bs).
    split; [reflexivity|]. split; [exact Hcs'|]. split; [exact HM'|]. split; [exact Hag | exact Hfp].
Qed.
End Segs.

Ltac rd_dis := let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]); destruct Hr.
Ltac rdm HR := rewrite (rinv_rdn SEGS _ _ _ _ _ HR) by first [lia | rd_dis].
Ltac gchain := first [ assumption
  | match goal with GA : regs_agree _ ?a ?b |- getr ?b ?r = _ =>
      rewrite (GA r) by (cbv beta; try unfold APJ; try unfold API; notin_list); gchain end ].
Ltac aincl := let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbv beta in Hr |- *; try unfold APJ in Hr; unfold API; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.

Section Segs.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Lemma ap_iloop : forall (n : nat) fr cs regs (M0 M : word -> option byte) (s kx kf ls wpl h w i datas dd pixd : Z) (linesf datak : Z -> Z),
  Z.of_nat n = (h - i)%Z -> (0 <= i < h)%Z -> frm_zero cs ->
  rinv [(dd, (4 * wpl * h)%Z); ((s - 136)%Z, 8%Z)] M0 M ->
  (4096 + 160 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (1 <= w < 2 ^ 31)%Z -> (w <= 4 * wpl)%Z -> (wpl <= 20000)%Z -> (h <= 20000)%Z ->
  (datas mod 4 = 0)%Z -> (4096 <= datas)%Z -> (datas + 4 * wpl * h <= 2 ^ 47)%Z ->
  (dd mod 4 = 0)%Z -> (4096 <= dd)%Z -> (dd + 4 * wpl * h <= 2 ^ 47)%Z -> (dd + 4 * wpl * h <= s - 160 \/ s <= dd)%Z ->
  (kx mod 4 = 0)%Z -> (4096 <= kx)%Z -> (kx + 1024 <= 2 ^ 47)%Z -> (kf mod 4 = 0)%Z -> (4096 <= kf)%Z -> (kf + 1024 <= 2 ^ 47)%Z ->
  (ls mod 8 = 0)%Z -> (4096 <= ls)%Z -> (ls + 80 <= 2 ^ 47)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
  (forall p, (datas <= p < datas + 4 * wpl * h)%Z -> exists b, rdn SEGS M0 (Z_to_bv 64 p) 1 = Some [b]) ->
  (forall p, (dd <= p < dd + 4 * wpl * h)%Z -> store_ok SEGS M0 (Z_to_bv 64 p) 1 = true) ->
  store_ok SEGS M0 (Z_to_bv 64 (s - 136)) 8 = true ->
  ap_rds M0 kx kf ls (4 * wpl) h linesf datak -> ap_ro M0 ->
  ap_apart dd (4 * wpl * h) kx kf ls (4 * wpl) h linesf datak -> ap_apart (s - 160) 160 kx kf ls (4 * wpl) h linesf datak ->
  rdn SEGS M0 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixd) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wpl) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 wpl) ->
  rdn SEGS M (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 (i * wpl)) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 dd) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 datas) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 11 = Z_to_bv 64 (i * wpl) -> getr regs 12 = Z_to_bv 64 i ->
  getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 3 -> getr regs 18 = Z_to_bv 64 wpl ->
  getr regs 22 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 kx -> getr regs 24 = Z_to_bv 64 kf -> getr regs 25 = Z_to_bv 64 ls ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a6a0) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3aa18) M' rom /\ frm_zero cs' /\
       rinv [(dd, (4 * wpl * h)%Z); ((s - 136)%Z, 8%Z)] M0 M' /\ getr regs' 8 = Z_to_bv 64 pixd /\
       regs_agree (fun r => In r API) regs regs' /\ ap_fp fr fr').
Proof.
  intros n; induction n as [|n IH];
  intros fr cs regs M0 M s kx kf ls wpl h w i datas dd pixd linesf datak Hn Hi Hcs HR Hs As Hw Hw4 Hwpl Hh Ads Hds Hds' Add Hdd Hdd' Hdf
    Akx Hkx Hkx' Akf Hkf Hkf' Als Hls Hls' Hpd Hpx Hst Hst136 Hrds Hro Hap Hapf R160 R152 R144 R136 R128 R120 R112 R108
    H2 H11 H12 H13 H14 H15 H18 H22 H23 H24 H25.
  { lia. }
  assert (Hwp : (1 <= wpl)%Z) by lia.
  assert (H4i : (0 <= 4 * wpl * i)%Z) by nia.
  assert (H4i1 : (4 * wpl * i + 4 * wpl <= 4 * wpl * h)%Z) by nia.
  assert (H4h : (0 <= 4 * wpl * h)%Z) by nia.
  assert (Hdd0 : (dd + 4 * wpl * h <= 75144 \/ 75224 <= dd)%Z) by (destruct Hap as (_ & _ & _ & _ & X); exact X).
  assert (Hs0 : (s - 160 + 160 <= 75144 \/ 75224 <= s - 160)%Z) by (destruct Hapf as (_ & _ & _ & _ & X); exact X).
  assert (Hg : mem_grows M0 M) by exact (proj1 HR).
  assert (M144 : rdn SEGS M (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 wpl)) by (rdm HR; exact R144).
  assert (M128 : rdn SEGS M (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 dd)) by (rdm HR; exact R128).
  assert (M120 : rdn SEGS M (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 datas)) by (rdm HR; exact R120).
  assert (M108 : rdn SEGS M (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w)) by (rdm HR; exact R108).
  eapply reach_bind.
  { eapply (ap_row rom (mkFP fr cs) regs M s datas dd wpl h w i); first [assumption | lia]. }
  intros ? (regs1 & -> & G5 & G6 & G7 & G21 & G28 & G31 & G16 & G17 & G29 & G30 & GA1).
  eapply reach_bind.
  { eapply (ap_jloop rom (Z.to_nat w) fr cs regs1 M M s kx kf ls (4 * wpl) h w i 0
              (datas + 4 * wpl * i) (dd + 4 * wpl * i) linesf datak);
    rewrite ?Z.add_0_r;
    lazymatch goal with
         | |- ((4 * wpl) mod 4 = 0)%Z => replace (4 * wpl)%Z with (wpl * 4)%Z by ring; apply Z.mod_mul; lia
         | |- ((datas + 4 * wpl * i) mod 4 = 0)%Z =>
             replace (datas + 4 * wpl * i)%Z with (datas + (wpl * i) * 4)%Z by ring; rewrite Z.mod_add by lia; exact Ads
         | |- ((dd + 4 * wpl * i) mod 4 = 0)%Z =>
             replace (dd + 4 * wpl * i)%Z with (dd + (wpl * i) * 4)%Z by ring; rewrite Z.mod_add by lia; exact Add
         | |- forall p, _ -> exists b, _ =>
             let p := fresh "p" in let Hp := fresh "Hp" in intros p Hp;
             let b := fresh "b" in let Hb := fresh "Hb" in destruct (Hpx p ltac:(lia)) as [b Hb];
             let bs' := fresh "bs" in let Hb' := fresh "Hb" in let Hl := fresh "Hl" in
             destruct (rdn_grows SEGS M0 M 1 (Z_to_bv 64 p) [b] Hg Hb) as [bs' [Hb' Hl]];
             let b' := fresh "b" in destruct bs' as [|b' [|? ?]]; cbn [length] in Hl; try lia; exists b'; exact Hb'
         | |- forall p, _ -> store_ok _ _ _ _ = true =>
             let p := fresh "p" in let Hp := fresh "Hp" in intros p Hp;
             apply (reg_sok SEGS M0 M p 1 p 1); [exact Hg | apply Hst; lia | lia | lia | lia | lia]
         | |- ap_rds _ _ _ _ _ _ _ _ =>
             eapply ap_rds_keepR; [exact HR | | lia | lia | lia | lia | lia | lia | lia | exact Hrds];
             constructor; [split; [exact Hap | cbn [snd]; lia] |];
             constructor; [split; [eapply ap_apart_sub; [exact Hapf | cbn [fst snd]; lia | cbn [fst snd]; lia] | cbn [snd]; lia] |];
             constructor
         | |- ap_ro _ =>
             eapply ap_ro_keepR; [exact HR | | exact Hro];
             constructor; [cbn [fst snd]; lia | constructor; [cbn [fst snd]; lia | constructor]]
         | |- ap_apart _ _ _ _ _ _ _ _ _ => eapply ap_apart_sub; [exact Hap | lia | lia]
         | |- getr _ _ = _ => gchain
         | |- rinv _ _ _ => apply rinv_refl
         | |- _ => first [assumption | lia]
         end. }
  intros ? (fr2 & cs2 & regs2 & M2 & -> & Hcs2 & HR2 & GA2 & Hfp2).
  assert (HRM2 : rinv [(dd, (4 * wpl * h)%Z); ((s - 136)%Z, 8%Z)] M0 M2).
  { eapply rinv_trans; [exact HR |]. eapply rinv_weaken; [exact HR2 |].
    intros r Hr; cbn [In] in Hr; destruct Hr as [<-|[]].
    exists (dd, (4 * wpl * h)%Z); split; [left; reflexivity | cbn [fst snd]; lia]. }
  assert (Hg2 : mem_grows M0 M2) by exact (proj1 HRM2).
  assert (N136 : rdn SEGS M2 (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 (i * wpl))) by (rdm HR2; exact R136).
  assert (S136 : store_ok SEGS M2 (Z_to_bv 64 (s - 136)) 8 = true).
  { apply (reg_sok SEGS M0 M2 (s - 136) 8 (s - 136) 8); [exact Hg2 | exact Hst136 | lia | lia | lia | lia]. }
  assert (N152 : rdn SEGS M2 (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wpl)) by (rdm HRM2; exact R152).
  assert (N144 : rdn SEGS M2 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 wpl)) by (rdm HRM2; exact R144).
  assert (N112 : rdn SEGS M2 (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h)) by (rdm HRM2; exact R112).
  destruct (Z_lt_ge_dec (i + 1) h) as [Hlt | Hge].
  -
    eapply reach_bind.
    { eapply (ap_rowinc rom (mkFP fr2 cs2) regs2 M2 s wpl h i); first [assumption | lia | gchain]. }
    intros ? (regs3 & M3 & -> & HR3 & N136' & G11 & G12 & G18 & GA3).
    assert (HRM3 : rinv [(dd, (4 * wpl * h)%Z); ((s - 136)%Z, 8%Z)] M0 M3).
    { eapply rinv_trans; [exact HRM2 |]. eapply rinv_incl; [exact HR3 |].
      intros r Hr; cbn [In] in Hr; destruct Hr as [<-|[]]. right; left; reflexivity. }
    eapply reach_weaken.
    2: { eapply (IH fr2 cs2 regs3 M0 M3 s kx kf ls wpl h w (i + 1)%Z datas dd pixd linesf datak).
         all: first [assumption | lia | gchain]. }
    intros ? (fr4 & cs4 & regs4 & M4 & -> & Hcs4 & HR4 & G8 & GA4 & Hfp4).
    exists fr4, cs4, regs4, M4.
    split; [reflexivity |]. split; [exact Hcs4 |]. split; [exact HR4 |]. split; [exact G8 |]. split.
    + eapply regs_agree_trans; [| exact GA4].
      eapply regs_agree_trans; [| eapply regs_agree_mono; [| exact GA3]; aincl].
      eapply regs_agree_trans; [| eapply regs_agree_mono; [| exact GA2]; aincl].
      eapply regs_agree_mono; [| exact GA1]; aincl.
    + eapply ap_fp_trans; [exact Hfp2 | exact Hfp4].
  -
    eapply reach_weaken.
    2: { eapply (ap_iexit rom (mkFP fr2 cs2) regs2 M2 s wpl h i pixd).
         all: first [assumption | lia | gchain | (rdm HRM2; exact R160)]. }
    intros ? (regs3 & M3 & -> & HR3 & G8 & GA3).
    exists fr2, cs2, regs3, M3.
    split; [reflexivity |]. split; [exact Hcs2 |].
    split.
    { eapply rinv_trans; [exact HRM2 |]. eapply rinv_incl; [exact HR3 |].
      intros r Hr; cbn [In] in Hr; destruct Hr as [<-|[]]. right; left; reflexivity. }
    split; [exact G8 |]. split.
    + eapply regs_agree_trans; [| eapply regs_agree_mono; [| exact GA3]; aincl].
      eapply regs_agree_trans; [| eapply regs_agree_mono; [| exact GA2]; aincl].
      eapply regs_agree_mono; [| exact GA1]; aincl.
    + exact Hfp2.
Qed.
End Segs.
