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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptBilSegs V2LeptBilSegs2 V2LeptBilSegs2vR V2LeptBilSegs2vS.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition VR (datad wpld h : Z) : list (Z * Z) := [(datad, (4 * (wpld * h))%Z)].
Definition VKT : list reg := [7; 28; 29; 30; 31]%bv.

Definition vgeo (s datat datad wpl wpld w h spat rng kval : Z) : Prop :=
  (4096 + 320 <= s <= 2 ^ 47)%Z /\ (s mod 16 = 0)%Z /\
  (1 <= w)%Z /\ (1 <= h)%Z /\ (w + 22 <= 20000)%Z /\ (h + 22 <= 20000)%Z /\ wpl = wpl_of (w + 22) 8 /\ (4 * (wpl * (h + 22)) <= 67108864)%Z /\
  wpld = wpl_of w 8 /\
  (4096 <= datat)%Z /\ (datat + 4 * (wpl * (h + 22)) <= 2 ^ 47)%Z /\ (datat mod 4 = 0)%Z /\
  (4096 <= datad)%Z /\ (datad + 4 * (wpld * h) <= 2 ^ 47)%Z /\ (datad mod 4 = 0)%Z /\
  (4096 <= spat)%Z /\ (spat + 44 <= 2 ^ 47)%Z /\ (spat mod 4 = 0)%Z /\ (4096 <= rng)%Z /\ (rng + 1024 <= 2 ^ 47)%Z /\ (0 <= kval <= 255)%Z /\
  (datad + 4 * (wpld * h) <= datat \/ datat + 4 * (wpl * (h + 22)) <= datad)%Z /\
  (datad + 4 * (wpld * h) <= s - 320 \/ s <= datad)%Z /\
  (datad + 4 * (wpld * h) <= spat \/ spat + 44 <= datad)%Z /\
  (datad + 4 * (wpld * h) <= rng \/ rng + 1024 <= datad)%Z /\
  (datad + 4 * (wpld * h) <= bc_chalf \/ bc_chalf + 8 <= datad)%Z.

Definition vmem0 (s datat datad wpl wpld w h spat rng : Z) (M : word -> option byte) : Prop :=
  rd_bytes M datat (4 * (wpl * (h + 22))) /\ store_ok SEGS M (Z_to_bv 64 datad) (Z.to_nat (4 * (wpld * h))) = true /\
  kcell_ok spat 11 M /\ kcell_ok rng 256 M /\ img_none M bc_chalf 8 /\
  rdn SEGS M (Z_to_bv 64 (s - 232)) 8 = Some (Z_to_le_bytes 8 datad) /\
  rdn SEGS M (Z_to_bv 64 (s - 216)) 8 = Some (Z_to_le_bytes 8 h) /\
  rdn SEGS M (Z_to_bv 64 (s - 208)) 8 = Some (Z_to_le_bytes 8 datat) /\
  rdn SEGS M (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 bc_cptr) /\
  rdn SEGS M (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 0) /\
  rdn SEGS M (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 w).

Definition vfix (regs : bvmap 5 word) (s kval wpld spat rng wpl : Z) : Prop :=
  getr regs 1 = Z_to_bv 64 11 /\ getr regs 2 = Z_to_bv 64 (s - 320) /\ getr regs 8 = Z_to_bv 64 (-10) /\ getr regs 9 = Z_to_bv 64 kval /\
  getr regs 10 = Z_to_bv 64 wpld /\ getr regs 18 = Z_to_bv 64 10 /\ getr regs 19 = Z_to_bv 64 (- 2 ^ 31) /\ getr regs 20 = Z_to_bv 64 1 /\
  getr regs 21 = Z_to_bv 64 spat /\ getr regs 22 = Z_to_bv 64 3 /\ getr regs 23 = Z_to_bv 64 rng /\ getr regs 24 = Z_to_bv 64 1 /\
  getr regs 25 = Z_to_bv 64 wpl /\ getr regs 26 = Z_to_bv 64 (2 ^ 64 - 1 - rng).

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma vtp_swrap32 : forall t r k : Z, (- 2 ^ 31 <= r < 2 ^ 31)%Z -> t = (r + k * 2 ^ 32)%Z -> bv_swrap 32 t = r.
Proof. intros t r k Hr ->. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia. Qed.

Lemma vtp_addw : forall a b : Z, (- 2 ^ 31 <= a + b < 2 ^ 31)%Z -> v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b H. unfold v_addw. rewrite !u_Z2bv_mod. f_equal.
  apply vtp_swrap32 with (k := (- 2 ^ 32 * (a / 2 ^ 64) - 2 ^ 32 * (b / 2 ^ 64))%Z); lia.
Qed.

Lemma vtp_subw : forall a b : Z, (- 2 ^ 31 <= a - b < 2 ^ 31)%Z -> v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b H. unfold v_subw. rewrite !u_Z2bv_mod. f_equal.
  apply vtp_swrap32 with (k := (- 2 ^ 32 * (a / 2 ^ 64) + 2 ^ 32 * (b / 2 ^ 64))%Z); lia.
Qed.

Lemma vtp_swrap32_mod : forall t r : Z, (- 2 ^ 31 <= r < 2 ^ 31)%Z -> (t mod 2 ^ 32 = r mod 2 ^ 32)%Z -> bv_swrap 32 t = r.
Proof. intros t r Hr Ht. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia. Qed.

Lemma vtp_mulw : forall a b : Z, (- 2 ^ 31 <= a * b < 2 ^ 31)%Z -> v_mulw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b H. unfold v_mulw. rewrite !u_Z2bv_mod. f_equal. apply vtp_swrap32_mod; [exact H |].
  assert (Ea : ((a mod 2 ^ 64) mod 2 ^ 32 = a mod 2 ^ 32)%Z) by lia.
  assert (Eb : ((b mod 2 ^ 64) mod 2 ^ 32 = b mod 2 ^ 32)%Z) by lia.
  rewrite (Z.mul_mod (a mod 2 ^ 64) (b mod 2 ^ 64) (2 ^ 32)) by lia. rewrite Ea, Eb.
  rewrite <- (Z.mul_mod a b (2 ^ 32)) by lia. reflexivity.
Qed.

Lemma vtp_addiw : forall (a i : Z), (- 2 ^ 31 <= a + i < 2 ^ 31)%Z -> v_addiw (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof.
  intros a i H. unfold v_addiw. rewrite u_Z2bv_mod. f_equal.
  apply vtp_swrap32 with (k := (- 2 ^ 32 * (a / 2 ^ 64))%Z); lia.
Qed.

Lemma vtp_signed : forall a : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 a) = a.
Proof.
  intros a Ha. unfold bv_signed. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia.
Qed.

Lemma vtp_lts : forall a b : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. intros a b Ha Hb. unfold c_lts, bv_lts. rewrite !vtp_signed by lia. reflexivity. Qed.

Lemma vtp_ltu : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma vtp_eq : forall a b : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b)%Z.
Proof.
  intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_Z2bv_mod.
  destruct (Z.eqb_spec a b) as [E | E].
  - subst b. rewrite !Z.eqb_refl. reflexivity.
  - apply Z.eqb_neq. lia.
Qed.

Lemma vtp_sltu : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if (a <? b)%Z then 1 else 0).
Proof. intros a b Ha Hb. unfold v_sltu. rewrite vtp_ltu by lia. destruct (a <? b)%Z; reflexivity. Qed.

Lemma vtp_slti : forall a i : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z ->
  v_slti (Z_to_bv 64 a) i = Z_to_bv 64 (if (a <? i)%Z then 1 else 0).
Proof. intros a i Ha. unfold v_slti, zsig. rewrite vtp_signed by lia. destruct (a <? i)%Z; reflexivity. Qed.

Lemma vtp_slli2 : forall a : Z, v_slli (Z_to_bv 64 a) 2 = Z_to_bv 64 (4 * a).
Proof. intros a. rewrite zbv_slli by lia. f_equal. change (2 ^ 2)%Z with 4%Z. ring. Qed.

Lemma vtp_andi3 : forall b x : Z, (0 <= b + 4 * x < 2 ^ 64)%Z -> (b mod 4 = 0)%Z -> v_andi (Z_to_bv 64 (b + 4 * x)) 3 = Z_to_bv 64 0.
Proof.
  intros b x H Hb. unfold v_andi. rewrite u_Z2bv by lia. change (bv_wrap 64 3) with 3%Z.
  change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z. f_equal. lia.
Qed.

Lemma vtp_lx3 : forall a W c : Z, (0 <= a)%Z -> (a mod 4 = 0)%Z -> (W mod 4 = 0)%Z -> (0 <= c < W)%Z ->
  (a <= Z.lxor (a + c) 3 < a + W)%Z.
Proof. intros a W c Ha Aa AW Hc. rewrite lxor3_eq by lia. lia. Qed.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma vtp_cell : forall z, (0 <= z < 2 ^ 32)%Z -> bv_extract 0%N 32%N (le_bytes_to_word (Z_to_le_bytes 4 z)) = Z_to_bv 32 z.
Proof.
  intros z Hz. unfold le_bytes_to_word. rewrite (lez4 z Hz).
  apply bv_eq. rewrite bv_extract_unsigned, !Z_to_bv_unsigned. change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z. change (Z.of_N 32) with 32%Z.
  rewrite (Z.mod_small z (2 ^ 64)) by lia. rewrite (Z.mod_small z (2 ^ 64)) by lia. reflexivity.
Qed.

Lemma vtp_sbox_rd : forall x, (0 <= x < 2 ^ 32)%Z -> fpv_rdw FMT_S (Z_to_bv 64 (sbox x)) = x.
Proof.
  intros x Hx. unfold sbox. rewrite zbv_self. cbn [fpv_rdw fpv_box]. rewrite fpv_unbox_box, Z_to_bv_unsigned.
  apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.

Lemma vtp_box : forall x, nan_box (Z_to_bv 32 x) = Z_to_bv 64 (sbox x).
Proof. intros x. unfold sbox. cbn [fpv_box]. rewrite zbv_self. reflexivity. Qed.

Lemma vtp_xori3 : forall a, (0 <= a < 2 ^ 64)%Z -> v_xori (Z_to_bv 64 a) 3 = Z_to_bv 64 (Z.lxor a 3).
Proof. intros a Ha. unfold v_xori. rewrite u_Z2bv by lia. change (bv_wrap 64 3) with 3%Z. reflexivity. Qed.

#[local] Instance vtp_fxd : FPState | 100 := mkFP bvmap_empty (Z_to_bv 32 0).

Definition vtp_lit (n : N) (z : Z) : bv n := Z_to_bv n z.

Local Ltac canon1 t :=
  match t with
  | context C [@BV ?n ?z _] => let t' := context C [vtp_lit n z] in canon1 t'
  | _ => t
  end.
Local Ltac canon2 t :=
  match t with
  | context C [vtp_lit ?n ?z] => let t' := context C [@BV n z (I <: BvWf n z)] in canon2 t'
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

Local Ltac frd :=
  repeat match goal with
  | |- context [fpv_read ?F ?fmt ?r] =>
      is_var F;
      match goal with
      | H : reg_get F ?r0 = ?val |- _ =>
          let b := eval vm_compute in (bv_eqb r r0) in
          lazymatch b with
          | true => let E := fresh "E" in
                    assert (E : fpv_read F fmt r = fpv_rdw fmt val)
                      by (change (fpv_rdw fmt (reg_get F r) = fpv_rdw fmt val); replace r with r0 by bveq; rewrite H; reflexivity);
                    rewrite E; clear E
          end
      end
  end;
  rewrite ?vtp_sbox_rd by lia.

Local Ltac csgen FZ :=
  repeat lazymatch goal with |- context [mkFP _ (fpv_acc ?c ?fl)] =>
    let H := fresh "FZ" in
    pose proof (fpv_frm_acc c fl FZ) as H;
    let c' := fresh "cs" in
    set (c' := fpv_acc c fl) in *; clearbody c'; clear FZ; rename H into FZ
  end.

Local Ltac wcl :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_closed (v_addi a b)
  | |- context [v_xor ?a ?b] => wlit_closed (v_xor a b)
  | |- context [v_xori ?a ?b] => wlit_closed (v_xori a b)
  | |- context [v_sltiu ?a ?b] => wlit_closed (v_sltiu a b)
  end.

Local Ltac vsimp :=
  repeat match goal with
  | |- context [bv_extract _ _ (le_bytes_to_word (Z_to_le_bytes 4 ?z))] => rewrite (vtp_cell z) by lia
  | |- context [v_addi (Z_to_bv 64 ?a) ?i] => rewrite (zbv_addi a i)
  | |- context [v_add (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_add a b)
  | |- context [v_sub (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_sub a b)
  | |- context [v_addw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (vtp_addw a b) by lia
  | |- context [v_subw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (vtp_subw a b) by lia
  | |- context [v_addiw (Z_to_bv 64 ?a) ?i] => rewrite (vtp_addiw a i) by lia
  | |- context [v_slli (Z_to_bv 64 ?a) 2] => rewrite (vtp_slli2 a)
  | |- context [v_andi (Z_to_bv 64 (?b + 4 * ?x)) 3] => rewrite (vtp_andi3 b x) by (first [lia | assumption])
  | |- context [v_sltiu (Z_to_bv 64 ?a) 1] => rewrite (zbv_seqz_nz a) by lia
  | |- context [v_sltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (vtp_sltu a b) by lia
  | |- context [v_slti (Z_to_bv 64 ?a) ?i] => rewrite (vtp_slti a i) by lia
  | |- context [v_mul (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_mul a b)
  | |- context [v_mulw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (vtp_mulw a b) by lia
  | |- context [if (?a <? ?b)%Z then ?x else ?y] =>
      first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
  | |- context [if true then ?x else ?y] => change (if true then x else y) with x
  | |- context [if false then ?x else ?y] => change (if false then x else y) with y
  | |- context [v_xori (Z_to_bv 64 ?a) 3] => rewrite (vtp_xori3 a) by lia
  end.

Local Ltac unorm2 :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (u_Z2bv z) by lia
  | |- context [bv_unsigned (Z_to_bv 32 ?z)] => rewrite (fp_u_Z2bv32 z) by lia
  end.

Local Ltac fold_all :=
  repeat match goal with
  | n := ?b |- _ => progress change b with n
  end.

Local Ltac disj := first [ (repeat split; reflexivity) | (left; disj) | (right; disj) ].

Local Ltac ldt := gsimp; hregs; lits; wcl; vsimp; rewrite ?zbv_addi, ?Z.add_0_r;
  first [ eassumption
        | match goal with H : rdn ?sg ?m (Z_to_bv 64 ?a') ?n = _ |- rdn ?sg ?m (Z_to_bv 64 ?a) ?n = _ =>
            replace a with a' by (first [lia | (f_equal; lia)]); exact H end ].

Local Ltac brt := gsimp; hregs; lits; wcl; vsimp; unorm2;
  first [ cond_compute
        | (rewrite ?vtp_eq by lia; rewrite ?vtp_lts by lia; rewrite ?vtp_ltu by lia;
           first [ apply Z.eqb_neq | apply Z.eqb_eq | apply Z.ltb_ge | apply Z.ltb_lt ]; lia) ].

Local Ltac st1 FZ :=
  let Fw := fresh "Fw" in let Dw := fresh "Dw" in
  here Fw Dw;
  eapply reach_step; [ reflexivity |
    lazymatch type of Dw with
    | _ = Some (OpImm ALU_ADD _ _ _, _) => eapply step_addi; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm ALU_XOR _ _ _, _) => eapply step_xori; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm ALU_AND _ _ _, _) => eapply step_andi; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm ALU_SLTU _ _ _, _) => eapply step_sltiu; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm ALU_SLT _ _ _, _) => eapply step_slti; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm32 _ _ _, _) => eapply step_addiw; [exact Fw | reflexivity | exact Dw]
    | _ = Some (ShiftImm ALU_SLL _ _ _, _) => eapply step_slli; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op ALU_ADD _ _ _, _) => eapply step_add; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Mul M_MUL _ _ _, _) => eapply step_mul; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Mul32 M_MUL _ _ _, _) => eapply step_mulw; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op ALU_SUB _ _ _, _) => eapply step_sub; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op ALU_SLTU _ _ _, _) => eapply step_sltu; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op ALU_XOR _ _ _, _) => eapply step_xor; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op32 ALU_ADD _ _ _, _) => eapply step_addw; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op32 ALU_SUB _ _ _, _) => eapply step_subw; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu; [exact Fw | reflexivity | exact Dw | ldt]
    | _ = Some (Branch BC_EQ _ _ _, _) =>
        first [ eapply step_beq_ft; [exact Fw | reflexivity | exact Dw | brt]
              | eapply step_beq_tk; [exact Fw | reflexivity | exact Dw | brt] ]
    | _ = Some (Branch BC_NE _ _ _, _) =>
        first [ eapply step_bne_ft; [exact Fw | reflexivity | exact Dw | brt]
              | eapply step_bne_tk; [exact Fw | reflexivity | exact Dw | brt] ]
    | _ = Some (Branch BC_LT _ _ _, _) =>
        first [ eapply step_blt_ft; [exact Fw | reflexivity | exact Dw | brt]
              | eapply step_blt_tk; [exact Fw | reflexivity | exact Dw | brt] ]
    | _ = Some (Branch BC_GE _ _ _, _) =>
        first [ eapply step_bge_ft; [exact Fw | reflexivity | exact Dw | brt]
              | eapply step_bge_tk; [exact Fw | reflexivity | exact Dw | brt] ]
    | _ = Some (Branch BC_LTU _ _ _, _) =>
        first [ eapply step_bltu_ft; [exact Fw | reflexivity | exact Dw | brt]
              | eapply step_bltu_tk; [exact Fw | reflexivity | exact Dw | brt] ]
    | _ = Some (FLoad FMT_S _ _ _, _) => eapply fp_step_flw; [exact Fw | reflexivity | exact Dw | reflexivity | ldt]
    | _ = Some (Fari _ _ _ _ _ _, _) => eapply fpv_step_fari; [exact Fw | reflexivity | exact Dw | exact FZ | reflexivity]
    | _ = Some (Fma _ _ _ _ _ _ _, _) => eapply fpv_step_fma; [exact Fw | reflexivity | exact Dw | exact FZ | reflexivity]
    | _ = Some (Fcvt _ FC_WU _ _ _, _) =>
        eapply fpv_step_fcvt_f_of_x; [exact Fw | reflexivity | exact Dw | disj | disj | exact FZ | reflexivity]
    end | ];
  clear Fw Dw.

Local Ltac nrm FZ :=
  cbn [fp_regs fp_csr]; reduce_bv_eqb_ifs; pcn; fsimp; frd; gsimp; hregs; lits; wcl; vsimp; unorm2;
  rewrite ?Z.add_0_r; fold_all; csgen FZ.

Local Ltac sn FZ := st1 FZ; nrm FZ.

Local Ltac at_exit :=
  lazymatch goal with |- reach _ (@mkst _ _ (Z_to_bv 64 ?p) _ _) _ =>
    let b := eval vm_compute in (orb (Z.eqb p 0x3a3a8) (Z.eqb p 0x3a488)) in
    lazymatch b with true => idtac end
  end.

Local Ltac run FZ := sn FZ; repeat (tryif at_exit then fail else sn FZ).

Section Segs.
Variable rom : word -> option byte.

Lemma v_tap : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (datat H wpl i j k kval spat rng kk s n : Z),
  frm_zero cs ->
  (4096 <= datat)%Z -> (datat + 4 * (wpl * H) <= 2 ^ 47)%Z -> (datat mod 4 = 0)%Z ->
  (1 <= wpl <= 5000)%Z -> (4 * (wpl * H) <= 67108864)%Z ->
  (0 <= j)%Z -> (j + 22 <= 4 * wpl)%Z -> (0 <= i)%Z -> (i + 22 <= H)%Z -> (-10 <= k <= 10)%Z ->
  (4096 <= spat)%Z -> (spat + 44 <= 2 ^ 47)%Z -> (spat mod 4 = 0)%Z -> (4096 <= rng)%Z -> (rng + 1024 <= 2 ^ 47)%Z -> (0 <= kval <= 255)%Z ->
  rd_bytes M datat (4 * (wpl * H)) -> kcell_ok spat 11 M -> kcell_ok rng 256 M ->
  bc_avg kk s n -> (0 <= kk)%Z -> (kk + 1 <= 2048)%Z ->
  getr regs 5 = Z_to_bv 64 0 -> getr regs 6 = Z_to_bv 64 0 ->
  getr regs 7 = Z_to_bv 64 k -> getr regs 8 = Z_to_bv 64 (-10) -> getr regs 9 = Z_to_bv 64 kval ->
  getr regs 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl)) -> getr regs 17 = Z_to_bv 64 (j + 11) ->
  getr regs 18 = Z_to_bv 64 10 -> getr regs 19 = Z_to_bv 64 (- 2 ^ 31) -> getr regs 20 = Z_to_bv 64 1 ->
  getr regs 21 = Z_to_bv 64 spat -> getr regs 22 = Z_to_bv 64 3 -> getr regs 23 = Z_to_bv 64 rng -> getr regs 24 = Z_to_bv 64 1 ->
  getr regs 25 = Z_to_bv 64 wpl -> getr regs 26 = Z_to_bv 64 (2 ^ 64 - 1 - rng) ->
  reg_get fr 14 = Z_to_bv 64 (sbox n) -> reg_get fr 15 = Z_to_bv 64 (sbox s) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a3a8) M rom)
    (fun fin => exists fr' cs' regs' s' n', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 (if (k <? 10)%Z then 0x3a3a8 else 0x3a488)) M rom /\
       frm_zero cs' /\ regs_agree (fun x => In x VKT) regs regs' /\ getr regs' 7 = Z_to_bv 64 (k + 1) /\
       bc_avg (kk + 1) s' n' /\ reg_get fr' 14 = Z_to_bv 64 (sbox n') /\ reg_get fr' 15 = Z_to_bv 64 (sbox s') /\
       pass_fp fr fr').
Proof.
  intros fr cs regs M datat H wpl i j k kval spat rng kk s n FZ Hd1 Hd2 Hd3 Hwpl Hsz Hj1 Hj2 Hi1 Hi2 Hk
    Hp1 Hp2 Hp3 Hg1 Hg2 Hkv RD KS KR BA Hkk1 Hkk2 H5 H6 H7 H8 H9 H12 H17
    H18 H19 H20 H21 H22 H23 H24 H25 H26 F14 F15.
  pose proof (bc_avg_range _ _ _ BA) as (Rs & Rn).
  assert (Hkw : (- 50000 <= k * wpl <= 50000)%Z) by nia.
  assert (Hm1 : (0 <= (i + 11) * wpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hrk1 : (0 <= (i + 11 + k) * wpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hrk2 : (0 <= (H - i - 12 - k) * wpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hrb4 : ((datat + 4 * ((i + 11 + k) * wpl)) mod 4 = 0)%Z).
  { replace (datat + 4 * ((i + 11 + k) * wpl))%Z with (datat + ((i + 11 + k) * wpl) * 4)%Z by ring.
    rewrite Z_mod_plus_full. exact Hd3. }
  assert (XA : (datat + 4 * ((i + 11 + k) * wpl) <= Z.lxor (datat + 4 * ((i + 11 + k) * wpl) + (j + 11)) 3
                < datat + 4 * ((i + 11 + k) * wpl) + 4 * wpl)%Z).
  { apply vtp_lx3; [lia | exact Hrb4 | rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
  destruct (RD (Z.lxor (datat + 4 * ((i + 11 + k) * wpl) + (j + 11)) 3) ltac:(lia)) as [b RB].
  assert (Rb : (0 <= bv_unsigned b <= 255)%Z)
    by (pose proof (bv_unsigned_in_range _ b) as R; unfold bv_modulus in R; cbn in R; lia).
  set (tv := bv_unsigned b) in *.
  remember (datat + 4 * ((i + 11) * wpl))%Z as rp eqn:Erp.
  destruct (KS (Z.abs k) ltac:(lia)) as (xsp & Hxsp & FBsp).
  destruct (KR (Z.abs (kval - tv)) ltac:(lia)) as (xrg & Hxrg & FBrg).
  pose (kern := fst (fpv_ari F_MUL FMT_S RNE xsp xrg)).
  pose (bb := fst (fp_of_int (fp_format FMT_S) RNE false 32 tv)).
  pose (n1 := fst (fpv_ari F_ADD FMT_S RNE n kern)).
  pose (s1 := fst (fpv_fma F_MADD FMT_S RNE kern bb s)).
  assert (T : bc_avg (kk + 1) s1 n1 /\ (0 <= xsp < 2 ^ 32)%Z /\ (0 <= xrg < 2 ^ 32)%Z /\ (0 <= kern < 2 ^ 32)%Z /\
              (0 <= bb < 2 ^ 32)%Z /\ (0 <= s1 < 2 ^ 32)%Z /\ (0 <= n1 < 2 ^ 32)%Z)
    by exact (bc_tap_full kk s n xsp xrg tv BA Hkk1 Hkk2 FBsp FBrg Rb).
  destruct T as (BA1 & Rsp & Rrg & Rk & Rbb & Rs1 & Rn1).
  destruct (Z_lt_le_dec k 0) as [Kn | Kp];
    [assert (Ksg : (k * wpl < 0)%Z) by nia | assert (Ksg : (0 <= k * wpl)%Z) by nia];
    destruct (Z_lt_le_dec (kval - tv) 0) as [Dn | Dp];
    destruct (Z.ltb_spec k 10) as [K10 | K10]; cbv iota.
  all: try (exfalso; lia).
  all: run FZ.
  all: apply reach_done; cbv beta.
  all: eexists; eexists; eexists; exists s1, n1.
  all: split; [reflexivity|].
  all: split; [exact FZ|].
  all: split; [unfold VKT; solve_regs_agree|].
  all: split; [gsimp; first [reflexivity | (f_equal; lia)]|].
  all: split; [exact BA1|].
  all: split; [fsimp; apply vtp_box|].
  all: split; [fsimp; apply vtp_box|].
  all: intros x Hx.
  all: assert (N12 : x <> 12%bv) by (intro E; apply Hx; rewrite E; vm_compute; auto).
  all: assert (N13 : x <> 13%bv) by (intro E; apply Hx; rewrite E; vm_compute; auto).
  all: assert (N14 : x <> 14%bv) by (intro E; apply Hx; rewrite E; vm_compute; auto).
  all: assert (N15 : x <> 15%bv) by (intro E; apply Hx; rewrite E; vm_compute; auto).
  all: rewrite ?fpv_get_other by assumption; reflexivity.
Qed.

Lemma vk_loop : forall (m : nat) (fr : bvmap 5 word) cs regs (M : word -> option byte) (s datat wpl wpld kval spat rng H i j k sm nm : Z),
  Z.of_nat m = (11 - k)%Z -> (-10 <= k <= 10)%Z -> frm_zero cs ->
  (4096 <= datat)%Z -> (datat + 4 * (wpl * H) <= 2 ^ 47)%Z -> (datat mod 4 = 0)%Z -> (1 <= wpl <= 5000)%Z -> (4 * (wpl * H) <= 67108864)%Z ->
  (0 <= i)%Z -> (i + 22 <= H)%Z -> (0 <= j)%Z -> (j + 22 <= 4 * wpl)%Z ->
  (4096 <= spat)%Z -> (spat + 44 <= 2 ^ 47)%Z -> (spat mod 4 = 0)%Z -> (4096 <= rng)%Z -> (rng + 1024 <= 2 ^ 47)%Z -> (0 <= kval <= 255)%Z ->
  rd_bytes M datat (4 * (wpl * H)) -> kcell_ok spat 11 M -> kcell_ok rng 256 M ->
  bc_avg (k + 10) sm nm ->
  getr regs 5 = Z_to_bv 64 0 -> getr regs 6 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 k -> vfix regs s kval wpld spat rng wpl ->
  getr regs 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl)) -> getr regs 17 = Z_to_bv 64 (j + 11) ->
  reg_get fr 14 = Z_to_bv 64 (sbox nm) -> reg_get fr 15 = Z_to_bv 64 (sbox sm) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a3a8) M rom)
    (fun fin => exists fr' cs' regs' sm' nm', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a488) M rom /\ frm_zero cs' /\
       regs_agree (fun x => In x VKT) regs regs' /\ bc_avg 21 sm' nm' /\
       reg_get fr' 14 = Z_to_bv 64 (sbox nm') /\ reg_get fr' 15 = Z_to_bv 64 (sbox sm') /\ pass_fp fr fr').
Proof.
  induction m as [|m IH];
    intros fr cs regs M s datat wpl wpld kval spat rng H i j k sm nm Hm Hk FZ Hd1 Hd2 Hd3 Hwpl Hsz Hi1 Hi2 Hj1 Hj2
      Hp1 Hp2 Hp3 Hg1 Hg2 Hkv RD KS KR BA H5 H6 H7 VF H12 H17 F14 F15.
  - lia.
  - pose proof VF as (V1 & V2 & V8 & V9 & V10 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26).
    eapply reach_bind.
    { exact (v_tap fr cs regs M datat H wpl i j k kval spat rng (k + 10)%Z sm nm FZ Hd1 Hd2 Hd3 Hwpl Hsz Hj1 Hj2 Hi1 Hi2 Hk
               Hp1 Hp2 Hp3 Hg1 Hg2 Hkv RD KS KR BA ltac:(lia) ltac:(lia) H5 H6 H7 V8 V9 H12 H17
               V18 V19 V20 V21 V22 V23 V24 V25 V26 F14 F15). }
    intros fin (fr1 & cs1 & regs1 & s1 & n1 & E1 & FZ1 & RA1 & R7 & BA1 & F141 & F151 & PF1).
    subst fin.
    assert (K : forall r, ~ In r VKT -> getr regs1 r = getr regs r) by exact RA1.
    destruct (Z.ltb_spec k 10) as [Hk10 | Hk10]; cbv iota.
    + eapply reach_weaken;
        [| eapply (IH fr1 cs1 regs1 M s datat wpl wpld kval spat rng H i j (k + 1)%Z s1 n1);
           first [ lia | eassumption
                 | (replace (k + 1 + 10)%Z with (k + 10 + 1)%Z by ring; exact BA1)
                 | (rewrite K by (unfold VKT; notin_list); eassumption)
                 | (unfold vfix; rewrite !K by (unfold VKT; notin_list); exact VF) ] ].
      intros fin (fr2 & cs2 & regs2 & s2 & n2 & E2 & FZ2 & RA2 & BA2 & F142 & F152 & PF2).
      exists fr2, cs2, regs2, s2, n2.
      split; [exact E2|]. split; [exact FZ2|].
      split; [exact (regs_agree_trans _ _ _ _ RA1 RA2)|].
      split; [exact BA2|]. split; [exact F142|]. split; [exact F152|].
      intros x Hx. rewrite (PF2 x Hx). exact (PF1 x Hx).
    + apply reach_done.
      exists fr1, cs1, regs1, s1, n1.
      split; [reflexivity|]. split; [exact FZ1|]. split; [exact RA1|].
      split; [replace 21%Z with (k + 10 + 1)%Z by lia; exact BA1|].
      split; [exact F141|]. split; [exact F151|]. exact PF1.
Qed.

Lemma vl_ag_keep : forall (L : list reg) regs regs' (r : reg) (v : word),
  regs_agree (fun x => In x L) regs regs' -> existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = false ->
  getr regs r = v -> getr regs' r = v.
Proof.
  intros L regs regs' r v AG E H. rewrite AG; [exact H|]. intros Hin.
  assert (T : existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = true).
  { apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

Lemma vl_ag_comp : forall (L1 L2 L : list reg) r1 r2 r3,
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

Lemma vl_pass_refl : forall fr, pass_fp fr fr.
Proof. intros fr r _. reflexivity. Qed.

Lemma vl_pass_trans : forall fr1 fr2 fr3, pass_fp fr1 fr2 -> pass_fp fr2 fr3 -> pass_fp fr1 fr3.
Proof. intros fr1 fr2 fr3 P Q r Hr. rewrite (Q r Hr). exact (P r Hr). Qed.

Lemma vl_fsc_pass : forall fr fr', bc_fsc fr -> pass_fp fr fr' -> bc_fsc fr'.
Proof.
  intros fr fr' (A & B & C) P. unfold bc_fsc.
  rewrite (P 8%bv), (P 9%bv), (P 18%bv); [split; [exact A | split; [exact B | exact C]] | | |];
    let H := fresh "H" in intro H; vm_compute in H; lia.
Qed.

Lemma vl_pass_sub : forall fr fr', (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr r) -> pass_fp fr fr'.
Proof. intros fr fr' P r Hr. apply P. intros H. apply Hr. cbn [In] in *. tauto. Qed.

Lemma vl_fzero : Z_to_bv 64 bc_fzero = Z_to_bv 64 (sbox p_zero).
Proof. vm_compute. reflexivity. Qed.

Ltac vl_agk AG H := apply (vl_ag_keep _ _ _ _ _ AG); [vm_compute; reflexivity | exact H].
Ltac vl_agc A1 A2 := eapply vl_ag_comp; [exact A1 | exact A2 | vm_compute; reflexivity].
Ltac vl_as := match goal with H : ?T |- ?G => constr_eq T G; exact H end.

Lemma vl_out : forall (datad wpld h z : Z) (n : nat),
  (datad + 4 * (wpld * h) <= z \/ z + Z.of_nat n <= datad)%Z ->
  forall r, In r (VR datad wpld h) -> (z + Z.of_nat n <= fst r \/ fst r + snd r <= z)%Z.
Proof. intros datad wpld h z n D r Hr. destruct Hr as [<-|[]]. cbn [fst snd]. lia. Qed.

Lemma vmem_keep : forall s datat datad wpl wpld w h spat rng kval (M0 M : word -> option byte),
  vgeo s datat datad wpl wpld w h spat rng kval -> vmem0 s datat datad wpl wpld w h spat rng M0 ->
  rinv (VR datad wpld h) M0 M -> vmem0 s datat datad wpl wpld w h spat rng M.
Proof.
  intros s datat datad wpl wpld w h spat rng kval M0 M G V RI.
  destruct G as (Gs1 & Gs2 & Gw & Gh & Gw2 & Gh2 & Gwpl & Gsz & Gwpld & Gt1 & Gt2 & Gt3 & Gd1 & Gd2 & Gd3 &
                 Gp1 & Gp2 & Gp3 & Gr1 & Gr2 & Gk & Dt & Ds & Dp & Dr & Dc).
  destruct V as (Rt & SOK & Ksp & Krn & Inone & C232 & C216 & C208 & C200 & C192 & C184).
  assert (RD : forall z (n : nat), (0 <= z)%Z -> (z + Z.of_nat n <= 2 ^ 64)%Z ->
                 (datad + 4 * (wpld * h) <= z \/ z + Z.of_nat n <= datad)%Z ->
                 rdn SEGS M (Z_to_bv 64 z) n = rdn SEGS M0 (Z_to_bv 64 z) n).
  { intros z n Z0 Z1 D. apply (rinv_rdn SEGS _ _ _ z n RI Z0 Z1). apply vl_out. exact D. }
  unfold vmem0. repeat (lazymatch goal with |- _ /\ _ => split end).
  - intros p Hp. destruct (Rt p Hp) as [b Hb]. exists b. rewrite RD; [exact Hb | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia |].
    cbn [Z.of_nat Pos.of_succ_nat]. lia.
  - eapply store_ok_mono; [exact (proj1 RI) | exact SOK].
  - intros k Hk. destruct (Ksp k Hk) as (x & Hx & F). exists x. split; [|exact F].
    rewrite RD; [exact Hx | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - intros k Hk. destruct (Krn k Hk) as (x & Hx & F). exists x. split; [|exact F].
    rewrite RD; [exact Hx | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - intros j Hj. rewrite (proj2 RI (Z_to_bv 64 j)); [exact (Inone j Hj)|].
    intros r Hr. destruct Hr as [<-|[]]. unfold inreg. cbn [fst snd]. unfold bc_chalf in *.
    rewrite u_Z2bv by lia. lia.
  - rewrite RD; [exact C232 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - rewrite RD; [exact C216 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - rewrite RD; [exact C208 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - rewrite RD; [exact C200 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - rewrite RD; [exact C192 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
  - rewrite RD; [exact C184 | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia].
Qed.

Ltac vl_fix AG V :=
  let V' := fresh "V" in pose proof V as V'; unfold vfix in V';
  let f1 := fresh "f" in let f2 := fresh "f" in let f3 := fresh "f" in let f4 := fresh "f" in let f5 := fresh "f" in
  let f6 := fresh "f" in let f7 := fresh "f" in let f8 := fresh "f" in let f9 := fresh "f" in let f10 := fresh "f" in
  let f11 := fresh "f" in let f12 := fresh "f" in let f13 := fresh "f" in let f14 := fresh "f" in
  destruct V' as (f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & f9 & f10 & f11 & f12 & f13 & f14);
  unfold vfix; repeat (lazymatch goal with |- _ /\ _ => split end);
  first [ vl_agk AG f1 | vl_agk AG f2 | vl_agk AG f3 | vl_agk AG f4 | vl_agk AG f5 | vl_agk AG f6 | vl_agk AG f7
        | vl_agk AG f8 | vl_agk AG f9 | vl_agk AG f10 | vl_agk AG f11 | vl_agk AG f12 | vl_agk AG f13 | vl_agk AG f14 ].

Lemma vl_wpl : forall w, (1 <= w)%Z -> (w + 22 <= 20000)%Z ->
  (1 <= wpl_of (w + 22) 8 <= 5000)%Z /\ (w + 22 <= 4 * wpl_of (w + 22) 8)%Z.
Proof.
  intros w H1 H2. unfold wpl_of.
  pose proof (Z.div_mod ((w + 22) * 8 + 31)%Z 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound ((w + 22) * 8 + 31)%Z 32 ltac:(lia)) as B.
  set (q := (((w + 22) * 8 + 31) / 32)%Z) in *. set (r := (((w + 22) * 8 + 31) mod 32)%Z) in *. lia.
Qed.

Lemma vj_loop : forall (m : nat) (fr : bvmap 5 word) cs regs (M0 M : word -> option byte) (s datat datad wpl wpld w h spat rng kval i j : Z),
  Z.of_nat m = (w - j)%Z -> (0 <= j < w)%Z -> (0 <= i < h)%Z -> frm_zero cs ->
  vgeo s datat datad wpl wpld w h spat rng kval -> vmem0 s datat datad wpl wpld w h spat rng M0 -> rinv (VR datad wpld h) M0 M ->
  bc_fsc fr -> vfix regs s kval wpld spat rng wpl ->
  getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl)) -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 (datad + 4 * (i * wpld)) -> getr regs 15 = Z_to_bv 64 j ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a380) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a2d8) M' rom /\ frm_zero cs' /\
       rinv (VR datad wpld h) M0 M' /\ regs_agree (fun r => In r VPL) regs regs' /\ getr regs' 11 = Z_to_bv 64 i /\ pass_fp fr fr').
Proof.
  intros m. induction m as [|m IH];
    intros fr cs regs M0 M s datat datad wpl wpld w h spat rng kval i j Hm Hj Hi FZ G V0 RI FSC FX H11 H12 H13 H14 H15.
  { lia. }
  pose proof (vmem_keep _ _ _ _ _ _ _ _ _ _ M0 M G V0 RI) as V.
  pose proof G as (Gs1 & Gs2 & Gw & Gh & Gw2 & Gh2 & Gwpl & Gsz & Gwpld & Gt1 & Gt2 & Gt3 & Gd1 & Gd2 & Gd3 &
                   Gp1 & Gp2 & Gp3 & Gr1 & Gr2 & Gk & Dt & Ds & Dp & Dr & Dc).
  pose proof V as (Rt & SOK & Ksp & Krn & Inone & C232 & C216 & C208 & C200 & C192 & C184).
  pose proof FX as (X1 & X2 & X8 & X9 & X10 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26).
  pose proof FSC as (Q8 & Q9 & Q18).
  destruct (vl_wpl w ltac:(lia) ltac:(lia)) as [Wp1 Wp2].
  eapply reach_bind; [apply (v_colent rom fr cs regs M s w j); first [vl_as | lia]|].
  intros fin1 (fr1 & r1 & M1 & -> & F14 & F15 & P1 & A5 & A6 & A7 & A16 & A17 & AG1 & EM1). subst M1.
  apply vl_pass_sub in P1.
  assert (FX1 : vfix r1 s kval wpld spat rng wpl) by vl_fix AG1 FX.
  assert (B11 : getr r1 11 = Z_to_bv 64 i) by vl_agk AG1 H11.
  assert (B12 : getr r1 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl))) by vl_agk AG1 H12.
  assert (B13 : getr r1 13 = Z_to_bv 64 1) by vl_agk AG1 H13.
  assert (B14 : getr r1 14 = Z_to_bv 64 (datad + 4 * (i * wpld))) by vl_agk AG1 H14.
  assert (B15 : getr r1 15 = Z_to_bv 64 j) by vl_agk AG1 H15.
  eapply reach_bind;
    [apply vk_loop with (m := 21%nat) (fr := fr1) (cs := cs) (regs := r1) (M := M) (s := s) (datat := datat) (wpl := wpl)
       (wpld := wpld) (kval := kval) (spat := spat) (rng := rng) (H := (h + 22)%Z) (i := i) (j := j) (k := (-10)%Z)
       (sm := p_zero) (nm := p_zero);
       first [vl_as | reflexivity | lia | exact bc_avg_init | (rewrite F14; exact vl_fzero) | (rewrite F15; exact vl_fzero)]|].
  intros fin2 (fr2 & cs2 & r2 & sm & nm & -> & FZ2 & AG2 & AV & F14b & F15b & P2).
  assert (FX2 : vfix r2 s kval wpld spat rng wpl) by vl_fix AG2 FX1.
  pose proof FX2 as (X1b & X2b & X8b & X9b & X10b & X18b & X19b & X20b & X21b & X22b & X23b & X24b & X25b & X26b).
  assert (C11 : getr r2 11 = Z_to_bv 64 i) by vl_agk AG2 B11.
  assert (C12 : getr r2 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl))) by vl_agk AG2 B12.
  assert (C13 : getr r2 13 = Z_to_bv 64 1) by vl_agk AG2 B13.
  assert (C14 : getr r2 14 = Z_to_bv 64 (datad + 4 * (i * wpld))) by vl_agk AG2 B14.
  assert (C15 : getr r2 15 = Z_to_bv 64 j) by vl_agk AG2 B15.
  assert (C16 : getr r2 16 = Z_to_bv 64 j) by vl_agk AG2 A16.
  assert (P12 : pass_fp fr fr2) by (eapply vl_pass_trans; [exact P1 | exact P2]).
  assert (FSC2 : bc_fsc fr2) by (eapply vl_fsc_pass; [exact FSC | exact P12]).
  eapply reach_bind; [apply (v_site rom fr2 cs2 r2 M s datat wpl w h i j sm nm); first [vl_as | lia]|].
  intros fin3 (fr3 & cs3 & r3 & v & -> & FZ3 & Hv & S16 & AG3 & P3).
  assert (FX3 : vfix r3 s kval wpld spat rng wpl) by vl_fix AG3 FX2.
  pose proof FX3 as (Y1 & Y2 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26).
  assert (D11 : getr r3 11 = Z_to_bv 64 i) by vl_agk AG3 C11.
  assert (D12 : getr r3 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl))) by vl_agk AG3 C12.
  assert (D13 : getr r3 13 = Z_to_bv 64 1) by vl_agk AG3 C13.
  assert (D14 : getr r3 14 = Z_to_bv 64 (datad + 4 * (i * wpld))) by vl_agk AG3 C14.
  assert (D15 : getr r3 15 = Z_to_bv 64 j) by vl_agk AG3 C15.
  assert (P13 : pass_fp fr fr3) by (eapply vl_pass_trans; [exact P12 | exact P3]).
  eapply reach_bind; [apply (v_store rom fr3 cs3 r3 M s datad wpld w h i j v); first [vl_as | lia]|].
  intros fin4 (r4 & M4 & -> & S5 & S15 & S16b & S17 & AG4 & RI4).
  assert (RIa : rinv (VR datad wpld h) M0 M4) by (eapply rinv_trans; [exact RI | exact RI4]).
  assert (A12 : regs_agree (fun r => In r VPL) regs r2) by vl_agc AG1 AG2.
  assert (A13 : regs_agree (fun r => In r VPL) regs r3) by vl_agc A12 AG3.
  assert (A14 : regs_agree (fun r => In r VPL) regs r4) by vl_agc A13 AG4.
  assert (E11 : getr r4 11 = Z_to_bv 64 i) by vl_agk AG4 D11.
  destruct (Z.ltb_spec (j + 1) w) as [Hmore|Hlast].
  - assert (FX4 : vfix r4 s kval wpld spat rng wpl) by vl_fix AG4 FX3.
    assert (E12 : getr r4 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl))) by vl_agk AG4 D12.
    assert (E13 : getr r4 13 = Z_to_bv 64 1) by vl_agk AG4 D13.
    assert (E14 : getr r4 14 = Z_to_bv 64 (datad + 4 * (i * wpld))) by vl_agk AG4 D14.
    assert (FSC3 : bc_fsc fr3) by (eapply vl_fsc_pass; [exact FSC | exact P13]).
    eapply reach_weaken; [|apply (IH fr3 cs3 r4 M0 M4 s datat datad wpl wpld w h spat rng kval i (j + 1)%Z); first [vl_as | lia]].
    intros fin (fr5 & cs5 & r5 & M5 & -> & FZ5 & RI5 & AG5 & G11 & P5).
    exists fr5, cs5, r5, M5. split; [reflexivity|].
    split; [exact FZ5|]. split; [exact RI5|]. split; [vl_agc A14 AG5|]. split; [exact G11|].
    eapply vl_pass_trans; [exact P13 | exact P5].
  - apply reach_done. exists fr3, cs3, r4, M4. split; [reflexivity|].
    split; [exact FZ3|]. split; [exact RIa|]. split; [exact A14|]. split; [exact E11|]. exact P13.
Qed.

Lemma vi_loop : forall (m : nat) (fr : bvmap 5 word) cs regs (M0 M : word -> option byte) (s datat datad wpl wpld w h spat rng kval i : Z),
  Z.of_nat m = (h - i)%Z -> (0 <= i < h)%Z -> frm_zero cs ->
  vgeo s datat datad wpl wpld w h spat rng kval -> vmem0 s datat datad wpl wpld w h spat rng M0 -> rinv (VR datad wpld h) M0 M ->
  bc_fsc fr -> vfix regs s kval wpld spat rng wpl -> getr regs 11 = Z_to_bv 64 i ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a2e4) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a010) M' rom /\ frm_zero cs' /\
       rinv (VR datad wpld h) M0 M' /\ regs_agree (fun r => In r VPL) regs regs' /\ pass_fp fr fr').
Proof.
  intros m. induction m as [|m IH];
    intros fr cs regs M0 M s datat datad wpl wpld w h spat rng kval i Hm Hi FZ G V0 RI FSC FX H11.
  { lia. }
  pose proof (vmem_keep _ _ _ _ _ _ _ _ _ _ M0 M G V0 RI) as V.
  pose proof G as (Gs1 & Gs2 & Gw & Gh & Gw2 & Gh2 & Gwpl & Gsz & Gwpld & Gt1 & Gt2 & Gt3 & Gd1 & Gd2 & Gd3 &
                   Gp1 & Gp2 & Gp3 & Gr1 & Gr2 & Gk & Dt & Ds & Dp & Dr & Dc).
  pose proof V as (Rt & SOK & Ksp & Krn & Inone & C232 & C216 & C208 & C200 & C192 & C184).
  pose proof FX as (X1 & X2 & X8 & X9 & X10 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26).
  eapply reach_bind; [apply (v_rowset rom fr cs regs M s datat datad wpl wpld w h i); first [vl_as | lia]|].
  intros fin1 (r1 & M1 & -> & R12 & R13 & R14 & R15 & R16 & AG1 & EM1). subst M1.
  assert (FX1 : vfix r1 s kval wpld spat rng wpl) by vl_fix AG1 FX.
  assert (B11 : getr r1 11 = Z_to_bv 64 i) by vl_agk AG1 H11.
  eapply reach_bind;
    [apply (vj_loop (Z.to_nat w) fr cs r1 M0 M s datat datad wpl wpld w h spat rng kval i 0%Z);
       first [vl_as | lia | (rewrite Z2Nat.id by lia; lia)]|].
  intros fin2 (fr2 & cs2 & r2 & M2 & -> & FZ2 & RI2 & AG2 & G11 & P2).
  pose proof (vmem_keep _ _ _ _ _ _ _ _ _ _ M0 M2 G V0 RI2) as V2.
  pose proof V2 as (Rt2 & SOK2 & Ksp2 & Krn2 & Inone2 & C232b & C216b & C208b & C200b & C192b & C184b).
  assert (FX2 : vfix r2 s kval wpld spat rng wpl) by vl_fix AG2 FX1.
  pose proof FX2 as (X1b & X2b & X8b & X9b & X10b & X18b & X19b & X20b & X21b & X22b & X23b & X24b & X25b & X26b).
  eapply reach_bind; [apply (v_latch rom fr2 cs2 r2 M2 s h i); first [vl_as | lia]|].
  intros fin3 (r3 & M3 & -> & L11 & L12 & AG3 & EM3). subst M3.
  assert (A12 : regs_agree (fun r => In r VPL) regs r2) by vl_agc AG1 AG2.
  assert (A13 : regs_agree (fun r => In r VPL) regs r3) by vl_agc A12 AG3.
  destruct (Z.ltb_spec (i + 1) h) as [Hmore|Hlast].
  - assert (FX3 : vfix r3 s kval wpld spat rng wpl) by vl_fix AG3 FX2.
    assert (FSC2 : bc_fsc fr2) by (eapply vl_fsc_pass; [exact FSC | exact P2]).
    eapply reach_weaken; [|apply (IH fr2 cs2 r3 M0 M2 s datat datad wpl wpld w h spat rng kval (i + 1)%Z); first [vl_as | lia]].
    intros fin (fr5 & cs5 & r5 & M5 & -> & FZ5 & RI5 & AG5 & P5).
    exists fr5, cs5, r5, M5. split; [reflexivity|].
    split; [exact FZ5|]. split; [exact RI5|]. split; [vl_agc A13 AG5|].
    eapply vl_pass_trans; [exact P2 | exact P5].
  - apply reach_done. exists fr2, cs2, r3, M2. split; [reflexivity|].
    split; [exact FZ2|]. split; [exact RI2|]. split; [exact A13|]. exact P2.
Qed.

Lemma bc_vpass : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (s datat datad wpl wpld w h spat rng kval : Z),
  frm_zero cs -> bc_fsc fr ->
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (1 <= w)%Z -> (1 <= h)%Z -> (w + 22 <= 20000)%Z -> (h + 22 <= 20000)%Z -> wpl = wpl_of (w + 22) 8 -> (4 * (wpl * (h + 22)) <= 67108864)%Z ->
  wpld = wpl_of w 8 ->
  (4096 <= datat)%Z -> (datat + 4 * (wpl * (h + 22)) <= 2 ^ 47)%Z -> (datat mod 4 = 0)%Z ->
  (4096 <= datad)%Z -> (datad + 4 * (wpld * h) <= 2 ^ 47)%Z -> (datad mod 4 = 0)%Z ->
  (4096 <= spat)%Z -> (spat + 44 <= 2 ^ 47)%Z -> (spat mod 4 = 0)%Z -> (4096 <= rng)%Z -> (rng + 1024 <= 2 ^ 47)%Z -> (0 <= kval <= 255)%Z ->
  (datad + 4 * (wpld * h) <= datat \/ datat + 4 * (wpl * (h + 22)) <= datad)%Z ->
  (datad + 4 * (wpld * h) <= s - 320 \/ s <= datad)%Z ->
  (datad + 4 * (wpld * h) <= spat \/ spat + 44 <= datad)%Z ->
  (datad + 4 * (wpld * h) <= rng \/ rng + 1024 <= datad)%Z ->
  (datad + 4 * (wpld * h) <= bc_chalf \/ bc_chalf + 8 <= datad)%Z ->
  rd_bytes M datat (4 * (wpl * (h + 22))) -> store_ok SEGS M (Z_to_bv 64 datad) (Z.to_nat (4 * (wpld * h))) = true ->
  kcell_ok spat 11 M -> kcell_ok rng 256 M -> img_none M bc_chalf 8 ->
  rdn SEGS M (Z_to_bv 64 (s - 232)) 8 = Some (Z_to_le_bytes 8 datad) ->
  rdn SEGS M (Z_to_bv 64 (s - 216)) 8 = Some (Z_to_le_bytes 8 h) ->
  rdn SEGS M (Z_to_bv 64 (s - 208)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS M (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 bc_cptr) ->
  rdn SEGS M (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS M (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 1 = Z_to_bv 64 11 -> getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 (-10) -> getr regs 9 = Z_to_bv 64 kval ->
  getr regs 10 = Z_to_bv 64 wpld -> getr regs 11 = Z_to_bv 64 0 ->
  getr regs 18 = Z_to_bv 64 10 -> getr regs 19 = Z_to_bv 64 (- 2 ^ 31) -> getr regs 20 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 spat ->
  getr regs 22 = Z_to_bv 64 3 -> getr regs 23 = Z_to_bv 64 rng -> getr regs 24 = Z_to_bv 64 1 -> getr regs 25 = Z_to_bv 64 wpl ->
  getr regs 26 = Z_to_bv 64 (2 ^ 64 - 1 - rng) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a2e4) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a010) M' rom /\ frm_zero cs' /\
       rinv [(datad, (4 * (wpld * h))%Z)] M M' /\ regs_agree (fun r => In r VPL) regs regs' /\ pass_fp fr fr').
Proof.
  intros fr cs regs M s datat datad wpl wpld w h spat rng kval FZ FSC Hs1 Hs2 Hw Hh Hw2 Hh2 Hwpl Hsz Hwpld Ht1 Ht2 Ht3
    Hd1 Hd2 Hd3 Hp1 Hp2 Hp3 Hr1 Hr2 Hk Dt Ds Dp Dr Dc RT SOK KS KR IN C232 C216 C208 C200 C192 C184
    R1 R2 R8 R9 R10 R11 R18 R19 R20 R21 R22 R23 R24 R25 R26.
  eapply reach_weaken;
    [| apply (vi_loop (Z.to_nat h) fr cs regs M M s datat datad wpl wpld w h spat rng kval 0%Z);
       first [ (rewrite Z2Nat.id by lia; lia) | lia | exact FZ | exact FSC | exact R11 | apply rinv_refl
             | (unfold vgeo, vmem0, vfix; repeat (lazymatch goal with |- _ /\ _ => split end); first [assumption | lia]) ] ].
  intros fin (fr' & cs' & regs' & M' & E & FZ' & RI & AG & P).
  exists fr', cs', regs', M'. split; [exact E|]. split; [exact FZ'|]. split; [exact RI|]. split; [exact AG|]. exact P.
Qed.

End Segs.
