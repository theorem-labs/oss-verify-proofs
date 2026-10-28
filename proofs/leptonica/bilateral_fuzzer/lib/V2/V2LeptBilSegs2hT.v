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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptBilSegs V2LeptBilSegs2 V2LeptBilSegs2hD.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma bht_swrap32 : forall t r k : Z, (- 2 ^ 31 <= r < 2 ^ 31)%Z -> t = (r + k * 2 ^ 32)%Z -> bv_swrap 32 t = r.
Proof. intros t r k Hr ->. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia. Qed.

Lemma bht_addw : forall a b : Z, (- 2 ^ 31 <= a + b < 2 ^ 31)%Z -> v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b H. unfold v_addw. rewrite !u_Z2bv_mod. f_equal.
  apply bht_swrap32 with (k := (- 2 ^ 32 * (a / 2 ^ 64) - 2 ^ 32 * (b / 2 ^ 64))%Z); lia.
Qed.

Lemma bht_subw : forall a b : Z, (- 2 ^ 31 <= a - b < 2 ^ 31)%Z -> v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b H. unfold v_subw. rewrite !u_Z2bv_mod. f_equal.
  apply bht_swrap32 with (k := (- 2 ^ 32 * (a / 2 ^ 64) + 2 ^ 32 * (b / 2 ^ 64))%Z); lia.
Qed.

Lemma bht_addiw : forall (a i : Z), (- 2 ^ 31 <= a + i < 2 ^ 31)%Z -> v_addiw (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof.
  intros a i H. unfold v_addiw. rewrite u_Z2bv_mod. f_equal.
  apply bht_swrap32 with (k := (- 2 ^ 32 * (a / 2 ^ 64))%Z); lia.
Qed.

Lemma bht_signed : forall a : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 a) = a.
Proof.
  intros a Ha. unfold bv_signed. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia.
Qed.

Lemma bht_lts : forall a b : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. intros a b Ha Hb. unfold c_lts, bv_lts. rewrite !bht_signed by lia. reflexivity. Qed.

Lemma bht_ltu : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma bht_eq : forall a b : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b)%Z.
Proof.
  intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_Z2bv_mod.
  destruct (Z.eqb_spec a b) as [E | E].
  - subst b. rewrite !Z.eqb_refl. reflexivity.
  - apply Z.eqb_neq. lia.
Qed.

Lemma bht_slli2 : forall a : Z, v_slli (Z_to_bv 64 a) 2 = Z_to_bv 64 (4 * a).
Proof. intros a. rewrite zbv_slli by lia. f_equal. change (2 ^ 2)%Z with 4%Z. ring. Qed.

Lemma bht_andi3 : forall b x : Z, (0 <= b + 4 * x < 2 ^ 64)%Z -> (b mod 4 = 0)%Z -> v_andi (Z_to_bv 64 (b + 4 * x)) 3 = Z_to_bv 64 0.
Proof.
  intros b x H Hb. unfold v_andi. rewrite u_Z2bv by lia. change (bv_wrap 64 3) with 3%Z.
  change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z. f_equal. lia.
Qed.

Lemma bht_lx3 : forall a W c : Z, (0 <= a)%Z -> (a mod 4 = 0)%Z -> (W mod 4 = 0)%Z -> (0 <= c < W)%Z ->
  (a <= Z.lxor (a + c) 3 < a + W)%Z.
Proof. intros a W c Ha Aa AW Hc. rewrite lxor3_eq by lia. lia. Qed.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma bht_cell : forall z, (0 <= z < 2 ^ 32)%Z -> bv_extract 0%N 32%N (le_bytes_to_word (Z_to_le_bytes 4 z)) = Z_to_bv 32 z.
Proof.
  intros z Hz. unfold le_bytes_to_word. rewrite (lez4 z Hz).
  apply bv_eq. rewrite bv_extract_unsigned, !Z_to_bv_unsigned. change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z. change (Z.of_N 32) with 32%Z.
  rewrite (Z.mod_small z (2 ^ 64)) by lia. rewrite (Z.mod_small z (2 ^ 64)) by lia. reflexivity.
Qed.

Lemma bht_sbox_rd : forall x, (0 <= x < 2 ^ 32)%Z -> fpv_rdw FMT_S (Z_to_bv 64 (sbox x)) = x.
Proof.
  intros x Hx. unfold sbox. rewrite zbv_self. cbn [fpv_rdw fpv_box]. rewrite fpv_unbox_box, Z_to_bv_unsigned.
  apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.

Lemma bht_box : forall x, nan_box (Z_to_bv 32 x) = Z_to_bv 64 (sbox x).
Proof. intros x. unfold sbox. cbn [fpv_box]. rewrite zbv_self. reflexivity. Qed.

Lemma bht_xori3 : forall a, (0 <= a < 2 ^ 64)%Z -> v_xori (Z_to_bv 64 a) 3 = Z_to_bv 64 (Z.lxor a 3).
Proof. intros a Ha. unfold v_xori. rewrite u_Z2bv by lia. change (bv_wrap 64 3) with 3%Z. reflexivity. Qed.

#[local] Instance bht_fxd : FPState | 100 := mkFP bvmap_empty (Z_to_bv 32 0).

Definition bht_lit (n : N) (z : Z) : bv n := Z_to_bv n z.

Local Ltac canon1 t :=
  match t with
  | context C [@BV ?n ?z _] => let t' := context C [bht_lit n z] in canon1 t'
  | _ => t
  end.
Local Ltac canon2 t :=
  match t with
  | context C [bht_lit ?n ?z] => let t' := context C [@BV n z (I <: BvWf n z)] in canon2 t'
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
  rewrite ?bht_sbox_rd by lia.

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
  | |- context [bv_extract _ _ (le_bytes_to_word (Z_to_le_bytes 4 ?z))] => rewrite (bht_cell z) by lia
  | |- context [v_addi (Z_to_bv 64 ?a) ?i] => rewrite (zbv_addi a i)
  | |- context [v_add (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_add a b)
  | |- context [v_sub (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_sub a b)
  | |- context [v_addw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (bht_addw a b) by lia
  | |- context [v_subw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (bht_subw a b) by lia
  | |- context [v_addiw (Z_to_bv 64 ?a) ?i] => rewrite (bht_addiw a i) by lia
  | |- context [v_slli (Z_to_bv 64 ?a) 2] => rewrite (bht_slli2 a)
  | |- context [v_andi (Z_to_bv 64 (?b + 4 * ?x)) 3] => rewrite (bht_andi3 b x) by (first [lia | assumption])
  | |- context [v_sltiu (Z_to_bv 64 ?a) 1] => rewrite (zbv_seqz_nz a) by lia
  | |- context [v_sltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_sltu_ge a b) by lia
  | |- context [v_slti (Z_to_bv 64 ?a) 0] => rewrite (zbv_slti0 a) by lia
  | |- context [v_xori (Z_to_bv 64 ?a) 3] => rewrite (bht_xori3 a) by lia
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
        | (rewrite ?bht_eq by lia; rewrite ?bht_lts by lia; rewrite ?bht_ltu by lia;
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
    let b := eval vm_compute in (orb (Z.eqb p 0x3a158) (Z.eqb p 0x3a218)) in
    lazymatch b with true => idtac end
  end.

Local Ltac run FZ := sn FZ; repeat (tryif at_exit then fail else sn FZ).

Section Segs.
Variable rom : word -> option byte.

Lemma bh_tap : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (s datas wpl H i j k kval spat rng kk sm nm : Z),
  frm_zero cs ->
  (4096 <= datas)%Z -> (datas + 4 * (wpl * H) <= 2 ^ 47)%Z -> (datas mod 4 = 0)%Z ->
  (1 <= wpl <= 5000)%Z -> (4 * (wpl * H) <= 67108864)%Z ->
  (0 <= j)%Z -> (j + 22 <= 4 * wpl)%Z -> (0 <= i)%Z -> (i + 22 <= H)%Z -> (-10 <= k <= 10)%Z ->
  (4096 <= spat)%Z -> (spat + 44 <= 2 ^ 47)%Z -> (spat mod 4 = 0)%Z -> (4096 <= rng)%Z -> (rng + 1024 <= 2 ^ 47)%Z -> (0 <= kval <= 255)%Z ->
  rd_bytes M datas (4 * (wpl * H)) -> kcell_ok spat 11 M -> kcell_ok rng 256 M ->
  bc_avg kk sm nm -> (0 <= kk)%Z -> (kk + 1 <= 2048)%Z ->
  hfix regs s kval spat rng wpl ->
  getr regs 11 = Z_to_bv 64 (datas + 4 * ((i + 11) * wpl)) -> getr regs 14 = Z_to_bv 64 (j + 11) -> getr regs 15 = Z_to_bv 64 (j + 11) ->
  getr regs 17 = Z_to_bv 64 k ->
  reg_get fr 14 = Z_to_bv 64 (sbox nm) -> reg_get fr 15 = Z_to_bv 64 (sbox sm) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a158) M rom)
    (fun fin => exists fr' cs' regs' sm' nm', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 (if (k <? 10)%Z then 0x3a158 else 0x3a218)) M rom /\
       frm_zero cs' /\ regs_agree (fun x => In x HKT) regs regs' /\ getr regs' 16 = Z_to_bv 64 (j + 11) /\ getr regs' 17 = Z_to_bv 64 (k + 1) /\
       bc_avg (kk + 1) sm' nm' /\ reg_get fr' 14 = Z_to_bv 64 (sbox nm') /\ reg_get fr' 15 = Z_to_bv 64 (sbox sm') /\
       pass_fp fr fr').
Proof.
  intros fr cs regs M s datas wpl H i j k kval spat rng kk sm nm FZ Hd1 Hd2 Hd3 Hwpl Hsz Hj1 Hj2 Hi1 Hi2 Hk
    Hp1 Hp2 Hp3 Hg1 Hg2 Hkv RD KS KR BA Hkk1 Hkk2 HF H11 H14 H15 H17 F14 F15.
  destruct HF as (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H29).
  pose proof (bc_avg_range _ _ _ BA) as (Rsm & Rnm).
  assert (Hm1 : (0 <= (i + 11) * wpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hm2 : (0 <= (H - i - 12) * wpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hrow : (4 * ((i + 11) * wpl) + 4 * wpl <= 4 * (wpl * H))%Z) by lia.
  assert (Hrp4 : ((datas + 4 * ((i + 11) * wpl)) mod 4 = 0)%Z).
  { replace (datas + 4 * ((i + 11) * wpl))%Z with (datas + ((i + 11) * wpl) * 4)%Z by ring.
    rewrite Z_mod_plus_full. exact Hd3. }
  remember (datas + 4 * ((i + 11) * wpl))%Z as rs eqn:Ers.
  assert (XA : (rs <= Z.lxor (rs + (j + 11 + k)) 3 < rs + 4 * wpl)%Z).
  { apply bht_lx3; [lia | exact Hrp4 | rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
  destruct (RD (Z.lxor (rs + (j + 11 + k)) 3) ltac:(lia)) as [b RB].
  assert (Rb : (0 <= bv_unsigned b <= 255)%Z)
    by (pose proof (bv_unsigned_in_range _ b) as R; unfold bv_modulus in R; cbn in R; lia).
  set (tv := bv_unsigned b) in *.
  destruct (KS (Z.abs k) ltac:(lia)) as (xsp & Hxsp & FBsp).
  destruct (KR (Z.abs (kval - tv)) ltac:(lia)) as (xrg & Hxrg & FBrg).
  pose (kern := fst (fpv_ari F_MUL FMT_S RNE xsp xrg)).
  pose (bb := fst (fp_of_int (fp_format FMT_S) RNE false 32 tv)).
  pose (n1 := fst (fpv_ari F_ADD FMT_S RNE nm kern)).
  pose (s1 := fst (fpv_fma F_MADD FMT_S RNE kern bb sm)).
  assert (T : bc_avg (kk + 1) s1 n1 /\ (0 <= xsp < 2 ^ 32)%Z /\ (0 <= xrg < 2 ^ 32)%Z /\ (0 <= kern < 2 ^ 32)%Z /\
              (0 <= bb < 2 ^ 32)%Z /\ (0 <= s1 < 2 ^ 32)%Z /\ (0 <= n1 < 2 ^ 32)%Z)
    by exact (bc_tap_full kk sm nm xsp xrg tv BA Hkk1 Hkk2 FBsp FBrg Rb).
  destruct T as (BA1 & Rsp & Rrg & Rk & Rbb & Rs1 & Rn1).
  destruct (Z_lt_le_dec k 0) as [Kn | Kp]; destruct (Z_lt_le_dec (kval - tv) 0) as [Dn | Dp];
    destruct (Z.ltb_spec k 10) as [K10 | K10]; cbv iota.
  all: try (exfalso; lia).
  all: run FZ.
  all: apply reach_done; cbv beta.
  all: eexists; eexists; eexists; exists s1, n1.
  all: split; [reflexivity|].
  all: split; [exact FZ|].
  all: split; [unfold HKT; solve_regs_agree|].
  all: split; [gsimp; first [reflexivity | (f_equal; lia)]|].
  all: split; [gsimp; first [reflexivity | (f_equal; lia)]|].
  all: split; [exact BA1|].
  all: split; [fsimp; apply bht_box|].
  all: split; [fsimp; apply bht_box|].
  all: intros x Hx.
  all: assert (N12 : x <> 12%bv) by (intro E; apply Hx; rewrite E; vm_compute; auto).
  all: assert (N13 : x <> 13%bv) by (intro E; apply Hx; rewrite E; vm_compute; auto).
  all: assert (N14 : x <> 14%bv) by (intro E; apply Hx; rewrite E; vm_compute; auto).
  all: assert (N15 : x <> 15%bv) by (intro E; apply Hx; rewrite E; vm_compute; auto).
  all: rewrite ?fpv_get_other by assumption; reflexivity.
Qed.

End Segs.
