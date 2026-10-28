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


Lemma hs_sbox_box : forall x, fpv_box FMT_S x = Z_to_bv 64 (sbox x).
Proof. intros x. unfold sbox. symmetry. apply zbv_self. Qed.

Lemma hs_sbox_rd : forall x, (0 <= x < 2 ^ 32)%Z -> fpv_rdw FMT_S (Z_to_bv 64 (sbox x)) = x.
Proof.
  intros x Hx. rewrite <- hs_sbox_box. cbn [fpv_rdw fpv_box]. rewrite fpv_unbox_box, Z_to_bv_unsigned.
  apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.

Lemma hs_rdw_d : forall z, (0 <= z < 2 ^ 64)%Z -> fpv_rdw FMT_D (Z_to_bv 64 z) = z.
Proof. intros z Hz. cbn [fpv_rdw]. apply u_Z2bv; lia. Qed.

Lemma hs_fz : fpv_rdw FMT_S (Z_to_bv 64 bc_fzero) = p_zero.
Proof. vm_compute. reflexivity. Qed.

Lemma hs_ld8 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_extract 0%N 64%N (le_bytes_to_word (Z_to_le_bytes 8 z)) = Z_to_bv 64 z.
Proof. intros z Hz. rewrite exf_extract64. unfold le_bytes_to_word. rewrite (lez8 z Hz). rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma hs_xori3 : forall a, (0 <= a < 2 ^ 64)%Z -> v_xori (Z_to_bv 64 a) 3 = Z_to_bv 64 (Z.lxor a 3).
Proof. intros a Ha. unfold v_xori. rewrite u_Z2bv by lia. change (bv_wrap 64 3) with 3%Z. reflexivity. Qed.

Lemma hs_sext : forall v, (0 <= v < 2 ^ 31)%Z -> sext 64 (Z_to_bv 32 v) = Z_to_bv 64 v.
Proof. intros v Hv. rewrite OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.SymExec.sext64_lit. f_equal. rewrite Z_to_bv_signed. apply swrap32_small. lia. Qed.

Lemma hs_cvtw : forall a, (0 <= fst (fp_to_int (fp_format FMT_D) RTZ true 32 a) < 256)%Z ->
  fpv_x_of_f FMT_D RTZ true 32 a = Z_to_bv 64 (fst (fp_to_int (fp_format FMT_D) RTZ true 32 a)).
Proof.
  intros a Ha. unfold fpv_x_of_f. cbv zeta.
  lazymatch goal with |- (if ?c then ?A else ?B) = _ => change (if c then A else B) with A end.
  apply hs_sext. lia.
Qed.

Lemma hs_lx3 : forall a W j : Z, (0 <= a)%Z -> (a mod 4 = 0)%Z -> (W mod 4 = 0)%Z -> (0 <= j < W)%Z ->
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

#[local] Instance hs_fxd : FPState | 100 := mkFP bvmap_empty (Z_to_bv 32 0).

Ltac hs_bytes := vm_compute; apply (f_equal Some); repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]); reflexivity.

Definition hs_lit (n : N) (z : Z) : bv n := Z_to_bv n z.

Local Ltac canon1 t :=
  match t with
  | context C [@BV ?n ?z _] => let t' := context C [hs_lit n z] in canon1 t'
  | _ => t
  end.
Local Ltac canon2 t :=
  match t with
  | context C [hs_lit ?n ?z] => let t' := context C [@BV n z (I <: BvWf n z)] in canon2 t'
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
  rewrite ?hs_sbox_rd by lia; rewrite ?hs_fz; rewrite ?hs_rdw_d by lia.

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
  | |- context [v_xori ?a ?b] => wlit_closed (v_xori a b)
  end.

Local Ltac vsimp :=
  repeat match goal with
  | |- context [bv_extract _ _ (le_bytes_to_word (Z_to_le_bytes 8 ?z))] => rewrite (hs_ld8 z) by lia
  | |- context [v_addi (Z_to_bv 64 ?a) ?i] => rewrite (zbv_addi a i)
  | |- context [v_add (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_add a b)
  | |- context [v_addw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_addw_small a b) by lia
  | |- context [v_addiw (Z_to_bv 64 ?a) ?i] => rewrite (zbv_addiw_small a i) by lia
  | |- context [v_sltiu (Z_to_bv 64 ?a) 1] => rewrite (zbv_seqz_nz a) by lia
  | |- context [v_sltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_sltu_ge a b) by lia
  | |- context [v_slti (Z_to_bv 64 ?a) 0] => rewrite (zbv_slti0 a) by lia
  | |- context [v_xori (Z_to_bv 64 ?a) 3] => rewrite (hs_xori3 a) by lia
  | |- context [fpv_x_of_f FMT_D RTZ true 32 ?a] => rewrite (hs_cvtw a) by lia
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

Local Ltac ldt := gsimp; hregs; lits; wcl; rewrite ?zbv_addi, ?Z.add_0_r; eassumption.

Local Ltac brt := gsimp; hregs; lits; wcl; vsimp; unorm2;
  first [ cond_compute
        | (unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_Z2bv by lia;
           first [ apply Z.eqb_neq | apply Z.eqb_eq | apply Z.ltb_ge | apply Z.ltb_lt ]; lia) ].

Local Ltac st1 FZ :=
  let Fw := fresh "Fw" in let Dw := fresh "Dw" in
  here Fw Dw;
  eapply reach_step; [ reflexivity |
    lazymatch type of Dw with
    | _ = Some (OpImm ALU_XOR _ _ _, _) => eapply step_xori; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm ALU_SLTU _ _ _, _) => eapply step_sltiu; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm ALU_SLT _ _ _, _) => eapply step_slti; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm32 _ _ _, _) => eapply step_addiw; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op ALU_ADD _ _ _, _) => eapply step_add; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op ALU_SLTU _ _ _, _) => eapply step_sltu; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op ALU_XOR _ _ _, _) => eapply step_xor; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op32 ALU_ADD _ _ _, _) => eapply step_addw; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Jal _ _, _) => eapply OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.SeqExec.step_jal_link; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu; [exact Fw | reflexivity | exact Dw | ldt]
    | _ = Some (Load SZ8 true _ _ _, _) =>
        eapply step_ld; [exact Fw | reflexivity | exact Dw | ldt | rewrite lez8 by lia; reflexivity]
    | _ = Some (Branch BC_EQ _ _ _, _) =>
        first [ eapply step_beq_ft; [exact Fw | reflexivity | exact Dw | brt]
              | eapply step_beq_tk; [exact Fw | reflexivity | exact Dw | brt] ]
    | _ = Some (Branch BC_NE _ _ _, _) =>
        first [ eapply step_bne_ft; [exact Fw | reflexivity | exact Dw | brt]
              | eapply step_bne_tk; [exact Fw | reflexivity | exact Dw | brt] ]
    | _ = Some (Fcmp _ _ _ _ _, _) => eapply fpv_step_fcmp; [exact Fw | reflexivity | exact Dw]
    | _ = Some (FLoad FMT_D _ _ _, _) => eapply fp_step_fld; [exact Fw | reflexivity | exact Dw | reflexivity | ldt]
    | _ = Some (Fari _ _ _ _ _ _, _) => eapply fpv_step_fari; [exact Fw | reflexivity | exact Dw | exact FZ | reflexivity]
    | _ = Some (Fcvt FC_W _ _ _ _, _) =>
        eapply fpv_step_fcvt_x_of_f; [exact Fw | reflexivity | exact Dw | disj | disj | exact FZ | reflexivity]
    | _ = Some (Fcvt _ _ _ _ _, _) =>
        eapply fpv_step_fcvt_f_of_f; [exact Fw | reflexivity | exact Dw | disj | disj | exact FZ | reflexivity]
    end | ];
  clear Fw Dw.

Local Ltac cmps :=
  repeat match goal with
  | H : fst (fpv_cmp _ _ _ _) = _ |- context [fst (fpv_cmp _ _ _ _)] => rewrite H
  end;
  repeat match goal with
  | |- context [if true then ?A else ?B] => change (if true then A else B) with A
  | |- context [if false then ?A else ?B] => change (if false then A else B) with B
  end.

Local Ltac nrm FZ :=
  cbn [fp_regs fp_csr]; reduce_bv_eqb_ifs; pcn; fsimp; frd; gsimp; hregs; lits; wcl; vsimp; unorm2;
  rewrite ?Z.add_0_r; fold_all; cmps; csgen FZ.

Local Ltac sn FZ := st1 FZ; nrm FZ.

Lemma bhs_rinv1 : forall (M : word -> option byte) (lo n z : Z) (b : byte),
  (0 <= lo)%Z -> (lo <= z)%Z -> (z + 1 <= lo + n)%Z -> (lo + n <= 2 ^ 64)%Z ->
  rinv [(lo, n)] M (wbytes M (Z_to_bv 64 z) [b]).
Proof.
  intros M lo n z b H0 H1 H2 H3. split; [apply wbytes_grows|].
  intros a Ha. specialize (Ha (lo, n) (or_introl eq_refl)). unfold inreg in Ha. cbn [fst snd] in Ha.
  pose proof (bv_unsigned_in_range _ a) as Ra. unfold bv_modulus in Ra. cbn [Z.of_N] in Ra.
  apply wbytes_outside; cbn [length]; rewrite u_Z2bv by lia; lia.
Qed.

Section Segs.
Variable rom : word -> option byte.

Lemma bh_site : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (s datas datat wpl w h spat rng kval i j sm nm : Z),
  frm_zero cs -> bc_fsc fr -> hgeo s datas datat wpl w h spat rng kval -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
  rd_bytes M datas (4 * (wpl * (h + 22))) -> store_ok SEGS M (Z_to_bv 64 datat) (Z.to_nat (4 * (wpl * (h + 22)))) = true ->
  img_none M bc_chalf 8 -> hframe s datas datat wpl w h M ->
  bc_avg 21 sm nm -> reg_get fr 14 = Z_to_bv 64 (sbox nm) -> reg_get fr 15 = Z_to_bv 64 (sbox sm) ->
  hfix regs s kval spat rng wpl -> getr regs 10 = Z_to_bv 64 i ->
  getr regs 11 = Z_to_bv 64 (datas + 4 * ((i + 11) * wpl)) -> getr regs 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl)) ->
  getr regs 13 = Z_to_bv 64 j -> getr regs 14 = Z_to_bv 64 (j + 11) -> getr regs 15 = Z_to_bv 64 (j + 11) ->
  getr regs 16 = Z_to_bv 64 (j + 11) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a218) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a278) M' rom /\ frm_zero cs' /\
       rinv (HR datat wpl h) M M' /\ regs_agree (fun x => In x HST) regs regs' /\ pass_fp fr fr').
Proof.
  intros fr cs regs M s datas datat wpl w h spat rng kval i j sm nm FZ FSC HG Hi Hj RDs SOK IMG HF BA F14 F15
    HFX H10 H11 H12 H13 H14 H15 H16.
  destruct FSC as (F8 & F9 & F18).
  destruct HG as (Hs1 & Hs2 & Hw1 & Hh1 & Hw & Hh & Ewpl & Hsz & Hds1 & Hds2 & Hds3 & Hdt1 & Hdt2 & Hdt3 & _).
  destruct HF as (_ & _ & _ & _ & Rcp & _).
  destruct HFX as (H2 & _ & _ & _ & _ & _ & _ & H22 & _ & H24 & _).
  clear RDs.
  pose proof (bc_avg_range _ _ _ BA) as (Rsm & Rnm).
  pose proof bc_consts as (Kz & Khalf & Klo & Khi).
  assert (Kcp : (0 <= bc_cptr < 2 ^ 64)%Z) by (unfold bc_cptr; lia).
  assert (Rcp' : rdn SEGS M (Z_to_bv 64 (s - 320 + 120)) 8 = Some (Z_to_le_bytes 8 bc_cptr))
    by (replace (s - 320 + 120)%Z with (s - 200)%Z by lia; exact Rcp).
  assert (Rhalf : rdn SEGS M (Z_to_bv 64 bc_chalf) 8 = Some (Z_to_le_bytes 8 p_half_d)).
  { rewrite (SumWalkTac.rdn_img SEGS M bc_chalf 8 bc_chalf (bc_chalf + 8)) by (first [exact IMG | unfold bc_chalf; lia]).
    hs_bytes. }
  assert (Hwpl : (w + 22 <= 4 * wpl)%Z).
  { subst wpl. unfold wpl_of.
    pose proof (Z.div_mod ((w + 22) * 8 + 31) 32 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound ((w + 22) * 8 + 31) 32 ltac:(lia)) as B. lia. }
  assert (Hm1 : (0 <= (i + 11) * wpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hm2 : (0 <= (h + 10 - i) * wpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hrow : (4 * ((i + 11) * wpl) + 4 * wpl <= 4 * (wpl * (h + 22)))%Z) by lia.
  assert (Hrp4 : ((datat + 4 * ((i + 11) * wpl)) mod 4 = 0)%Z).
  { replace (datat + 4 * ((i + 11) * wpl))%Z with (datat + ((i + 11) * wpl) * 4)%Z by ring.
    rewrite Z_mod_plus_full. exact Hdt3. }
  remember (datat + 4 * ((i + 11) * wpl))%Z as rp eqn:Erp.
  assert (XA : (rp <= Z.lxor (j + 11 + rp) 3 < rp + 4 * wpl)%Z).
  { replace (j + 11 + rp)%Z with (rp + (j + 11))%Z by ring.
    apply hs_lx3; [lia | exact Hrp4 | rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
  assert (Sok : store_ok SEGS M (Z_to_bv 64 (Z.lxor (j + 11 + rp) 3)) 1 = true).
  { eapply (store_ok_sub SEGS M (Z_to_bv 64 datat) _ (Z.to_nat (4 * (wpl * (h + 22)))) 1); [| exact SOK | |];
      rewrite ?u_Z2bv by lia; rewrite ?Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia. }
  destruct (fst (fpv_cmp F_LT FMT_S p_zero nm)) eqn:Hpos.
  - pose (q := fst (fpv_ari F_DIV FMT_S RNE sm nm)).
    pose (qd := fst (fp_convert (fp_format FMT_S) (fp_format FMT_D) RNE q)).
    pose (vr := fst (fpv_ari F_ADD FMT_D RNE qd p_half_d)).
    assert (Hst : (0 <= q < 2 ^ 32)%Z /\ (0 <= qd < 2 ^ 64)%Z /\ (0 <= vr < 2 ^ 64)%Z /\
                  fst (fpv_cmp F_LT FMT_D p_lo_d vr) = true /\ fst (fpv_cmp F_LT FMT_D vr p_hi_d) = true /\
                  (0 <= fst (fp_to_int (fp_format FMT_D) RTZ true 32 vr) < 256)%Z)
      by exact (bc_site_full 21 sm nm RNE RNE BA ltac:(lia) Hpos).
    destruct Hst as (Rq & Rqd & Rvr & Lt1 & Lt2 & Hcv).
    do 11 sn FZ.
    do 12 sn FZ.
    let Fw := fresh "Fw" in let Dw := fresh "Dw" in
    here Fw Dw;
    eapply reach_step; [ reflexivity
      | eapply MmapSim.step_sb_at with (a := Z_to_bv 64 (Z.lxor (j + 11 + rp) 3));
        [ exact Fw | reflexivity | exact Dw | gsimp; hregs; lits; rewrite ?zbv_addi, ?Z.add_0_r; reflexivity
        | gsimp; reflexivity | reflexivity | exact Sok ] | ];
    clear Fw Dw.
    nrm FZ.
    apply reach_done. cbv beta.
    do 4 eexists.
    split; [reflexivity|].
    split; [exact FZ|].
    split.
    { unfold HR. eapply bhs_rinv1; lia. }
    split; [unfold HST; solve_regs_agree|].
    intros x Hx.
    assert (N13 : x <> 13%bv) by (intro E; apply Hx; rewrite E; vm_compute; auto).
    assert (N15 : x <> 15%bv) by (intro E; apply Hx; rewrite E; vm_compute; auto).
    rewrite ?fpv_get_other by assumption. reflexivity.
  - do 2 sn FZ.
    apply reach_done. cbv beta.
    do 4 eexists.
    split; [reflexivity|].
    split; [exact FZ|].
    split; [apply rinv_refl|].
    split; [unfold HST; solve_regs_agree|].
    intros x Hx. reflexivity.
Qed.

End Segs.
