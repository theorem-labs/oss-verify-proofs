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

Definition bhl_lit (n : N) (z : Z) : bv n := Z_to_bv n z.

Local Ltac bhl_canon1 t :=
  match t with
  | context C [@BV ?n ?z _] => let t' := context C [bhl_lit n z] in bhl_canon1 t'
  | _ => t
  end.
Local Ltac bhl_canon2 t :=
  match t with
  | context C [bhl_lit ?n ?z] => let t' := context C [@BV n z (I <: BvWf n z)] in bhl_canon2 t'
  | _ => t
  end.
Local Ltac bhl_canon t := let t1 := bhl_canon1 t in bhl_canon2 t1.

Local Ltac bhl_here Fw Dw :=
  lazymatch goal with |- reach ?sg (@mkst _ _ ?p _ _) _ =>
    let f := eval vm_compute in (fetch_word sg p) in
    lazymatch f with Some ?w =>
      assert (Fw : fetch_word sg p = Some w) by (vm_cast_no_check (eq_refl (Some w)));
      let d0 := eval vm_compute in (decode_any w) in
      let d := bhl_canon d0 in
      assert (Dw : decode_any w = d) by vm_refl_bv
    end
  end.

Local Ltac bhl_pcn :=
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

Local Ltac bhl_lits :=
  repeat match goal with
  | |- context [bv_signed (@BV ?n ?z ?pf)] =>
      let v := eval vm_compute in (bv_signed (@BV n z pf)) in change (bv_signed (@BV n z pf)) with v
  | |- context [bv_unsigned (@BV ?n ?z ?pf)] => change (bv_unsigned (@BV n z pf)) with z
  end.

Local Ltac bhl_rneq := let Hc := fresh "Hc" in intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate Hc.

Local Ltac bhl_gsimp :=
  repeat match goal with
  | |- context [getr (regupd ?R ?r ?v) ?r'] =>
      first [ (let E := fresh "E" in
               assert (E : getr (regupd R r v) r' = v) by (replace r' with r by bveq; apply getr_same; bhl_rneq);
               rewrite E; clear E)
            | (let E := fresh "E" in
               assert (E : getr (regupd R r v) r' = getr R r') by (apply getr_other; bhl_rneq);
               rewrite E; clear E) ]
  end.

Local Ltac bhl_hregs :=
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

Local Ltac bhl_vsimp :=
  repeat match goal with
  | |- context [v_addiw (Z_to_bv 64 ?a) ?i] => rewrite (zbv_addiw_small a i) by lia
  | |- context [v_addi (Z_to_bv 64 ?a) ?i] => rewrite (zbv_addi a i)
  end;
  rewrite ?Z.add_0_r.

Local Ltac bhl_ldt := bhl_gsimp; bhl_hregs; bhl_lits; rewrite ?zbv_addi, ?Z.add_0_r; eassumption.

Local Ltac bhl_br := bhl_gsimp; bhl_hregs; bhl_lits; bhl_vsimp; rewrite WalksLib.c_lts_Z by lia;
  first [ assumption | (apply Z.ltb_ge; lia) | (apply Z.ltb_lt; lia) ].

Local Ltac bhl_st :=
  let Fw := fresh "Fw" in let Dw := fresh "Dw" in
  bhl_here Fw Dw;
  eapply reach_step; [ reflexivity |
    lazymatch type of Dw with
    | _ = Some (OpImm ALU_ADD _ _ _, _) => eapply step_addi; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm32 _ _ _, _) => eapply step_addiw; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Load SZ8 true _ _ _, _) =>
        eapply step_ld; [exact Fw | reflexivity | exact Dw | bhl_ldt | rewrite lez8 by lia; reflexivity]
    | _ = Some (Branch BC_LT _ _ _, _) =>
        first [ eapply step_blt_ft; [exact Fw | reflexivity | exact Dw | bhl_br]
              | eapply step_blt_tk; [exact Fw | reflexivity | exact Dw | bhl_br] ]
    end | ];
  clear Fw Dw.

Local Ltac bhl_nrm := reduce_bv_eqb_ifs; bhl_pcn; bhl_gsimp; bhl_hregs; bhl_lits; bhl_vsimp.
Local Ltac bhl_sn := bhl_st; bhl_nrm.

Local Ltac bhl_gsimpc :=
  repeat match goal with
  | |- context [getr (regupd ?R ?r ?v) ?r'] =>
      first [ (let E := fresh "E" in
               assert (E : getr (regupd R r v) r' = v) by (replace r' with r by bveq; apply getr_same; bhl_rneq);
               rewrite E; clear E)
            | (let E := fresh "E" in
               assert (E : getr (regupd R r v) r' = getr R r') by (apply getr_other; bhl_rneq);
               rewrite E; clear E) ]
  | |- context [getr ?R ?r] =>
      lazymatch r with @BV _ _ _ =>
        let b := eval vm_compute in (bv_eqb r (Z_to_bv 5 0)) in
        lazymatch b with true => change (getr R r) with (Z_to_bv 64 0) end
      end
  end.

Local Ltac bhl_fget :=
  repeat match goal with
  | |- context [reg_get (bvmap_set ?r ?v ?F) ?x] =>
      first [ (let E := fresh "E" in
               assert (E : reg_get (bvmap_set r v F) x = v) by (replace x with r by bveq; apply fpv_get_same);
               rewrite E; clear E)
            | (let E := fresh "E" in
               assert (E : reg_get (bvmap_set r v F) x = reg_get F x) by (apply fpv_get_other; bhl_rneq);
               rewrite E; clear E) ]
  end.

Local Ltac bhl_fhyp :=
  repeat match goal with
  | |- context [reg_get ?F ?r] =>
      is_var F;
      match goal with
      | H : reg_get F ?r0 = ?val |- _ =>
          let b := eval vm_compute in (bv_eqb r r0) in
          lazymatch b with
          | true => let E := fresh "E" in
                    assert (E : reg_get F r = val) by (replace r with r0 by bveq; exact H);
                    rewrite E; clear E
          end
      end
  end.

Local Ltac bhl_vsimpc :=
  repeat match goal with
  | |- context [v_addw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_addw_small a b) by lia
  | |- context [v_add (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_add a b)
  | |- context [v_addiw (Z_to_bv 64 ?a) ?i] => rewrite (zbv_addiw_small a i) by lia
  | |- context [v_addi (Z_to_bv 64 ?a) ?i] => rewrite (zbv_addi a i)
  end;
  rewrite ?Z.add_0_r.

Local Ltac bhl_brc := bhl_gsimpc; bhl_hregs; bhl_lits; bhl_vsimpc;
  first [ cond_compute
        | (rewrite WalksLib.c_lts_Z by lia; first [ (apply Z.ltb_ge; lia) | (apply Z.ltb_lt; lia) ])
        | (unfold c_eq, bv_eqb; rewrite ?u_Z2bv by lia; first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia) ].

Local Ltac bhl_ldc := bhl_gsimpc; bhl_hregs; bhl_lits; rewrite ?zbv_addi, ?Z.add_0_r; eassumption.

Local Ltac bhl_stc :=
  let Fw := fresh "Fw" in let Dw := fresh "Dw" in
  bhl_here Fw Dw;
  eapply reach_step; [ reflexivity |
    lazymatch type of Dw with
    | _ = Some (OpImm ALU_ADD _ _ _, _) => eapply step_addi; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm32 _ _ _, _) => eapply step_addiw; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op ALU_ADD _ _ _, _) => eapply step_add; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op32 ALU_ADD _ _ _, _) => eapply step_addw; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Load SZ8 true _ _ _, _) =>
        eapply step_ld; [exact Fw | reflexivity | exact Dw | bhl_ldc | rewrite lez8 by lia; reflexivity]
    | _ = Some (Branch BC_NE _ _ _, _) =>
        first [ eapply step_bne_ft; [exact Fw | reflexivity | exact Dw | bhl_brc]
              | eapply step_bne_tk; [exact Fw | reflexivity | exact Dw | bhl_brc] ]
    | _ = Some (Branch BC_LT _ _ _, _) =>
        first [ eapply step_blt_ft; [exact Fw | reflexivity | exact Dw | bhl_brc]
              | eapply step_blt_tk; [exact Fw | reflexivity | exact Dw | bhl_brc] ]
    | _ = Some (Fsgnj _ _ _ _ _, _) => eapply fpv_step_fsgnj; [exact Fw | reflexivity | exact Dw]
    end | ];
  clear Fw Dw.

Local Ltac bhl_nrmc := cbn [fp_regs fp_csr]; reduce_bv_eqb_ifs; bhl_pcn; bhl_gsimpc; bhl_hregs; bhl_lits; bhl_vsimpc.
Local Ltac bhl_snc := bhl_stc; bhl_nrmc.

Local Ltac bhl_wcl :=
  repeat match goal with
  | |- context [v_xor ?a ?b] => wlit_closed (v_xor a b)
  | |- context [v_xori ?a ?b] => wlit_closed (v_xori a b)
  end.

Local Ltac bhl_vsimpr :=
  repeat match goal with
  | |- context [v_addw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_addw_small a b) by lia
  | |- context [v_add (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_add a b)
  | |- context [v_addiw (Z_to_bv 64 ?a) ?i] => rewrite (zbv_addiw_small a i) by lia
  | |- context [v_addi (Z_to_bv 64 ?a) ?i] => rewrite (zbv_addi a i)
  | |- context [v_mulw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_mulw_small a b) by lia
  | |- context [v_mul (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_mul a b)
  | |- context [v_slli (Z_to_bv 64 ?a) ?k] => rewrite (zbv_slli a k) by lia
  | |- context [v_sltiu (Z_to_bv 64 ?a) 1] => rewrite (zbv_seqz_nz a) by lia
  | |- context [v_sltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (zbv_sltu_ge a b) by lia
  | |- context [v_slti (Z_to_bv 64 ?a) 0] => rewrite (zbv_slti0 a) by lia
  end;
  rewrite ?Z.add_0_r.

Local Ltac bhl_brr := bhl_gsimpc; bhl_hregs; bhl_lits; bhl_wcl; bhl_vsimpr;
  first [ cond_compute
        | (rewrite WalksLib.c_lts_Z by lia; first [ (apply Z.ltb_ge; lia) | (apply Z.ltb_lt; lia) ])
        | (unfold c_eq, bv_eqb; rewrite ?u_Z2bv by lia; first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia) ].

Local Ltac bhl_str :=
  let Fw := fresh "Fw" in let Dw := fresh "Dw" in
  bhl_here Fw Dw;
  eapply reach_step; [ reflexivity |
    lazymatch type of Dw with
    | _ = Some (OpImm ALU_ADD _ _ _, _) => eapply step_addi; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm ALU_XOR _ _ _, _) => eapply step_xori; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm ALU_SLTU _ _ _, _) => eapply step_sltiu; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm ALU_SLT _ _ _, _) => eapply step_slti; [exact Fw | reflexivity | exact Dw]
    | _ = Some (OpImm32 _ _ _, _) => eapply step_addiw; [exact Fw | reflexivity | exact Dw]
    | _ = Some (ShiftImm ALU_SLL _ _ _, _) => eapply step_slli; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op ALU_ADD _ _ _, _) => eapply step_add; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op ALU_SLTU _ _ _, _) => eapply step_sltu; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op ALU_XOR _ _ _, _) => eapply step_xor; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Op32 ALU_ADD _ _ _, _) => eapply step_addw; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Mul M_MUL _ _ _, _) => eapply step_mul; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Mul32 M_MUL _ _ _, _) => eapply step_mulw; [exact Fw | reflexivity | exact Dw]
    | _ = Some (Load SZ8 true _ _ _, _) =>
        eapply step_ld; [exact Fw | reflexivity | exact Dw | bhl_ldc | rewrite lez8 by lia; reflexivity]
    | _ = Some (Branch BC_EQ _ _ _, _) =>
        first [ eapply step_beq_ft; [exact Fw | reflexivity | exact Dw | bhl_brr]
              | eapply step_beq_tk; [exact Fw | reflexivity | exact Dw | bhl_brr] ]
    | _ = Some (Branch BC_NE _ _ _, _) =>
        first [ eapply step_bne_ft; [exact Fw | reflexivity | exact Dw | bhl_brr]
              | eapply step_bne_tk; [exact Fw | reflexivity | exact Dw | bhl_brr] ]
    | _ = Some (Branch BC_GE _ _ _, _) =>
        first [ eapply step_bge_ft; [exact Fw | reflexivity | exact Dw | bhl_brr]
              | eapply step_bge_tk; [exact Fw | reflexivity | exact Dw | bhl_brr] ]
    end | ];
  clear Fw Dw.

Local Ltac bhl_nrmr := reduce_bv_eqb_ifs; bhl_pcn; bhl_gsimpc; bhl_hregs; bhl_lits; bhl_wcl; bhl_vsimpr.
Local Ltac bhl_snr := bhl_str; bhl_nrmr.

Section Segs.
Variable rom : word -> option byte.

Lemma bh_row : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (s datas datat wpl w h spat rng kval i : Z),
  frm_zero cs -> hgeo s datas datat wpl w h spat rng kval -> (0 <= i < h)%Z -> hframe s datas datat wpl w h M ->
  hfix regs s kval spat rng wpl -> getr regs 10 = Z_to_bv 64 i ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a09c) M rom)
    (fun fin => exists regs', fin = @mkst (mkFP fr cs) regs' (Z_to_bv 64 0x3a134) M rom /\
       getr regs' 11 = Z_to_bv 64 (datas + 4 * ((i + 11) * wpl)) /\ getr regs' 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl)) /\
       getr regs' 13 = Z_to_bv 64 0 /\
       regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28]%bv) regs regs').
Proof.
  intros fr cs regs M s datas datat wpl w h spat rng kval i FZ HG Hi HF HFX H10.
  destruct HG as (Hs1 & Hs2 & Hw1 & Hh1 & Hw & Hh & Ewpl & Hsz & Hds1 & Hds2 & Hds3 & Hdt1 & Hdt2 & Hdt3 & _).
  destruct HF as (Rwpl & Rds & _ & Rdt & _ & _ & Rw).
  destruct HFX as (H2 & _ & _ & _ & _ & _ & _ & _ & _ & H24 & H25 & _ & H27 & H29).
  assert (Hwpl : (w + 22 <= 4 * wpl)%Z).
  { subst wpl. unfold wpl_of.
    pose proof (Z.div_mod ((w + 22) * 8 + 31) 32 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound ((w + 22) * 8 + 31) 32 ltac:(lia)) as B. lia. }
  assert (Hm0 : (0 <= (i + 10) * wpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hm2 : (0 <= (h + 10 - i) * wpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hrow : (4 * ((i + 11) * wpl) + 4 * wpl <= 4 * (wpl * (h + 22)))%Z) by lia.
  assert (Rwpl' : rdn SEGS M (Z_to_bv 64 (s - 320 + 80)) 8 = Some (Z_to_le_bytes 8 wpl))
    by (replace (s - 320 + 80)%Z with (s - 240)%Z by lia; exact Rwpl).
  assert (Rds' : rdn SEGS M (Z_to_bv 64 (s - 320 + 96)) 8 = Some (Z_to_le_bytes 8 datas))
    by (replace (s - 320 + 96)%Z with (s - 224)%Z by lia; exact Rds).
  assert (Rdt' : rdn SEGS M (Z_to_bv 64 (s - 320 + 112)) 8 = Some (Z_to_le_bytes 8 datat))
    by (replace (s - 320 + 112)%Z with (s - 208)%Z by lia; exact Rdt).
  assert (Rw' : rdn SEGS M (Z_to_bv 64 (s - 320 + 136)) 8 = Some (Z_to_le_bytes 8 w))
    by (replace (s - 320 + 136)%Z with (s - 184)%Z by lia; exact Rw).
  do 38 bhl_snr.
  apply reach_done. cbv beta.
  eexists. split; [reflexivity|].
  split; [bhl_gsimpc; first [reflexivity | (f_equal; lia) | (f_equal; ring)]|].
  split; [bhl_gsimpc; first [reflexivity | (f_equal; lia) | (f_equal; ring)]|].
  split; [bhl_gsimpc; first [reflexivity | (f_equal; lia)]|].
  solve_regs_agree.
Qed.

Lemma bh_col : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (s datas datat wpl w h spat rng kval j : Z),
  frm_zero cs -> bc_fsc fr -> hgeo s datas datat wpl w h spat rng kval -> (0 <= j < w)%Z -> hframe s datas datat wpl w h M ->
  hfix regs s kval spat rng wpl -> getr regs 13 = Z_to_bv 64 j ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a134) M rom)
    (fun fin => exists fr' cs' regs', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a158) M rom /\ frm_zero cs' /\
       getr regs' 14 = Z_to_bv 64 (j + 11) /\ getr regs' 15 = Z_to_bv 64 (j + 11) /\ getr regs' 17 = Z_to_bv 64 (-10) /\
       regs_agree (fun r => In r [5; 6; 7; 14; 15; 16; 17; 28]%bv) regs regs' /\
       reg_get fr' 14 = Z_to_bv 64 (sbox p_zero) /\ reg_get fr' 15 = Z_to_bv 64 (sbox p_zero) /\ pass_fp fr fr').
Proof.
  intros fr cs regs M s datas datat wpl w h spat rng kval j FZ FSC HG Hj HF HFX H13.
  destruct FSC as (_ & _ & F18).
  destruct HG as (Hs1 & Hs2 & Hw1 & Hh1 & Hw & Hh & _).
  destruct HF as (_ & _ & _ & _ & _ & R0 & _).
  destruct HFX as (H2 & H8 & _ & H18 & _ & _ & _ & _ & _ & _ & _ & _ & _ & H29).
  assert (R0' : rdn SEGS M (Z_to_bv 64 (s - 320 + 128)) 8 = Some (Z_to_le_bytes 8 0))
    by (replace (s - 320 + 128)%Z with (s - 192)%Z by lia; exact R0).
  do 9 bhl_snc.
  apply reach_done. cbv beta.
  do 3 eexists. split; [reflexivity|].
  split; [exact FZ|].
  split; [bhl_gsimpc; first [reflexivity | (f_equal; lia)]|].
  split; [bhl_gsimpc; first [reflexivity | (f_equal; lia)]|].
  split; [bhl_gsimpc; first [reflexivity | (f_equal; lia)]|].
  split; [solve_regs_agree|].
  split; [bhl_fget; bhl_fhyp; apply bv_eq; vm_compute; reflexivity|].
  split; [bhl_fget; bhl_fhyp; apply bv_eq; vm_compute; reflexivity|].
  unfold pass_fp. intros x Hx.
  assert (N14 : x <> 14%bv) by (intro E; apply Hx; rewrite E; vm_compute; auto).
  assert (N15 : x <> 15%bv) by (intro E; apply Hx; rewrite E; vm_compute; auto).
  rewrite ?fpv_get_other by assumption. reflexivity.
Qed.

Lemma bh_clatch : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (s datas datat wpl w h spat rng kval j : Z),
  frm_zero cs -> hgeo s datas datat wpl w h spat rng kval -> (0 <= j < w)%Z -> hframe s datas datat wpl w h M ->
  hfix regs s kval spat rng wpl -> getr regs 13 = Z_to_bv 64 j ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a278) M rom)
    (fun fin => exists regs', fin = @mkst (mkFP fr cs) regs' (Z_to_bv 64 (if (j + 1 <? w)%Z then 0x3a134 else 0x3a28c)) M rom /\
       getr regs' 13 = Z_to_bv 64 (j + 1) /\
       regs_agree (fun r => In r [5; 6; 7; 13; 14; 15; 16; 17; 28]%bv) regs regs').
Proof.
  intros fr cs regs M s datas datat wpl w h spat rng kval j FZ HG Hj HF HFX H13.
  destruct HG as (Hs1 & Hs2 & Hw1 & Hh1 & Hw & Hh & _).
  destruct HF as (_ & _ & _ & _ & _ & _ & Rw).
  destruct HFX as (H2 & _).
  assert (Rw' : rdn SEGS M (Z_to_bv 64 (s - 320 + 136)) 8 = Some (Z_to_le_bytes 8 w))
    by (replace (s - 320 + 136)%Z with (s - 184)%Z by lia; exact Rw).
  destruct (j + 1 <? w)%Z eqn:E.
  - do 5 bhl_sn.
    apply reach_done. cbv beta.
    eexists. split; [reflexivity|].
    split; [bhl_gsimp; reflexivity|].
    solve_regs_agree.
  - do 5 bhl_sn.
    apply reach_done. cbv beta.
    eexists. split; [reflexivity|].
    split; [bhl_gsimp; reflexivity|].
    solve_regs_agree.
Qed.

Lemma bh_rlatch : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (s datas datat wpl w h spat rng kval i : Z),
  frm_zero cs -> hgeo s datas datat wpl w h spat rng kval -> (0 <= i < h)%Z -> hframe s datas datat wpl w h M ->
  hfix regs s kval spat rng wpl -> getr regs 10 = Z_to_bv 64 i ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a28c) M rom)
    (fun fin => exists regs', fin = @mkst (mkFP fr cs) regs' (Z_to_bv 64 (if (i + 1 <? h)%Z then 0x3a09c else 0x3a2a0)) M rom /\
       getr regs' 10 = Z_to_bv 64 (i + 1) /\ regs_agree (fun r => In r HPL) regs regs').
Proof.
  intros fr cs regs M s datas datat wpl w h spat rng kval i FZ HG Hi HF HFX H10.
  destruct HG as (Hs1 & Hs2 & Hw1 & Hh1 & Hw & Hh & _).
  destruct HF as (_ & _ & Rh & _).
  destruct HFX as (H2 & _).
  assert (Rh' : rdn SEGS M (Z_to_bv 64 (s - 320 + 104)) 8 = Some (Z_to_le_bytes 8 h))
    by (replace (s - 320 + 104)%Z with (s - 216)%Z by lia; exact Rh).
  destruct (i + 1 <? h)%Z eqn:E.
  - do 5 bhl_sn.
    apply reach_done. cbv beta.
    eexists. split; [reflexivity|].
    split; [bhl_gsimp; reflexivity|].
    unfold HPL; solve_regs_agree.
  - do 5 bhl_sn.
    apply reach_done. cbv beta.
    eexists. split; [reflexivity|].
    split; [bhl_gsimp; reflexivity|].
    unfold HPL; solve_regs_agree.
Qed.

End Segs.
