(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Malloc Stdio Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr FuzzPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA ImplAX BnIfaceA UnwindA EdgesA AsStruct AsByte RtCallA W_cryptoA W_expandA W_smallA BnAKitA BnCallA W_callsA BnRep2A W_bin2bnA W_cmpA W_uaddA W_addA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2024696 => 1
  | 2024700 => 2
  | 2024704 => 2
  | 2024752 => 1
  | 2024764 => 1
  | 2024816 => 1
  | 2024872 => 1
  | 2024876 => 2
  | 2024880 => 1
  | 2024884 => 1
  | 2024888 => 1
  | 2024892 => 2
  | 2024896 => 1
  | 2024900 => 1
  | 2024904 => 1
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac fix_ret :=
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

(* [comment removed for export] *)
Ltac br_lit :=
  let K := fresh "KBR" in
  step; if_cases K; zify_cond K; try (exfalso; rewrite ?unsigned_lit in K by lia; lia); try clear K.

(* [comment removed for export] *)
Lemma lib_state_statics : forall cxo hs ls m OW AD EA, lib_state_hc cxo hs ls m OW AD EA -> ad_statics m AD.
Proof. intros cxo hs ls m OW AD EA (_ & _ & _ & (_ & _ & (H & _))). exact H. Qed.

Ltac get_stat LS S1 S2 S3 S4 S5 S6 :=
  destruct (lib_state_statics _ _ _ _ _ _ _ LS) as (S1 & S2 & S3 & S4 & S5 & S6);
  unfold BN_B1, BN_B2, BN_B3, BN_B4, BN_B5, BN_CTX, MallocRep.wz in S1, S2, S3, S4, S5, S6.

Definition nonpool (r : bnref) : Prop := forall i, r <> RPool i.

Definition FUZZER_TEST_ONE : Z := 0x1ee4b4.
Definition LX_FUZZ_ENTRY : Z := 0x1ee35c.
Definition ERR_CLEAR_ERROR : Z := 0x1f4354.
Definition BN_MUL : Z := 0x24e4f4.
Definition BN_DIV : Z := 0x2524b4.

(* [comment removed for export] *)
Definition payload_okA (m : mem) (LB : list block) (D : Z) (d : list Z) : Prop :=
  bytes_at bsegs m D (to_bytes d) /\ Forall (fun c => 0 <= c < 256) d
  /\ 0 < D /\ zlength d < 2^30
  /\ (d = [] \/ exists b, In b LB /\ blk_addr b <= D /\ D + zlength d <= blk_addr b + blk_size b).

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).


(* [comment removed for export] *)
Definition BN_mul_walkA_stmt (BN_MUL_STACK BN_MUL_COST : Z) : Prop := forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo : Z) (ras : list Z) (rr rx ry : bnref) (ar ax ay : Z),
    bn_preA Σ ls m OW LB AD EA sp lo BN_MUL_STACK BN_MUL_COST ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MUL (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW AD rr ar -> ref_at ls OW AD rx ax -> ref_at ls OW AD ry ay ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz (ad_ctx AD) ->
    nonpool rr -> nonpool rx -> nonpool ry ->
    implA (BN_mul (tree_ops bptr) rr rx ry ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA BN_MUL_COST (fun _ _ _ a0' => a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL) fc None m (seg_rom bsegs)).


Definition BN_div_walkA_stmt (BN_DIV_STACK BN_DIV_COST : Z) : Prop := forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo : Z) (ras : list Z) (dv rm num dvs : bnref) (adv arm anum advs : Z),
    bn_preA Σ ls m OW LB AD EA sp lo BN_DIV_STACK BN_DIV_COST ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_DIV (bv_unsigned ra :: ras) ->
    tp = wz TP_A ->
    ref_at ls OW AD dv adv -> ref_at ls OW AD rm arm -> ref_at ls OW AD num anum -> ref_at ls OW AD dvs advs ->
    a0 = wz adv -> a1 = wz arm -> a2 = wz anum -> a3 = wz advs -> a4 = wz (ad_ctx AD) ->
    nonpool dv -> nonpool rm -> nonpool num -> nonpool dvs -> dv <> num -> dv <> dvs ->
    implA (BN_div (tree_ops bptr) dv rm num dvs ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA BN_DIV_COST (fun _ _ _ a0' => a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_DIV) fc None m (seg_rom bsegs)).


  (* [comment removed for export] *)
Definition ece_postA (ECE_COST : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (EA : err_addrs)
      (lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
      ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ AHEAP Σ' OW LB m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (ea_ES EA <= a < ea_ES EA + 904)) m m'
      /\ rw_cells bsegs m' (ea_ES EA) [CB 904 ES_CLEARED]
      /\ rt_credit RT Σ - ECE_COST <= rt_credit RT Σ'.

Definition ERR_clear_error_cpsA_stmt (ECE_STACK ECE_COST : Z) : Prop := forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (EA : err_addrs) (lo : Z),
    AHEAP Σ OW LB m -> stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - ECE_STACK ->
    bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> mem_inv bsegs m -> tp = wz TP_A ->
    ra = wz 2024948 ->                                                    (* [comment removed for export] *)
    (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->      (* [comment removed for export] *)
    crypto_statics m -> err_inv m OW EA -> cnt_ok ls OW LB -> st_okm ls -> ECE_COST <= rt_credit RT Σ ->
    cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                     F (wz ERR_CLEAR_ERROR) fc None m (seg_rom bsegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (ece_postA ECE_COST ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB EA lo m Σ') c).


Section Proofs.
  (* [comment removed for export] *)
  Variables (BN_MUL_STACK BN_DIV_STACK ECE_STACK BN_MUL_COST BN_DIV_COST ECE_COST : Z).
  Hypothesis STK_MUL : 0 <= BN_MUL_STACK <= 0x18000.
  Hypothesis STK_DIV : 0 <= BN_DIV_STACK <= 0x18000.
  Hypothesis STK_ECE : 0 <= ECE_STACK <= 0x18000.
  Hypothesis COST_MUL : 0 <= BN_MUL_COST.
  Hypothesis COST_DIV : 0 <= BN_DIV_COST.
  Hypothesis COST_ECE : 0 <= ECE_COST.

  Hypothesis BN_mul_walkA_h : BN_mul_walkA_stmt BN_MUL_STACK BN_MUL_COST.
  Hypothesis BN_div_walkA_h : BN_div_walkA_stmt BN_DIV_STACK BN_DIV_COST.
  Hypothesis ERR_clear_error_cpsA_h : ERR_clear_error_cpsA_stmt ECE_STACK ECE_COST.

  Definition FUZZ_TOTAL : Z := 3 * MC + BN_DIV_COST + BN_MUL_COST + ECE_COST.
  Definition FUZZ_STACK_A : Z := 96 + 0x18000.

  Section Env.
    (* [comment removed for export] *)
    Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jb : list byte).
    Variables (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z).
    Notation SP := (bv_unsigned sp).
    Notation FB := (bv_unsigned sp + -96).
    Notation PREC := [CB 8 jb; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
    Notation CENV := (cenvA LB AD lo SP FB s0 ra None FUZZ_TOTAL Σ ls OW m PREC).
    Notation QPOST := (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA FUZZ_TOTAL
                                (fun (rc : Z) (_ : lstate bptr) (_ : list block) (a0' : word) => rc = 0 /\ a0' = wz 0)).
    Hypothesis LOS : lo <= SP - FUZZ_STACK_A.

    (* [comment removed for export] *)
    Lemma fuzz_doneA : forall used Σx lsx mx OWx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31
        (F : bvmap 5 word) (fc : bv 32),
      CENV used Σx lsx mx OWx -> used + ECE_COST <= FUZZ_TOTAL -> lib_state lsx mx OWx AD EA -> bv_unsigned x8 <= lo ->
      implA (TRet (0, lsx)) Σx QPOST
        (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1ee5f0) fc None mx (seg_rom bsegs)).
    Proof.
      intros until fc. intros ENV HU LS' HX8.
      pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW).
      pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0).
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
      pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
      unfold FUZZ_STACK_A in *.
      pose proof LS' as (CS & EI & _).
      destruct (lib_state_h_parts _ _ _ _ _ _ LS') as (IDS & ADB & (_ & _ & _ & EB4) & SOK).
      pose proof (AH_range _ _ _ _ _ _ _ HEAP EB4) as (E0 & _ & _ & EC & EI').
      assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; lia).
      apply implA_from_evt. step. apply evt_done.
      eapply implA_step.
      { eapply ERR_clear_error_cpsA_h with (lo := lo) (OW := OWx) (LB := LB) (EA := EA) (ls := lsx);
          [exact HEAP | rewrite ESP; exact ST | exact CEIL | rewrite ESP; lia | rewrite ESP; unfold USTACK_TOP; lia | rewrite ESP; exact FB16 | exact MI | reflexivity
          | reflexivity | left; exact HX8
          | exact CS | exact EI | exact (cnt_ok_eq _ _ _ _ _ CNT0 CNT) | exact SOK | lia]. }
      intros Σ2 ms2 PO. unfold ece_postA in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & -> & HEAP2 & MI2 & ST2 & AG2 & ES2 & CR2).
      rewrite ESP in *. fix_ret.
      assert (LS2 : lib_state lsx m2 OWx AD EA) by (eapply lib_state_err_clearedA; [exact HEAP | exact LS' | exact AG2 | exact ES2]).
      assert (CP : cpostA LB AD EA lo FB Σx lsx mx OWx ECE_COST Σ2 lsx m2 OWx).
      { unfold cpostA. split; [exact HEAP2|]. split; [exact LS2|]. split; [exact ST2|]. split; [exact MI2|].
        split; [eapply (ax_pres_of_icall Σx OWx LB mx m2 FB LIBW_A (ea_ES EA) 904 (ea_pe EA, ea_ES EA, 904) HEAP EB4);
                 [cbn; lia | cbn; lia | unfold BnHeapA.ACEIL in *; lia | exact AG2]|].
        split; [exact CR2|]. split; [apply cnt_eq_refl | apply refs_stable_refl]. }
      assert (ENV2 : CENV (used + ECE_COST) Σ2 lsx m2 OWx) by (eapply cenv_postA; [exact ENV | exact CP]).
      pose proof ENV2 as ENVF. eapply cenv_finalA in ENVF; [| exact LS2 | lia].
      destruct ENVF as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      pose proof ENV2 as (_ & _ & ST3 & _ & _ & _ & _ & _ & FR3 & _ & _).
      clear ENV ENV2 CP HEAP ST MI AXP CR CNT RS FR UW.
      cbn [app] in FR3.
      pose proof (munch_refl [(FB, bv_unsigned sp)]%Z m2) as MUe. pose proof (wmono_refl bsegs m2) as WMe.
      apply implA_ret_evt.
      step. do 11 step.
      release_frame FR3 ST3 (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_postA. do 17 eexists. exists m2, OWx. split; [reflexivity|]. cbn [fst snd].
      split; [exact G1|]. split; [exact G2|]. split; [exact ST3|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
      split; [exact G6|]. split; [exact G7|]. split; reflexivity.
    Qed.

    (* [comment removed for export] *)
    Definition fz_success (lsx : lstate bptr) : bool :=
      let b1 := getbn RB1 lsx in let b2 := getbn RB2 lsx in let b3 := getbn RB3 lsx in let b4 := getbn RB4 lsx in
      let z (b : bignum bptr) := (bn_top b =? 0)%nat in
      if z b1 then z b3 && z b4
      else if bn_neg b1 then (negb (Bool.eqb (bn_neg b3) (bn_neg b2)) || z b3) && (bn_neg b4 || z b4)
      else (Bool.eqb (bn_neg b3) (bn_neg b2) || z b3) && (negb (bn_neg b4) || z b4).

    (* [comment removed for export] *)
    Notation S4V := (Z_to_bv 64 12412460). Notation S5V := (Z_to_bv 64 12412352).
    Notation S6V := (Z_to_bv 64 12412288). Notation S8V := (Z_to_bv 64 12412464).

    Lemma fuzz_checkA : forall (POST : machine_state -> Prop) used Σx lsx mx OWx
        x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x25 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32),
      CENV used Σx lsx mx OWx -> lib_state lsx mx OWx AD EA ->
      (forall m2 v y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
         CENV used Σx lsx m2 OWx -> lib_state lsx m2 OWx AD EA -> v = Z.b2z (fz_success lsx) ->
         evt bsegs POST (MS (mkR y1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y5 y6 y7 (Z_to_bv 64 v) y9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19
                                 S4V x23 S6V S5V S8V x25 s10 s11 y28 y29 y30 y31)
                            F (Z_to_bv 64 0x1ee6f0) fc None m2 (seg_rom bsegs))) ->
      evt bsegs POST (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                              S4V x23 S6V S5V S8V x25 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x1ee654) fc None mx (seg_rom bsegs)).
    Proof.
      intros until fc. intros ENV LS' K.
      assert (LOFB16 : lo <= FB - 16) by (unfold FUZZ_STACK_A in LOS; lia).
      pose proof (is_zero_callA LB AD EA lo SP FB s0 ra None FUZZ_TOTAL Σ ls OW m LOFB16) as IZC.
      pose proof (is_neg_callA LB AD EA lo SP FB s0 ra None FUZZ_TOTAL Σ ls OW m LOFB16) as INC.
      unfold BN_IS_ZERO, BN_IS_NEGATIVE in *.
      remember (bn_top (getbn RB1 lsx) =? 0)%nat as z1 eqn:EZ1. remember (bn_top (getbn RB3 lsx) =? 0)%nat as z3 eqn:EZ3.
      remember (bn_top (getbn RB4 lsx) =? 0)%nat as z4 eqn:EZ4.
      remember (bn_neg (getbn RB1 lsx)) as n1 eqn:EN1. remember (bn_neg (getbn RB2 lsx)) as n2 eqn:EN2.
      remember (bn_neg (getbn RB3 lsx)) as n3 eqn:EN3. remember (bn_neg (getbn RB4 lsx)) as n4 eqn:EN4.
      assert (ESUC : fz_success lsx = if z1 then z3 && z4 else if n1 then (negb (Bool.eqb n3 n2) || z3) && (n4 || z4) else (Bool.eqb n3 n2 || z3) && (negb n4 || z4))
        by (unfold fz_success; rewrite <- EZ1, <- EZ3, <- EZ4, <- EN1, <- EN2, <- EN3, <- EN4; reflexivity).
      (* [comment removed for export] *)
      assert (BZ4 : forall mz q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31,
                 CENV used Σx lsx mz OWx -> lib_state lsx mz OWx AD EA -> Z.b2z z4 = Z.b2z (fz_success lsx) ->
                 evt bsegs POST (MS (mkR q1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 x18 x19
                                         S4V x23 S6V S5V S8V x25 s10 s11 q28 q29 q30 q31)
                                    F (Z_to_bv 64 0x1ee66c) fc None mz (seg_rom bsegs))).
      { intros mz q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVx LSx EQ.
        get_stat LSx T1 T2 T3 T4 T5 T6.
        step. step.
        eapply (IZC POST _ used Σx lsx mz OWx RB4 (ad_b4 AD)); [exact ENVx | exact LSx | exact eq_refl |].
        intros m2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2. fix_ret. rewrite <- EZ4.
        do 2 step.
        setreg 8%Z (Z_to_bv 64 (Z.b2z z4)) ltac:(destruct z4; reflexivity).
        eapply K; [exact ENV2 | exact LS2 | exact EQ]. }
      (* [comment removed for export] *)
      assert (B1 : forall mz q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31,
                 CENV used Σx lsx mz OWx -> lib_state lsx mz OWx AD EA -> fz_success lsx = true ->
                 evt bsegs POST (MS (mkR q1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 x18 x19
                                         S4V x23 S6V S5V S8V x25 s10 s11 q28 q29 q30 q31)
                                    F (Z_to_bv 64 0x1ee6e4) fc None mz (seg_rom bsegs))).
      { intros mz q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVx LSx EQ.
        do 2 step. eapply K; [exact ENVx | exact LSx | rewrite EQ; reflexivity]. }
      assert (B0 : forall mz q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31,
                 CENV used Σx lsx mz OWx -> lib_state lsx mz OWx AD EA -> fz_success lsx = false ->
                 evt bsegs POST (MS (mkR q1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 x18 x19
                                         S4V x23 S6V S5V S8V x25 s10 s11 q28 q29 q30 q31)
                                    F (Z_to_bv 64 0x1ee6ec) fc None mz (seg_rom bsegs))).
      { intros mz q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVx LSx EQ.
        step. eapply K; [exact ENVx | exact LSx | rewrite EQ; reflexivity]. }
      (* [comment removed for export] *)
      get_stat LS' T1 T2 T3 T4 T5 T6.
      step. step.
      eapply (IZC POST _ used Σx lsx mx OWx RB1 (ad_b1 AD)); [exact ENV | exact LS' | exact eq_refl |].
      intros ma ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVa LSa. fix_ret. rewrite <- EZ1. clear T1 T2 T3 T4 T5 T6.
      get_stat LSa T1 T2 T3 T4 T5 T6.
      destruct z1; cbn [Z.b2z].
      - (* [comment removed for export] *)
        br_lit. step. step.
        eapply (IZC POST _ used Σx lsx ma OWx RB3 (ad_b3 AD)); [exact ENVa | exact LSa | exact eq_refl |].
        intros mb ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVb LSb. fix_ret. rewrite <- EZ3. clear T1 T2 T3 T4 T5 T6.
        destruct z3; cbn [Z.b2z].
        + br_lit. eapply BZ4; [exact ENVb | exact LSb | rewrite ESUC; reflexivity].
        + br_lit. eapply B0; [exact ENVb | exact LSb | rewrite ESUC; reflexivity].
      - (* [comment removed for export] *)
        br_lit. step. step.
        eapply (INC POST _ used Σx lsx ma OWx RB1 (ad_b1 AD)); [exact ENVa | exact LSa | exact eq_refl |].
        intros mb ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVb LSb. fix_ret. rewrite <- EN1. clear T1 T2 T3 T4 T5 T6.
        get_stat LSb T1 T2 T3 T4 T5 T6. step. do 3 step.
        eapply (INC POST _ used Σx lsx mb OWx RB3 (ad_b3 AD)); [exact ENVb | exact LSb | exact eq_refl |].
        intros mc ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVc LSc. fix_ret. rewrite <- EN3. clear T1 T2 T3 T4 T5 T6.
        get_stat LSc T1 T2 T3 T4 T5 T6. step. do 3 step.
        eapply (INC POST _ used Σx lsx mc OWx RB2 (ad_b2 AD)); [exact ENVc | exact LSc | exact eq_refl |].
        intros md ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVd LSd. fix_ret. rewrite <- EN2. clear T1 T2 T3 T4 T5 T6.
        destruct n1; cbn [Z.b2z].
        + (* [comment removed for export] *)
          assert (B3c4 : forall mz q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31,
                   CENV used Σx lsx mz OWx -> lib_state lsx mz OWx AD EA -> (negb (Bool.eqb n3 n2) || z3) = true ->
                   evt bsegs POST (MS (mkR q1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 x18 x19
                                           S4V x23 S6V S5V S8V x25 s10 s11 q28 q29 q30 q31)
                                      F (Z_to_bv 64 0x1ee6b8) fc None mz (seg_rom bsegs))).
          { intros mz q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVx LSx HP.
            get_stat LSx U1 U2 U3 U4 U5 U6. step. step.
            eapply (INC POST _ used Σx lsx mz OWx RB4 (ad_b4 AD)); [exact ENVx | exact LSx | exact eq_refl |].
            intros my ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVy LSy. fix_ret. rewrite <- EN4. clear U1 U2 U3 U4 U5 U6.
            destruct n4; cbn [Z.b2z].
            - br_lit. step. eapply B1; [exact ENVy | exact LSy | rewrite ESUC, HP; reflexivity].
            - br_lit. eapply BZ4; [exact ENVy | exact LSy | rewrite ESUC, HP; reflexivity]. }
          br_lit.
          destruct (Bool.eqb n3 n2) eqn:E32.
          * (* [comment removed for export] *)
            step. if_cases KN; zify_cond KN.
            { exfalso. apply KN. rewrite (Bool.eqb_prop _ _ E32). reflexivity. }
            clear KN. get_stat LSd U1 U2 U3 U4 U5 U6. step. step.
            eapply (IZC POST _ used Σx lsx md OWx RB3 (ad_b3 AD)); [exact ENVd | exact LSd | exact eq_refl |].
            intros me ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVe LSe. fix_ret. rewrite <- EZ3. clear U1 U2 U3 U4 U5 U6.
            destruct z3; cbn [Z.b2z].
            -- br_lit. eapply B3c4; [exact ENVe | exact LSe | rewrite ?E32; reflexivity].
            -- br_lit. eapply B0; [exact ENVe | exact LSe | rewrite ESUC, ?E32; reflexivity].
          * step. if_cases KN; zify_cond KN.
            2:{ exfalso. destruct n3, n2; cbn in E32, KN; try discriminate; rewrite ?unsigned_lit in KN by lia; lia. }
            clear KN. eapply B3c4; [exact ENVd | exact LSd | rewrite ?E32; reflexivity].
        + (* [comment removed for export] *)
          assert (B3e4 : forall mz q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31,
                   CENV used Σx lsx mz OWx -> lib_state lsx mz OWx AD EA -> (Bool.eqb n3 n2 || z3) = true ->
                   evt bsegs POST (MS (mkR q1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 x18 x19
                                           S4V x23 S6V S5V S8V x25 s10 s11 q28 q29 q30 q31)
                                      F (Z_to_bv 64 0x1ee6d8) fc None mz (seg_rom bsegs))).
          { intros mz q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVx LSx HP.
            get_stat LSx U1 U2 U3 U4 U5 U6. step. step.
            eapply (INC POST _ used Σx lsx mz OWx RB4 (ad_b4 AD)); [exact ENVx | exact LSx | exact eq_refl |].
            intros my ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVy LSy. fix_ret. rewrite <- EN4. clear U1 U2 U3 U4 U5 U6.
            destruct n4; cbn [Z.b2z].
            - br_lit. eapply BZ4; [exact ENVy | exact LSy | rewrite ESUC, HP; reflexivity].
            - br_lit. eapply B1; [exact ENVy | exact LSy | rewrite ESUC, HP; reflexivity]. }
          br_lit.
          destruct (Bool.eqb n3 n2) eqn:E32.
          * step. if_cases KN; zify_cond KN.
            2:{ exfalso. apply KN. rewrite (Bool.eqb_prop _ _ E32). reflexivity. }
            clear KN. eapply B3e4; [exact ENVd | exact LSd | rewrite ?E32; reflexivity].
          * (* [comment removed for export] *)
            step. if_cases KN; zify_cond KN.
            { exfalso. destruct n3, n2; cbn in E32, KN; try discriminate; rewrite ?unsigned_lit in KN by lia; lia. }
            clear KN. get_stat LSd U1 U2 U3 U4 U5 U6. step. step.
            eapply (IZC POST _ used Σx lsx md OWx RB3 (ad_b3 AD)); [exact ENVd | exact LSd | exact eq_refl |].
            intros me ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVe LSe. fix_ret. rewrite <- EZ3. clear U1 U2 U3 U4 U5 U6.
            destruct z3; cbn [Z.b2z].
            -- br_lit. eapply B3e4; [exact ENVe | exact LSe | rewrite ?E32; reflexivity].
            -- br_lit. eapply B0; [exact ENVe | exact LSe | rewrite ESUC, ?E32; reflexivity].
    Qed.

    (* [comment removed for export] *)
    Lemma bytes_clientA : forall used Σx lsx mx OWx A bs,
      CENV used Σx lsx mx OWx -> bytes_at bsegs m A bs ->
      (bs = [] \/ exists b, In b LB /\ blk_addr b <= A /\ A + Z.of_nat (length bs) <= blk_addr b + blk_size b) ->
      bytes_at bsegs mx A bs.
    Proof.
      intros used Σx lsx mx OWx A bs (OK & HEAP & _ & _ & AXP & _) BY [->|(b & Hb & Hb1 & Hb2)].
      - destruct BY as (B1 & B2 & _). split; [exact B1|]. split; [exact B2|]. intros i Hi. cbn in Hi. lia.
      - eapply bytes_at_agree; [exact AXP | exact BY |].
        intros a Ha.
        pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; right; exact Hb)) as (B0 & _ & _ & _ & BI).
        split; [| right; right; exists b; split; [exact Hb| lia]].
        unfold LIBW_A. cbn [rin_ivs fst snd]. lia.
    Qed.

    Hypothesis CTXR : True.   (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma fuzz_mainA : forall (buf : Z) (n1 n2 : list Z) (v1 v2 : Z) m1
        x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32),
      CENV 0 Σ ls m1 OW -> lib_state ls m1 OW AD EA ->
      bytes_at bsegs m buf (to_bytes n1) -> bytes_at bsegs m (buf + zlength n1) (to_bytes n2) ->
      Forall (fun c => 0 <= c < 256) n1 -> Forall (fun c => 0 <= c < 256) n2 ->
      0 < buf -> buf <= lo -> zlength n1 < 2^31 -> zlength n2 < 2^31 ->
      (n1 = [] \/ exists b, In b LB /\ blk_addr b <= buf /\ buf + zlength n1 <= blk_addr b + blk_size b) ->
      (n2 = [] \/ exists b, In b LB /\ blk_addr b <= buf + zlength n1 /\ buf + zlength n1 + zlength n2 <= blk_addr b + blk_size b) ->
      0 <= v1 < 2^64 -> 0 <= v2 < 2^64 -> (n1 <> [] \/ n2 <> [] -> 1 < buf) ->
      implA (fuzz_body (negb (v1 =? 0)) (negb (v2 =? 0)) n1 n2 ls) Σ QPOST
        (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) x5 x6 x7 (Z_to_bv 64 buf) (Z_to_bv 64 v2) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (zlength n2)) (Z_to_bv 64 v1) (Z_to_bv 64 (zlength n1)) (Z_to_bv 64 SHB) x22 x21 x24 x25 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1ee580) fc None m1 (seg_rom bsegs)).
    Proof.
      intros until fc. intros ENV0 LS0 BY1 BY2 BF1 BF2 BUF0 BUFFB L1 L2 CB1 CB2 RV1 RV2 SRC12.
      pose proof ENV0 as (OK & HEAP0 & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0).
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
      pose proof (AH_ceil _ _ _ _ HEAP0) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
      unfold FUZZ_STACK_A in *.
      assert (LOFB16 : lo <= FB - 16) by lia.
      assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; lia).
      pose proof (is_zero_callA LB AD EA lo SP FB s0 ra None FUZZ_TOTAL Σ ls OW m LOFB16) as IZC.
      pose proof (set_neg_callA LB AD EA lo SP FB s0 ra None FUZZ_TOTAL Σ ls OW m LOFB16) as SNC.
      pose proof (fun A => @bn_postA_cpost _ LB AD EA lo SP FB FUZZ_TOTAL Σ ls OW A) as BPC.
      unfold BN_IS_ZERO, BN_SET_NEGATIVE in *.
      unfold fuzz_body. cbv zeta.
      assert (CBx : forall A n, (n = [] \/ exists b, In b LB /\ blk_addr b <= A /\ A + zlength n <= blk_addr b + blk_size b) ->
                    (to_bytes n = [] \/ exists b, In b LB /\ blk_addr b <= A /\ A + Z.of_nat (length (to_bytes n)) <= blk_addr b + blk_size b)).
      { intros A n [->|H]; [left; reflexivity| right]. unfold to_bytes. rewrite length_map. exact H. }
      assert (FPS : forall mz, uw_chain USTACK_TOP mz (bv_unsigned (Z_to_bv 64 FB)) (bv_unsigned (Z_to_bv 64 buf)) []).
      { intros mz. cbn [uw_chain]. left. rewrite ESP, unsigned_lit by lia. lia. }
      (* [comment removed for export] *)
      get_stat LS0 T1 T2 T3 T4 T5 T6.
      apply implA_from_evt.
      do 5 step.
      apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
      eapply implA_bind.
      { eapply BN_bin2bn_walkA with (lo := lo) (OW := OW) (LB := LB) (AD := AD) (EA := EA) (r := RB1) (a := ad_b1 AD) (SRC := buf) (bs := n1) (ras := []);
          [eapply cenv_preA; [exact ENV0 | exact LS0 | unfold BN_BIN2BN_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia | unfold FUZZ_TOTAL, MC; lia]
          | apply FPS | rewrite unsigned_lit by lia; exact R_BN_bin2bn_1f32b0 | reflexivity | exact eq_refl
          | eapply bytes_clientA; [exact ENV0 | exact BY1 | apply CBx; exact CB1]
          | exact BF1 | exact L1 | exact BUF0 | exact CB1 | reflexivity | reflexivity | reflexivity
          | intros NE; apply SRC12; left; exact NE]. }
      cbv beta. intros [u1 ls1] Σ1 ms1 PO.
      apply (bn_postA_cpost LB AD EA lo SP FB FUZZ_TOTAL Σ ls OW) in PO; [| exact OK | exact HEAP0].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m2 & OW1 & -> & CP1 & (-> & _)).
      assert (E1 : CENV (0 + MC) Σ1 ls1 m2 OW1 /\ lib_state ls1 m2 OW1 AD EA) by (eapply cenv_postA; [exact ENV0 | exact CP1]).
      destruct E1 as (ENV1 & LS1).
      cbn [fst snd] in *. fix_ret. clear CP1 T1 T2 T3 T4 T5 T6.
      (* [comment removed for export] *)
      get_stat LS1 T1 T2 T3 T4 T5 T6.
      unfold MallocRep.wz. apply implA_from_evt.
      step. br_lit. do 3 step.
      eapply (SNC _ _ (0 + MC) Σ1 ls1 m2 OW1 RB1 (ad_b1 AD)); [exact ENV1 | exact LS1 | exact eq_refl |].
      intros m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. fix_ret. clear T1 T2 T3 T4 T5 T6.
      rewrite (unsigned_lit v1) in ENV2, LS2 by lia.
      lazymatch type of LS2 with lib_state ?l _ _ _ _ => set (ls2 := l) in * end.
      (* [comment removed for export] *)
      get_stat LS2 T1 T2 T3 T4 T5 T6.
      zstep.
      chk ltac:(fun C => unfold zlength, FUZZ_STACK_A in *; rewrite ?land_m64_small in C by lia; lia).
      do 3 zstep.
      rewrite ?land_m64_small by (unfold zlength, FUZZ_STACK_A in *; lia).
      try replace (0 <? buf) with true by (symmetry; apply Z.ltb_lt; exact BUF0).
      try replace (zlength n1 + buf <? 1) with false by (symmetry; apply Z.ltb_ge; clear - BUF0; unfold zlength; lia).
      try change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1.
      first [ chk_lit | chk ltac:(fun C => unfold zlength, FUZZ_STACK_A in *; rewrite ?land_m64_small in C by lia; lia) ].
      try replace (zlength n1 + buf) with (buf + zlength n1) by (clear; lia).
      do 3 step. step.
      pose proof ENV2 as (_ & HEAP2 & _).
      apply evt_done. unfold BN_set_negative at 1. rewrite bbind_get_set. fold ls2.
      unfold bbind at 1. cbn [bind tree_ops].
      eapply implA_bind.
      { eapply BN_bin2bn_walkA with (lo := lo) (OW := OW1) (LB := LB) (AD := AD) (EA := EA) (r := RB2) (a := ad_b2 AD) (SRC := buf + zlength n1) (bs := n2) (ras := []);
          [eapply cenv_preA; [exact ENV2 | exact LS2 | unfold BN_BIN2BN_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia | unfold FUZZ_TOTAL, MC; lia]
          | apply FPS | rewrite unsigned_lit by lia; exact R_BN_bin2bn_1f32d8 | reflexivity | exact eq_refl
          | eapply bytes_clientA; [exact ENV2 | exact BY2 | apply CBx; exact CB2]
          | exact BF2 | exact L2 | unfold zlength in *; lia | exact CB2 | reflexivity | reflexivity | reflexivity
          | intros NE; pose proof (SRC12 (or_intror NE)) as S12; unfold zlength in *; lia]. }
      cbv beta. intros [u3 ls3] Σ3 ms3 PO.
      apply (bn_postA_cpost LB AD EA lo SP FB FUZZ_TOTAL Σ ls OW) in PO; [| exact OK | exact HEAP2].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m4 & OW3 & -> & CP3 & (-> & _)).
      assert (E3 : CENV (0 + MC + MC) Σ3 ls3 m4 OW3 /\ lib_state ls3 m4 OW3 AD EA) by (eapply cenv_postA; [exact ENV2 | exact CP3]).
      destruct E3 as (ENV3 & LS3).
      cbn [fst snd] in *. fix_ret. clear CP3 T1 T2 T3 T4 T5 T6 HEAP2.
      (* [comment removed for export] *)
      get_stat LS3 T1 T2 T3 T4 T5 T6.
      unfold MallocRep.wz. apply implA_from_evt.
      step. br_lit. do 3 step.
      eapply (SNC _ _ (0 + MC + MC) Σ3 ls3 m4 OW3 RB2 (ad_b2 AD)); [exact ENV3 | exact LS3 | exact eq_refl |].
      intros m5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV4 LS4. fix_ret. clear T1 T2 T3 T4 T5 T6.
      rewrite (unsigned_lit v2) in ENV4, LS4 by lia.
      lazymatch type of LS4 with lib_state ?l _ _ _ _ => set (ls4 := l) in * end.
      (* [comment removed for export] *)
      get_stat LS4 T1 T2 T3 T4 T5 T6.
      step. step.
      eapply (IZC _ _ (0 + MC + MC) Σ3 ls4 m5 OW3 RB2 (ad_b2 AD)); [exact ENV4 | exact LS4 | exact eq_refl |].
      intros m6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV5 LS5. fix_ret. clear T1 T2 T3 T4 T5 T6.
      apply evt_done. cbv beta. unfold BN_set_negative at 1. rewrite bbind_get_set. fold ls4. rewrite bbind_get.
      destruct (bn_top (getbn RB2 ls4) =? 0)%nat eqn:Z2; cbn [Z.b2z].
      { (* [comment removed for export] *)
        unfold bbind, bret. cbn [bind ret tree_ops tbind fst snd].
        apply implA_from_evt. br_lit. apply evt_done.
        eapply fuzz_doneA; [exact ENV5 | unfold FUZZ_TOTAL, MC; lia | exact LS5 | rewrite unsigned_lit by lia; exact BUFFB]. }
      (* [comment removed for export] *)
      get_stat LS5 T1 T2 T3 T4 T5 T6.
      pose proof ENV5 as (_ & HEAP5 & _).
      apply implA_from_evt. br_lit.
      do 9 step.
      apply evt_done. unfold bbind at 1. cbn [bind tree_ops]. unfold bbind at 1. cbn [bind tree_ops].
      apply implA_assoc.
      eapply implA_bind.
      { eapply BN_div_walkA_h with (lo := lo) (OW := OW3) (LB := LB) (AD := AD) (EA := EA) (ras := [])
                 (dv := RB3) (rm := RB4) (num := RB1) (dvs := RB2) (adv := ad_b3 AD) (arm := ad_b4 AD) (anum := ad_b1 AD) (advs := ad_b2 AD);
          [eapply cenv_preA; [exact ENV5 | exact LS5 | lia | unfold FUZZ_TOTAL, MC; lia]
          | apply FPS | rewrite unsigned_lit by lia; exact R_BN_div_1f3358 | reflexivity | exact eq_refl | exact eq_refl | exact eq_refl | exact eq_refl
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | intros i; discriminate | intros i; discriminate | intros i; discriminate | intros i; discriminate | discriminate | discriminate]. }
      cbv beta. intros [u6 ls6] Σ6 ms6 PO.
      apply (bn_postA_cpost LB AD EA lo SP FB FUZZ_TOTAL Σ ls OW) in PO; [| exact OK | exact HEAP5].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F6 & fc6 & m7 & OW6 & -> & CP6 & ->).
      assert (E6 : CENV (0 + MC + MC + BN_DIV_COST) Σ6 ls6 m7 OW6 /\ lib_state ls6 m7 OW6 AD EA) by (eapply cenv_postA; [exact ENV5 | exact CP6]).
      destruct E6 as (ENV6 & LS6).
      cbn [fst snd] in *. fix_ret. clear CP6 T1 T2 T3 T4 T5 T6 HEAP5.
      (* [comment removed for export] *)
      unfold MallocRep.wz. apply implA_from_evt.
      br_lit.
      eapply (fuzz_checkA _ (0 + MC + MC + BN_DIV_COST) Σ6 ls6 m7 OW6); [exact ENV6 | exact LS6 |].
      intros m8 v ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV7 LS7 EV.
      assert (RV : 0 <= v <= 1) by (subst v; destruct (fz_success ls6); cbn; lia).
      (* [comment removed for export] *)
      get_stat LS7 T1 T2 T3 T4 T5 T6.
      pose proof ENV7 as (_ & HEAP7 & _).
      do 6 step.
      assert (FPV : forall mz, uw_chain USTACK_TOP mz (bv_unsigned (Z_to_bv 64 FB)) (bv_unsigned (Z_to_bv 64 v)) []).
      { intros mz. cbn [uw_chain]. left. rewrite ESP, unsigned_lit by lia. lia. }
      apply evt_done. cbv beta. cbn [fst snd]. rewrite !bbind_get. cbv zeta.
      unfold bbind at 1. cbn [bind tree_ops].
      apply implA_assoc.
      eapply implA_bind.
      { eapply BN_mul_walkA_h with (lo := lo) (OW := OW6) (LB := LB) (AD := AD) (EA := EA) (ras := [])
                 (rr := RB5) (rx := RB3) (ry := RB2) (ar := ad_b5 AD) (ax := ad_b3 AD) (ay := ad_b2 AD);
          [eapply cenv_preA; [exact ENV7 | exact LS7 | lia | unfold FUZZ_TOTAL, MC; lia]
          | apply FPV | rewrite unsigned_lit by lia; exact R_BN_mul_1f3410 | reflexivity | exact eq_refl | exact eq_refl | exact eq_refl
          | reflexivity | reflexivity | reflexivity | reflexivity
          | intros i; discriminate | intros i; discriminate | intros i; discriminate]. }
      cbv beta. intros [u8 ls8] Σ8 ms8 PO.
      apply (bn_postA_cpost LB AD EA lo SP FB FUZZ_TOTAL Σ ls OW) in PO; [| exact OK | exact HEAP7].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F8 & fc8 & m9 & OW8 & -> & CP8 & ->).
      assert (E8 : CENV (0 + MC + MC + BN_DIV_COST + BN_MUL_COST) Σ8 ls8 m9 OW8 /\ lib_state ls8 m9 OW8 AD EA) by (eapply cenv_postA; [exact ENV7 | exact CP8]).
      destruct E8 as (ENV8 & LS8).
      cbn [fst snd] in *. fix_ret. clear CP8 T1 T2 T3 T4 T5 T6 HEAP7.
      (* [comment removed for export] *)
      get_stat LS8 T1 T2 T3 T4 T5 T6.
      pose proof ENV8 as (_ & HEAP8 & _).
      unfold MallocRep.wz. apply implA_from_evt.
      br_lit.
      do 4 step.
      apply evt_done.
      unfold bbind at 1. cbn [bind tree_ops].
      apply implA_assoc.
      eapply implA_bind.
      { eapply BN_add_walkA with (lo := lo) (OW := OW8) (LB := LB) (AD := AD) (EA := EA) (ras := [])
                 (rr := RB5) (x := RB5) (y := RB4) (R := ad_b5 AD) (X := ad_b5 AD) (Y := ad_b4 AD);
          [eapply cenv_preA; [exact ENV8 | exact LS8 | unfold BN_ADD_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia | unfold FUZZ_TOTAL, MC; lia]
          | apply FPV | rewrite unsigned_lit by lia; exact R_BN_add_1f3424 | reflexivity | exact eq_refl | exact eq_refl | exact eq_refl
          | reflexivity | reflexivity | reflexivity]. }
      cbv beta. intros [u9 ls9] Σ9 ms9 PO.
      apply (bn_postA_cpost LB AD EA lo SP FB FUZZ_TOTAL Σ ls OW) in PO; [| exact OK | exact HEAP8].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F9 & fc9 & m10 & OW9 & -> & CP9 & ->).
      assert (E9 : CENV (0 + MC + MC + BN_DIV_COST + BN_MUL_COST + MC) Σ9 ls9 m10 OW9 /\ lib_state ls9 m10 OW9 AD EA) by (eapply cenv_postA; [exact ENV8 | exact CP9]).
      destruct E9 as (ENV9 & LS9).
      cbn [fst snd] in *. fix_ret. clear CP9 T1 T2 T3 T4 T5 T6 HEAP8.
      (* [comment removed for export] *)
      rewrite !bbind_get.
      lazymatch goal with |- context [if (?e && (cmp_pure _ _ =? 0)) then _ else _] => change e with (fz_success ls6) end.
      set (c := cmp_pure (getbn RB5 ls9) (getbn RB1 ls9)).
      get_stat LS9 T1 T2 T3 T4 T5 T6.
      pose proof ENV9 as (_ & HEAP9 & _).
      unfold MallocRep.wz. apply implA_from_evt.
      br_lit.
      subst v. destruct (fz_success ls6); cbn [Z.b2z].
      2:{ (* [comment removed for export] *)
          br_lit. apply evt_done. cbv beta. cbn [andb].
          unfold bbind, bunr. cbn [bind unreachable tree_ops tbind]. apply implA_unr. }
      br_lit. do 2 step. step.
      eapply evt_cut.
      { eapply BN_cmp_evtA with (lo := lo) (OW := OW9) (LB := LB) (AD := AD) (EA := EA) (r1 := RB5) (r2 := RB1) (a := ad_b5 AD) (b := ad_b1 AD);
          [eapply cenv_preA; [exact ENV9 | exact LS9 | unfold BN_CMP_STACK; lia | unfold FUZZ_TOTAL, MC; lia]
          | reflexivity | exact eq_refl | exact eq_refl | reflexivity | reflexivity]. }
      intros ms' PO.
      apply (bn_postA_cpost LB AD EA lo SP FB FUZZ_TOTAL Σ ls OW) in PO; [| exact OK | exact HEAP9].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F10 & fc10 & m11 & OW10 & -> & CP10 & (-> & RC & _ & ->)).
      assert (E10 : CENV (0 + MC + MC + BN_DIV_COST + BN_MUL_COST + MC + 0) Σ9 ls9 m11 OW9 /\ lib_state ls9 m11 OW9 AD EA)
        by (eapply cenv_postA; [exact ENV9 | exact CP10]).
      destruct E10 as (ENV10 & LS10).
      cbn [fst snd] in *. fix_ret. fold c in RC |- *. clear CP10 T1 T2 T3 T4 T5 T6.
      step. if_cases KC; zify_cond KC.
      - (* [comment removed for export] *)
        assert (C0 : c = 0).
        { change 18446744073709551615 with (Z.ones 64) in KC. rewrite Z.land_ones in KC by lia. change (2 ^ 64) with 18446744073709551616 in KC.
          destruct (Z.eq_dec c 0) as [E|NE]; [exact E| exfalso].
          destruct (Z.lt_ge_cases c 0); [rewrite <- (Z.mod_add c 1) in KC by lia; rewrite Z.mod_small in KC by lia; lia | rewrite Z.mod_small in KC by lia; lia]. }
        apply evt_done. cbv beta. rewrite C0. cbn [andb Z.eqb].
        unfold bbind, bret. cbn [bind ret tree_ops tbind fst snd].
        eapply fuzz_doneA; [exact ENV10 | unfold FUZZ_TOTAL, MC; lia | exact LS10 | rewrite unsigned_lit by lia; lia].
      - (* [comment removed for export] *)
        apply evt_done. cbv beta.
        replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; intros E; apply KC; rewrite E; reflexivity).
        cbn [andb]. unfold bbind, bunr. cbn [bind unreachable tree_ops tbind]. apply implA_unr.
    Qed.
  End Env.

  (* [comment removed for export] *)
  Lemma fuzz_one_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo : Z) (D : Z) (d : list Z),
    bn_preA Σ ls m OW LB AD EA sp lo FUZZ_STACK_A FUZZ_TOTAL -> tp = wz TP_A ->
    payload_okA m LB D d -> D <= lo -> a0 = wz D -> a1 = wz (zlength d) ->
    implA (fuzz_one (tree_ops bptr) d ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA FUZZ_TOTAL
                (fun rc _ _ a0' => rc = 0 /\ a0' = wz 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz LX_FUZZ_ENTRY) fc None m (seg_rom bsegs)).
  Proof.
    intros until d. intros PRE -> PL DLO -> ->.
    pose proof PRE as (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED).
    pose proof PL as (PLB & PLF & PLD & PLN & PLK).
    unfold FUZZ_STACK_A, LX_FUZZ_ENTRY, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (OFF : offshW [(bv_unsigned sp - 96, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
    (* [comment removed for export] *)
    assert (PLHI : d = [] \/ (0 < D /\ D + zlength d <= ACEIL /\ acc bsegs m D (zlength d))).
    { destruct PLK as [E|(b & Hb & Hb1 & Hb2)]; [left; exact E| right].
      pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      split; [exact PLD|]. split; [lia|].
      exact (AH_acc_in _ _ _ _ b D (zlength d) HEAP ltac:(apply in_or_app; right; exact Hb) Hb1 Hb2). }
    apply hide_intro in PLB.
    apply implA_from_evt.
    step.
    carve_frame 96%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 12 step. do 4 step.
    apply hide_elim in PLB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -96, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -96, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
    assert (ENV : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -96) s0 ra None FUZZ_TOTAL Σ ls OW m
                    [CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
    { unfold cenvA, cenv_ok. split; [repeat split; try assumption; try (unfold USTACK_TOP; lia); clear - SP16; Z.div_mod_to_equations; lia|].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
      split; [exact ST|]. split; [exact MI|].
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))|].
      split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
      split; [cbn [app]; exact FR|]. split; [cbn; lia|]. exact I. }
    assert (LOS : lo <= bv_unsigned sp - FUZZ_STACK_A) by (unfold FUZZ_STACK_A; lia).
    step. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      assert (E0 : d = []).
      { rewrite land_m64_small in KE by (unfold zlength in *; lia). destruct d; [reflexivity| exfalso; unfold zlength in KE; cbn [length] in KE; lia]. }
      subst d.
      do 4 step.
      apply evt_done. rewrite fuzz_one_nil.
      eapply (fuzz_mainA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB AD EA lo LOS I D [] [] 0 0 m1);
        [exact ENV | exact LS1 | exact PLB | | constructor | constructor | exact PLD | lia | | | left; reflexivity | left; reflexivity | lia | lia
        | intros [NE|NE]; exfalso; apply NE; reflexivity].
      + replace (D + zlength []) with D by (unfold zlength; cbn [length]; lia). exact PLB.
      + unfold zlength; cbn [length]; lia.
      + unfold zlength; cbn [length]; lia.
    - (* [comment removed for export] *)
      destruct d as [|b0 d']. { exfalso. apply KE. reflexivity. }
      assert (Rb0 : 0 <= b0 < 256) by (inversion PLF; assumption).
      assert (ZL : zlength (b0 :: d') = zlength d' + 1) by (unfold zlength; cbn [length]; lia).
      assert (ZL0 : 0 <= zlength d') by (unfold zlength; lia).
      destruct PLHI as [PLHI|(_ & PLHI & ACCD)]; [discriminate PLHI|].
      ub. do 2 step.
      assert (PLB1 : bytes_at bsegs m1 D (to_bytes (b0 :: d'))).
      { eapply bytes_at_transport; [exact PLB | exact MU |]. cbn [disjoint_from]. unfold to_bytes. rewrite length_map. fold (zlength (b0 :: d')).
        split; [left; unfold BnHeapA.ACEIL in *; lia| exact I]. }
      assert (RD : ov_read_bytes bsegs m1 (Z_to_bv 64 D) 1 = Some [Z_to_bv 8 b0]).
      { pose proof (bytes_at_read bsegs m1 D (to_bytes (b0 :: d')) 0 1 PLB1 ltac:(lia) ltac:(unfold to_bytes; rewrite length_map; cbn [length]; lia)) as R0.
        rewrite Z.add_0_r in R0. exact R0. }
      (* [comment removed for export] *)
      eassert (CJ : _); [ |
        step; if_cases KC; zify_cond KC;
        [ step; setreg 11%Z (Z_to_bv 64 (Z.min (zlength (b0 :: d')) 256000)) ltac:(f_equal; rewrite ?unsigned_lit in KC by lia; lia); exact CJ
        | step; step; setreg 11%Z (Z_to_bv 64 (Z.min (zlength (b0 :: d')) 256000)) ltac:(f_equal; rewrite ?unsigned_lit in KC by lia; lia); exact CJ ] ].
      clear KE.
      assert (D47 : 0 <= D < 140737488355328) by (unfold BnHeapA.ACEIL in *; lia).
      step. shl1 sb OK.
      (* [comment removed for export] *)
      eassert (REST : _); [ |
        destruct (sh_ok_cases sb D OK) as [-> | (k & K1 & K2 & E1 & E2)];
        [ step; rewrite sxb_z8; if_false; do 3 step; exact REST
        | rewrite E1; step; if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia; [|exfalso; lia]; clear KS;
          step; rewrite ?(unsigned_lit D) by lia; rewrite (land7_mod8 D) by lia;
          step; if_cases KB; zify_cond KB;
          [ do 3 step; exact REST
          | exfalso; rewrite ?signed_small in KB by (pose proof (Z.mod_pos_bound D 8 ltac:(lia)); lia); lia ] ] ].
      clear OK sb.
      rewrite (zxb_small b0) by lia.
      set (len' := Z.min (zlength (b0 :: d')) 256000 - 1).
      replace (Z.min (zlength (b0 :: d')) 256000 + -1) with len' by (unfold len'; lia).
      assert (RL : 0 <= len' <= 255999) by (unfold len'; lia).
      set (x := Z.land b0 63 * len').
      assert (RB63 : 0 <= Z.land b0 63 <= 63) by (apply land63_range; lia).
      assert (RX : 0 <= x <= 16127937) by (unfold x; nia).
      do 6 zstep.
      replace (Z.land (Z.land b0 63 * len') 18446744073709551615) with x by (fold x; symmetry; apply land_m64_small; lia).
      do 2 zstep. rewrite (magic63_hi x RX).
      zstep. rewrite (magic63_q x RX).
      pose proof (div63_le (Z.land b0 63) len' RB63 ltac:(lia)) as RQ. fold x in RQ.
      assert (L1X : x / 63 <= x) by (apply Z.div_le_upper_bound; lia).
      set (l1 := x / 63) in *.
      zstep. fold x. rewrite (bk_swrap32_small (x - l1)) by lia.
      zstep.
      rewrite ?(land_m64_small (x - l1)) by lia.
      replace (bv_wrap 32 (x - l1)) with (x - l1) by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; rewrite Z.mod_small; [reflexivity | lia]).
      rewrite (bk_swrap32_small ((x - l1) ≫ 1))
        by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2; split; [apply (Z.le_trans _ 0); [lia| apply Z.div_pos; lia] | apply Z.div_lt_upper_bound; lia]).
      do 2 zstep.
      assert (RT : 0 <= (x - l1) ≫ 1 + l1 < 18446744073709551616)
        by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2; pose proof (Z.div_pos (x - l1) 2 ltac:(lia) ltac:(lia));
            pose proof (Z.div_lt_upper_bound (x - l1) 2 16127938 ltac:(lia) ltac:(lia)); lia).
      rewrite ?(land_m64_small _ RT). change l1 with (x / 63). rewrite (magic63_t x RX). fold l1.
      do 2 zstep. rewrite (bk_swrap32_small (len' - l1)) by lia.
      zstep.
      (* [comment removed for export] *)
      set (rest := firstn (MAX_LEN - 1) d').
      assert (Lrest : Z.of_nat (length rest) = len') by (unfold rest, len'; rewrite firstn_MAX1_len, ZL; reflexivity).
      set (l1n := Z.to_nat ((Z.land b0 63 * Z.of_nat (length rest)) / 63)).
      assert (El1 : Z.of_nat l1n = l1) by (unfold l1n; rewrite Lrest; fold x; fold l1; lia).
      assert (Hl1n : (l1n <= length rest)%nat) by lia.
      set (n1 := firstn l1n rest). set (n2 := skipn l1n rest).
      assert (ZN1 : zlength n1 = l1) by (unfold zlength, n1; rewrite firstn_length_le by exact Hl1n; exact El1).
      assert (ZN2 : zlength n2 = len' - l1) by (unfold zlength, n2; rewrite length_skipn; lia).
      pose proof (payload_split d' l1n Hl1n) as SPLIT. cbv zeta in SPLIT. fold rest in SPLIT. fold n1 n2 in SPLIT.
      assert (PLBs : bytes_at bsegs m (D + 1) (to_bytes n1) /\ bytes_at bsegs m (D + 1 + zlength n1) (to_bytes n2)).
      { change (b0 :: d') with ([b0] ++ d') in PLB. rewrite SPLIT in PLB. unfold to_bytes in PLB. rewrite !map_app in PLB.
        apply bytes_at_app in PLB. destruct PLB as [_ PLB]. cbn [length map] in PLB.
        apply bytes_at_app in PLB. destruct PLB as [P1 PLB]. apply bytes_at_app in PLB. destruct PLB as [P2 _].
        rewrite length_map in P2. split; [exact P1| exact P2]. }
      destruct PLBs as [P1 P2].
      assert (PLFs : Forall (fun c => 0 <= c < 256) n1 /\ Forall (fun c => 0 <= c < 256) n2).
      { inversion PLF as [|? ? _ PLF']. subst. rewrite SPLIT in PLF'. apply Forall_app in PLF'. destruct PLF' as [F1 PLF'].
        apply Forall_app in PLF'. destruct PLF' as [F2 _]. split; assumption. }
      destruct PLFs as [F1 F2].
      assert (ZD : len' <= zlength d') by (unfold len'; lia).
      assert (PLKs : exists b, In b LB /\ blk_addr b <= D /\ D + zlength (b0 :: d') <= blk_addr b + blk_size b)
        by (destruct PLK as [E|H]; [discriminate E| exact H]).
      destruct PLKs as (bb & Hbb & Hbb1 & Hbb2).
      assert (RV1 : 0 <= Z.land b0 64 < 2 ^ 64) by (pose proof (land_byte_range b0 64 Rb0 ltac:(lia)); lia).
      assert (RV2 : 0 <= Z.land b0 128 < 2 ^ 64) by (pose proof (land_byte_range b0 128 Rb0 ltac:(lia)); lia).
      apply evt_done. rewrite fuzz_one_cons. cbv zeta. fold rest. fold l1n. fold n1 n2.
      rewrite <- ZN2, <- ZN1.
      eapply (fuzz_mainA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB AD EA lo LOS I (D + 1) n1 n2 (Z.land b0 64) (Z.land b0 128) m1);
        [exact ENV | exact LS1 | exact P1 | exact P2 | exact F1 | exact F2 | lia | unfold BnHeapA.ACEIL in *; lia | lia | lia | | | exact RV1 | exact RV2
        | intros _; lia].
      + right. exists bb. split; [exact Hbb|]. lia.
      + right. exists bb. split; [exact Hbb|]. lia.
  Qed.
End Proofs.
End WithRT.
