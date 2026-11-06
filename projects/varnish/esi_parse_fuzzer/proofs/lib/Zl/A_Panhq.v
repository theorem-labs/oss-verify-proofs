(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_La0bg A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_crc32.

Module A_crvyv.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_CrcLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_La0bg A_Img A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_crc32.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_crc32.A_CrcKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac hot_qset := lazymatch goal with |- evt _ ?Q _ => lazymatch Q with (fun _ => _) => set (hotQ := Q) | _ => idtac end | |- _ => idtac end.
Ltac hot_qend := lazymatch goal with |- evt _ ?Q _ => first [ is_var Q; subst Q | idtac ] | |- ?Q _ => first [ is_var Q; subst Q; cbv beta | idtac ] | |- _ => idtac end.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.slim; lia ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_arith_prep; lia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Definition x2nmodp_entry := 0x91858%Z.
Definition crc32_combine64_entry := 0x917d4%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma x2n_tab_at : forall m, mem_inv rsegs m -> bytes_at rsegs m X2N_TAB_A x2n_bytes.
Proof. intros m MI. apply (ro_table_at rsegs m); [exact MI | vm_compute; reflexivity | unfold X2N_TAB_A; lia | rewrite x2n_bytes_length; unfold X2N_TAB_A; lia]. Qed.

Lemma rd_x2n_a : forall m (k : Z) a,
  bytes_at rsegs m X2N_TAB_A x2n_bytes ->
  a = wa (X2N_TAB_A + Z.shiftl (Z.land k 31) 2) ->
  ov_read_bytes rsegs m a 4 = Some (le4 (Z_to_bv 64 (tabz (Z.to_nat (Z.land k 31))))).
Proof.
  intros m k a Hb ->. pose proof (land31_range k) as R.
  rewrite Z.shiftl_mul_pow2 by lia. change (2^2)%Z with 4%Z.
  rewrite (bytes_at_read rsegs m X2N_TAB_A x2n_bytes (Z.land k 31 * 4) 4 Hb) by (try rewrite x2n_bytes_length; lia).
  f_equal. unfold x2n_bytes, tabz.
  replace (Z.to_nat (Z.land k 31 * 4)) with (4 * Z.to_nat (Z.land k 31))%nat by lia.
  apply flat4_chunk. cbn [length x2n_tab]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition X2N_FRAME := 16%Z.

Definition x2nmodp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (p : Z) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SX p)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ (0 < p < 2^32)%Z.

Section X2N.
  Context {Clg : Ceiling}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte) (lo : Z) (junk : list byte).
  Hypothesis MU1 : munch [(bv_unsigned sp + -16, bv_unsigned sp)]%Z m m1.
  Hypothesis WM1 : wmono rsegs m m1.
  Hypothesis MI1 : mem_inv rsegs m1.
  Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -16).
  Hypothesis LO : (lo + 16 <= bv_unsigned sp)%Z.
  Hypothesis LJ : length junk = 8%nat.
  Hypothesis FR1 : rw_cells rsegs m1 (bv_unsigned sp + -16) [CB 8 junk; C8 ra].
  Hypothesis X2N1 : bytes_at rsegs m1 0x25f60 x2n_bytes.
  Hypothesis SHX : bytes_at rsegs m1 (sh 0x25f60) (repeat (Z_to_bv 8 0) 16).

  (* [comment removed for export] *)
  Notation AT pc x6 x7 x10 x11 x12 x13 x5 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 (Z_to_bv 64 2147450880) (Z_to_bv 64 0x25f60)
            (Z_to_bv 64 18446744073709396127) (Z_to_bv 64 18446744073402876704) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

  Section AnyPost.
  Variable Q : machine_state -> Prop.

  (* [comment removed for export] *)
  #[using="LJ MI1 junk"] Lemma x2n_shift : forall (k : nat) (a b p : Z) x6 x10 x13,
    (0 < a < 2^32)%Z -> (0 <= b < 2^32)%Z -> (0 <= p < 2^32)%Z -> (1 <= k <= 31)%nat ->
    (forall x6', evt rsegs Q (AT 0x918d8 (Z_to_bv 64 (SX (2 ^ Z.of_nat (k - 1)))) x6' x10 (Z_to_bv 64 (SX p)) (Z_to_bv 64 (SX a)) x13 (Z_to_bv 64 (SX (cstep b))))) ->
    evt rsegs Q (AT 0x918f0 (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) x6 x10 (Z_to_bv 64 (SX p)) (Z_to_bv 64 (SX a)) x13 (Z_to_bv 64 (SX b))).
  Proof.
    intros k a b p x6 x10 x13 Ha Hb Hp Hk H.
    pose proof MI1 as MI.
    pose proof (SX_range a ltac:(lia)) as Ra. pose proof (SX_range b Hb) as Rb. pose proof (SX_range p Hp) as Rp.
    assert (Hm : (0 < 2 ^ Z.of_nat k <= 2^31)%Z). { split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]. }
    pose proof (SX_range (2 ^ Z.of_nat k) ltac:(lia)) as Rm.
    pose proof (cstep_range b Hb) as Rc. pose proof (SX_range _ Rc) as Rc'.
    do 7 zstep.
    rewrite (srliw1_SX b Hb). rewrite (srliw1_SX (2 ^ Z.of_nat k)) by lia.
    rewrite (signmask_SX b Hb). rewrite (shr1_mod64 b Hb). rewrite (bstep_SX b Hb).
    rewrite (pow2k_half k) by lia.
    rewrite <- (SX_small (2 ^ Z.of_nat (k - 1))) by (pose proof (pow2k_range (k-1)%nat ltac:(lia)); split; [lia|]; apply Z.pow_lt_mono_r; lia).
    apply H.
  Qed.

  (* [comment removed for export] *)
  #[using="LJ MI1 junk"] Lemma x2n_inner : forall (k : nat) (a b p : Z) x6 x10 x13,
    (0 < a < 2^32)%Z -> (0 <= b < 2^32)%Z -> (0 <= p < 2^32)%Z -> (k <= 31)%nat ->
    lowbits_nz a (Z.of_nat k) ->
    (forall x5' x6' x17',
       evt rsegs Q (AT 0x91898 x5' x6' x10 (Z_to_bv 64 (SX (mm_loop (S k) (2 ^ Z.of_nat k) a b p))) (Z_to_bv 64 (SX a)) x13 x17')) ->
    evt rsegs Q (AT 0x918d8 (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) x6 x10 (Z_to_bv 64 (SX p)) (Z_to_bv 64 (SX a)) x13 (Z_to_bv 64 (SX b))).
  Proof.
    induction k as [|k IH]; intros a b p x6 x10 x13 Ha Hb Hp Hk LB CONT.
    - (* [comment removed for export] *)
      pose proof MI1 as MI.
      destruct (lowbits_0 a ltac:(lia) LB) as [T0 L0].
      pose proof (SX_range a ltac:(lia)) as Ra. pose proof (SX_range b Hb) as Rb. pose proof (SX_range p Hp) as Rp.
      change (2 ^ Z.of_nat 0)%Z with 1%Z in *. change (SX 1) with 1%Z.
      zstep. zstep. if_cases K; zify_cond K.
      { exfalso. rewrite land_small_SX in K by lia. change 1%Z with (2^0)%Z in K. apply land_pow2_zero in K; [|lia]. rewrite T0 in K. discriminate. }
      do 4 zstep.
      change (bv_swrap 32 (1 + -1)) with 0%Z. rewrite Z.land_0_l.
      if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
      rewrite (lxor_SX p b) by lia.
      rewrite land_small_SX in K by lia.
      rewrite mm_loop_exit in CONT by (first [exact K | exact L0]).
      apply CONT.
    - pose proof MI1 as MI.
      pose proof (SX_range a ltac:(lia)) as Ra. pose proof (SX_range b Hb) as Rb. pose proof (SX_range p Hp) as Rp.
      pose proof (pow2k_range (S k) Hk) as Hm. pose proof (SX_range (2 ^ Z.of_nat (S k)) ltac:(lia)) as Rm.
      pose proof (lxor_bound 32 p b ltac:(lia) Hp Hb) as Rx. pose proof (SX_range _ Rx) as Rx'.
      zstep. zstep. if_cases K; zify_cond K.
      + (* [comment removed for export] *)
        rewrite land_SX in K by lia. apply (proj1 (SX_nz _ (land_bound_l 32 (2 ^ Z.of_nat (S k)) a ltac:(lia) ltac:(lia)))) in K.
        pose proof (land_pow2_zero a (Z.of_nat (S k)) ltac:(lia) K) as Tk.
        apply x2n_shift; try lia. intros x6'.
        rewrite mm_loop_skip in CONT by exact K. rewrite pow2k_half in CONT by lia.
        replace (S k - 1)%nat with k in * by lia.
        apply IH; try lia. 1:{ apply cstep_range; lia. } 2:{ exact CONT. }
        replace (Z.of_nat k) with (Z.of_nat (S k) - 1)%Z by lia. apply lowbits_step; try lia; try exact LB; try (left; exact Tk).
      + (* [comment removed for export] *)
        do 4 zstep.
        rewrite (addiw_m1_SX (2 ^ Z.of_nat (S k))) by lia.
        rewrite (Z.mod_small (2 ^ Z.of_nat (S k) - 1) 18446744073709551616) by lia.
        rewrite (land_small_SX (2 ^ Z.of_nat (S k) - 1) a) by lia.
        rewrite (lxor_SX p b) by lia.
        rewrite land_SX in K by lia.
        assert (K' : Z.land (2 ^ Z.of_nat (S k)) a <> 0%Z). { intros E. apply K. rewrite E. reflexivity. }
        if_cases K2; zify_cond K2.
        * (* [comment removed for export] *)
          rewrite mm_loop_exit in CONT by (first [exact K' | exact K2]). apply CONT.
        * apply x2n_shift; try lia. intros x6'.
          rewrite mm_loop_cont in CONT by (first [exact K' | exact K2]). rewrite pow2k_half in CONT by lia.
          replace (S k - 1)%nat with k in * by lia.
          apply IH; try lia. 1:{ apply cstep_range; lia. } 2:{ exact CONT. }
          replace (Z.of_nat k) with (Z.of_nat (S k) - 1)%Z by lia. apply lowbits_step; try lia; try exact LB; try (right; exact K2).
  Qed.

  End AnyPost.

  Notation POST := (x2nmodp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  (* [comment removed for export] *)
  #[using="FR1 LJ LO ST1 MI1 WM1 MU1 junk"] Lemma x2n_exit : forall (p : Z) x5 x6 x10 x12 x13 x17,
    (0 < p < 2^32)%Z ->
    evt rsegs POST (AT 0x91924 x5 x6 x10 (Z_to_bv 64 (SX p)) x12 x13 x17).
  Proof.
    intros p x5 x6 x10 x12 x13 x17 Hp. unfold x2nmodp_post.
    pose proof MU1 as MU. pose proof WM1 as WM. pose proof FR1 as FR. pose proof ST1 as STK. pose proof MI1 as MI.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp + -16)%Z by lia.
    hot_qset.
    do 3 zstep.
    release_frame FR STK (bv_unsigned sp).
    zstep.
    all: hot_qend. finish; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="SHX X2N1 FR1 LJ LO ST1 MI1 WM1 MU1 junk"] Lemma x2n_outer : forall (N : nat) (n k p : Z) x5 x6 x11 x12,
    (Z.to_nat n < N)%nat -> (0 < n < 2^63)%Z -> (0 <= k)%Z -> (k + Z.of_nat N <= 2^63 + 8)%Z -> (0 < p < 2^32)%Z ->
    evt rsegs POST (AT 0x9188c x5 x6 (Z_to_bv 64 n) x11 x12 (Z_to_bv 64 k) (Z_to_bv 64 (SX p))).
  Proof.
    induction N as [N IH] using lt_wf_ind; intros n k p x5 x6 x11 x12 HN Hn Hk HkN Hp.
    pose proof MI1 as MI. pose proof (SX_range p ltac:(lia)) as Rp.
    (* [comment removed for export] *)
    assert (CONT : forall (p' : Z) x5' x6' x12' x17', (0 < p' < 2^32)%Z ->
      evt rsegs POST (AT 0x91898 x5' x6' (Z_to_bv 64 n) (Z_to_bv 64 (SX p')) x12' (Z_to_bv 64 k) x17')).
    { intros p' x5' x6' x12' x17' Hp'. pose proof (SX_range p' ltac:(lia)) as Rp'.
      zstep. rewrite (signed_small n) by lia.
      assert (Hs : (0 <= Z.shiftr n 1 < n)%Z) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1)%Z with 2%Z; Z.div_mod_to_equations; lia).
      try rewrite (Z.mod_small (Z.shiftr n 1) 18446744073709551616) by lia.
      do 3 zstep.
      if_cases K; zify_cond K.
      all: lazymatch type of K with
           | _ = _ => (* [comment removed for export] *) zstep; apply x2n_exit; lia
           | _ => (* [comment removed for export] *) apply (IH (S (Z.to_nat (Z.shiftr n 1)))); lia
           end. }
    zstep. zstep. if_cases K0; zify_cond K0.
    all: lazymatch type of K0 with
         | _ = _ => (* [comment removed for export] *) zstep; apply CONT; lia
         | _ => idtac
         end.
    (* [comment removed for export] *)
    pose proof (rd_x2n_a m1 k _ X2N1 eq_refl) as RD. cbv delta [X2N_TAB_A] in RD.
    pose proof (land31_range k) as Hi.
    set (i := Z.to_nat (Z.land k 31)) in RD.
    assert (Hi32 : (i < 32)%nat) by lia.
    pose proof (tabz_range i Hi32) as Ht.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. rewrite ?Z.shiftl_mul_pow2 by lia. clear - Hi. intros KU. first [rewrite Z.mod_small in KU by lia | idtac]. lia. } clear KU.
    zstep. tidx. rewrite (Z.shiftl_mul_pow2 _ 2) in RD by lia. change (2 ^ 2)%Z with 4%Z in RD.
    tchk SHX 4%Z.
    (* [comment removed for export] *)
    zstep. zstep.
    rewrite (sx32_SX (Z_to_bv 64 (tabz i)) (tabz i) (tabz_word i Hi32) ltac:(lia)).
    zstep.
    replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2 ^ Z.of_nat 31))) by (apply bv_eq; reflexivity).
    change (Z_to_bv 64 0) with (Z_to_bv 64 (SX 0)).
    (* [comment removed for export] *)
    apply (x2n_inner _ 31 (tabz i) p 0); [lia|lia|lia|lia| apply lowbits_nz_init; lia |].
    intros x5' x6' x17'. apply CONT.
    exact (mm_tab_pos i p Hi32 ltac:(lia)).
  Qed.
End X2N.

Section Specs.
  Context {Clg : Ceiling}.

  Lemma x2nmodp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> (lo + 16 <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
    cenv m ->
    (bv_unsigned a0 < 2^63)%Z ->
    evt rsegs (x2nmodp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x91858) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros MI ST LO CEIL CE Hn. unfold x2nmodp_post.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range _ a0) as Ra0. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof alloc_ceiling_num as ACV. assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    pose proof (map_cells_of_consts m (proj1 CE)) as MC. open_map_cells MC. clear Gmb Cmb Gme Cme Ghe Che.
    pose proof (x2n_tab_at m MI) as X2N. cbv delta [X2N_TAB_A] in X2N.
    pose proof (x2n_tab_shadow m CE) as SHX.
    assert (EX : sh 155488 = 2147470316%Z) by reflexivity.
    assert (LX : Z.of_nat (length x2n_bytes) = 128%Z) by reflexivity.
    assert (LS : Z.of_nat (length (repeat (Z_to_bv 8 0) 16)) = 16%Z) by reflexivity.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hot_qset.
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep.
      replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp + -16)%Z in MU by lia.
      do 3 zstep.
      lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp + -16) _, STq : stk _ ?mq lo _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        release_frame FRq STq (bv_unsigned sp) end.
      zstep. replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2^31))) by (apply bv_eq; reflexivity). finish; lia.
    - (* [comment removed for export] *)
      do 10 zstep.
      all: hot_qend.
      replace (Z_to_bv 64 (Z.lxor 155488 (-1))) with (Z_to_bv 64 18446744073709396127) by (apply bv_eq; reflexivity).
      rewrite <- (Z_to_bv_bv_unsigned a0).
      replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2^31))) by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 (-306674912)) with (Z_to_bv 64 18446744073402876704) by (apply bv_eq; reflexivity).
      lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp + -16) (CB 8 ?jk :: _), STq : stk _ ?mq lo _, MUq : munch _ m ?mq, WMq : wmono _ m ?mq, MIq : mem_inv _ ?mq,
                          Xq : bytes_at _ ?mq 155488 _, Sq : bytes_at _ ?mq (sh 155488) _ |- _ =>
        apply (x2n_outer ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mq lo jk
                 MUq WMq MIq STq LO (proj1 (proj1 (proj1 FRq))) FRq Xq Sq
                 (S (Z.to_nat (bv_unsigned a0))) (bv_unsigned a0) 3 (2^31)); lia
      end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition C64_FRAME := 32%Z.

  Section C64Loop.
    Variables (sp gp tp t0 t1 t2 s0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
              (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (a : Z).
    Variable Q : machine_state -> Prop.
    Hypothesis Ha : (0 < a < 2^32)%Z.
    Hypothesis MI1 : mem_inv rsegs m1.

    Notation AT2 pc x9 x11 x12 x14 x15 :=
      (MS (mkR (Z_to_bv 64 0x917f4) sp gp tp t0 t1 t2 s0 x9 (Z_to_bv 64 (SX a)) x11 x12 (Z_to_bv 64 (-306674912)) x14 x15 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

    #[using="MI1 Ha"] Lemma c64_loop : forall (k : nat) (x9 x11 x14 x15 : word),
      (k <= 31)%nat -> lowbits_nz a (Z.of_nat k) ->
      (forall x9' x11' x12' x14' x15', evt rsegs Q (AT2 0x91838 x9' x11' x12' x14' x15')) ->
      evt rsegs Q (AT2 0x91804 x9 x11 (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) x14 x15).
    Proof.
      induction k as [|k IH]; intros x9 x11 x14 x15 Hk LB CONT.
      - pose proof MI1 as MI.
        destruct (lowbits_0 a ltac:(lia) LB) as [T0 L0].
        pose proof (SX_range a ltac:(lia)) as Ra.
        change (2 ^ Z.of_nat 0)%Z with 1%Z in *. change (SX 1) with 1%Z.
        zstep. zstep. if_cases K; zify_cond K.
        { exfalso. rewrite land_small_SX in K by lia. change 1%Z with (2^0)%Z in K. apply land_pow2_zero in K; [|lia]. rewrite T0 in K. discriminate. }
        do 4 zstep.
        change (bv_swrap 32 (1 + -1)) with 0%Z. rewrite Z.land_0_l.
        if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
        apply CONT.
      - pose proof MI1 as MI.
        pose proof (SX_range a ltac:(lia)) as Ra.
        pose proof (pow2k_range (S k) Hk) as Hm. pose proof (SX_range (2 ^ Z.of_nat (S k)) ltac:(lia)) as Rm.
        assert (SHIFT : forall x9' x11' x14' x15',
          lowbits_nz a (Z.of_nat k) ->
          evt rsegs Q (AT2 0x9181c x9' x11' (Z_to_bv 64 (SX (2 ^ Z.of_nat (S k)))) x14' x15')).
        { intros x9' x11' x14' x15' LB'. do 7 zstep.
          rewrite (srliw1_SX (2 ^ Z.of_nat (S k))) by lia. rewrite pow2k_half by lia.
          replace (S k - 1)%nat with k by lia.
          rewrite <- (SX_small (2 ^ Z.of_nat k)) by (pose proof (pow2k_range k ltac:(lia)); split; [lia|]; apply Z.pow_lt_mono_r; lia).
          apply IH; [lia | exact LB' | exact CONT]. }
        zstep. zstep. if_cases K; zify_cond K.
        + rewrite land_SX in K by lia. apply (proj1 (SX_nz _ (land_bound_l 32 (2 ^ Z.of_nat (S k)) a ltac:(lia) ltac:(lia)))) in K.
          pose proof (land_pow2_zero a (Z.of_nat (S k)) ltac:(lia) K) as Tk.
          apply SHIFT. replace (Z.of_nat k) with (Z.of_nat (S k) - 1)%Z by lia. apply lowbits_step; try lia; try exact LB; try (left; exact Tk).
        + do 4 zstep.
          rewrite (addiw_m1_SX (2 ^ Z.of_nat (S k))) by lia.
          rewrite (Z.mod_small (2 ^ Z.of_nat (S k) - 1) 18446744073709551616) by lia.
          rewrite (land_small_SX (2 ^ Z.of_nat (S k) - 1) a) by lia.
          if_cases K2; zify_cond K2.
          * apply CONT.
          * apply SHIFT. replace (Z.of_nat k) with (Z.of_nat (S k) - 1)%Z by lia. apply lowbits_step; try lia; try exact LB; try (right; exact K2).
    Qed.
  End C64Loop.

  Lemma crc32_combine64_ok : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
    cenv m ->
    (bv_unsigned a2 < 2^63)%Z ->
    evt rsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc None 48 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x917d4) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros MI ST LO CEIL CE LEN. unfold leaf_post.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_num as ACV.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    carve_frame 32%nat ST.
    hot_qset.
    do 8 zstep.
    (* [comment removed for export] *)
    lazymatch goal with MUq : munch _ m ?mq |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      assert (CEq : cenv mq)
        by (eapply cenv_munch; [exact CE| exact MUq| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; clear - LO CEIL ACV; lia])
    end.
    (* [comment removed for export] *)
    icall x2nmodp_spec by (rewrite ?unsigned_lit by lia; first [eassumption | lia]).
    lazymatch goal with PC : (0 < ?p)%Z |- _ => rename p into pa end.
    pose proof (SX_range pa ltac:(lia)) as Rpa.
    do 4 zstep.
    replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2 ^ Z.of_nat 31))) by (apply bv_eq; reflexivity).
    eapply c64_loop; [lia | assumption | lia | apply lowbits_nz_init; lia |].
    intros x9' x11' x12' x14' x15'.
    do 7 zstep.
    lazymatch goal with FR : rw_cells _ ?mq (bv_unsigned sp + -32) _, STK : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      release_frame FR STK (bv_unsigned sp) end.
    zstep.
    all: hot_qend. finish.
  Qed.

  (* [comment removed for export] *)
  Theorem crc32_combine_ok : crc32_combine_stmt2.
  Proof.
    intros lo. intros until v. intros CE ST LO CEIL MI LEN. unfold C64_STACK in *. unfold crc32_combine_entry.
    pose proof (munch_refl [] v) as MU. pose proof (wmono_refl rsegs v) as WM.
    zstep. apply crc32_combine64_ok; try assumption; lia.
  Qed.
End Specs.
End A_crvyv.


Module A_vejvm.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac dead_b2z :=
  repeat match goal with |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor_2_63 x) by lia end;
  repeat match goal with
  | |- context [?x =? ?y] => first [ rewrite (proj2 (Z.eqb_neq x y)) by lia | rewrite (proj2 (Z.eqb_eq x y)) by lia | destruct (Z.eqb_spec x y) ]
  | |- context [?x <? ?y] => first [ rewrite (proj2 (Z.ltb_ge x y)) by lia | rewrite (proj2 (Z.ltb_lt x y)) by lia | destruct (Z.ltb_spec x y) ]
  end;
  cbn; first [ congruence | lia | discriminate ].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  #[using="AI"] Lemma vep_default_cb_ok : vep_default_cb_stmt.
  Proof.
    unfold vep_default_cb_stmt.
    intros VEP vv tag q H l lo. intros until v. intros A0 A1 A2 VEPC TAG PADS HOBJ HSH HG CE SHD VLO V8 VHI VFR B0 B1 B2 ST LO CEIL MI.
    rewrite A0, A1, A2. unfold vep_default_cb_entry, CB_STACK in *.
    pose proof alloc_ceiling_num as ACV.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3, VLO, VFR. all_app_facts.
    pose proof (hff_al8 H 2608 HG eq_refl) as ALc.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (first [ pose proof (HSH) as dR_2; dand10 dR_2 as _ _ _ _ SHc _ _ _ _ _ | pose proof HSH as (_ & _ & _ & _ & SHc & _ & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vc in SHc.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(lia) ltac:(lia) ltac:(lia)) as SHcR. rewrite SHMAX_val in SHcR.
    (first [ dand8 SHD as PV NV SHP PAL P0 PLE PGE PCE | destruct SHD as (PV & NV & SHP & PAL & P0 & PLE & PGE & PCE) ]). fold_cl_segs.
    pose proof (shpat_sh_boundL (Clg:=Clg) PV NV ltac:(lia) ltac:(lia) ltac:(lia)) as SHPR. rewrite SHMAX_val in SHPR.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    pose proof HOBJ as (VC & _). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold h_vc, h_resp, h_wrk in VC.
    pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size vv tag q TAG PADS) in VEPB; change (Z.of_nat 312) with 312 in VEPB.
    (first [ pose proof (PADS) as dR_5; dand7 dR_5 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC. unfold h_vc.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (VEP + 56, VEP + 64)] v) as MU.
    pose proof (wmono_refl rsegs v) as WM.
    open_map_cells MC.
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; [lia| exact ALc]. } clear KU.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk SHc 4 14.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. kdead.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; [lia|]. rewrite Z.add_mod, V8 by lia. reflexivity. } clear KU.
    (* [comment removed for export] *)
    shadow_chk0 SHP 8. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. dead_b2z. } clear KU.
    (* [comment removed for export] *)
    shadow_rechk0 SHP (VEP + 56) 8. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold vep_default_cb_post, CB_STACK.
    do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    unfold vep_cells. cbn [fupd vf_beq vf_index N.eqb Pos.eqb]. exact VEPC.
  Qed.
End S.
End A_vejvm.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vezat A_ve9e8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_veqih.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vemo8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_WS7e8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_VSa8f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_VStbd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_VShb8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_VSe3i A_VShb8 A_vei6d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vexn5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vexn5 A_ve4jd.

Module A_veoi5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4 RA_vrdi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pnyh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pf3s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pis0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_p0nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcpnnp AIcptdg AIcp2kv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpoo5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpoo5 AIcpzt2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp2kv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpoo5.AIcp1os OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpoo5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpzt2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.AIcp8zl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_La0bg A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vei6d A_vez59 A_VSe3i A_VSa8f A_VStbd A_VEr47 A_VSbb4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve5c7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve5c7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve5c7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve5c7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve5c7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve5c7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve5c7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_veqih.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve5c7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve5c7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve2so.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve2so.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve2so.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve2so.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve2so.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ve2so.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSbb4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSqtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS160 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSe90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSq5u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSt8w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS8zm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_veqih OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_veq11 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve2so.A_vemjo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve2so.A_ve6k0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve2so.A_vep3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve2so.A_ve8qw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve2so.A_ver79 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve2so.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import B_Co6gg B_vehfs.   (* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strchr_icpt_post, vep_error_post, DATA_STACK, LEN_STACK, ASSERT_STACK, STRCHR_ICPT_STACK, VEPERR_STACK, h_vsc in H.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac simpl_sizes ::=
  rewrite ?app_length;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length];
  try (rewrite vep_cells_size by assumption); try (rewrite vsb_cells_size).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@CNT]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].




(* [comment removed for export] *)
Lemma stack_shadow_sp_hi {Clg : Ceiling} : forall v SB N lo hi, stack_shadow LPA v SB N lo hi -> hi <= 2^47.
Proof.
  (intros v SB N lo hi; (first [ intro dR_26; dand6 dR_26 as _ _ _ SH _ NK | intros (_ & _ & _ & SH & _ & NK) ])). unfold sh, kShadowOffset, kHighMemBeg in *.
  Z.div_mod_to_equations. lia.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (vi : option vsb_rec) (H : henv) (lo SB N : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis VBASE : vep_base H VEP vv.
  Hypothesis HENV : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis HFL : 0 <= vv Fflags < 16.
  Hypothesis HET : bool01 (vv Femptytag).
  Hypothesis HIC : bool01 (vv Finclude_continue).
  Hypothesis HLM : vv Flast_mark = 1.
  Hypothesis HAZ : vv Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis SZB : vb_size vr <= vb_len vr + 4096.
  Hypothesis LENB : vb_len vr + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  Hypothesis LBM : a_livebytes A0 + vb_size vr + vb_len vr + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : match vi with Some yi => vb_len yi / 4096 | None => 0 end + 8 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM + (PPOT_CAP - vsb_ppot vr) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis LF : lib_frames A0.
  Hypothesis HVI : match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A0 (aview A0 m0) (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fvsb /\ vv Finclude_src <> vb_buf vr /\
                   vb_buf yi <> vv Fvsb /\ vb_buf yi <> vb_buf vr
      end.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis WMAP00 : mapped (aview A0 m0) (bv_unsigned sp - DOINCL_STACK) DOINCL_STACK.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - DOINCL_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
      vep_obj LPA A' v' VEP vv' tag q -> vkeep vv vv' [Fstate; Finclude_src; Finclude_continue] ->
      (vv' Fstate = vv Fstate \/ vv' Fstate = vi_st VIA S_TagError) -> bool01 (vv' Finclude_continue) -> vv' Finclude_src = 0 ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      match vi with
      | None => (forall r, a_live A' r = a_live A0 r) /\ a_livebytes A' = a_livebytes A0 /\ a_nlive A' = a_nlive A0
      | Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                   (forall r, r <> vb_buf vr -> r <> vb_buf vr' -> r <> vv Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A0 r) /\
                   a_livebytes A' = a_livebytes A0 + (vb_size vr' - vb_size vr) - 40 - vb_size yi /\ a_nlive A' = a_nlive A0 - 2
      end ->
      frames_aged A0 A' 1 1 -> a_tinycred A' = a_tinycred A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) DOINCL_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40)
                       \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                       \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj VOBJ (conj VBASE (conj HENV (conj HFL (conj HET (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB
      (conj SZB (conj LENB (conj LBM (conj NLV (conj SCM (conj PRM (conj LF (conj HVI (conj TP (conj SP16 (conj WMAP00 (conj CEIL (conj LO (conj SPHI
      (conj STKSH K))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Let TINV := tinv VEP vv tag q vr vi H lo SB N sp m0 md0 A0.
  Let FRAME' := FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Local Ltac pose_parts :=
    pose proof (CFP VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as CFP';
    pose proof (W_cover VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as W_cover';
    pose proof (seg_main3 VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_main3'.

  Local Ltac unpack_tinv TI :=
    (first [ dand26 TI as EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & VEPC & SOBJk & NEBk & LENk & SZk & RELk & LIVEk & LBk & TCk & NLk & SCk & PCk & FSk & STKSHk
                    & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Let SCR5' := SCR5 VEP.
  (* [comment removed for export] *)
  Let W : list (Z * Z) := [(bv_unsigned sp - DOINCL_STACK, bv_unsigned sp); (h_ff H + 1336, h_ff H + 1352); (VEP, VEP + 312)].

  (* [comment removed for export] *)
  Local Ltac henv_here mx MU WM CNT HENVx DJ GCE GHI SHF VEPlo :=
    try unhide DJ;
    lazymatch goal with HGx : henv_geom LPA H |- _ =>
    let ACV := fresh "ACV" in pose proof alloc_ceiling_num as ACV;
    let HFRM := fresh "HFRM" in let GLOB := fresh "GLOB" in let HOBJ := fresh "HOBJ" in let HSH := fresh "HSH" in
    let BSSV := fresh "BSSV" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT'" in
    pose proof HENV as (HFRM & GLOB & HOBJ & HSH);
    (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as BSSV BSS CP _ | pose proof GLOB as (BSSV & BSS & CP & _) ]); fold_cl_segs; cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS; unfold h_vsc, h_cp in BSSV, BSS, CP;
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in BSS; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in CP; [| exact MU| exact WM| cbn; keeplia DJ GHI GCE VEPlo ACV CEIL LO];
    destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
    assert (HENVx : henv_ok LPA VIA H A0 mx);
    [ split; [exact HFRM|]; split;
      [ eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp;
        [exact BSSV| exact BSS| exact CP| replace (h_ff H + 32 + 1304) with (h_ff H + 1336) by lia; exact C]
      | split; [ eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|];
                 intros a__ Ha__; unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_vsc in *; cbn [outside]; keeplia Ha__ DJ GHI GCE ACV CEIL LO
               | eapply (hshadow_munch LPA); [exact HSH| exact MU| exact HGx|];
                 intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ SHF GCE VEPlo ACV CEIL LO ] ]
    | clear BSSV BSS CP C c HFRM GLOB HOBJ HSH ACV ]
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB vr"] Lemma seg_nosrc : forall (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs0 xs1 xs2 xs3 xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (m1 : mem) (j40 cnt : list byte),
    vi = None ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -160) ->
    rw_cells rsegs m1 (bv_unsigned sp + -160) (FRAME' [CB 56 j40]) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp xt0 xt1 xt2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7
                 xs2 xs3 (Z_to_bv 64 VEP) xs5 xs6 xs7 xs8 (Z_to_bv 64 2147450880) xs10 xs11 xt3 xt4 xt5 xt6)   (* [comment removed for export] *)
            F (Z_to_bv 64 0x8eb44) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM. pose_parts.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as ISRC0. rewrite EVI in ISRC0.
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_3; dand7 dR_3 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ)) as dR_4; dand11 dR_4 as S16 Slo Shi _ B16 Blo Bhi _ DSB _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ) as (S16 & Slo & Shi & _ & B16 & Blo & Bhi & _ & DSB & _ & _) ]).
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS. pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB.
    unfold kHighMemBeg in VEPlo, Slo, Blo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 S 40 AINV00 VLV LS NES) as DVS.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 (vb_buf vr) (vb_size vr) AINV00 VLV LB NEB) as DVB.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LB) as DJfB.
    change (fsize HCLASS) with 8192 in DJfV, DJfS, DJfB.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    (* [comment removed for export] *)
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0. remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    (* [comment removed for export] *)
    pose proof (got_vsc_cell m1 (proj1 CE1)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    pose proof HENV as (_ & GLOB & HOBJ & HSH).
    (first [ pose proof (HSH) as dR_5; dand10 dR_5 as SHvs _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHvs & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHvs, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHwR. rewrite SHMAX_val in SHwR.
    eapply (bytes_at_munch LPA) in SHvs; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHVR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHc; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHcR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHw; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHwR GCE VEPlo LO CEIL ACV].
    (first [ pose proof ((shadowed_bss_vsc _ (proj1 CE1))) as dR_6; dand8 dR_6 as PG NG SHG GAL G0 GLE GGE GCE' | destruct (shadowed_bss_vsc _ (proj1 CE1)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE') ]). fold_cl_segs.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (first [ pose proof (GLOB) as dR_7; dand4 dR_7 as BSSV _ _ _ | pose proof GLOB as (BSSV & _ & _ & _) ]). fold_cl_segs. cbn [vi_bss_vsc VIA] in BSSV. unfold h_vsc in BSSV.
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO].
    (first [ pose proof (HOBJ) as dR_8; dand3 dR_8 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    eapply (rw_cells_munch LPA) in VC; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    eapply (rw_cells_munch LPA) in WK; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    hide DVS. hide DVB. hide DJfS. hide DJfB. hide DSB. hide_neqs.
    cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    fold_cl_segs.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    do 13 zstep. zstep.
    try replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -160) _, STq : stk _ ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      release_frame FRq STq (bv_unsigned sp); rename STq into STw end.
    try clear GOTV. try clear SHvs. try clear SHc. try clear SHw. try clear SHG. try clear BSSV. try clear VC. try clear WK.
    henv_here m1 MU WM CNT HENVe DJfV GCE GHI SHF VEPlo.
    (first [ pose proof (HENVe) as dR_11; dand4 dR_11 as _ GLOBe0 HOBJe0 HSHe0 | pose proof HENVe as (_ & GLOBe0 & HOBJe0 & HSHe0) ]).
    assert (SHDq : shadowed LPA m1 VEP 312)
      by (exists VEP, 312; split; [pose proof SHV as T__; rewrite EzsV in T__; exact T__|]; split; [exact V8| keeplia VEPlo VEPhi]).
    icall (vep_error_ok VEP vv tag q H lo) by
      (idtac;   (* [comment removed for export] *)
       lazymatch goal with
       | |- @eq (bv _) _ _ => reflexivity
       | |- rw_cells _ _ VEP _ => exact VEPC
       | |- length _ = _ => exact TAG8
       | |- vep_pads_wf _ => exact PADS
       | |- vv Fvc = _ => exact EVC
       | |- glob_ok _ _ _ _ => exact GLOBe0
       | |- hobj_ok _ _ _ _ => exact HOBJe0
       | |- hshadow _ _ _ => exact HSHe0
       | |- henv_geom LPA _ => exact HG
       | |- cenv _ => exact CE1
       | |- shadowed _ _ _ _ => exact SHDq
       | |- stk _ _ _ _ => exact STw
       | |- mem_inv _ _ => assumption
       | |- _ => unfold kHighMemBeg, HFSIZE, VEPERR_STACK; ufs; keeplia VEPlo VEPhi V8 DJfV LO CEIL ACV SPR
       end).
    clear HENVe GLOBe0 HOBJe0 HSHe0.
    (* [comment removed for export] *)
    lazymatch goal with X : glob_ok _ _ _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      (first [ pose proof (X) as dR_12; dand4 dR_12 as _ _ _ [cnt' CNT'] | pose proof X as (_ & _ & _ & [cnt' CNT']) ]); fold_cl_segs; cbn [vi_bss_vsc VIA] in CNT'; unfold h_vsc in CNT';
      replace (h_ff H + 32 + 1304) with (h_ff H + 1336) in CNT' by (clear; lia); clear X end.
    try match goal with X : hobj_ok _ _ _ _ |- _ => clear X end.
    (* [comment removed for export] *)
    astop AINV00 MU WM CFP'.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, VEPCq : rw_cells _ ?ma VEP _, CNTq : rw_cells _ ?ma (h_ff H + 1336) _, STq : stk _ ?ma lo _
      |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename VEPCq into VEPC1; rename STq into STv;
      henv_here ma MU WM CNTq HENVa DJfV GCE GHI SHF VEPlo;
      assert (SOBJa : vsb_obj LPA A0 ma S vr false)
        by (unhide DJfS; unhide DJfB; unhide DVS; unhide DVB;
            eapply vsb_obj_munch; [exact SOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ Shi Bhi DJfS DJfB DVS DVB ACV CEIL LO])
    end.
    unhide_neqs.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A0 _ _ vv vr);
      [ exact AINVa | assumption
      | apply amd_frame_sbm; [exact SBM| exact MH]
      | exact STv | exact HENVa
      | split; [exact VLV|]; split; [exact VEPC1| split; [exact TAG8| exact PADS]]
      | exact (vkeep_refl vv [Fstate; Finclude_src; Finclude_continue])
      | left; reflexivity
      | exact HIC
      | exact ISRC0
      | exact SOBJa
      | rewrite EVI; clear; cbn; lia
      | clear; lia
      | left; reflexivity
      | rewrite EVI; split; [intros r; reflexivity|]; split; reflexivity
      | apply frames_same_aged; intros ff; reflexivity
      | reflexivity
      | clear; lia
      | clear; lia (* [comment removed for export] *)
      | ].
    (* [comment removed for export] *)
    eapply (cframe_noalloc LPA); [exact MU| ufs; apply W_cover'| eapply (stk_mapped (L:=LPA)); [exact STv | exact CEIL | keeplia LO | clear; lia]
      | intros a__ X; right; left; exact X].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB vi vr"] Lemma seg_head2 : forall (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs0 xs1 xs2 xs3 xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (m1 : mem) (j40 cnt : list byte),
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -160) ->
    rw_cells rsegs m1 (bv_unsigned sp + -160) (FRAME' [CB 56 j40]) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp xt0 xt1 xt2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7
                 xs2 xs3 (Z_to_bv 64 VEP) xs5 xs6 xs7 xs8 (Z_to_bv 64 2147450880) xs10 xs11 xt3 xt4 xt5 xt6)   (* [comment removed for export] *)
            F (Z_to_bv 64 0x8eaa0) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros MI ST FR VEPC CNT MU WM. pose_parts.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_13; dand7 dR_13 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    unfold kHighMemBeg in VEPlo. all_app_facts.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0. remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    hide_neqs.
    pose proof VEPC as VEPCu. unfold vep_cells in VEPCu. rewrite HLM in VEPCu.
    cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. try rewrite (shr3_div8 (VEP + 280)). zstep.
    assert (EV : (exists yi, vi = Some yi) \/ vi = None) by (clear; destruct vi; [left; eexists; reflexivity | right; reflexivity]).
    destruct EV as [[yi EVI]|EVI].
    - (* [comment removed for export] *)
      pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand3 HVI' as INZ IOBJ _ | destruct HVI' as (INZ & IOBJ & _) ]).
      (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_15; dand4 dR_15 as _ SIlo SIhi _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (_ & SIlo & SIhi & _) ]). unfold kHighMemBeg in SIlo. all_app_facts.
      pose proof IOBJ as IO. vsb_open IO. clear VSBC VINV VLS VLB VNE. (first [ dex1 VBUF as bs; dand3 VBUF as U8 LBS NULi | dand4 VBUF as bs U8 LBS NULi | destruct VBUF as (bs & U8 & LBS & NULi) ]). pose proof (NULi eq_refl) as NUL. clear NULi.
      zstep. if_cases KT; zify_cond KT; [exfalso; apply INZ; clear - KT SIlo SIhi ACV; try pose proof alloc_ceiling_val as ACV__; mlia|]. clear KT.
      (* [comment removed for export] *)
      zstep. vchk SHV EzsV 8 0. zstep.
      zstep; if_cases KW; zify_cond KW.
      { clear VEPCu KW.
        lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -160) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, CNTq : rw_cells _ ?mx (h_ff H + 1336) _
          |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply (seg_main3' yi bs); [exact EVI | exact MIq | exact STq | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq | exact VEPC | exact CNTq
            | exact MU | exact WM | exact U8 | exact LBS | exact NUL] end. }
      (* [comment removed for export] *)
      zstep. vchk SHV EzsV 4 0. zstep. rewrite ?sx32_small by (clear; lia). zstep.
      zstep; if_cases KT; zify_cond KT; [exfalso; apply KT; reflexivity|]. clear KT KW VEPCu.
      lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -160) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, CNTq : rw_cells _ ?mx (h_ff H + 1336) _
        |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (seg_main3' yi bs); [exact EVI | exact MIq | exact STq | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq | exact VEPC | exact CNTq
          | exact MU | exact WM | exact U8 | exact LBS | exact NUL] end.
    - (* [comment removed for export] *)
      pose proof HVI as ISRC0. rewrite EVI in ISRC0. rewrite ISRC0.
      zstep. if_cases KT; zify_cond KT; [| exfalso; apply KT; reflexivity]. clear KT VEPCu.
      lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -160) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, CNTq : rw_cells _ ?mx (h_ff H + 1336) _
        |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply seg_nosrc; [exact EVI | exact MIq | exact STq | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq | exact VEPC | exact CNTq | exact MU | exact WM] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 W FRAME' S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB H vi vr q tag vv"] Lemma main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv rsegs (aview A0 m0) -> a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 1 ->
    stk rsegs (aview A0 m0) lo (bv_unsigned sp) ->
    srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 vep_do_include_entry) fc None m0 (seg_rom rsegs)) md0) T.
  Proof.
    touch_all. intros until t6. intros MI -> -> ST. unfold vep_do_include_entry. pose_parts.
    prelims.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    (* [comment removed for export] *)
    pose proof VOBJ as (VLV & VEPC & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_17; dand7 dR_17 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    change (fsize HCLASS) with 8192 in DJfV.
    unfold kHighMemBeg in VEPlo. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    (* [comment removed for export] *)
    pose proof HENV as (_ & GLOB & HOBJ & HSH). (first [ pose proof (GLOB) as dR_18; dand4 dR_18 as BSSV _ _ [cnt CNT] | pose proof GLOB as (BSSV & _ & _ & [cnt CNT]) ]). fold_cl_segs. unfold h_vsc in CNT.
    replace (h_ff H + 32 + 1304) with (h_ff H + 1336) in CNT by lia.
    cbn [vi_bss_vsc VIA] in BSSV. unfold h_vsc in BSSV.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    pose proof (map_cells_of_consts _ (proj1 CE0)) as MC. fold_aview. open_map_cells MC.
    pose proof (got_vsc_cell _ (proj1 CE0)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    (first [ pose proof (HSH) as dR_19; dand10 dR_19 as SHvs _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHvs & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHvs, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHwR. rewrite SHMAX_val in SHwR.
    (first [ pose proof ((shadowed_bss_vsc _ (proj1 CE0))) as dR_20; dand8 dR_20 as PG NG SHG GAL G0 GLE GGE GCE' | destruct (shadowed_bss_vsc _ (proj1 CE0)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE') ]). fold_cl_segs. fold_aview.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (first [ pose proof (HOBJ) as dR_21; dand3 dR_21 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. fold_aview. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    hide_neqs.
    pose proof (munch_refl W (aview A0 m0)) as MU. cbv delta [W] in MU. pose proof (wmono_refl rsegs (aview A0 m0)) as WM.
    pose proof VEPC as VEPCu. unfold vep_cells in VEPCu. rewrite EVC in VEPCu. unfold h_vc in VEPCu.
    ago AINV00. fold_cl_segs.
    carve_frame 160%nat ST.
    (* [comment removed for export] *)
    do 14 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT; [| exfalso; apply KT; reflexivity]. clear KT.
    (* [comment removed for export] *)
    zstep. if_cases KU; zify_cond KU. { exfalso. rewrite ?Z.mod_small in KU by (keeplia VEPlo VEPhi ACV). keeplia KU VEPlo. } clear KU.
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; [keeplia VEPlo| exact V8]. } clear KU.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 4 0.
    zstep. pose proof HET as ET; destruct ET as [ET|ET]; rewrite ET, ?sx32_small by (clear; lia).
    2:{ (* [comment removed for export] *)
      zstep; if_cases KT; zify_cond KT; [| exfalso; clear - KT; lia]. clear KT VEPCu.
      lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -160) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, CNTq : rw_cells _ ?mx (h_ff H + 1336) _,
                          VEq : rw_cells _ ?mx VEP (vep_cells vv tag q) |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply seg_head2; [exact MIq | exact STq | exact FRq | exact VEq | exact CNTq | exact MU | exact WM] end. }
    (* [comment removed for export] *)
    zstep; if_cases KT; zify_cond KT; [exfalso; apply KT; reflexivity|]. clear KT.
    zstep. zstep. zstep. zstep.
    try clear VEPCu. try clear GOTV. try clear SHvs. try clear SHc. try clear SHw. try clear SHG. try clear BSSV. try clear VC. try clear WK.
    lazymatch goal with CNTq : rw_cells _ ?mx (h_ff H + 1336) _, VEq : rw_cells _ ?mx VEP (vep_cells vv tag q), STq : stk _ ?mx lo _, SHq : bytes_at _ ?mx (sh VEP) zsV
                        |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (CE1w : cenv mx)
        by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]);
      henv_here mx MU WM CNTq HENVe DJfV GCE GHI SHF VEPlo;
      (first [ pose proof (HENVe) as dR_24; dand4 dR_24 as _ GLOBe0 HOBJe0 HSHe0 | pose proof HENVe as (_ & GLOBe0 & HOBJe0 & HSHe0) ]);
      assert (SHDq : shadowed LPA mx VEP 312)
        by (exists VEP, 312; split; [pose proof SHq as T__; rewrite EzsV in T__; exact T__|]; split; [exact V8| keeplia VEPlo VEPhi]);
      icall (vep_warn_ok VEP vv tag q H lo) by
        (rewrite ?unsigned_lit by (keeplia SPR LO CEIL ACV);
         lazymatch goal with
         | |- @eq (bv _) _ _ => reflexivity
         | |- rw_cells _ _ VEP _ => exact VEq
         | |- length _ = _ => exact TAG8
         | |- vep_pads_wf _ => exact PADS
         | |- vv Fvc = _ => exact EVC
         | |- glob_ok _ _ _ _ => exact GLOBe0
         | |- hobj_ok _ _ _ _ => exact HOBJe0
         | |- hshadow _ _ _ => exact HSHe0
         | |- henv_geom LPA _ => exact HG
         | |- cenv _ => exact CE1w
         | |- shadowed _ _ _ _ => exact SHDq
         | |- stk _ _ _ _ => exact STq
         | |- mem_inv _ _ => assumption
         | |- _ => unfold kHighMemBeg, HFSIZE, VEPERR_STACK; ufs; keeplia VEPlo VEPhi V8 DJfV LO CEIL ACV SPR
         end)
    end.
    try clear HENVe. try clear GLOBe0. try clear HOBJe0. try clear HSHe0. try clear CE1w. try clear SHDq.
    (* [comment removed for export] *)
    lazymatch goal with X : glob_ok _ _ _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      (first [ pose proof (X) as dR_25; dand4 dR_25 as _ _ _ [cnt' CNT'] | pose proof X as (_ & _ & _ & [cnt' CNT']) ]); fold_cl_segs; cbn [vi_bss_vsc VIA] in CNT'; unfold h_vsc in CNT';
      replace (h_ff H + 32 + 1304) with (h_ff H + 1336) in CNT' by (clear; lia); clear X end.
    try match goal with X : hobj_ok _ _ _ _ |- _ => clear X end.
    lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -160) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx,
                        VEq : rw_cells _ ?mx VEP (vep_cells vv tag q) |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      eapply seg_head2; [exact MIq | exact STq | exact FRq | exact VEq | exact CNT' | exact MU | exact WM] end.
  Qed.
End S.

(* [comment removed for export] *)
Section T.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  #[using="AI16"] Theorem vep_do_include_tag_ok : vep_do_include_tag_stmt.
  Proof.
    unfold vep_do_include_tag_stmt. intros until T. cbv zeta.
    intros AINV MI A0e A1e VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 ST CEIL LO STKSH K.
    eapply (main VEP vv tag q vr vi H lo SB N); try eassumption.
    - eapply (stk_mapped (L:=LPA)); [exact ST| exact CEIL| pose proof (zr_word sp) as SPR; unfold inr64 in SPR; lia| unfold_stacks; lia].
    - exact (stack_shadow_sp_hi _ _ _ _ _ STKSH).
  Qed.
End T.
End A_veoi5.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDefs A_Parse.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDswi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDswi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PHcfh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PHcfh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PHol7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDswi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PHcfh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PHcfh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PHmhz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDswi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PHhja.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_crc32 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Panhq.A_crvyv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Panhq.A_vejvm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve9e8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_veqih.A_VEliw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vemo8.A_VE0r6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_WS7e8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSa8f.A_VS6ke OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VShb8.A_VSbwu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VShb8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vexn5.A_vej1r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vexn5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve4jd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Panhq.A_veoi5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Parse OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDncj.A_PHuri OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDncj.A_PH_BOM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDswi.A_PHobr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDncj.A_PHvy4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDswi.A_PHdsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PHcfh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PH7ea OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDncj.A_PHypf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PHcfh.A_PHcrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PHf78 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PHyoj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDncj.A_PH9dv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDncj.A_PHarb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PHuqr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDncj.A_PHxtw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDncj.A_PHcyi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PHol7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDswi.A_PH81r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDncj.A_PH0ci OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PHcfh.A_PHklh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDncj.A_PHmgj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PHcfh.A_PHqye OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PHmhz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDswi.A_PHucc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PHhja.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)

Section X.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Definition emit_common_closed : vep_emit_common_stmt := vep_emit_common_ok crc32_ok.
  Definition mark_common_closed : vep_mark_common_stmt :=
    vep_mark_common_ok emit_common_closed crc32_ok crc32_combine_ok vep_default_cb_ok.
  Definition VEP_Finish_closed : VEP_Finish_stmt :=
    VEP_Finish_ok mark_common_closed emit_common_closed vep_default_cb_ok VSB_destroy_ok VSB_finish_ok VSB_len_ok.
  Definition VEP_Init_closed : VEP_Init_stmt := VEP_Init_ok WS_Alloc_ok VSB_new_auto_ok crc32_ok.

  Let MC := mark_common_closed.
  Let ER := vep_error_ok.

  (* [comment removed for export] *)
  Definition PA_handlers (st : vstate) : st <> S_MatchBuf -> handler_stmt st :=
    match st as s return (s <> S_MatchBuf -> handler_stmt s) with
    | S_Start => fun _ => PH_Start
    | S_BOM => fun _ => PH_BOM MC
    | S_TestXml => fun _ => PH_TestXml MC
    | S_NotXml => fun _ => PH_NotXml MC
    | S_NotMyTag => fun _ => PH_NotMyTag MC
    | S_NxtTag => fun _ => PH_NxtTag MC
    | S_StartTag => fun _ => PH_StartTag
    | S_Comment => fun _ => PH_Comment
    | S_CommentESI => fun _ => PH_CommentESI MC ER   (* [comment removed for export] *)
    | S_CDATA => fun _ => PH_CDATA
    | S_end_ESITag => fun _ => PH_end_ESITag
    | S_ESITag => fun _ => PH_ESITag MC
    | S_ESI_Include => fun _ => PH_ESI_Include ER
    | S_ESI_Remove => fun _ => PH_ESI_Remove
    | S_ESI_Comment => fun _ => PH_ESI_Comment ER
    | S_ESI_Bogon => fun _ => PH_ESI_Bogon ER
    | S_InTag => fun _ => PH_InTag MC ER vep_do_comment_ok vep_do_remove_ok vep_do_include_tag_ok
    | S_TagError => fun _ => PH_TagError MC VSB_destroy_ok
    | S_Attr => fun _ => PH_Attr
    | S_SkipAttribute => fun _ => PH_SkipAttribute ER
    | S_AttrGetValue => fun _ => PH_AttrGetValue VSB_new_auto_ok
    | S_AttrDelim => fun _ => PH_AttrDelim ER
    | S_AttrValue => fun _ => PH_AttrValue ER VSB_destroy_ok VSB_putc_ok VSB_finish_ok vep_do_include_attr_ok
    | S_Until => fun _ => PH_Until MC
    | S_Match => fun _ => PH_Match
    | S_MatchBuf => fun NE => False_ind _ (NE eq_refl)
    end.

  Definition VEP_Parse_closed : VEP_Parse_stmt := VEP_Parse_ok MC crc32_ok PA_handlers.
End X.
