(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_World A_La0bg A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_crc32.

Module A_crvyv.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_CrcLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_La0bg A_World A_Img A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_crc32.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_CrcKit.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Definition x2nmodp_entry := 0x91e9c%Z.
Definition crc32_combine64_entry := 0x91e18%Z.

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
  Variables (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte) (lo : Z) (junk : list byte).
  Hypothesis MU1 : munch [(bv_unsigned sp + -16, bv_unsigned sp)]%Z m m1.
  Hypothesis WM1 : wmono rsegs m m1.
  Hypothesis MI1 : mem_inv rsegs m1.
  Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -16).
  Hypothesis LO : (lo + 16 <= bv_unsigned sp)%Z.
  Hypothesis LJ : length junk = 8%nat.
  Hypothesis FR1 : rw_cells rsegs m1 (bv_unsigned sp + -16) [CB 8 junk; C8 ra].
  Hypothesis X2N1 : bytes_at rsegs m1 0x26100 x2n_bytes.
  Hypothesis SHX : bytes_at rsegs m1 (sh 0x26100) (repeat (Z_to_bv 8 0) 16).

  (* [comment removed for export] *)
  Notation AT pc x5 x6 x10 x11 x12 x13 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 t2 s0 s1 x10 x11 x12 x13 (Z_to_bv 64 2147450880) (Z_to_bv 64 0x26100)
            (Z_to_bv 64 18446744073402876704) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

  Section AnyPost.
  Variable Q : machine_state -> Prop.

  (* [comment removed for export] *)
  #[using="LJ MI1 junk"] Lemma x2n_shift : forall (k : nat) (a b p : Z) x6 x10 x13,
    (0 < a < 2^32)%Z -> (0 <= b < 2^32)%Z -> (0 <= p < 2^32)%Z -> (1 <= k <= 31)%nat ->
    (forall x6', evt rsegs Q (AT 0x91f14 (Z_to_bv 64 (SX (2 ^ Z.of_nat (k - 1)))) x6' x10 (Z_to_bv 64 (SX p)) (Z_to_bv 64 (SX a)) x13 (Z_to_bv 64 (SX (cstep b))))) ->
    evt rsegs Q (AT 0x91f2c (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) x6 x10 (Z_to_bv 64 (SX p)) (Z_to_bv 64 (SX a)) x13 (Z_to_bv 64 (SX b))).
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
       evt rsegs Q (AT 0x91ed8 x5' x6' x10 (Z_to_bv 64 (SX (mm_loop (S k) (2 ^ Z.of_nat k) a b p))) (Z_to_bv 64 (SX a)) x13 x17')) ->
    evt rsegs Q (AT 0x91f14 (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) x6 x10 (Z_to_bv 64 (SX p)) (Z_to_bv 64 (SX a)) x13 (Z_to_bv 64 (SX b))).
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
    evt rsegs POST (AT 0x91f60 x5 x6 x10 (Z_to_bv 64 (SX p)) x12 x13 x17).
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
    evt rsegs POST (AT 0x91ecc x5 x6 (Z_to_bv 64 n) x11 x12 (Z_to_bv 64 k) (Z_to_bv 64 (SX p))).
  Proof.
    induction N as [N IH] using lt_wf_ind; intros n k p x5 x6 x11 x12 HN Hn Hk HkN Hp.
    pose proof MI1 as MI. pose proof (SX_range p ltac:(lia)) as Rp.
    (* [comment removed for export] *)
    assert (CONT : forall (p' : Z) x5' x6' x12' x17', (0 < p' < 2^32)%Z ->
      evt rsegs POST (AT 0x91ed8 x5' x6' (Z_to_bv 64 n) (Z_to_bv 64 (SX p')) x12' (Z_to_bv 64 k) x17')).
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
    zstep. zstep. zstep. tidx. rewrite (Z.shiftl_mul_pow2 _ 2) in RD by lia. change (2 ^ 2)%Z with 4%Z in RD.
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
          F (Z_to_bv 64 0x91e9c) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros MI ST LO CEIL CE Hn. unfold x2nmodp_post.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range _ a0) as Ra0. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof alloc_ceiling_num as ACV. assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    pose proof (map_cells_of_consts m (proj1 CE)) as MC. open_map_cells MC. clear Gmb Cmb Gme Cme Ghe Che.
    pose proof (x2n_tab_at m MI) as X2N. cbv delta [X2N_TAB_A] in X2N.
    pose proof (x2n_tab_shadow m CE) as SHX.
    assert (EX : sh 155904 = 2147470368%Z) by reflexivity.
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
      do 9 zstep.
      all: hot_qend.
      rewrite <- (Z_to_bv_bv_unsigned a0).
      replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2^31))) by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 (-306674912)) with (Z_to_bv 64 18446744073402876704) by (apply bv_eq; reflexivity).
      lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp + -16) (CB 8 ?jk :: _), STq : stk _ ?mq lo _, MUq : munch _ m ?mq, WMq : wmono _ m ?mq, MIq : mem_inv _ ?mq,
                          Xq : bytes_at _ ?mq 155904 _, Sq : bytes_at _ ?mq (sh 155904) _ |- _ =>
        apply (x2n_outer ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mq lo jk
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
      (MS (mkR (Z_to_bv 64 0x91e38) sp gp tp t0 t1 t2 s0 x9 (Z_to_bv 64 (SX a)) x11 x12 (Z_to_bv 64 (-306674912)) x14 x15 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

    #[using="MI1 Ha"] Lemma c64_loop : forall (k : nat) (x9 x11 x14 x15 : word),
      (k <= 31)%nat -> lowbits_nz a (Z.of_nat k) ->
      (forall x9' x11' x12' x14' x15', evt rsegs Q (AT2 0x91e7c x9' x11' x12' x14' x15')) ->
      evt rsegs Q (AT2 0x91e48 x9 x11 (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) x14 x15).
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
          evt rsegs Q (AT2 0x91e60 x9' x11' (Z_to_bv 64 (SX (2 ^ Z.of_nat (S k)))) x14' x15')).
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
          F (Z_to_bv 64 0x91e18) fc None m (seg_rom rsegs)).
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_World A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

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
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (VEP + 56, VEP + 64)] v) as MU.
    pose proof (wmono_refl rsegs v) as WM.
    open_map_cells MC.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk SHc 4 15.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. kdead.
    (* [comment removed for export] *)
    shadow_chk0 SHP 8. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold vep_default_cb_post, CB_STACK.
    do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    unfold vep_cells. cbn [fupd vf_beq vf_index N.eqb Pos.eqb]. exact VEPC.
  Qed.
End S.
End A_vejvm.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vezat A_ve9e8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_veqih.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemo8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_WS7e8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_VSa8f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_VStbd A_VSbwu A_VSe3i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_VSbb4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vexn5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vexn5 A_ve4jd A_veoi5 A_PDefs A_Parse.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDswi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PHcfh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PHcfh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PHcrk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PHcrk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDswi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDswi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PHcfh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PHmhz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PHcfh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PHhja.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Panhq.A_crvyv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Panhq.A_vejvm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vezat OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ve9e8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih.A_VEliw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemo8.A_VE0r6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_WS7e8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSa8f.A_VS6ke OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSbwu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSbb4.A_VShb8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vexn5.A_vej1r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vexn5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ve4jd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Parse OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PHuri OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PH_BOM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDswi.A_PHobr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PHvy4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHcfh.A_PHdsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHcfh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PH7ea OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PHypf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHcrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PHf78 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PHyoj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PH9dv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHcrk.A_PHarb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PHuqr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PHxtw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PHcyi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDswi.A_PHol7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDswi.A_PH81r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PH0ci OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHcfh.A_PHklh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PHmgj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PHqye OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHmhz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHcfh.A_PHucc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHhja.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)

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
    | S_CommentESI => fun _ => PH_CommentESI MC
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
