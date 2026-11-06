(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep RzBridge MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec RelSpec LibWbxd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct Lazyiq4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require DA_Eg3i DA_Cells DA_Ldix DA_Se7o DA_W756.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Exec.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Se7o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_W756.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqG3qt TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqG3qt.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

Definition WRITEV_ECALL1 : Z := 0x9df44.
Definition WRITEV_ECALL2 : Z := 0x9dfcc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Walks.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z) (Fa : Z) (f : mfile) (g : word) (sa l : Z) (fd : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 112 <= bv_unsigned sp.
  Hypothesis FAR : 0xaa000 <= Fa /\ Fa + 152 <= 0x608418.   (* [comment removed for export] *)
  Hypothesis FDR : fd = 1 \/ fd = 2.
  Hypothesis EFD : mf_fd f = fd.
  #[local] Notation rom := (seg_rom rsegs).
  (* [comment removed for export] *)
  #[local] Notation WFRAME m1 j b0 l0 b1 l1 :=
    (rw_cells rsegs m1 (bv_unsigned sp + -112)
       [CB 8 j; C8 (Z_to_bv 64 b0); C8 (Z_to_bv 64 l0); C8 (Z_to_bv 64 b1); C8 (Z_to_bv 64 l1); C8 g;
        C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  (* [comment removed for export] *)
  #[local] Notation WST pc ra' s3' s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' iovp cnt rem m1 :=
    (MSsvc (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 l) (Z_to_bv 64 Fa)
                (Z_to_bv 64 fd) (Z_to_bv 64 iovp) (Z_to_bv 64 cnt) a3' a4' a5' a6' (Z_to_bv 64 66)
                (Z_to_bv 64 cnt) s3' s4' (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F (Z_to_bv 64 pc) (Z_to_bv 64 66) fc None m1 rom) (only parsing).
  (* [comment removed for export] *)
  #[local] Notation RST pc ra' s4' t0' t1' t2' a1' a2' a3' a4' a5' a6' t3' t4' t5' t6' k iovp cnt rem m1 :=
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 l) (Z_to_bv 64 Fa)
             (Z_to_bv 64 k) a1' a2' a3' a4' a5' a6' (Z_to_bv 64 66)
             (Z_to_bv 64 cnt) (Z_to_bv 64 iovp) s4' (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 pc) fc None m1 rom) (only parsing).

  (* [comment removed for export] *)
  Definition sw1_post (t0 t1 t2 a4 a5 a6 t3 t4 t5 t6 : word) (n0 : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists a3' j m',
      ms' = WST WRITEV_ECALL1 ra (Z_to_bv 64 (if n0 =? 0 then bv_unsigned sp + -88 else bv_unsigned sp + -104)) s4 t0 t1 t2 a3' a4 a5 a6 t3 t4 t5 t6
                (if n0 =? 0 then bv_unsigned sp + -88 else bv_unsigned sp + -104) (if n0 =? 0 then 1 else 2) (n0 + l) m'
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -112)
      /\ WFRAME m' j (mf_buf f) n0 sa l.

  #[using="EFD FDR FAR LO CEIL Clg"] Lemma sw_walk1 : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (n0 wp : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> file_at m Fa f ->
    ro_cells rsegs m SSP_GOT [C8 (Z_to_bv 64 SSP_GUARD)] -> ro_cells rsegs m SSP_GUARD [C8 g] ->
    mf_wbase f = Z_to_bv 64 (mf_buf f) -> mf_wpos f = Z_to_bv 64 wp -> wp = mf_buf f + n0 ->
    0 <= mf_buf f -> mf_buf f + n0 < 2^47 -> 0 <= n0 -> 0 <= sa -> sa + l < 2^47 -> 0 <= l ->
    evt rsegs (sw1_post t0 t1 t2 a4 a5 a6 t3 t4 t5 t6 n0 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fa) (Z_to_bv 64 sa) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_WRITE) fc None m rom).
  Proof.
    intros until wp. intros MI ST FILE GOT CAN WB WP -> B0 B1 N0 S0 S1 L0.
    unfold file_at, file_cells in FILE. unfold SSP_GOT, SSP_GUARD, STDIO_WRITE in *. rewrite WB, WP, EFD in FILE.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 112%nat ST.
    run_to 0x9df20. at_pc 0x9df20.
    replace (mf_buf f + n0 - mf_buf f) with n0 in * by lia.
    azstep. if_cases K; zify_cond K.
    - assert (E0 : n0 = 0) by lia. subst n0.
      run_to 0x9df44. at_pc 0x9df44. rewrite sx32_small by lia.
      rewrite Z.lxor_nilpotent. change (Z.b2z (0 <? 0) + 1) with 1.
      step_ecall. unfold sw1_post. cbn [Z.eqb].
      eexists _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
    - assert (LX : 0 < Z.lxor (mf_buf f + n0) (mf_buf f)).
      { assert (Z.lxor (mf_buf f + n0) (mf_buf f) <> 0) by (intros HH; apply Z.lxor_eq in HH; lia).
        pose proof (proj2 (Z.lxor_nonneg (mf_buf f + n0) (mf_buf f)) ltac:(lia)). lia. }
      run_to 0x9df44. at_pc 0x9df44. rewrite sx32_small by lia.
      replace (Z.b2z (0 <? Z.lxor (mf_buf f + n0) (mf_buf f)) + 1) with 2 by (rewrite (proj2 (Z.ltb_lt _ _) LX); reflexivity).
      step_ecall. unfold sw1_post. replace (n0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      eexists _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.


  Lemma land_ones64 : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
  Proof. intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

  (* [comment removed for export] *)
  Definition swB_post (s3v s4v t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (k cnt rem : Z) (rav : Z) (m1 : word -> option byte)
      : machine_state -> Prop :=
    fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 rav) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 l) (Z_to_bv 64 Fa)
                    (Z_to_bv 64 k) (Z_to_bv 64 (-4095)) (Z_to_bv 64 cnt) a3' a4' a5' a6' (Z_to_bv 64 66)
                    (Z_to_bv 64 cnt) s3v s4v (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 (if k =? rem then 0x9df50 else 0x9dfdc)) fc None m1 rom
      /\ munch [] m1 m1 /\ wmono rsegs m1 m1 /\ mem_inv rsegs m1.

  Lemma sw_retB1 : forall (ra' s3' s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (k iovp cnt rem : Z) (m1 : word -> option byte),
    0 <= k <= rem -> rem <= 2^26 -> mem_inv rsegs m1 ->
    evt rsegs (swB_post s3' s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' k cnt rem 0x9df4c m1)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 l) (Z_to_bv 64 Fa)
               (Z_to_bv 64 k) (Z_to_bv 64 iovp) (Z_to_bv 64 cnt) a3' a4' a5' a6' (Z_to_bv 64 66)
               (Z_to_bv 64 cnt) s3' s4' (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 (WRITEV_ECALL1 + 4)) fc None m1 rom).
  Proof.
    intros until m1. intros KR RR MI1. unfold WRITEV_ECALL1, SSP_GUARD. lit_addrs_goal.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    azstep. run_to 0x98d0c. at_pc 0x98d0c. azstep. if_cases K0; zify_cond K0; [clear K0| exfalso; rewrite ?unsigned_lit in K0 by lia; blia].
    azstep. azstep. if_cases K1; zify_cond K1.
    - apply evt_done. unfold swB_post. replace (k =? rem) with false by (symmetry; apply Z.eqb_neq; lia). split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI1].
    - apply evt_done. unfold swB_post. replace (k =? rem) with true by (symmetry; apply Z.eqb_eq; lia). split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI1].
  Qed.

  Lemma sw_retB2 : forall (s3' s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' ra' : word) (k iovp cnt rem : Z) (m1 : word -> option byte),
    1 <= k <= rem -> rem <= 2^26 -> mem_inv rsegs m1 ->
    evt rsegs (swB_post s4' s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' k cnt rem 0x9dfd4 m1)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 l) (Z_to_bv 64 Fa)
               (Z_to_bv 64 k) (Z_to_bv 64 iovp) (Z_to_bv 64 cnt) a3' a4' a5' a6' (Z_to_bv 64 66)
               (Z_to_bv 64 cnt) s3' s4' (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 (WRITEV_ECALL2 + 4)) fc None m1 rom).
  Proof.
    intros until m1. intros KR RR MI1. unfold WRITEV_ECALL2, SSP_GUARD. lit_addrs_goal.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    azstep. run_to 0x98d0c. at_pc 0x98d0c. azstep. if_cases K0; zify_cond K0; [clear K0| exfalso; rewrite ?unsigned_lit in K0 by lia; blia].
    azstep. azstep. azstep. if_cases K1; zify_cond K1.
    - apply evt_done. unfold swB_post. replace (k =? rem) with true by (symmetry; apply Z.eqb_eq; lia). split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI1].
    - apply evt_done. unfold swB_post. replace (k =? rem) with false by (symmetry; apply Z.eqb_neq; lia). split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI1].
  Qed.

  (* [comment removed for export] *)
  Definition swC_post (t0' t1' t2' a6' t3' t4' t5' t6' : word) (rav : Z) (iovp iovp' cnt' rem' b0' l0' b1' l1' : Z) (j : list byte)
      (m1 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists a3' a4' a5' m',
      ms' = WST WRITEV_ECALL2 (Z_to_bv 64 rav) (Z_to_bv 64 iovp) (Z_to_bv 64 iovp') t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' iovp' cnt' rem' m'
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -112)
      /\ WFRAME m' j b0' l0' b1' l1'.
  #[local] Notation ADVPRE rav k cnt iovp rem s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' m1 :=
      (MS (mkR (Z_to_bv 64 rav) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 l) (Z_to_bv 64 Fa)
               (Z_to_bv 64 k) (Z_to_bv 64 (-4095)) (Z_to_bv 64 cnt) a3' a4' a5' a6' (Z_to_bv 64 66)
               (Z_to_bv 64 cnt) (Z_to_bv 64 iovp) s4' (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x9dfdc) fc None m1 rom) (only parsing).

  #[using="EFD FDR FAR LO CEIL Clg"] Lemma sw_advC2a : forall (s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (rav : Z) (k rem : Z) (m1 : word -> option byte) j b0 l0 b1 l1,
    1 <= k < rem -> rem <= 2^26 -> 0 <= l0 -> 0 <= l1 -> 0 <= b0 -> b0 + l0 < 2^47 -> 0 <= b1 -> b1 + l1 < 2^47 ->
    rem = l0 + l1 -> k <= l0 -> 0 <= rav < 2^64 ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -112) -> WFRAME m1 j b0 l0 b1 l1 -> file_at m1 Fa f ->
    evt rsegs (swC_post t0' t1' t2' a6' t3' t4' t5' t6' rav (bv_unsigned sp + -104) (bv_unsigned sp + -104) 2 (rem - k) (b0 + k) (l0 - k) b1 l1 j m1)
      (ADVPRE rav k 2 (bv_unsigned sp + -104) rem s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' m1).
  Proof.
    intros until l1. intros KR RR L0 L1 B0 B0' B1 B1' REM KLE RAV MI1 ST1 FR FILE. unfold SSP_GUARD, file_at, file_cells in *. rewrite EFD in FILE.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
    azstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. blia. }
    azstep. azstep.
    replace (Z.b2z (l0 <? k)) with 0 by (rewrite (proj2 (Z.ltb_ge _ _) KLE); reflexivity).
    do 5 azstep. rewrite Z.land_0_l. azstep. rewrite ?Z.sub_0_r, ?Z.add_0_r. do 2 azstep.
    azstep. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
    run_to 0x9dfcc. at_pc 0x9dfcc. rewrite sx32_small by lia.
    step_ecall. unfold swC_post, WRITEV_ECALL2, SSP_GUARD.
    eexists _, _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  #[using="EFD FDR FAR LO CEIL Clg"] Lemma sw_advC2b : forall (s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (rav : Z) (k rem : Z) (m1 : word -> option byte) j b0 l0 b1 l1,
    1 <= k < rem -> rem <= 2^26 -> 0 <= l0 -> 0 <= l1 -> 0 <= b0 -> b0 + l0 < 2^47 -> 0 <= b1 -> b1 + l1 < 2^47 ->
    rem = l0 + l1 -> l0 < k -> 0 <= rav < 2^64 ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -112) -> WFRAME m1 j b0 l0 b1 l1 -> file_at m1 Fa f ->
    evt rsegs (swC_post t0' t1' t2' a6' t3' t4' t5' t6' rav (bv_unsigned sp + -104) (bv_unsigned sp + -88) 1 (rem - k) b0 l0 (b1 + (k - l0)) (l1 - (k - l0)) j m1)
      (ADVPRE rav k 2 (bv_unsigned sp + -104) rem s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' m1).
  Proof.
    intros until l1. intros KR RR L0 L1 B0 B0' B1 B1' REM KGT RAV MI1 ST1 FR FILE. unfold SSP_GUARD, file_at, file_cells in *. rewrite EFD in FILE.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
    azstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. blia. }
    azstep. azstep.
    replace (Z.b2z (l0 <? k)) with 1 by (rewrite (proj2 (Z.ltb_lt _ _) KGT); reflexivity).
    do 5 azstep. rewrite land_ones64 by lia. do 3 azstep.
    azstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    azstep. run_to 0x9dfcc. at_pc 0x9dfcc. rewrite sx32_small by lia.
    step_ecall. unfold swC_post, WRITEV_ECALL2, SSP_GUARD.
    eexists _, _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  #[using="EFD FDR FAR LO CEIL Clg"] Lemma sw_advC1 : forall (s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (rav : Z) (k rem : Z) (m1 : word -> option byte) j b0 l0 b1 l1,
    1 <= k < rem -> rem <= 2^26 -> 0 <= l1 -> 0 <= b1 -> b1 + l1 < 2^47 ->
    rem = l1 -> 0 <= rav < 2^64 ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -112) -> WFRAME m1 j b0 l0 b1 l1 -> file_at m1 Fa f ->
    evt rsegs (swC_post t0' t1' t2' a6' t3' t4' t5' t6' rav (bv_unsigned sp + -88) (bv_unsigned sp + -88) 1 (rem - k) b0 l0 (b1 + k) (l1 - k) j m1)
      (ADVPRE rav k 1 (bv_unsigned sp + -88) rem s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' m1).
  Proof.
    intros until l1. intros KR RR L1 B1 B1' REM RAV MI1 ST1 FR FILE. unfold SSP_GUARD, file_at, file_cells in *. rewrite EFD in FILE.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
    azstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. blia. }
    azstep. azstep.
    assert (GE : k <= l1) by lia. replace (Z.b2z (l1 <? k)) with 0 by (rewrite (proj2 (Z.ltb_ge _ _) GE); reflexivity).
    do 5 azstep. rewrite Z.land_0_l. azstep. rewrite ?Z.sub_0_r, ?Z.add_0_r. do 2 azstep.
    azstep. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
    run_to 0x9dfcc. at_pc 0x9dfcc. rewrite sx32_small by lia.
    step_ecall. unfold swC_post, WRITEV_ECALL2, SSP_GUARD.
    eexists _, _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition swD_post (m1 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 l) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' rom
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fa, Fa + 152)] m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ file_at m' Fa (mf_set_w f (Z_to_bv 64 (mf_buf f)) (Z_to_bv 64 (mf_buf f)) (Z_to_bv 64 (mf_buf f + mf_bufsize f))).

  #[using="EFD FAR LO CEIL fd Clg"] Lemma sw_doneD : forall (s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (rav k cnt iovp : Z) (m1 : word -> option byte) j b0 l0 b1 l1,
    0 <= mf_buf f -> mf_buf f + mf_bufsize f < 2^47 -> 0 <= mf_bufsize f -> 0 <= k <= 2^26 ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -112) -> WFRAME m1 j b0 l0 b1 l1 -> file_at m1 Fa f ->
    ro_cells rsegs m1 SSP_GUARD [C8 g] ->
    evt rsegs (swD_post m1)
      (MS (mkR (Z_to_bv 64 rav) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 l) (Z_to_bv 64 Fa)
               (Z_to_bv 64 k) (Z_to_bv 64 (-4095)) (Z_to_bv 64 cnt) a3' a4' a5' a6' (Z_to_bv 64 66)
               (Z_to_bv 64 cnt) (Z_to_bv 64 iovp) s4' (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 k) s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x9df50) fc None m1 rom).
  Proof.
    intros until l1. intros B0 B1 B2 KR MI1 ST1 FR FILE CAN. unfold SSP_GUARD, file_at, file_cells in *. rewrite EFD in FILE.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (Fa, Fa + 152)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
    run_to 0x9df74. at_pc 0x9df74. azstep. br_not_taken.
    run_to 0x9df9c. at_pc 0x9df9c.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -112) _ |- _ => release_frame H ST1 (bv_unsigned sp) end.
    azstep. apply evt_done. unfold swD_post, file_at, file_cells, mf_set_w. cbn [mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148].
    rewrite EFD.
    hot_eexists_all. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.
End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold sw1_post, swB_post, swC_post, swD_post, SSP_GUARD, WRITEV_ECALL1, WRITEV_ECALL2 in H.

Section Loop.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z) (Fa : Z) (f : mfile) (g : word) (sa l : Z) (fd : Z)
            (A : AS) (v0 : mem) (md0 : Model) (K : TSet).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 112 <= bv_unsigned sp.
  Hypothesis FAR : 0xaa000 <= Fa /\ Fa + 152 <= 0x608418.
  Hypothesis IMGC : img_client (L:=LPA) Fa (Fa + 152).
  Hypothesis FDR : fd = 1 \/ fd = 2.
  Hypothesis EFD : mf_fd f = fd.
  Hypothesis BUF : 0 <= mf_buf f /\ mf_buf f + mf_bufsize f < 2^47 /\ 0 <= mf_bufsize f.
  Hypothesis HK : K [].
  Hypothesis SPHI : bv_unsigned sp <= 2^47.   (* [comment removed for export] *)
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation W0 := ([(bv_unsigned sp - 112, bv_unsigned sp); (Fa, Fa + 152)]).
  #[local] Notation WFRAME m1 j b0 l0 b1 l1 :=
    (rw_cells rsegs m1 (bv_unsigned sp + -112)
       [CB 8 j; C8 (Z_to_bv 64 b0); C8 (Z_to_bv 64 l0); C8 (Z_to_bv 64 b1); C8 (Z_to_bv 64 l1); C8 g;
        C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  (* [comment removed for export] *)
  Hypothesis DONEK : forall m' md', ainv A m' md' -> m_fs md' = m_fs md0 -> m_fds md' = m_fds md0 -> m_halted md' = None ->
      mem_inv rsegs (aview A m') -> stk rsegs (aview A m') lo (bv_unsigned sp) ->
      munch W0 v0 (aview A m') -> wmono rsegs v0 (aview A m') ->
      file_at (aview A m') Fa (mf_set_w f (Z_to_bv 64 (mf_buf f)) (Z_to_bv 64 (mf_buf f)) (Z_to_bv 64 (mf_buf f + mf_bufsize f))) ->
      forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      srealizes (cl_segs LPA)
        (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 l) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' rom) md') K.

  (* [comment removed for export] *)
  Lemma view_bytes_real' : forall m md p bs n,
    ainv A m md -> bytes_at rsegs (aview A m) p bs -> (n <= length bs)%nat ->
    rdn rsegs m (Z_to_bv 64 p) n = Some (firstn n bs) /\ bytes_in_hull (ahull A) (Z_to_bv 64 p) n.
  Proof.
    intros m md p bs n AINV PB HN.
    pose proof (bytes_at_rdn rsegs (aview A m) p bs 0 n PB ltac:(lia)) as RD.
    change (skipn 0 bs) with bs in RD. cbn [Z.of_nat] in RD. rewrite Z.add_0_r in RD.
    destruct (view_rdn_real (L:=LPA) A m md _ _ _ AINV RD) as [R1 R2]. split; [| exact R2].
    rewrite <- OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.ov_rdn, Lib.PropExec.ov_rdn. exact R1.
  Qed.

  (* [comment removed for export] *)
  Lemma frame_cell_real : forall m md j b0 l0 b1 l1 (k : nat) v,
    ainv A m md -> WFRAME (aview A m) j b0 l0 b1 l1 ->
    cell_at [CB 8 j; C8 (Z_to_bv 64 b0); C8 (Z_to_bv 64 l0); C8 (Z_to_bv 64 b1); C8 (Z_to_bv 64 l1); C8 g;
             C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] k = Some (C8 v) ->
    rdn rsegs m (Z_to_bv 64 (bv_unsigned sp + -112 + Z.of_nat k)) 8 = Some (word_to_le_bytes 8 v)
    /\ bytes_in_hull (ahull A) (Z_to_bv 64 (bv_unsigned sp + -112 + Z.of_nat k)) 8.
  Proof.
    intros m md j b0 l0 b1 l1 k v AINV FR Hk.
    pose proof (rw_cells_read_at rsegs (aview A m) _ _ k (C8 v) 8%nat _ FR Hk eq_refl eq_refl) as RD. cbn [cbytes] in RD.
    rewrite Lib.PropExec.ov_rdn in RD. unfold wa in RD.
    destruct (view_rdn_real (L:=LPA) A m md _ _ _ AINV RD) as [R1 R2]. split; [| exact R2].
    rewrite <- OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.ov_rdn, Lib.PropExec.ov_rdn. exact R1.
  Qed.

  Lemma bytes_in_hull_join : forall H (a : Z) (n1 n2 : nat),
    0 <= a -> a + Z.of_nat (n1 + n2) <= 2^64 ->
    bytes_in_hull H (Z_to_bv 64 a) n1 -> bytes_in_hull H (Z_to_bv 64 (a + Z.of_nat n1)) n2 -> bytes_in_hull H (Z_to_bv 64 a) (n1 + n2).
  Proof.
    intros H a n1 n2 Ha Hn X Y k Hk. destruct (Nat.lt_ge_cases k n1) as [LT|GE].
    - exact (X k LT).
    - specialize (Y (k - n1)%nat ltac:(lia)). revert Y. unfold woff.
      match goal with |- in_hullb _ (bv_unsigned ?u) = true -> in_hullb _ (bv_unsigned ?w) = true => replace u with w; [intros Y; exact Y|] end.
      rewrite !unsigned_lit by lia.
      match goal with |- Z_to_bv 64 ?x = Z_to_bv 64 ?y => replace y with x by lia; reflexivity end.
  Qed.

  (* [comment removed for export] *)
  #[using="DONEK SPHI HK BUF EFD FDR IMGC FAR LO CEIL"] Lemma sw_loop : forall (n : nat) (REST : list byte), (length REST <= n)%nat ->
    forall (pcv : Z) (ra' s3' s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (iovp cnt rem : Z)
           (m : mem) (md : Model) (j : list byte) (b0 l0 b1 l1 : Z),
    ((pcv = WRITEV_ECALL1 /\ s3' = Z_to_bv 64 iovp) \/ (pcv = WRITEV_ECALL2 /\ s4' = Z_to_bv 64 iovp)) ->
    ainv A m md -> mem_inv rsegs (aview A m) ->
    fd_lookup (m_fds md) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) -> m_fs md = m_fs md0 -> m_fds md = m_fds md0 ->
    stk rsegs (aview A m) lo (bv_unsigned sp + -112) -> WFRAME (aview A m) j b0 l0 b1 l1 -> file_at (aview A m) Fa f ->
    ro_cells rsegs (aview A m) SSP_GUARD [C8 g] ->
    0 <= l0 -> 0 <= l1 -> 0 <= b0 -> b0 + l0 < 2^47 -> 0 <= b1 -> b1 + l1 < 2^47 ->
    rem = Z.of_nat (length REST) -> 1 <= rem <= 2^26 -> 0 <= bv_unsigned ra' < 2^64 ->
    (b0 + l0 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= b0) -> (b1 + l1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= b1) ->
    (   (cnt = 2 /\ iovp = bv_unsigned sp + -104 /\ rem = l0 + l1 /\
         exists B0 B1, REST = B0 ++ B1 /\ bytes_at rsegs (aview A m) b0 B0 /\ bytes_at rsegs (aview A m) b1 B1 /\
                       Z.of_nat (length B0) = l0 /\ Z.of_nat (length B1) = l1)
     \/ (cnt = 1 /\ iovp = bv_unsigned sp + -88 /\ rem = l1 /\ bytes_at rsegs (aview A m) b1 REST)) ->
    munch W0 v0 (aview A m) -> wmono rsegs v0 (aview A m) ->
    srealizes (cl_segs LPA)
      (mkCfg (MSsvc (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 l) (Z_to_bv 64 Fa)
                         (Z_to_bv 64 fd) (Z_to_bv 64 iovp) (Z_to_bv 64 cnt) a3' a4' a5' a6' (Z_to_bv 64 66)
                         (Z_to_bv 64 cnt) s3' s4' (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (Z_to_bv 64 pcv) (Z_to_bv 64 66) fc None m rom) md)
      (t_emit (W fd REST) K).
  Proof.
    induction n as [|n IH]; intros REST HN pcv ra' s3' s4' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' iovp cnt rem m md j b0 l0 b1 l1
      PCV AINV MI FDL FS FDS ST FR FILE CAN L0 L1 B0 B0h B1 B1h REM RR RAV SEP0 SEP1 INV MU WM.
    { exfalso. destruct REST; cbn in HN, REM; lia. }
    unfold file_at, file_cells in FILE. unfold SSP_GUARD in CAN.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (as_minv LPA A m md AINV) as [HMI HH].
    (* [comment removed for export] *)
    destruct (frame_cell_real m md j b0 l0 b1 l1 8 (Z_to_bv 64 b0) AINV FR eq_refl) as [RDb0 Hb0].
    destruct (frame_cell_real m md j b0 l0 b1 l1 16 (Z_to_bv 64 l0) AINV FR eq_refl) as [RDl0 Hl0].
    destruct (frame_cell_real m md j b0 l0 b1 l1 24 (Z_to_bv 64 b1) AINV FR eq_refl) as [RDb1 Hb1].
    destruct (frame_cell_real m md j b0 l0 b1 l1 32 (Z_to_bv 64 l1) AINV FR eq_refl) as [RDl1 Hl1].
    replace (bv_unsigned sp + -112 + Z.of_nat 8) with (bv_unsigned sp + -104) in RDb0, Hb0 by lia.
    replace (bv_unsigned sp + -112 + Z.of_nat 16) with (bv_unsigned sp + -104 + 8) in RDl0 by lia.
    replace (bv_unsigned sp + -112 + Z.of_nat 16) with (bv_unsigned sp + -104 + Z.of_nat 8) in Hl0 by lia.
    replace (bv_unsigned sp + -112 + Z.of_nat 24) with (bv_unsigned sp + -88) in RDb1 by lia.
    replace (bv_unsigned sp + -112 + Z.of_nat 24) with (bv_unsigned sp + -104 + Z.of_nat 16) in Hb1 by lia.
    replace (bv_unsigned sp + -112 + Z.of_nat 32) with (bv_unsigned sp + -88 + 8) in RDl1 by lia.
    replace (bv_unsigned sp + -112 + Z.of_nat 32) with (bv_unsigned sp + -104 + Z.of_nat 16 + Z.of_nat 8) in Hl1 by lia.
    pose proof (bytes_in_hull_join _ (bv_unsigned sp + -104) 8 8 ltac:(lia) ltac:(lia) Hb0 Hl0) as H01.
    pose proof (bytes_in_hull_join _ (bv_unsigned sp + -104 + Z.of_nat 16) 8 8 ltac:(lia) ltac:(lia) Hb1 Hl1) as H23.
    pose proof (bytes_in_hull_join _ (bv_unsigned sp + -104) 16 16 ltac:(lia) ltac:(lia) H01 H23) as H0123. cbn [Nat.add] in H01, H23, H0123.
    replace (bv_unsigned sp + -104 + Z.of_nat 16) with (bv_unsigned sp + -88) in H23 by lia.
    (* [comment removed for export] *)
    assert (AFTER : forall (k : nat) md2, (1 <= k)%nat -> (k <= length REST)%nat -> MInv (ahull A) (alhull A) (aeager A) md2 -> same_but_materialized md md2 ->
      srealizes (cl_segs LPA)
        (mkCfg (advance_past_svc (set_gpr0
                  (MSsvc (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 l) (Z_to_bv 64 Fa)
                              (Z_to_bv 64 fd) (Z_to_bv 64 iovp) (Z_to_bv 64 cnt) a3' a4' a5' a6' (Z_to_bv 64 66)
                              (Z_to_bv 64 cnt) s3' s4' (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                         F (Z_to_bv 64 pcv) (Z_to_bv 64 66) fc None m rom) (Z_to_bv 64 (Z.of_nat k)))) md2)
        (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k REST)) K)).
    { intros k md2 Hk1 Hk2 HMI2 SB2.
      pose proof (ainv_mat (L:=LPA) A m md md2 AINV HMI2 SB2) as AINV2.
      pose proof (sbm_io md md2 SB2) as (FS2 & FDS2 & _).
      pose proof (as_minv LPA A m md2 AINV2) as [_ HH2].
      (* [comment removed for export] *)
      assert (CONT : forall (rav : Z) (s4v x5 x6 x7 x13 x14 x15 x16 x28 x29 x30 x31 : word), 0 <= rav < 2^64 ->
        evt (cl_segs LPA) (srz_at_r (cl_segs LPA) (ahull A) (alhull A) (aeager A) m md2 (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k REST)) K))
          (MS (mkR (Z_to_bv 64 rav) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 l) (Z_to_bv 64 Fa)
                   (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (-4095)) (Z_to_bv 64 cnt) x13 x14 x15 x16 (Z_to_bv 64 66)
                   (Z_to_bv 64 cnt) (Z_to_bv 64 iovp) s4v (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 (if Z.of_nat k =? rem then 0x9df50 else 0x9dfdc)) fc None (aview A m) rom)).
      { intros rav s4v x5 x6 x7 x13 x14 x15 x16 x28 x29 x30 x31 RAVR. fold_cl_segs.
        destruct (Z.eqb_spec (Z.of_nat k) rem) as [EK | NK].
        - (* [comment removed for export] *)
          pose proof (munch_refl W0 (aview A m)) as MU2. pose proof (wmono_refl rsegs (aview A m)) as WM2.
          assert (CF2 : client_fpx (L:=LPA) A (aview A m) W0).
          { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
              replace (bv_unsigned sp - (bv_unsigned sp - 112)) with 112 by lia.
              eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
            split; [| exact I]. right. exact IMGC. }
          replace (Z_to_bv 64 rem) with (Z_to_bv 64 (Z.of_nat k)) by (f_equal; lia).
          try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FR); icall (sw_doneD ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fa f g l fd CEIL LO FAR EFD
                   s4v x5 x6 x7 x13 x14 x15 x16 x28 x29 x30 x31 rav (Z.of_nat k) cnt iovp (aview A m) j b0 l0 b1 l1)
            by (first [exact MI | exact ST | exact FR | exact FILE | exact CAN | lia]).
          lazymatch goal with H : stk _ _ lo (bv_unsigned sp) |- _ => rename H into ST9 end.
          lazymatch goal with H : file_at _ Fa _ |- _ => rename H into FILE9 end.
          astopx AINV2 MU2 WM2 CF2.
          pose proof (as_minv LPA A _ _ AINV0) as [_ HH3]. pose proof (sbm_io _ _ SBM) as (FS3 & FDS3 & _).
          rewrite skipn_all2 by lia.
          eapply srz_conseq; [| apply t_eq_sym; apply t_emit_nil_eq; exact HK].
          apply DONEK; [exact AINV0 | rewrite FS3, FS2; exact FS | rewrite FDS3, FDS2; exact FDS | exact HH3 | assumption | exact ST9 | exact MU | exact WM | exact FILE9].
        - (* [comment removed for export] *)
          pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] (aview A m)) as MU3. pose proof (wmono_refl rsegs (aview A m)) as WM3.
          assert (CF3 : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 112, bv_unsigned sp)]).
          { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [lia|]. split; [lia|].
            replace (bv_unsigned sp - (bv_unsigned sp - 112)) with 112 by lia.
            eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
          destruct INV as [(Ecnt & Eiovp & REM2 & B0s & B1s & EREST & PB0 & PB1 & LB0 & LB1) | (Ecnt & Eiovp & REM1 & PB)]; subst cnt iovp.
          + destruct (Z_lt_le_dec l0 (Z.of_nat k)) as [KGT | KLE].
            * (* [comment removed for export] *)
              try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FR); icall (sw_advC2b ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fa f g l fd CEIL LO FAR FDR EFD
                       s4v x5 x6 x7 x13 x14 x15 x16 x28 x29 x30 x31 rav (Z.of_nat k) rem (aview A m) j b0 l0 b1 l1)
                by (first [exact MI | exact ST | exact FR | exact FILE | lia]).
              lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST9 end.
              lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -112) _ |- _ => rename H into FR9 end.
              lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI9 end.
              astop_svcx AINV2 MU3 WM3 CF3.
              pose proof (sbm_io _ _ SBM) as (FS3 & FDS3 & _).
              subst REST. rewrite skipn_app, skipn_all2 by lia. cbn [app].
              eapply (IH (skipn (k - length B0s) B1s) ltac:(rewrite length_skipn; rewrite length_app in Hk2, HN; lia) WRITEV_ECALL2
                        _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -88) 1 (rem - Z.of_nat k) _ _ j b0 l0 (b1 + (Z.of_nat k - l0)) (l1 - (Z.of_nat k - l0)));
                [ right; split; reflexivity
                | exact AINV0 | exact MI9
                | rewrite FDS3, FDS2; exact FDL | rewrite FS3, FS2; exact FS | rewrite FDS3, FDS2; exact FDS
                | exact ST9 | exact FR9 | exact FILE | exact CAN
                | lia | lia | lia | lia | lia | lia
                | rewrite length_skipn; rewrite length_app in Hk2; lia
                | lia
                | rewrite unsigned_lit by lia; lia
                | lia | lia
                | right; split; [reflexivity|]; split; [reflexivity|]; split; [lia|];
                  rewrite <- (firstn_skipn (k - length B0s) B1s) in PB1; apply bytes_at_app in PB1; destruct PB1 as [_ PB1];
                  rewrite length_firstn in PB1;
                  replace (b1 + (Z.of_nat k - l0)) with (b1 + Z.of_nat (Nat.min (k - length B0s) (length B1s))) by (rewrite length_app in Hk2; lia);
                  exact PB1
                | exact MU | exact WM ].
            * (* [comment removed for export] *)
              try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FR); icall (sw_advC2a ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fa f g l fd CEIL LO FAR FDR EFD
                       s4v x5 x6 x7 x13 x14 x15 x16 x28 x29 x30 x31 rav (Z.of_nat k) rem (aview A m) j b0 l0 b1 l1)
                by (first [exact MI | exact ST | exact FR | exact FILE | lia]).
              lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST9 end.
              lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -112) _ |- _ => rename H into FR9 end.
              lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI9 end.
              astop_svcx AINV2 MU3 WM3 CF3.
              pose proof (sbm_io _ _ SBM) as (FS3 & FDS3 & _).
              subst REST. rewrite skipn_app. replace (k - length B0s)%nat with 0%nat by lia. change (skipn 0 B1s) with B1s.
              eapply (IH (skipn k B0s ++ B1s) ltac:(rewrite length_app, length_skipn; rewrite length_app in Hk2, HN; lia) WRITEV_ECALL2
                        _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -104) 2 (rem - Z.of_nat k) _ _ j (b0 + Z.of_nat k) (l0 - Z.of_nat k) b1 l1);
                [ right; split; reflexivity
                | exact AINV0 | exact MI9
                | rewrite FDS3, FDS2; exact FDL | rewrite FS3, FS2; exact FS | rewrite FDS3, FDS2; exact FDS
                | exact ST9 | exact FR9 | exact FILE | exact CAN
                | lia | lia | lia | lia | lia | lia
                | rewrite length_app, length_skipn; rewrite length_app in Hk2; lia
                | lia
                | rewrite unsigned_lit by lia; lia
                | lia | lia
                | left; split; [reflexivity|]; split; [reflexivity|]; split; [lia|];
                  first [ hotw_ex2 (skipn k B0s) B1s | exists (skipn k B0s), B1s ]; split; [reflexivity|];
                  rewrite <- (firstn_skipn k B0s) in PB0; apply bytes_at_app in PB0; destruct PB0 as [_ PB0];
                  rewrite length_firstn in PB0; replace (b0 + Z.of_nat k) with (b0 + Z.of_nat (Nat.min k (length B0s))) by lia;
                  split; [exact PB0|]; split; [exact PB1|]; rewrite length_skipn; split; lia
                | exact MU | exact WM ].
          + (* [comment removed for export] *)
            try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FR); icall (sw_advC1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fa f g l fd CEIL LO FAR FDR EFD
                     s4v x5 x6 x7 x13 x14 x15 x16 x28 x29 x30 x31 rav (Z.of_nat k) rem (aview A m) j b0 l0 b1 l1)
              by (first [exact MI | exact ST | exact FR | exact FILE | lia]).
            lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST9 end.
            lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -112) _ |- _ => rename H into FR9 end.
            lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI9 end.
            astop_svcx AINV2 MU3 WM3 CF3.
            pose proof (sbm_io _ _ SBM) as (FS3 & FDS3 & _).
            eapply (IH (skipn k REST) ltac:(rewrite length_skipn; lia) WRITEV_ECALL2
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -88) 1 (rem - Z.of_nat k) _ _ j b0 l0 (b1 + Z.of_nat k) (l1 - Z.of_nat k));
              [ right; split; reflexivity
              | exact AINV0 | exact MI9
              | rewrite FDS3, FDS2; exact FDL | rewrite FS3, FS2; exact FS | rewrite FDS3, FDS2; exact FDS
              | exact ST9 | exact FR9 | exact FILE | exact CAN
              | lia | lia | lia | lia | lia | lia
              | rewrite length_skipn; lia
              | lia
              | rewrite unsigned_lit by lia; lia
              | lia | lia
              | right; split; [reflexivity|]; split; [reflexivity|]; split; [lia|];
                rewrite <- (firstn_skipn k REST) in PB; apply bytes_at_app in PB; destruct PB as [_ PB];
                rewrite length_firstn in PB; replace (b1 + Z.of_nat k) with (b1 + Z.of_nat (Nat.min k (length REST))) by lia;
                exact PB
              | exact MU | exact WM ]. }
      (* [comment removed for export] *)
      rewrite advance_set_gpr0_MSsvc.
      destruct PCV as [[-> ->] | [-> ->]]; simp_regs.
      - ago AINV2. fold_cl_segs.
        icall (sw_retB1 sp gp tp s7 s8 s9 s10 s11 F fc Fa l ra' _ _ t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' (Z.of_nat k) iovp cnt rem (aview A m))
          by (first [exact MI | lia]).
        apply CONT. lia.
      - ago AINV2. fold_cl_segs.
        icall (sw_retB2 sp gp tp s7 s8 s9 s10 s11 F fc Fa l _ _ t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' ra' (Z.of_nat k) iovp cnt rem (aview A m))
          by (first [exact MI | lia]).
        apply CONT. lia. }
    (* [comment removed for export] *)
    destruct INV as [(-> & -> & REM2 & B0s & B1s & -> & PB0 & PB1 & LB0 & LB1) | (-> & -> & REM1 & PB)].
    - (* [comment removed for export] *)
      destruct (view_bytes_real' m md b0 B0s (length B0s) AINV PB0 ltac:(lia)) as [RB0 HB0]. rewrite firstn_all in RB0.
      destruct (view_bytes_real' m md b1 B1s (length B1s) AINV PB1 ltac:(lia)) as [RB1 HB1]. rewrite firstn_all in RB1.
      unfold W. replace (B0s ++ B1s) with (concat [B0s; B1s]) by (cbn; rewrite app_nil_r; reflexivity).
      eapply (srz_writev_hull (cl_segs LPA) (ahull A) (alhull A) (aeager A) _ md (Z_to_bv 64 66) fd (Z_to_bv 64 (bv_unsigned sp + -104))
                [(Z_to_bv 64 b0, Z_to_bv 64 l0); (Z_to_bv 64 b1, Z_to_bv 64 l1)] [B0s; B1s] K);
        [ reflexivity | exact HH | reflexivity | exact FDL | lia | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia
        | cbn [iov_array]; rewrite !unsigned_lit by lia;
          replace (bv_unsigned sp + -104 + 16 + 8) with (bv_unsigned sp + -88 + 8) by lia; replace (bv_unsigned sp + -104 + 16) with (bv_unsigned sp + -88) by lia;
          OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [exact RDb0 | exact RDl0 | lia | exact RDb1 | exact RDl1 | lia]
        | cbn [iov_bufs]; unfold word_to_nat; rewrite !unsigned_lit by lia; rewrite <- LB0, <- LB1, !Nat2Z.id; split; [exact RB0 | split; [exact RB1 | exact I]]
        | cbn [iovs_total]; rewrite !unsigned_lit by lia; lia
        | cbn [iovs_total]; rewrite !unsigned_lit by lia; lia
        | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite unsigned_lit by lia; unfold TASK_SIZE; lia
        | cbn [iovs_access_okb forallb fst snd]; rewrite !access_okb_intro by (rewrite !unsigned_lit by lia; unfold TASK_SIZE; lia); reflexivity
        | exact HMI | exact H0123
        | intros b' n' [E|[E|[]]]; injection E as <- <-; unfold word_to_nat; rewrite unsigned_lit by lia; [rewrite <- LB0, Nat2Z.id; exact HB0 | rewrite <- LB1, Nat2Z.id; exact HB1]
        | exact HK | ].
      intros k md2 Hk1 Hk2 HMI2 SB2. cbn [concat] in Hk2 |- *. rewrite app_nil_r in Hk2 |- *.
      apply (AFTER k md2 Hk1 Hk2 HMI2 SB2).
    - (* [comment removed for export] *)
      destruct (view_bytes_real' m md b1 REST (length REST) AINV PB ltac:(lia)) as [RB1 HB1]. rewrite firstn_all in RB1.
      unfold W. replace REST with (concat [REST]) by (cbn; rewrite app_nil_r; reflexivity).
      eapply (srz_writev_hull (cl_segs LPA) (ahull A) (alhull A) (aeager A) _ md (Z_to_bv 64 66) fd (Z_to_bv 64 (bv_unsigned sp + -88))
                [(Z_to_bv 64 b1, Z_to_bv 64 l1)] [REST] K);
        [ reflexivity | exact HH | reflexivity | exact FDL | lia | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia
        | cbn [iov_array]; rewrite !unsigned_lit by lia; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [exact RDb1 | exact RDl1 | lia]
        | cbn [iov_bufs]; unfold word_to_nat; rewrite !unsigned_lit by lia; rewrite <- REM1, REM, !Nat2Z.id; split; [exact RB1 | exact I]
        | cbn [iovs_total]; rewrite !unsigned_lit by lia; lia
        | cbn [iovs_total]; rewrite !unsigned_lit by lia; lia
        | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite unsigned_lit by lia; unfold TASK_SIZE; lia
        | cbn [iovs_access_okb forallb fst snd]; rewrite !access_okb_intro by (rewrite !unsigned_lit by lia; unfold TASK_SIZE; lia); reflexivity
        | exact HMI | exact H23
        | intros b' n' [E|[]]; injection E as <- <-; unfold word_to_nat; rewrite unsigned_lit by lia; rewrite <- REM1, REM, Nat2Z.id; exact HB1
        | exact HK | ].
      intros k md2 Hk1 Hk2 HMI2 SB2. cbn [concat] in Hk2 |- *. rewrite app_nil_r in Hk2 |- *.
      apply (AFTER k md2 Hk1 Hk2 HMI2 SB2).
  Qed.
End Loop.

Ltac icall_consts_in H ::= unfold sw1_post, swB_post, swC_post, swD_post, SSP_GUARD, WRITEV_ECALL1, WRITEV_ECALL2 in H.

Section Top.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.

  Lemma stdio_write_ok : stdio_write_stmt.
  Proof.
    unfold stdio_write_stmt. intros until K. cbv zeta.
    intros AINV MI A0 A1 A2 FILE FDR FAlo FAhi IMGC FDL WB WP WPE PB PS LSUM LPOS B0 B1 B2 PLE S0 S1 SEP0 SEP1 [g CAN] GOT ST LO CEIL SPHI HK HKONT.
    unfold STDIO_WRITE_STACK in *. unfold SSP_GUARD in FAhi. subst a0 a1 a2.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof CAN as CAN'. unfold SSP_GUARD in CAN'. pose proof GOT as GOT'. unfold SSP_GOT, SSP_GUARD in GOT'.
    pose proof FILE as FILE'. unfold file_at, file_cells in FILE'.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 112, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [lia|]. split; [lia|].
      eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
    (* [comment removed for export] *)
    ago AINV. fold_cl_segs.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CAN); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_GOT); icall (sw_walk1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fa f g sa (Z.of_nat (length s)) (mf_fd f) CEIL LO
             (conj FAlo FAhi) FDR eq_refl t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (aview A m) (Z.of_nat (length pend)) wp)
      by (first [exact MI | exact ST | exact FILE' | exact GOT' | exact CAN' | exact A0 | exact A1 | exact A2 | exact WB | exact WP | exact WPE | lia]).
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -112) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astop_svcx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _).
    apply (munch_weaken _ [(bv_unsigned sp - 112, bv_unsigned sp); (Fa, Fa + 152)]) in MU; [| unfold sub_fp; cbn [outside]; intros; lia].
    eenough (DK : _).
    { eapply (sw_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fa f g (Z.of_nat (length s)) (mf_fd f) A (aview A m) md K
              CEIL LO (conj FAlo FAhi) IMGC FDR eq_refl (conj B0 (conj B1 B2)) HK SPHI DK
              (length pend + length s)%nat (pend ++ s) ltac:(rewrite length_app; lia) WRITEV_ECALL1
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.of_nat (length pend) + Z.of_nat (length s)) m1 md1 _ (mf_buf f) (Z.of_nat (length pend)) sa (Z.of_nat (length s)));
      [ left; split; [reflexivity|]; destruct (Z.of_nat (length pend) =? 0); reflexivity
      | exact AINV1 | exact MI1
      | rewrite FDS1; exact FDL | exact FS1 | exact FDS1
      | exact ST1 | exact FR1 | exact FILE' | exact CAN'
      | lia | lia | lia | lia | lia | lia
      | rewrite length_app; lia | lia | pose proof (zr_word ra); unfold inr64 in *; lia
      | lia | lia
      | | exact MU | exact WM ].
      (* [comment removed for export] *)
      destruct pend as [|p0 pend'] eqn:EP.
      + cbn [length Z.of_nat Z.eqb]. right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. cbn [app]. exact PS.
      + replace (Z.of_nat (length (p0 :: pend')) =? 0) with false by (symmetry; apply Z.eqb_neq; cbn; lia).
        left. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
        first [ hotw_ex2 (p0 :: pend') s | exists (p0 :: pend'), s ]. split; [reflexivity|]. split; [exact PB|]. split; [exact PS|]. split; reflexivity. }
    (* [comment removed for export] *)
    intros m' md' AINV' FS' FDS' HH' MI' ST' MU' WM' FILE9 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'.
    apply (HKONT m' md' AINV'); [split; [exact FS'| split; [exact FDS'| exact HH']] | exact FILE9 |].
    hot_eexists_all. split; [reflexivity|].
    split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'| exact ST'].
  Qed.

  (* [comment removed for export] *)
  Lemma stdio_write_zero_ok : stdio_write_zero_stmt.
  Proof.
    unfold stdio_write_zero_stmt. intros until K. cbv zeta.
    intros AINV MI A0 A1 A2 FILE FDR FAlo FAhi IMGC FDL WB WP B0 B1 B2 [g CAN] GOT ST LO CEIL SPHI HKONT.
    unfold STDIO_WRITE_STACK in *. unfold SSP_GUARD in FAhi. subst a0 a1 a2.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof CAN as CAN'. unfold SSP_GUARD in CAN'. pose proof GOT as GOT'. unfold SSP_GOT, SSP_GUARD in GOT'.
    pose proof FILE as FILE'. unfold file_at, file_cells in FILE'.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (Fa, Fa + 152)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 112, bv_unsigned sp); (Fa, Fa + 152)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|]. eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
      split; [| exact I]. right. exact IMGC. }
    (* [comment removed for export] *)
    ago AINV. fold_cl_segs. unfold STDIO_WRITE_ENTRY.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CAN); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_GOT); icall (sw_walk1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fa f g 0 0 (mf_fd f) CEIL LO
             (conj FAlo FAhi) FDR eq_refl t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (aview A m) 0 (mf_buf f))
      by (first [exact MI | exact ST | exact FILE' | exact GOT' | exact CAN' | exact WB | exact WP | lia]).
    cbn [Z.eqb] in *.
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -112) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astop_svcx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    pose proof (as_minv LPA A m1 md1 AINV1) as [HMI1 HH1].
    pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _).
    (* [comment removed for export] *)
    destruct (frame_cell_real ra sp s0 s1 s2 s3 s4 s5 s6 g A m1 md1 _ (mf_buf f) 0 0 0 24%nat (Z_to_bv 64 0) AINV1 FR1 eq_refl) as [RD3 BH3].
    destruct (frame_cell_real ra sp s0 s1 s2 s3 s4 s5 s6 g A m1 md1 _ (mf_buf f) 0 0 0 32%nat (Z_to_bv 64 0) AINV1 FR1 eq_refl) as [RD4 BH4].
    change (Z.of_nat 24) with 24 in RD3. change (Z.of_nat 24) with 24 in BH3. change (Z.of_nat 32) with 32 in RD4. change (Z.of_nat 32) with 32 in BH4.
    eapply (srz_writev1_zero_hull rsegs (ahull A) (alhull A) (aeager A)) with (x8 := Z_to_bv 64 66) (fd := mf_fd f) (b1 := Z_to_bv 64 0) (iov := Z_to_bv 64 (bv_unsigned sp + -88));
      [ reflexivity | exact HH1 | reflexivity | rewrite FDS1; exact FDL | lia | reflexivity | reflexivity | reflexivity | reflexivity
      | | | rewrite unsigned_lit by lia; unfold TASK_SIZE; lia | rewrite unsigned_lit by lia; unfold TASK_SIZE; lia | exact HMI1 | | ].
    { cbn [ms_mem]. replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in RD3 by lia. exact RD3. }
    { cbn [ms_mem]. rewrite ?unsigned_lit by lia. replace (bv_unsigned sp + -112 + 32) with (bv_unsigned sp + -88 + 8) in RD4 by lia. exact RD4. }
    { replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in BH3 by lia.
      replace (bv_unsigned sp + -112 + 32) with (bv_unsigned sp + -88 + Z.of_nat 8) in BH4 by lia.
      apply (bytes_in_hull_join _ _ 8 8); [lia | lia | exact BH3 | exact BH4]. }
    intros md2 HMI2 SBM2.
    rewrite advance_set_gpr0_MSsvc. simp_regs.
    pose proof (ainv_mat (L:=LPA) A m1 md1 md2 AINV1 HMI2 SBM2) as AINV2.
    pose proof (sbm_io md1 md2 SBM2) as (FS2 & FDS2 & _).
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (Fa, Fa + 152)] (aview A m1)) as MU2. pose proof (wmono_refl rsegs (aview A m1)) as WM2.
    assert (CF2 : client_fpx (L:=LPA) A (aview A m1) [(bv_unsigned sp - 112, bv_unsigned sp); (Fa, Fa + 152)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
        replace (bv_unsigned sp - (bv_unsigned sp - 112)) with 112 by lia.
        eapply (window_mapped LPA _ lo); [exact ST1 | exact FR1 | cbn; lia | exact CEIL | lia | lia]. }
      split; [| exact I]. right. exact IMGC. }
    ago AINV2. fold_cl_segs. unfold WRITEV_ECALL1.
    icall (sw_retB1 sp gp tp s7 s8 s9 s10 s11 F fc Fa 0 ra _ _ t0 t1 t2 _ a4 a5 a6 t3 t4 t5 t6 0 (bv_unsigned sp + -88) 1 0 (aview A m1))
      by (first [exact MI1 | lia]).
    cbn [Z.eqb] in *.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FR1); icall (sw_doneD ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fa f g 0 (mf_fd f) CEIL LO (conj FAlo FAhi) eq_refl
             _ t0 t1 t2 _ a4 a5 a6 t3 t4 t5 t6 0x9df4c 0 1 (bv_unsigned sp + -88) (aview A m1) _ (mf_buf f) 0 0 0)
      by (first [exact MI1 | exact ST1 | exact FR1 | exact FILE' | exact CAN' | lia | eassumption]).
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST3 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
    lazymatch goal with H : file_at _ _ _ |- _ => rename H into FILE3 end.
    astopx AINV2 MU2 WM2 CF2. rename m0 into m3. rename md0 into md3. rename AINV0 into AINV3.
    pose proof (as_minv LPA A m3 md3 AINV3) as [_ HH3].
    pose proof (sbm_io _ md3 SBM0) as (FS3 & FDS3 & _).
    eapply (HKONT m3 md3 AINV3).
    { split; [| split; [| exact HH3]]. rewrite FS3, FS2, FS1; reflexivity. rewrite FDS3, FDS2, FDS1; reflexivity. }
    { exact FILE3. }
    hot_eexists_all. split; [reflexivity|].
    split. { first [exact MU | eapply munch_trans; [exact MU| exact MU2]]. }
    split. { first [exact WM | eapply wmono_trans; [exact WM| exact WM2]]. }
    split; [exact MI3| exact ST3].
  Qed.
End Top.

