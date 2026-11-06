(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame ITree Nodes Decode.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time Require Import PosixTimers.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog STree Malloc MmNodes KLink CgNode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RMalloc_iface RMalloc_ifaceP HeapSR_iface MallocSR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import SReach SReachTree.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import STRW_tac RSegs RMallocRep RMallocTree RF_am_E F_syscalls.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition P_time : Z := 0x27de80.
Definition P_clock_gettime : Z := 0x27d940.
Definition P_cgt_init : Z := 0x27d9f8.
Definition P_vdsosym : Z := 0x27da80.
Definition A_vdso_func : Z := 0x2dc8a0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amo_aligned_Z : forall wd z, 0 <= z < 2^64 -> z mod amo_bytes wd = 0 -> amo_aligned wd (Z_to_bv 64 z) = true.
Proof. intros wd z Hz Hm. unfold amo_aligned. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
Ltac amo_fix :=
  repeat match goal with
  | |- context [amo_aligned ?wd (Z_to_bv 64 ?z)] =>
      rewrite (amo_aligned_Z wd z) by (first [cbn [amo_bytes]; lia | cbn [amo_bytes]; nia]); cbn [negb]
  end;
  repeat match goal with
  | |- context [Z.eqb ?x ?x] => rewrite (Z.eqb_refl x)
  end;
  cbv beta iota delta [amo_val inval_resv with_resv c_resv].
Ltac astep_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          amo_fix; simp_regs;
          try solve_load; try solve_store; reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
  | None => fail "no instruction at" pc
  end.
Ltac astep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => astep_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vdsosym_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Lemma vdsosym_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo B : Z),
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 112 -> mem_inv rsegs m ->
  evt rsegs (vdsosym_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 P_vdsosym) fc None m (seg_rom rsegs)).
Proof. try hcb. try hsb.
  intros until B. intros AUX HB ST CLO LO MI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AVC & AVL & RND & AB & BAV & AVH & BR & RH & X3 & X4 & X5 & X16 & X6 & X11 & X12 & X23 & XR).
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling, RAUXV_CELL in *. unfold wz in AVC.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold P_vdsosym.
  (* [comment removed for export] *)
  step. carve_frame 112%nat ST. do 13 step.
  (* [comment removed for export] *)
  step. step. step. step.
  (* [comment removed for export] *)
  Ltac key_ld i key HB addr :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (ru64s_read mX _ _ i (wz key) (Z_to_bv 64 addr) HB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end;
    step; try clear RD.
  key_ld 0 3 AVL av.
  (* [comment removed for export] *)
  step. change (bv_eqb (wz 3) (Z_to_bv 64 0)) with false. cbv iota.
  (* [comment removed for export] *)
  Ltac skip key i nkey HB avv :=
    step; change (bv_eqb (wz key) (Z_to_bv 64 33)) with false; cbv iota;
    step;
    key_ld i nkey HB (avv + 8 * i)%Z;
    step; change (negb (bv_eqb (wz nkey) (Z_to_bv 64 0))) with true; cbv iota.
  skip 3 2 4 AVL av. skip 4 4 5 AVL av. skip 5 6 16 AVL av. skip 16 8 6 AVL av. skip 6 10 11 AVL av.
  skip 11 12 12 AVL av. skip 12 14 23 AVL av. skip 23 16 25 AVL av.
  (* [comment removed for export] *)
  step. change (bv_eqb (wz 25) (Z_to_bv 64 33)) with false. cbv iota.
  step. key_ld 18 0 AVL (av + 8 * 18)%Z.
  step. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
  step.
  (* [comment removed for export] *)
  do 17 step.
  release_frame FR ST (bv_unsigned sp).
  unfold vdsosym_post. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cgt_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-38)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' A_vdso_func [C8 (Z_to_bv 64 0)].

Lemma cgt_init_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo B : Z),
  rauxv_ok m B -> bv_unsigned sp <= B ->
  rw_cells rsegs m A_vdso_func [C8 (Z_to_bv 64 P_cgt_init)] ->
  stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 144 -> mem_inv rsegs m ->
  evt rsegs (cgt_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 P_cgt_init) fc None m (seg_rom rsegs)).
Proof. try hcb. try hsb.
  intros until B. intros AUX HB VF ST CLO LO MI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling, A_vdso_func, P_cgt_init in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (0x2dc8a0, 0x2dc8a0 + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  step. carve_frame 32%nat ST. do 9 step.
  (* [comment removed for export] *)
  step.
  assert (AUX1 : rauxv_ok m0 B).
  { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn; lia|]. constructor; [cbn; hcb; lia| constructor]. }
  eapply evt_cut.
  { eapply (vdsosym_spec _ _ gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 lo B AUX1);
      rewrite ?unsigned_lit by lia; [lia| exact ST| exact CLO| lia| exact MI]. }
  intros ms1 PV. unfold vdsosym_post in PV.
  destruct PV as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1).
  rewrite unsigned_lit in MU1, ST1 by lia.
  replace (ret_pc (Z_to_bv 64 2611748)) with (Z_to_bv 64 2611748) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR| exact MU1| exact WM1|]. cbn. lia. }
  assert (VF1 : rw_cells rsegs m1 3000480 [C8 (Z_to_bv 64 2611704)]).
  { eapply rw_cells_transport; [exact VF| exact MU1| exact WM1|]. cbn. hcb. lia. }
  assert (MU' : munch [(bv_unsigned sp - 144, bv_unsigned sp); (3000480, 3000480 + 8)]%Z m m1).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn in Hx |- *. lia. }
  assert (WM' : wmono rsegs m m1) by (eapply wmono_trans; [exact WM| exact WM1]).
  clear MU WM MU1 WM1 FR VF MI ST AUX AUX1.
  (* [comment removed for export] *)
  step. step. step. step. step.
  (* [comment removed for export] *)
  astep. step. if_false. astep. step. if_false. step. if_true.
  (* [comment removed for export] *)
  step. step. step. step. step. step.
  lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -32) _, S : stk rsegs ?mX lo _ |- _ => release_frame H S (bv_unsigned sp) end.
  unfold cgt_init_post, A_vdso_func. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition time_front_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v : word) (F : bvmap 5 word) (fc : bv 32)
    (lo can : Z) (errv : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x12 x13 x14 x15 x16 x28 x29 x30 x31 : word) m1 junk16 junk8,
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 0)
                  (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -48)) x12 x13 x14 x15 x16 (Z_to_bv 64 113)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x27d990) fc None m1 (seg_rom rsegs)
    /\ rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 16 junk16; C8 (Z_to_bv 64 can); C8 s1v; C8 s0v; C8 rav]
    /\ rw_cells rsegs m1 (bv_unsigned sp + -80) [CB 8 junk8; C8 (Z_to_bv 64 RSSP_GUARD); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x27deb0)]
    /\ rw_cells rsegs m1 A_vdso_func [C8 (Z_to_bv 64 0)]
    /\ rw_cells rsegs m1 RGOT_SSP [C8 (Z_to_bv 64 RSSP_GUARD)] /\ rw_cells rsegs m1 RSSP_GUARD [C8 (Z_to_bv 64 can)]
    /\ rw_cells rsegs m1 (errno_addr tp) [C4 errv]
    /\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8)]%Z m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
    /\ stk rsegs m1 lo (bv_unsigned sp + -80).

Lemma time_front : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo B vf can : Z) (errv : word),
  rauxv_ok m B -> bv_unsigned sp <= B ->
  rw_cells rsegs m A_vdso_func [C8 (Z_to_bv 64 vf)] -> (vf = 0 \/ vf = P_cgt_init) ->
  rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RSSP_GUARD)] -> rw_cells rsegs m RSSP_GUARD [C8 (Z_to_bv 64 can)] -> 0 <= can < 2^64 ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> tp = Z_to_bv 64 RATP ->
  stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 224 -> mem_inv rsegs m -> a0 = Z_to_bv 64 0 ->
  evt rsegs (time_front_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 F fc lo can errv m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 P_time) fc None m (seg_rom rsegs)).
Proof. try hcb. try hsb.
  intros until errv. intros AUX HB VF HVF GOT CAN CANR ERR TP ST CLO LO MI A0. subst a0.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling, A_vdso_func, P_cgt_init, RGOT_SSP, RSSP_GUARD, P_time in *.
  assert (ETP : errno_addr tp = RERRNO) by (rewrite TP; unfold errno_addr, RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
  rewrite ETP in ERR. unfold RERRNO in *.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (0x2dc8a0, 0x2dc8a0 + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  step. carve_frame 48%nat ST. do 10 step.
  (* [comment removed for export] *)
  step. lstep. carve_frame 32%nat ST. do 7 lstep.
  assert (FIN : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) mX,
    rw_cells rsegs mX (bv_unsigned sp + -48) [CB 16 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk)))); C8 (Z_to_bv 64 can); C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mX (bv_unsigned sp + -80) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk0))); C8 (Z_to_bv 64 3208376); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2612912)] ->
    rw_cells rsegs mX 3000480 [C8 (Z_to_bv 64 0)] ->
    rw_cells rsegs mX 2994464 [C8 (Z_to_bv 64 3208376)] -> rw_cells rsegs mX 3208376 [C8 (Z_to_bv 64 can)] ->
    rw_cells rsegs mX 3077076 [C4 errv] ->
    munch [(bv_unsigned sp - 224, bv_unsigned sp); (3000480, 3000480 + 8)]%Z m mX -> wmono rsegs m mX -> mem_inv rsegs mX ->
    stk rsegs mX lo (bv_unsigned sp + -80) ->
    evt rsegs (time_front_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 F fc lo can errv m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x27d984) fc None mX (seg_rom rsegs))).
  { intros. (* [comment removed for export] *)
    step. step. step. apply evt_done. unfold time_front_post, A_vdso_func, RGOT_SSP, RSSP_GUARD. rewrite ETP. do 16 eexists. split; [reflexivity|].
    repeat (split; [eassumption|]). eassumption. }
  destruct HVF as [-> | ->].
  - (* [comment removed for export] *)
    step. if_true. eapply FIN; eassumption.
  - (* [comment removed for export] *)
    step. if_false. step. step. step.
    assert (AUX0 : rauxv_ok m0 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn; lia|]. constructor; [cbn; hcb; lia| constructor]. }
    eapply evt_cut.
    { eapply (cgt_init_spec _ _ gp tp t0 t1 t2 _ _ _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 lo B AUX0);
        rewrite ?unsigned_lit by lia; [lia| unfold A_vdso_func, P_cgt_init; exact VF| exact ST| exact CLO| lia| exact MI]. }
    intros ms1 PG. unfold cgt_init_post, A_vdso_func in PG.
    destruct PG as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & VF1).
    rewrite unsigned_lit in MU1, ST1 by lia.
    replace (ret_pc (Z_to_bv 64 2611568)) with (Z_to_bv 64 2611568) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FRa : rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 16 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk)))); C8 (Z_to_bv 64 can); C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR| exact MU1| exact WM1|]. cbn. lia. }
    assert (FRb : rw_cells rsegs m1 (bv_unsigned sp + -80) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk0))); C8 (Z_to_bv 64 3208376); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2612912)]).
    { eapply rw_cells_transport; [exact FR0| exact MU1| exact WM1|]. cbn. lia. }
    assert (GOT1 : rw_cells rsegs m1 2994464 [C8 (Z_to_bv 64 3208376)]) by (eapply rw_cells_transport; [exact GOT| exact MU1| exact WM1|]; cbn; hcb; lia).
    assert (CAN1 : rw_cells rsegs m1 3208376 [C8 (Z_to_bv 64 can)]) by (eapply rw_cells_transport; [exact CAN| exact MU1| exact WM1|]; cbn; hcb; lia).
    assert (ERR1 : rw_cells rsegs m1 3077076 [C4 errv]) by (eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]; cbn; hcb; lia).
    assert (MU' : munch [(bv_unsigned sp - 224, bv_unsigned sp); (3000480, 3000480 + 8)]%Z m m1).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn in Hx |- *. lia. }
    assert (WM' : wmono rsegs m m1) by (eapply wmono_trans; [exact WM| exact WM1]).
    clear MU WM MU1 WM1 FR FR0 GOT CAN ERR VF MI ST AUX AUX0.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit_wrap. vm_compute. discriminate. }
    step. step. if_cases K1; zify_cond K1. 2:{ exfalso. revert K1. rewrite ?unsigned_lit_wrap. vm_compute. discriminate. }
    eapply FIN; eassumption.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dec_cg (tp : Z) (rsp : resp) : option (list byte) :=
  if no_cc rsp then match rsp with
  | mkEffectU r [(a, bs)] [] [] _ _ =>
      if (bv_unsigned r =? 0) && bv_eqb a (Z_to_bv 64 tp) && (Z.of_nat (length bs) =? 16) then Some bs else None
  | _ => None
  end else None.

Lemma dec_cg_Some : forall tp rsp bs, dec_cg tp rsp = Some bs -> rsp = mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 tp, bs)] [] /\ length bs = 16%nat.
Proof.
  intros tp [r ws zs us cs ci] bs H. unfold dec_cg in H. dec_cc cs ci H.
  destruct ws as [|[a0 bs0] [|? ?]]; try discriminate. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. destruct (bv_eqb a0 (Z_to_bv 64 tp)) eqn:EA; [|discriminate].
  destruct (Z.eqb_spec (Z.of_nat (length bs0)) 16); [|discriminate]. cbn [andb] in H. injection H as ->.
  apply bv_eqb_eq in EA. subst a0. split; [| lia]. f_equal. apply bv_eq. rewrite unsigned_lit by lia. exact e.
Qed.

Lemma dec_cg_nstep : forall tp mo rsp mo' evs, cg_nstep (CGRealtime tp) mo rsp mo' evs ->
  exists bs, dec_cg tp rsp = Some bs /\ realtime_ok_b bs = true /\ mo' = mo /\ evs = [].
Proof.
  intros tp mo rsp mo' evs (-> & -> & bs & Hbs & ->). exists bs. pose proof (realtime_ok_length bs Hbs) as L.
  split; [| auto]. unfold dec_cg. cbn [no_cc eff_copies eff_copyins]. rewrite unsigned_lit by lia. rewrite L.
  replace (bv_eqb (Z_to_bv 64 tp) (Z_to_bv 64 tp)) with true by (symmetry; apply bv_eqb_eq; reflexivity). reflexivity.
Qed.

Definition TIME_STACK : Z := 224.

Section Iface.
  Variable H : HeapSR_iface.hsr.
  (* [comment removed for export] *)
  Definition time_sr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list RMalloc_iface_stmt.block) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 (tv : word) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 tv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ HeapSR_iface.hs_KREL H s (cfg_model c) /\ HeapSR_iface.hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv] /\ HeapSR_iface.hs_rauxv_ok H m' B /\ HeapSR_iface.hs_RHEAP H s LB m'
      /\ munch [(bv_unsigned sp - TIME_STACK, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8); (errno_addr tp, errno_addr tp + 4)]%Z m m' /\ wmono rsegs m m'
      /\ rw_cells rsegs m' A_vdso_func [C8 (Z_to_bv 64 0)].

  Definition time_sr_stmt_at (entry stack : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list RMalloc_iface_stmt.block) (lo B vf : Z) (errv : word) (mo : Model),
      HeapSR_iface.hs_RHEAP H s LB m -> HeapSR_iface.hs_KREL H s mo -> HeapSR_iface.hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      a0 = Z_to_bv 64 0 -> rw_cells rsegs m A_vdso_func [C8 (Z_to_bv 64 vf)] -> (vf = 0 \/ vf = P_cgt_init) ->
      HeapSR_iface.hs_SR H (time_sr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B errv m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)) mo).
  Definition time_sr_stmt : Prop := time_sr_stmt_at P_time TIME_STACK.
End Iface.

(* [comment removed for export] *)
Theorem time_sr : time_sr_stmt HS.
Proof. try hcb. try hsb.
  unfold time_sr_stmt, time_sr_stmt_at. cbn [HeapSR_iface.hs_SR HeapSR_iface.hs_KREL HeapSR_iface.hs_MPRES HeapSR_iface.hs_RHEAP HeapSR_iface.hs_rauxv_ok HS].
  intros until mo. intros HR KMs AUX HB ST CLO LO ERR MI TP A0 VF HVF.
  pose proof KMs as (Lk & CRk & Kk & Bk). unfold TIME_STACK in LO.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof HR as (st & LB0 & PERM & Hst & MR & HI & RZ). pose proof MR as (_ & _ & (G1 & G2 & G3 & G4 & G5 & G6) & _).
  unfold wz in G4, G5.
  set (ts := bv_unsigned sp + -48).
  set (Q := fun (bs : list byte) (ms' : machine_state) => exists t0' t1' t2' (tv : word) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 tv a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
      /\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8); (errno_addr tp, errno_addr tp + 4)]%Z m m' /\ wmono rsegs m m'
      /\ rw_cells rsegs m' A_vdso_func [C8 (Z_to_bv 64 0)]).
  eapply sreach_mono.
  { eapply (impl_sreach_post rsegs (cg_at_node rsegs) cg_nstep cg_nexit mminv cg_safe (cg_node_sound rsegs) mminv_lazy
              (enode (CGRealtime ts) (dec_cg ts)) (epost Q) _ mo (fun r mo' => mo' = mo /\ exists bs, r = Exc.Ok bs)).
    - (* [comment removed for export] *)
      apply impl_enode.
      eapply evt_cut.
      { eapply (time_front ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B vf hcanary errv AUX HB VF HVF);
          [unfold RGOT_SSP, RSSP_GUARD; exact G4| unfold RSSP_GUARD; exact G5| exact HCANB| exact ERR| exact TP| exact ST| exact CLO| exact LO| exact MI| exact A0]. }
      intros ms1 (x1 & x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x28 & x29 & x30 & x31 & m1 & junk16 & junk8 & -> & FRa & FRb & VF1 & GOT1 & CAN1 & ERR1 & MU1 & WM1 & MI1 & ST1).
      fold ts in FRa. unfold A_vdso_func, RGOT_SSP, RSSP_GUARD in *.
      assert (ETP : errno_addr tp = RERRNO) by (rewrite TP; unfold errno_addr, RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
      rewrite ETP in ERR1. unfold RERRNO in ERR1.
      (* [comment removed for export] *)
      step_ecall. split.
      { unfold cg_at_node. at_node_red. split_spine; try reflexivity.
        apply (rw_cells_wr_at rsegs _ _ _ 16 FRa). cbn [cells_size csize]. lia. }
      intros rsp bs Hdec. apply dec_cg_Some in Hdec as [-> L16].
      destruct (rrw_cells_app_split _ _ [CB 16 junk16] [C8 (Z_to_bv 64 hcanary); C8 s1; C8 s0; C8 ra] FRa) as [FR16 FRr].
      cbn [cells_size csize Nat.add] in FRr. replace (ts + Z.of_nat 16) with (bv_unsigned sp + -32) in FRr by (subst ts; lia). clear FRa.
      subst ts. sys_nret. rewrite L16 in FR16. change (16 - 16)%nat with 0%nat in FR16.
      (* [comment removed for export] *)
      step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. revert K1. rewrite ?unsigned_lit_wrap. vm_compute. discriminate. }
      step. step.
      eapply evt_cut.
      { eapply (sysret_spec _ _ gp tp); rewrite ?unsigned_lit by lia; [exact ST1| rewrite ETP; unfold RERRNO; exact ERR1| exact MI1| lia| rewrite ETP; unfold RERRNO; hcb; lia| rewrite TP; unfold RATP; rewrite unsigned_lit by lia; lia]. }
      intros ms2 PS. unfold sysret_post in PS.
      destruct PS as (v0 & v1 & v2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2).
      rewrite unsigned_lit in MU2, ST2 by lia. rewrite ETP in MU2, ERR2. unfold RERRNO in MU2, ERR2.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_small in * by (rewrite unsigned_lit by lia; lia).
      replace (ret_pc (Z_to_bv 64 0x27d9b0)) with (Z_to_bv 64 0x27d9b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FR16' : rw_cells rsegs m2 (bv_unsigned sp + -48) [CB 16 bs; CB 0 (skipn 16 junk16)]) by (eapply rw_cells_transport; [exact FR16| exact MU2| exact WM2|]; cbn; hcb; lia).
      assert (FRr' : rw_cells rsegs m2 (bv_unsigned sp + -32) [C8 (Z_to_bv 64 hcanary); C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact FRr| exact MU2| exact WM2|]; cbn; hcb; lia).
      assert (FRb' : rw_cells rsegs m2 (bv_unsigned sp + -80) [CB 8 junk8; C8 (Z_to_bv 64 RSSP_GUARD); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2612912)]) by (eapply rw_cells_transport; [exact FRb| exact MU2| exact WM2|]; cbn; hcb; lia).
      assert (VF2 : rw_cells rsegs m2 3000480 [C8 (Z_to_bv 64 0)]) by (eapply rw_cells_transport; [exact VF1| exact MU2| exact WM2|]; cbn; hcb; lia).
      assert (CAN2 : rw_cells rsegs m2 3208376 [C8 (Z_to_bv 64 hcanary)]) by (eapply rw_cells_transport; [exact CAN1| exact MU2| exact WM2|]; cbn; hcb; lia).
      assert (MU3 : munch [(bv_unsigned sp - 224, bv_unsigned sp); (3000480, 3000480 + 8); (3077076, 3077076 + 4)]%Z m m2).
      { eapply munch_trans; [| eapply munch_weaken; [| exact MU2]; intros x Hx; cbn in Hx |- *; hcb; lia].
        eapply munch_weaken; [| exact MU1]. intros x Hx; cbn in Hx |- *; lia. }
      assert (WM3 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1| exact WM2]).
      clear MU1 WM1 MU2 WM2 FR16 FRr FRb VF1 CAN1 ERR1 ST1 MI1.
      (* [comment removed for export] *)
      step. step. step. step. step. step.
      (* [comment removed for export] *)
      unfold RSSP_GUARD. step. step. if_true. step. step. step. if_cases KC; zify_cond KC. { exfalso. apply KC. reflexivity. }
      step. step. step. step. step.
      release_frame FRb' ST2 (bv_unsigned sp + -48). release_frame FR16' ST2 (bv_unsigned sp + -32). release_frame FRr' ST2 (bv_unsigned sp).
      apply evt_done. subst Q. cbv beta. do 16 eexists. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|].
      split; [rewrite ETP; unfold RERRNO; exact ERR2|]. unfold A_vdso_func. rewrite ETP. unfold RERRNO. split; [exact MU3|]. split; [exact WM3| exact VF2].
    - exact (kb_halt _ _ _ Kk).
    - exact (kb_minv _ _ _ Kk).
    - cbn. split; [exact I|]. intros rsp mo' evs NS. destruct (dec_cg ts rsp); exact I.
    - cbn. split; [intros code mo' X; exact X|]. intros rsp mo' evs NS. destruct (dec_cg_nstep _ _ _ _ _ NS) as (bs & D & _ & -> & ->). rewrite D. cbn. auto.
    - intros r mo' TP'. cbn in TP'. destruct TP' as (rsp & mo1 & evs & tr' & NS & TP' & _).
      destruct (dec_cg_nstep _ _ _ _ _ NS) as (bs & D & _ & -> & ->). rewrite D in TP'. cbn in TP'. destruct TP' as (<- & -> & _). split; [reflexivity| exists bs; reflexivity]. }
  cbv beta. intros cf (r & HQ & (EMO & bs & ->) & _ & _). cbn [epost] in HQ. destruct cf as [msf mof]. cbn in HQ, EMO |- *. subst mof.
  destruct HQ as (u0 & u1 & u2 & tv & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & Ems & MI3 & ST3 & ERR3 & MU & WM & VF3).
  unfold time_sr_post, TIME_STACK. exists u0, u1, u2, tv, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m'.
  split; [exact Ems|]. split; [exact KMs|]. split; [apply vm_only_refl|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|].
  assert (ETP : errno_addr tp = RERRNO) by (rewrite TP; unfold errno_addr, RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
  rewrite ETP in MU. unfold A_vdso_func, RERRNO in MU.
  split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. hcb.
           constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
  split. { eapply RHEAP_frame_proof; [exact HR| exact MU| exact WM|]. hcb. unfold rclient_write_ok, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP.
           constructor; [left; cbn; lia|]. constructor; [right; left; cbn; lia|]. constructor; [right; left; cbn; lia| constructor]. }
  split; [rewrite ETP; unfold A_vdso_func, RERRNO; exact MU|]. split; [exact WM| exact VF3].
Qed.
End HCW.
